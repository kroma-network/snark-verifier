use std::{
    fs::{self, File},
    io::BufWriter,
    path::Path,
};

use crate::{
    circuit_ext::CircuitExt,
    file_io::{read_pk, read_snark},
    read_instances,
    types::{PoseidonTranscript, POSEIDON_SPEC},
    write_instances, Snark,
};

#[cfg(feature = "display")]
use ark_std::end_timer;
#[cfg(feature = "display")]
use ark_std::start_timer;
use halo2_base::halo2_proofs::{
    bn254::{
        GWCProver, ProvingKey as TachyonProvingKey, SHPlonkProver,
        SnarkVerifierPoseidonWrite as TachyonPoseidonWrite, TachyonProver,
    },
    consts::TranscriptType,
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::{
        create_proof, keygen_pk, keygen_vk, tachyon::create_proof as tachyon_create_proof,
        verify_proof, Circuit, ProvingKey, VerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver, Prover, Verifier},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            msm::DualMSM,
            multiopen::{ProverGWC, ProverSHPLONK, VerifierGWC, VerifierSHPLONK},
            strategy::{AccumulatorStrategy, GuardKZG, SingleStrategy},
        },
        LagrangeCoeff, Polynomial, VerificationStrategy,
    },
    rng::SerializableRng,
    transcript::TranscriptReadBuffer,
    SerdeFormat,
};
use itertools::Itertools;
use rand::Rng;
use snark_verifier::{
    loader::native::NativeLoader,
    system::halo2::{compile, Config},
};

#[allow(clippy::let_and_return)]
pub fn gen_pk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>, // TODO: read pk without params
    circuit: &C,
    path: Option<&Path>,
) -> ProvingKey<G1Affine> {
    if let Some(path) = path {
        if let Ok(pk) = read_pk::<C>(path) {
            return pk;
        }
    }
    #[cfg(feature = "display")]
    let pk_time = start_timer!(|| "Generating vkey & pkey");

    let vk = keygen_vk(params, circuit).unwrap();
    let pk = keygen_pk(params, vk, circuit).unwrap();

    #[cfg(feature = "display")]
    end_timer!(pk_time);

    if let Some(path) = path {
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| format!("Writing pkey to {path:?}"));

        path.parent().and_then(|dir| fs::create_dir_all(dir).ok()).unwrap();
        let mut f = BufWriter::new(File::create(path).unwrap());
        pk.write(&mut f, SerdeFormat::RawBytesUnchecked).unwrap();

        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    pk
}

/// Generates a native proof using either SHPLONK or GWC proving method. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof<'params, C, P, V>(
    // TODO: pass Option<&'params ParamsKZG<Bn256>> but hard to get lifetimes to work with `Cow`
    params: &'params ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    rng: &mut (impl Rng + Send),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error>
where
    C: Circuit<Fr>,
    P: Prover<'params, KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    /*
    #[cfg(debug_assertions)]
    {
        use halo2_proofs::poly::commitment::Params;
        halo2_proofs::dev::MockProver::run(params.k(), &circuit, instances.clone())
            .unwrap()
            .assert_satisfied_par();
    }
    */

    if let Some((instance_path, proof_path)) = path {
        let cached_instances = read_instances(instance_path);
        if matches!(cached_instances, Ok(tmp) if tmp == instances) && proof_path.exists() {
            #[cfg(feature = "display")]
            let read_time = start_timer!(|| format!("Reading proof from {proof_path:?}"));

            let proof = fs::read(proof_path).unwrap();

            #[cfg(feature = "display")]
            end_timer!(read_time);
            return Ok(proof);
        }
    }

    let instances = instances.iter().map(Vec::as_slice).collect_vec();

    #[cfg(feature = "display")]
    let proof_time = start_timer!(|| "Create proof");

    let mut transcript =
        PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(vec![], POSEIDON_SPEC.clone());
    create_proof::<_, P, _, _, _, _>(params, pk, &[circuit], &[&instances], rng, &mut transcript)?;
    let proof = transcript.finalize();

    #[cfg(feature = "display")]
    end_timer!(proof_time);

    if let Some((instance_path, proof_path)) = path {
        write_instances(&instances, instance_path);
        fs::write(proof_path, &proof).unwrap();
    }

    let verification_ok = {
        let mut transcript_read = PoseidonTranscript::<NativeLoader, &[u8]>::new(proof.as_slice());
        VerificationStrategy::<_, V>::finalize(verify_proof::<_, V, _, _, _>(
            params.verifier_params(),
            pk.get_vk(),
            AccumulatorStrategy::new(params.verifier_params()),
            &[instances.as_slice()],
            &mut transcript_read,
        )?)
    };
    if !verification_ok {
        return Err(halo2_base::halo2_proofs::plonk::Error::ConstraintSystemFailure);
    }

    Ok(proof)
}

/// Generates a native proof using original Plonk (GWC '19) multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof_gwc<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    rng: &mut (impl Rng + Send),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error> {
    gen_proof::<C, ProverGWC<_>, VerifierGWC<_>>(params, pk, circuit, instances, rng, path)
}

/// Generates a native proof using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path` is specified.
pub fn gen_proof_shplonk<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    rng: &mut (impl Rng + Send),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error> {
    gen_proof::<C, ProverSHPLONK<_>, VerifierSHPLONK<_>>(params, pk, circuit, instances, rng, path)
}

/// Generates a native proof using either SHPLONK or GWC proving method. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof_tachyon<'params, C, P, V>(
    // TODO: pass Option<&'params ParamsKZG<Bn256>> but hard to get lifetimes to work with `Cow`
    params: &'params ParamsKZG<Bn256>,
    prover: &mut P,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    fixed_values: Vec<Polynomial<Fr, LagrangeCoeff>>,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error>
where
    C: Circuit<Fr>,
    P: TachyonProver<KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    /*
    #[cfg(debug_assertions)]
    {
        use halo2_proofs::poly::commitment::Params;
        halo2_proofs::dev::MockProver::run(params.k(), &circuit, instances.clone())
            .unwrap()
            .assert_satisfied_par();
    }
    */

    if let Some((instance_path, proof_path)) = path {
        let cached_instances = read_instances(instance_path);
        if matches!(cached_instances, Ok(tmp) if tmp == instances) && proof_path.exists() {
            #[cfg(feature = "display")]
            let read_time = start_timer!(|| format!("Reading proof from {proof_path:?}"));

            let proof = fs::read(proof_path).unwrap();

            #[cfg(feature = "display")]
            end_timer!(read_time);
            return Ok(proof);
        }
    }

    let instances = instances.iter().map(Vec::as_slice).collect_vec();

    #[cfg(feature = "display")]
    let proof_time = start_timer!(|| "Create proof");

    let mut tachyon_pk = {
        let mut pk_bytes: Vec<u8> = vec![];
        pk.write_including_cs(&mut pk_bytes).unwrap();
        TachyonProvingKey::from(pk_bytes.as_slice())
    };
    let proof = {
        let mut transcript = TachyonPoseidonWrite::init(vec![]);
        tachyon_create_proof::<_, _, _, _, _, _>(
            prover,
            &mut tachyon_pk,
            &[circuit],
            &[&instances],
            fixed_values,
            rng.clone(),
            &mut transcript,
        )?;
        let mut proof = transcript.finalize();
        let proof_last = prover.get_proof();
        proof.extend_from_slice(&proof_last);
        proof
    };

    #[cfg(feature = "display")]
    end_timer!(proof_time);

    if let Some((instance_path, proof_path)) = path {
        write_instances(&instances, instance_path);
        fs::write(proof_path, &proof).unwrap();
    }

    let verification_ok = {
        let mut transcript_read = PoseidonTranscript::<NativeLoader, &[u8]>::new(proof.as_slice());
        VerificationStrategy::<_, V>::finalize(verify_proof::<_, V, _, _, _>(
            params.verifier_params(),
            pk.get_vk(),
            AccumulatorStrategy::new(params.verifier_params()),
            &[instances.as_slice()],
            &mut transcript_read,
        )?)
    };
    if !verification_ok {
        return Err(halo2_base::halo2_proofs::plonk::Error::ConstraintSystemFailure);
    }

    Ok(proof)
}

/// Generates a native proof using original Plonk (GWC '19) multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path = Some(instance_path, proof_path)` is specified.
pub fn gen_proof_gwc_tachyon<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    fixed_values: Vec<Polynomial<Fr, LagrangeCoeff>>,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error> {
    let mut prover = {
        let mut params_bytes = vec![];
        params.write(&mut params_bytes).unwrap();
        GWCProver::<KZGCommitmentScheme<Bn256>>::from_params(
            TranscriptType::SnarkVerifierPoseidon as u8,
            params.k,
            params_bytes.as_slice(),
        )
    };
    gen_proof_tachyon::<C, _, VerifierSHPLONK<_>>(
        params,
        &mut prover,
        pk,
        circuit,
        instances,
        fixed_values,
        rng,
        path,
    )
}

/// Generates a native proof using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Caches the instances and proof if `path` is specified.
pub fn gen_proof_shplonk_tachyon<C: Circuit<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
    fixed_values: Vec<Polynomial<Fr, LagrangeCoeff>>,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<(&Path, &Path)>,
) -> Result<Vec<u8>, halo2_base::halo2_proofs::plonk::Error> {
    let mut prover = {
        let mut params_bytes = vec![];
        params.write(&mut params_bytes).unwrap();
        SHPlonkProver::<KZGCommitmentScheme<Bn256>>::from_params(
            TranscriptType::SnarkVerifierPoseidon as u8,
            params.k,
            params_bytes.as_slice(),
        )
    };
    gen_proof_tachyon::<C, _, VerifierSHPLONK<_>>(
        params,
        &mut prover,
        pk,
        circuit,
        instances,
        fixed_values,
        rng,
        path,
    )
}

/// Generates a SNARK using either SHPLONK or GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark<'params, ConcreteCircuit, P, V>(
    params: &'params ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error>
where
    ConcreteCircuit: CircuitExt<Fr>,
    P: Prover<'params, KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    if let Some(path) = &path {
        if let Ok(snark) = read_snark(path) {
            return Ok(snark);
        }
    }
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg()
            .with_num_instance(circuit.num_instance())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );

    let instances = circuit.instances();
    let proof =
        gen_proof::<ConcreteCircuit, P, V>(params, pk, circuit, instances.clone(), rng, None)?;

    let snark = Snark::new(protocol, instances, proof);
    if let Some(path) = &path {
        let f = File::create(path).unwrap();
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| "Write SNARK");
        bincode::serialize_into(f, &snark).unwrap();
        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    Ok(snark)
}

/// Generates a SNARK using GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_gwc<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error> {
    gen_snark::<ConcreteCircuit, ProverGWC<_>, VerifierGWC<_>>(params, pk, circuit, rng, path)
}

/// Generates a SNARK using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_shplonk<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + Send),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error> {
    gen_snark::<ConcreteCircuit, ProverSHPLONK<_>, VerifierSHPLONK<_>>(
        params, pk, circuit, rng, path,
    )
}

/// Generates a SNARK using either SHPLONK or GWC multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_tachyon<'params, ConcreteCircuit, P, V>(
    params: &'params ParamsKZG<Bn256>,
    prover: &mut P,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error>
where
    ConcreteCircuit: CircuitExt<Fr>,
    P: TachyonProver<KZGCommitmentScheme<Bn256>>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    if let Some(path) = &path {
        if let Ok(snark) = read_snark(path) {
            return Ok(snark);
        }
    }
    let protocol = compile(
        params,
        pk.get_vk(),
        Config::kzg()
            .with_num_instance(circuit.num_instance())
            .with_accumulator_indices(ConcreteCircuit::accumulator_indices()),
    );

    let instances = circuit.instances();
    let proof = gen_proof_tachyon::<ConcreteCircuit, P, V>(
        params,
        prover,
        pk,
        circuit,
        instances.clone(),
        pk.fixed_values.clone(),
        rng,
        None,
    )?;

    let snark = Snark::new(protocol, instances, proof);
    if let Some(path) = &path {
        let f = File::create(path).unwrap();
        #[cfg(feature = "display")]
        let write_time = start_timer!(|| "Write SNARK");
        bincode::serialize_into(f, &snark).unwrap();
        #[cfg(feature = "display")]
        end_timer!(write_time);
    }
    Ok(snark)
}

/// Generates a SNARK using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_gwc_tachyon<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error> {
    let mut prover = {
        let mut params_bytes = vec![];
        params.write(&mut params_bytes).unwrap();
        GWCProver::<KZGCommitmentScheme<Bn256>>::from_params(
            TranscriptType::SnarkVerifierPoseidon as u8,
            params.k,
            params_bytes.as_slice(),
        )
    };
    gen_snark_tachyon::<ConcreteCircuit, _, VerifierGWC<_>>(
        params,
        &mut prover,
        pk,
        circuit,
        rng,
        path,
    )
}

/// Generates a SNARK using SHPLONK multi-open scheme. Uses Poseidon for Fiat-Shamir.
///
/// Tries to first deserialize from / later serialize the entire SNARK into `path` if specified.
/// Serialization is done using `bincode`.
pub fn gen_snark_shplonk_tachyon<ConcreteCircuit: CircuitExt<Fr>>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: ConcreteCircuit,
    rng: &mut (impl Rng + SerializableRng + Send + Clone),
    path: Option<impl AsRef<Path>>,
) -> Result<Snark, halo2_base::halo2_proofs::plonk::Error> {
    let mut prover = {
        let mut params_bytes = vec![];
        params.write(&mut params_bytes).unwrap();
        SHPlonkProver::<KZGCommitmentScheme<Bn256>>::from_params(
            TranscriptType::SnarkVerifierPoseidon as u8,
            params.k,
            params_bytes.as_slice(),
        )
    };
    gen_snark_tachyon::<ConcreteCircuit, _, VerifierSHPLONK<_>>(
        params,
        &mut prover,
        pk,
        circuit,
        rng,
        path,
    )
}

/// Verifies a native proof using either SHPLONK or GWC proving method. Uses Poseidon for Fiat-Shamir.
///
pub fn verify_snark<'params, ConcreteCircuit, V>(
    verifier_params: &'params ParamsKZG<Bn256>,
    snark: Snark,
    vk: &VerifyingKey<G1Affine>,
) -> bool
where
    ConcreteCircuit: CircuitExt<Fr>,
    V: Verifier<
        'params,
        KZGCommitmentScheme<Bn256>,
        Guard = GuardKZG<'params, Bn256>,
        MSMAccumulator = DualMSM<'params, Bn256>,
    >,
{
    let mut transcript: PoseidonTranscript<_, _> =
        TranscriptReadBuffer::<_, G1Affine, _>::init(snark.proof.as_slice());
    let strategy = SingleStrategy::new(verifier_params);
    let instance_slice = snark.instances.iter().map(|x| &x[..]).collect::<Vec<_>>();
    match verify_proof::<_, V, _, _, _>(
        verifier_params,
        vk,
        strategy,
        &[instance_slice.as_slice()],
        &mut transcript,
    ) {
        Ok(_p) => true,
        Err(_e) => false,
    }
}

/// Verifies a native proof using SHPLONK proving method. Uses Poseidon for Fiat-Shamir.
///
pub fn verify_snark_shplonk<ConcreteCircuit>(
    verifier_params: &ParamsKZG<Bn256>,
    snark: Snark,
    vk: &VerifyingKey<G1Affine>,
) -> bool
where
    ConcreteCircuit: CircuitExt<Fr>,
{
    verify_snark::<ConcreteCircuit, VerifierSHPLONK<_>>(verifier_params, snark, vk)
}

/// Verifies a native proof using GWC proving method. Uses Poseidon for Fiat-Shamir.
///
pub fn verify_snark_gwc<ConcreteCircuit>(
    verifier_params: &ParamsKZG<Bn256>,
    snark: Snark,
    vk: &VerifyingKey<G1Affine>,
) -> bool
where
    ConcreteCircuit: CircuitExt<Fr>,
{
    verify_snark::<ConcreteCircuit, VerifierGWC<_>>(verifier_params, snark, vk)
}

mod test {
    use std::io;

    use crate::types::{PoseidonTranscript, POSEIDON_SPEC};
    use ff::Field;
    use halo2_base::halo2_proofs::{
        bn254::SnarkVerifierPoseidonWrite,
        halo2curves::{
            bn256::{Bn256, Fr, G1Affine},
            group::cofactor::CofactorCurveAffine,
            pairing::Engine,
        },
        transcript::{Challenge255, ChallengeScalar, EncodedChallenge, TranscriptWrite},
    };
    use rand_core::OsRng;
    use snark_verifier::loader::native::NativeLoader;

    #[derive(Clone, Copy, Debug)]
    struct Theta;
    type ChallengeTheta<F> = ChallengeScalar<F, Theta>;

    fn squeeze_challenge<
        E: Engine,
        C: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, C>,
    >(
        transcript: &mut T,
    ) -> ChallengeTheta<E::G1Affine> {
        transcript.squeeze_challenge_scalar()
    }

    fn write_point_to_proof<
        E: Engine,
        C: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, C>,
    >(
        transcript: &mut T,
        point: E::G1Affine,
    ) -> io::Result<()> {
        transcript.write_point(point)
    }

    fn write_scalar_to_proof<
        E: Engine,
        C: EncodedChallenge<E::G1Affine>,
        T: TranscriptWrite<E::G1Affine, C>,
    >(
        transcript: &mut T,
        scalar: E::Scalar,
    ) -> io::Result<()> {
        transcript.write_scalar(scalar)
    }

    #[test]
    fn test_poseidon_write_scalar_to_proof() {
        let fr = Fr::random(OsRng);
        let proof = {
            let mut transcript = PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(
                vec![],
                POSEIDON_SPEC.clone(),
            );
            write_scalar_to_proof::<Bn256, _, _>(&mut transcript, fr).unwrap();
            transcript.finalize()
        };
        let proof_tachyon = {
            let mut transcript =
                SnarkVerifierPoseidonWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
            write_scalar_to_proof::<Bn256, _, _>(&mut transcript, fr.clone()).unwrap();
            transcript.finalize()
        };
        assert_eq!(proof, proof_tachyon);
    }

    #[test]
    fn test_poseidon_write_point_to_proof() {
        const LEN: i32 = 100;
        let mut points = (0..LEN).map(|_| G1Affine::random(OsRng)).collect::<Vec<_>>();
        points.push(G1Affine::identity());

        let proof = {
            let mut transcript = PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(
                vec![],
                POSEIDON_SPEC.clone(),
            );
            for point in points.iter() {
                write_point_to_proof::<Bn256, _, _>(&mut transcript, point.clone()).unwrap();
            }
            transcript.finalize()
        };
        let proof_tachyon = {
            let mut transcript =
                SnarkVerifierPoseidonWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
            for point in points.iter() {
                write_point_to_proof::<Bn256, _, _>(&mut transcript, point.clone()).unwrap();
            }
            transcript.finalize()
        };
        assert_eq!(proof, proof_tachyon);
    }

    #[test]
    fn test_poseidon_squeeze_challenge() {
        const LEN: usize = 100;
        let points: Vec<G1Affine> = (0..LEN).map(|_| G1Affine::random(OsRng)).collect::<Vec<_>>();

        let theta = {
            let mut transcript = PoseidonTranscript::<NativeLoader, Vec<u8>>::from_spec(
                vec![],
                POSEIDON_SPEC.clone(),
            );
            for point in points.iter() {
                write_point_to_proof::<Bn256, _, _>(&mut transcript, point.clone()).unwrap();
            }
            let theta = squeeze_challenge::<Bn256, _, _>(&mut transcript);
            *theta
        };
        let theta_tachyon = {
            let mut transcript: SnarkVerifierPoseidonWrite<
                Vec<u8>,
                G1Affine,
                Challenge255<G1Affine>,
            > = SnarkVerifierPoseidonWrite::<_, G1Affine, Challenge255<_>>::init(vec![]);
            for point in points.iter() {
                write_point_to_proof::<Bn256, _, _>(&mut transcript, point.clone()).unwrap();
            }
            let theta = squeeze_challenge::<Bn256, _, _>(&mut transcript);
            *theta
        };
        assert_eq!(theta, theta_tachyon);
    }
}

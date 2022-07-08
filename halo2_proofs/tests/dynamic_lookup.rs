//! This file is adopted from https://github.com/privacy-scaling-explorations/halo2/blob/main/halo2_proofs/tests/lookup_any.rs
//! with modifications.

use std::marker::PhantomData;

use halo2_proofs::circuit::Value;
use halo2_proofs::pasta::{Eq, EqAffine, Fp};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner},
    dev::MockProver,
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Instance, Selector, SingleVerifier,
    },
    poly::commitment::Params,
    poly::Rotation,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use rand_core::OsRng;

//#[cfg(feature = "dev-graph")]
#[test]
fn lookup_dynamic() {
    #[derive(Clone, Debug)]
    struct MyConfig<F: FieldExt> {
        input: Column<Advice>,
        // Selector to enable lookups on even numbers.
        q_even: Selector,
        // Use an advice column as the lookup table column for even numbers.
        table_even: [Column<Advice>; 2],
        // Selector to enable lookups on odd numbers.
        q_odd: Selector,
        // Use an instance column as the lookup table column for odd numbers.
        table_odd: Column<Instance>,
        _marker: PhantomData<F>,
    }

    impl<F: FieldExt> MyConfig<F> {
        fn configure(meta: &mut ConstraintSystem<F>) -> Self {
            let config = Self {
                input: meta.advice_column(),
                q_even: meta.complex_selector(),
                table_even: [meta.advice_column(), meta.advice_column()],
                q_odd: meta.complex_selector(),
                table_odd: meta.instance_column(),
                _marker: PhantomData,
            };

            // Lookup on even numbers
            meta.lookup_dynamic_table("even number", |meta| {
                let input = meta.query_advice(config.input, Rotation::cur());

                let q_even = meta.query_selector(config.q_even);
                let table_even = meta.query_advice(config.table_even[0], Rotation::cur());

                vec![(q_even * input, table_even)]
            });

            // Lookup on odd numbers
            meta.lookup_dynamic_table("odd number", |meta| {
                let input = meta.query_advice(config.input, Rotation::cur());

                let q_odd = meta.query_selector(config.q_odd);
                let table_odd = meta.query_instance(config.table_odd, Rotation::cur());

                vec![(q_odd * input, table_odd)]
            });

            config
        }

        fn witness_even(
            &self,
            mut layouter: impl Layouter<F>,
            value: Value<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "witness even number",
                |mut region| {
                    // Enable the even lookup.
                    self.q_even.enable(&mut region, 0)?;

                    region.assign_advice(|| "even input", self.input, 0, || value)?;
                    Ok(())
                },
            )
        }

        fn witness_odd(
            &self,
            mut layouter: impl Layouter<F>,
            value: Value<F>,
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "witness odd number",
                |mut region| {
                    // Enable the odd lookup.
                    self.q_odd.enable(&mut region, 0)?;

                    region.assign_advice(|| "odd input", self.input, 0, || value)?;
                    Ok(())
                },
            )
        }

        fn load_lookup(
            &self,
            mut layouter: impl Layouter<F>,
            values: &[Value<F>],
        ) -> Result<(), Error> {
            layouter.assign_region(
                || "load values for even lookup table",
                |mut region| {
                    for (offset, value) in values.iter().enumerate() {
                        region.assign_advice(
                            || "even table value",
                            self.table_even[0],
                            offset,
                            || *value,
                        )?;
                    }

                    Ok(())
                },
            )
        }
    }

    #[derive(Default, Clone)]
    struct MyCircuit<F: FieldExt> {
        even_lookup: Vec<F>,
        even_witnesses: Vec<Value<F>>,
        odd_witnesses: Vec<Value<F>>,
    }

    impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
        // Since we are using a single chip for everything, we can just reuse its config.
        type Config = MyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            Self::Config::configure(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Load allowed values for even lookup table
            config.load_lookup(
                layouter.namespace(|| "witness even numbers"),
                self.even_lookup
                    .iter()
                    .map(|x| Value::known(*x))
                    .collect::<Vec<Value<F>>>()
                    .as_ref(),
            )?;

            // Witness even numbers
            for even in self.even_witnesses.iter() {
                config.witness_even(layouter.namespace(|| "witness even numbers"), *even)?;
            }

            // Witness odd numbers
            for odd in self.odd_witnesses.iter() {
                config.witness_odd(layouter.namespace(|| "witness odd numbers"), *odd)?;
            }

            Ok(())
        }
    }

    // Run MockProver.
    let k = 7;

    // Prepare the private and public inputs to the circuit.
    let even_lookup = vec![
        Fp::from(2),
        Fp::from(4),
        Fp::from(6),
        Fp::from(8),
        Fp::from(10),
    ];
    let odd_lookup = vec![
        Fp::from(1),
        Fp::from(3),
        Fp::from(5),
        Fp::from(7),
        Fp::from(9),
    ];
    let even_witnesses = vec![
        Value::known(Fp::from(0)), // cheat with 0, break soundness
        Value::known(Fp::from(2)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
        Value::known(Fp::from(4)),
    ];
    let odd_witnesses = vec![
        Value::known(Fp::from(1)),
        Value::known(Fp::from(3)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(5)),
        Value::known(Fp::from(0)), // cheat with 0, break soundness
    ];

    // Instantiate the circuit with the private inputs.
    let circuit = MyCircuit {
        even_lookup: even_lookup.clone(),
        even_witnesses,
        odd_witnesses,
    };

    #[cfg(feature = "dev-graph")]
    {
        use plotters::prelude::*;
        let root = BitMapBackend::new("dynamic_lookup.png", (1024, 3096)).into_drawing_area();
        root.fill(&WHITE).unwrap();
        let root = root.titled("dynamic lookup", ("sans-serif", 60)).unwrap();
        halo2_proofs::dev::CircuitLayout::default()
            .render(4, &circuit, &root)
            .unwrap();
    }

    // Given the correct public input, our circuit will verify.
    //    let prover = MockProver::run(k, &circuit, vec![odd_lookup]).unwrap();
    //    assert_eq!(prover.verify(), Ok(()));

    // If we pass in a public input containing only even numbers,
    // the odd number lookup will fail.
    //    let prover = MockProver::run(k, &circuit, vec![even_lookup]).unwrap();
    //    assert!(prover.verify().is_err());

    let params = Params::<EqAffine>::new(k);
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");
    let input_odd = &[&odd_lookup[..]];
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof(
        &params,
        &pk,
        &[circuit.clone()],
        &[&input_odd[..]],
        OsRng,
        &mut transcript,
    )
    .expect("even proof generation should not fail");
    let proof = transcript.finalize();
    // Verify the proof
    let strategy = SingleVerifier::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let res = verify_proof(
        &params,
        pk.get_vk(),
        strategy,
        &[&input_odd[..]],
        &mut transcript,
    );
    println!("{:?}", res);

    //    use plotters::prelude::*;
    //    let root = BitMapBackend::new("lookup-any-layout.png", (1024, 3096)).into_drawing_area();
    //    root.fill(&WHITE).unwrap();
    //    let root = root
    //        .titled("lookup any layout", ("sans-serif", 60))
    //        .unwrap();
    //    halo2_proofs::dev::CircuitLayout::default()
    //        .render(4, &circuit, &root)
    //        .unwrap();
}

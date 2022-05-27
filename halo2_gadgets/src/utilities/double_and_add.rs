//! Helper for single-row double-and-add.

use std::marker::PhantomData;

use halo2_proofs::{
    arithmetic::{CurveAffine, FieldExt},
    plonk::{Advice, Column, ConstraintSystem, Constraints, Expression, VirtualCells},
    poly::Rotation,
};

/// A helper struct for implementing single-row double-and-add using incomplete addition.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct DoubleAndAdd<C: CurveAffine> {
    // x-coordinate of the accumulator in each double-and-add iteration.
    pub(crate) x_a: Column<Advice>,
    // x-coordinate of the point being added in each double-and-add iteration.
    pub(crate) x_p: Column<Advice>,
    // lambda1 in each double-and-add iteration.
    pub(crate) lambda_1: Column<Advice>,
    // lambda2 in each double-and-add iteration.
    pub(crate) lambda_2: Column<Advice>,
    _marker: PhantomData<C>,
}

impl<C: CurveAffine> DoubleAndAdd<C> {
    pub(crate) fn configure(
        meta: &mut ConstraintSystem<C::Base>,
        x_a: Column<Advice>,
        x_p: Column<Advice>,
        lambda_1: Column<Advice>,
        lambda_2: Column<Advice>,
        main_selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
    ) -> Self {
        let config = Self {
            x_a,
            x_p,
            lambda_1,
            lambda_2,
            _marker: PhantomData,
        };

        config.main_gate(meta, main_selector);

        config
    }

    /// Gate checking double-and-add at each step in the steady state.
    fn main_gate(
        &self,
        meta: &mut ConstraintSystem<C::Base>,
        selector: &dyn Fn(&mut VirtualCells<C::Base>) -> Expression<C::Base>,
    ) {
        meta.create_gate("main check", |meta| {
            let for_loop = |meta: &mut VirtualCells<C::Base>, y_a_next: Expression<C::Base>| {
                // x_{A,i}
                let x_a_cur = meta.query_advice(self.x_a, Rotation::cur());
                // x_{A,i-1}
                let x_a_next = meta.query_advice(self.x_a, Rotation::next());
                // λ_{2,i}
                let lambda2_cur = meta.query_advice(self.lambda_2, Rotation::cur());

                let y_a_cur = self.y_a(meta, Rotation::cur());

                // λ_{2,i}^2 − x_{A,i-1} − x_{R,i} − x_{A,i} = 0
                let secant_line = lambda2_cur.clone().square()
                    - x_a_next.clone()
                    - self.x_r(meta, Rotation::cur())
                    - x_a_cur.clone();

                // λ_{2,i}⋅(x_{A,i} − x_{A,i-1}) − y_{A,i} − y_{A,i-1} = 0
                let gradient_2 = lambda2_cur * (x_a_cur - x_a_next) - y_a_cur - y_a_next;

                std::iter::empty()
                    .chain(Some(("secant_line", secant_line)))
                    .chain(Some(("gradient_2", gradient_2)))
            };

            let selector = selector(meta);
            let y_a_next = self.y_a(meta, Rotation::next());
            Constraints::with_selector(selector, for_loop(meta, y_a_next))
        })
    }

    /// Derives the expression `x_r = lambda_1^2 - x_a - x_p`.
    pub(crate) fn x_r(
        &self,
        meta: &mut VirtualCells<C::Base>,
        rotation: Rotation,
    ) -> Expression<C::Base> {
        let x_a = meta.query_advice(self.x_a, rotation);
        let x_p = meta.query_advice(self.x_p, rotation);
        let lambda_1 = meta.query_advice(self.lambda_1, rotation);
        lambda_1.square() - x_a - x_p
    }

    /// Derives the expression `y_a = [(lambda_1 + lambda_2) * (x_a - x_r)] / 2`.
    #[allow(non_snake_case)]
    pub(crate) fn y_a(
        &self,
        meta: &mut VirtualCells<C::Base>,
        rotation: Rotation,
    ) -> Expression<C::Base> {
        let x_a = meta.query_advice(self.x_a, rotation);
        let lambda_1 = meta.query_advice(self.lambda_1, rotation);
        let lambda_2 = meta.query_advice(self.lambda_2, rotation);
        (lambda_1 + lambda_2) * (x_a - self.x_r(meta, rotation)) * C::Base::TWO_INV
    }
}

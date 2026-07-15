import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeCutoffSecondDerivative

/-!
# Support of quantitative collar derivatives

The first and second derivatives of the smooth transition vanish outside the
open unit interval.  Affine transport localizes the logarithmic collar
derivatives and makes the left-right mixed derivative identically zero on an
ordered integer block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.smoothTransitionDerivative_eq_zero_of_neg
    {x : ℝ}
    (hx : x < 0) :
    Real.smoothTransitionDerivative x = 0 := by
  have heventual : Real.smoothTransition =ᶠ[nhds x]
      (fun _y : ℝ => (0 : ℝ)) := by
    exact Filter.mem_of_superset
      (Iio_mem_nhds hx)
      (fun y hy => Real.smoothTransition.zero_of_nonpos hy.le)
  have hconstantDeriv : deriv (fun _y : ℝ => (0 : ℝ)) x = 0 :=
    deriv_const x (0 : ℝ)
  have hderiv : deriv Real.smoothTransition x = 0 :=
    heventual.deriv_eq.trans hconstantDeriv
  exact
    (Real.deriv_smoothTransition_exact x).symm.trans hderiv

theorem Real.smoothTransitionDerivative_eq_zero_of_one_lt
    {x : ℝ}
    (hx : 1 < x) :
    Real.smoothTransitionDerivative x = 0 := by
  have heventual : Real.smoothTransition =ᶠ[nhds x]
      (fun _y : ℝ => (1 : ℝ)) := by
    exact Filter.mem_of_superset
      (Ioi_mem_nhds hx)
      (fun y hy => Real.smoothTransition.one_of_one_le hy.le)
  have hconstantDeriv : deriv (fun _y : ℝ => (1 : ℝ)) x = 0 :=
    deriv_const x (1 : ℝ)
  have hderiv : deriv Real.smoothTransition x = 0 :=
    heventual.deriv_eq.trans hconstantDeriv
  exact
    (Real.deriv_smoothTransition_exact x).symm.trans hderiv

theorem Real.smoothTransitionDerivative_eq_zero_of_nonpos
    {x : ℝ}
    (hx : x ≤ 0) :
    Real.smoothTransitionDerivative x = 0 := by
  match hx.eq_or_lt with
  | Or.inl hxZero =>
      exact Eq.subst
        (motive := fun value : ℝ =>
          Real.smoothTransitionDerivative value = 0)
        hxZero.symm Real.smoothTransitionDerivative_zero
  | Or.inr hxNeg =>
      exact Real.smoothTransitionDerivative_eq_zero_of_neg hxNeg

theorem Real.smoothTransitionDerivative_eq_zero_of_one_le
    {x : ℝ}
    (hx : 1 ≤ x) :
    Real.smoothTransitionDerivative x = 0 := by
  match hx.eq_or_lt with
  | Or.inl hxOne =>
      exact Eq.subst
        (motive := fun value : ℝ =>
          Real.smoothTransitionDerivative value = 0)
        hxOne Real.smoothTransitionDerivative_one
  | Or.inr hxGt =>
      exact Real.smoothTransitionDerivative_eq_zero_of_one_lt hxGt

theorem Real.smoothTransitionSecondDerivative_eq_zero_of_neg
    {x : ℝ}
    (hx : x < 0) :
    Real.smoothTransitionSecondDerivative x = 0 := by
  have heventual : Real.smoothTransitionDerivative =ᶠ[nhds x]
      (fun _y : ℝ => (0 : ℝ)) := by
    exact Filter.mem_of_superset
      (Iio_mem_nhds hx)
      (fun y hy => Real.smoothTransitionDerivative_eq_zero_of_neg hy)
  have hconstantDeriv : deriv (fun _y : ℝ => (0 : ℝ)) x = 0 :=
    deriv_const x (0 : ℝ)
  have hderiv : deriv Real.smoothTransitionDerivative x = 0 :=
    heventual.deriv_eq.trans hconstantDeriv
  exact (Real.deriv_smoothTransitionDerivative x).symm.trans hderiv

theorem Real.smoothTransitionSecondDerivative_eq_zero_of_one_lt
    {x : ℝ}
    (hx : 1 < x) :
    Real.smoothTransitionSecondDerivative x = 0 := by
  have heventual : Real.smoothTransitionDerivative =ᶠ[nhds x]
      (fun _y : ℝ => (0 : ℝ)) := by
    exact Filter.mem_of_superset
      (Ioi_mem_nhds hx)
      (fun y hy => Real.smoothTransitionDerivative_eq_zero_of_one_lt hy)
  have hconstantDeriv : deriv (fun _y : ℝ => (0 : ℝ)) x = 0 :=
    deriv_const x (0 : ℝ)
  have hderiv : deriv Real.smoothTransitionDerivative x = 0 :=
    heventual.deriv_eq.trans hconstantDeriv
  exact (Real.deriv_smoothTransitionDerivative x).symm.trans hderiv

theorem Real.quantitativeLogarithmicLeftCutoffDerivative_eq_zero_of_le_supportLeft
    (a : ℤ) {x : ℝ}
    (hx : x ≤ (a : ℝ) - 1 / 3) :
    Real.quantitativeLogarithmicLeftCutoffDerivative a x = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoffDerivative
  have hargument : 3 * (x - (a : ℝ)) + 1 ≤ 0 := by
    have hsub := sub_le_sub_right hx (a : ℝ)
    have hendpoint : ((a : ℝ) - 1 / 3) - (a : ℝ) = -(1 / 3) :=
      sub_sub_cancel_left (a : ℝ) (1 / 3)
    have hscaled := mul_le_mul_of_nonneg_left
      (Eq.subst (motive := fun value : ℝ => x - (a : ℝ) ≤ value)
        hendpoint hsub) (Nat.cast_nonneg 3)
    exact le_trans (add_le_add_right hscaled 1)
      (le_of_eq Real.three_mul_neg_one_div_three_add_one_eq_zero)
  exact
    (congrArg (fun value : ℝ => 3 * value)
      (Real.smoothTransitionDerivative_eq_zero_of_nonpos hargument)).trans
      (mul_zero 3)

theorem Real.quantitativeLogarithmicLeftCutoffDerivative_eq_zero_of_core_le
    (a : ℤ) {x : ℝ}
    (hx : (a : ℝ) ≤ x) :
    Real.quantitativeLogarithmicLeftCutoffDerivative a x = 0 := by
  unfold Real.quantitativeLogarithmicLeftCutoffDerivative
  have hsub : 0 ≤ x - (a : ℝ) := sub_nonneg.mpr hx
  have hscaled : 0 ≤ 3 * (x - (a : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg 3) hsub
  have hargument : (1 : ℝ) ≤ 3 * (x - (a : ℝ)) + 1 :=
    le_trans (le_of_eq (zero_add 1).symm) (add_le_add_right hscaled 1)
  exact
    (congrArg (fun value : ℝ => 3 * value)
      (Real.smoothTransitionDerivative_eq_zero_of_one_le hargument)).trans
      (mul_zero 3)

theorem Real.quantitativeLogarithmicRightCutoffDerivative_eq_zero_of_le_core
    (b : ℤ) {x : ℝ}
    (hx : x ≤ (b : ℝ)) :
    Real.quantitativeLogarithmicRightCutoffDerivative b x = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffDerivative
  have hsub : 0 ≤ (b : ℝ) - x := sub_nonneg.mpr hx
  have hscaled : 0 ≤ 3 * ((b : ℝ) - x) :=
    mul_nonneg (Nat.cast_nonneg 3) hsub
  have hargument : (1 : ℝ) ≤ 3 * ((b : ℝ) - x) + 1 :=
    le_trans (le_of_eq (zero_add 1).symm) (add_le_add_right hscaled 1)
  exact
    (congrArg (fun value : ℝ => (-3) * value)
      (Real.smoothTransitionDerivative_eq_zero_of_one_le hargument)).trans
      (mul_zero (-3))

theorem Real.quantitativeLogarithmicRightCutoffDerivative_eq_zero_of_supportRight_le
    (b : ℤ) {x : ℝ}
    (hx : (b : ℝ) + 1 / 3 ≤ x) :
    Real.quantitativeLogarithmicRightCutoffDerivative b x = 0 := by
  unfold Real.quantitativeLogarithmicRightCutoffDerivative
  have hsub := sub_le_sub_left hx (b : ℝ)
  have hendpoint : (b : ℝ) - ((b : ℝ) + 1 / 3) = -(1 / 3) := by
    exact (sub_add_eq_sub_sub (b : ℝ) (b : ℝ) (1 / 3)).trans
      ((congrArg (fun value : ℝ => value - 1 / 3) (sub_self (b : ℝ))).trans
        (zero_sub (1 / 3)))
  have hscaled := mul_le_mul_of_nonneg_left
    (Eq.subst (motive := fun value : ℝ => (b : ℝ) - x ≤ value)
      hendpoint hsub) (Nat.cast_nonneg 3)
  have hargument : 3 * ((b : ℝ) - x) + 1 ≤ 0 :=
    le_trans (add_le_add_right hscaled 1)
      (le_of_eq Real.three_mul_neg_one_div_three_add_one_eq_zero)
  exact
    (congrArg (fun value : ℝ => (-3) * value)
      (Real.smoothTransitionDerivative_eq_zero_of_nonpos hargument)).trans
      (mul_zero (-3))

theorem Real.quantitativeLogarithmicCollarDerivative_product_eq_zero
    (a b : ℤ)
    (hab : a ≤ b)
    (x : ℝ) :
    Real.quantitativeLogarithmicLeftCutoffDerivative a x *
      Real.quantitativeLogarithmicRightCutoffDerivative b x = 0 := by
  match le_total x (a : ℝ) with
  | Or.inl hxa =>
      have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
      have hxb : x ≤ (b : ℝ) := le_trans hxa habReal
      have hright :=
        Real.quantitativeLogarithmicRightCutoffDerivative_eq_zero_of_le_core
          b hxb
      exact
        (congrArg
          (fun value : ℝ =>
            Real.quantitativeLogarithmicLeftCutoffDerivative a x * value)
          hright).trans
          (mul_zero _)
  | Or.inr hax =>
      have hleft :=
        Real.quantitativeLogarithmicLeftCutoffDerivative_eq_zero_of_core_le
          a hax
      exact
        (congrArg
          (fun value : ℝ =>
            value * Real.quantitativeLogarithmicRightCutoffDerivative b x)
          hleft).trans
          (zero_mul _)

end
end LFunctions
end Boundary

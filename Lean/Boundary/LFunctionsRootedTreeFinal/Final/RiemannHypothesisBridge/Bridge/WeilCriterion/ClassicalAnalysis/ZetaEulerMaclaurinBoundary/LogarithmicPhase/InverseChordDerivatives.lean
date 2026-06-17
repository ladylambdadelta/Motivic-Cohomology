import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcGeometry
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section
/-- The inverse-chord denominator is nonzero on the positive reduced arc. -/
theorem Real.inverseChord_denominator_ne_zero_on_pos :
    ∀ ψ : ℝ,
      ψ ∈ Set.Ioc (0 : ℝ) Real.pi →
        2 * (1 - Real.cos ψ) ≠ 0 := by
  intro ψ hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ.1, hψ.2⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_gt hψ.1
  exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne

/-- The inverse-chord denominator is nonzero on the negative reduced arc. -/
theorem Real.inverseChord_denominator_ne_zero_on_neg :
    ∀ ψ : ℝ,
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) →
        2 * (1 - Real.cos ψ) ≠ 0 := by
  intro ψ hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hψ.1, le_of_lt (lt_trans hψ.2 Real.pi_pos)⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_lt hψ.2
  exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne

/-- The inverse-chord denominator is positive on the punctured reduced arc. -/
theorem Real.inverseChord_denominator_pos_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    0 < 2 * (1 - Real.cos ψ) := by
  have hcos_le_one : Real.cos ψ ≤ 1 :=
    Real.cos_le_one ψ
  have hone_sub_cos_nonneg : 0 ≤ 1 - Real.cos ψ :=
    sub_nonneg.mpr hcos_le_one
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hone_sub_cos_pos : 0 < 1 - Real.cos ψ :=
    lt_of_le_of_ne hone_sub_cos_nonneg hone_sub_cos_ne.symm
  exact mul_pos zero_lt_two hone_sub_cos_pos

/-- Raw quotient-rule derivative of the inverse-chord imaginary coordinate. -/
theorem Real.inverseChord_imCoordFormula_deriv_raw
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
      (deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ) /
        (2 * (1 - Real.cos ψ)) ^ 2 := by
  have hnum :
      DifferentiableAt ℝ Real.sin ψ :=
    Real.differentiable_sin ψ
  have hcos :
      DifferentiableAt ℝ Real.cos ψ :=
    Real.differentiable_cos ψ
  have hden_base :
      DifferentiableAt ℝ
        (fun θ : ℝ => 1 - Real.cos θ) ψ :=
    (differentiableAt_const 1).sub hcos
  have hden :
      DifferentiableAt ℝ
        (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ :=
    (differentiableAt_const 2).mul hden_base
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 :=
    Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  exact deriv_div hnum hden hden_ne

/-- Derivative of the inverse-chord denominator. -/
theorem Real.inverseChord_denominator_deriv_eq
    (ψ : ℝ) :
    deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
      2 * Real.sin ψ := by
  have hinner :
      deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
        Real.sin ψ := by
    have hconst_sub :
        deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
          -deriv Real.cos ψ :=
      deriv_const_sub (f := Real.cos) (x := ψ) (1 : ℝ)
    have hcos :
        deriv Real.cos ψ = -Real.sin ψ :=
      Real.deriv_cos
    have hneg_transport :
        -deriv Real.cos ψ = -(-Real.sin ψ) :=
      congrArg Neg.neg hcos
    have hneg :
        -(-Real.sin ψ) = Real.sin ψ :=
      neg_neg (Real.sin ψ)
    calc
      deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
          -deriv Real.cos ψ :=
        hconst_sub
      _ = -(-Real.sin ψ) :=
        hneg_transport
      _ = Real.sin ψ :=
        hneg
  calc
    deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        2 * deriv (fun θ : ℝ => 1 - Real.cos θ) ψ :=
      deriv_const_mul_field (v := fun θ : ℝ => 1 - Real.cos θ)
        (x := ψ) (2 : ℝ)
    _ = 2 * Real.sin ψ :=
      congrArg (fun r : ℝ => 2 * r) hinner

/-- Polynomial form of the inverse-chord derivative numerator identity. -/
theorem Real.inverseChord_deriv_trig_numerator_eq_of_unit_circle
    {s c : ℝ}
    (hunit : s ^ 2 + c ^ 2 = 1) :
    c * (2 * (1 - c)) - s * (2 * s) =
      -2 * (1 - c) := by
  exact real_inverse_chord_derivative_numerator_algebra_for_logarithmicPhase hunit

/-- Trigonometric numerator identity behind the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_trig_numerator_eq
    (ψ : ℝ) :
    Real.cos ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ * (2 * Real.sin ψ) =
      -2 * (1 - Real.cos ψ) := by
  exact
    Real.inverseChord_deriv_trig_numerator_eq_of_unit_circle
      (s := Real.sin ψ)
      (c := Real.cos ψ)
      (Real.sin_sq_add_cos_sq ψ)

/-- Numerator simplification in the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_raw_numerator_eq
    (ψ : ℝ) :
    deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ *
          deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
      -2 * (1 - Real.cos ψ) := by
  have hsin_deriv :
      deriv Real.sin ψ = Real.cos ψ :=
    congrFun Real.deriv_sin ψ
  have hden_deriv :
      deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        2 * Real.sin ψ :=
    Real.inverseChord_denominator_deriv_eq ψ
  have htransport :
      deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        Real.cos ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ * (2 * Real.sin ψ) := by
    exact congrArg₂ Sub.sub
      (congrArg
        (fun r : ℝ => r * (2 * (1 - Real.cos ψ)))
        hsin_deriv)
      (congrArg
        (fun r : ℝ => Real.sin ψ * r)
        hden_deriv)
  exact Eq.trans htransport (Real.inverseChord_deriv_trig_numerator_eq ψ)

/-- Field identity used to cancel the derivative quotient. -/
theorem Real.neg_div_sq_eq_neg_inv
    {d : ℝ}
    (hd : d ≠ 0) :
    (-d) / d ^ 2 = -1 / d := by
  have hd_inv :
      d * d⁻¹ = 1 :=
    mul_inv_cancel₀ hd
  have hpow :
      d ^ 2 = d * d :=
    pow_two d
  have hmain :
      (-d) * (d ^ 2)⁻¹ = -1 * d⁻¹ := by
    calc
      (-d) * (d ^ 2)⁻¹ =
          -(d * (d ^ 2)⁻¹) :=
        neg_mul d (d ^ 2)⁻¹
      _ = -(d * (d * d)⁻¹) :=
        congrArg (fun r : ℝ => -(d * r⁻¹)) hpow
      _ = -(d * (d⁻¹ * d⁻¹)) := by
        exact congrArg (fun r : ℝ => -(d * r))
          (mul_inv_rev d d)
      _ = -((d * d⁻¹) * d⁻¹) := by
        exact congrArg Neg.neg (mul_assoc d d⁻¹ d⁻¹).symm
      _ = -(1 * d⁻¹) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * d⁻¹) hd_inv)
      _ = -d⁻¹ := by
        exact congrArg Neg.neg (one_mul d⁻¹)
      _ = -((1 : ℝ) * d⁻¹) := by
        exact Eq.symm (congrArg Neg.neg (one_mul d⁻¹))
      _ = -1 * d⁻¹ :=
        neg_mul_eq_neg_mul 1 d⁻¹
  have hleft :
      (-d) / d ^ 2 = (-d) * (d ^ 2)⁻¹ :=
    div_eq_mul_inv (-d) (d ^ 2)
  have hright :
      -1 / d = -1 * d⁻¹ :=
    div_eq_mul_inv (-1 : ℝ) d
  exact Eq.trans hleft (Eq.trans hmain hright.symm)

/-- Quotient simplification in the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_raw_quotient_eq
    {ψ : ℝ}
    (hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0) :
    (-2 * (1 - Real.cos ψ)) / (2 * (1 - Real.cos ψ)) ^ 2 =
      -1 / (2 * (1 - Real.cos ψ)) := by
  let d : ℝ := 2 * (1 - Real.cos ψ)
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hd : d ≠ 0 :=
    mul_ne_zero htwo_ne hone_sub_cos_ne
  have hneg :
      -2 * (1 - Real.cos ψ) = -d := by
    calc
      -2 * (1 - Real.cos ψ) =
          -(2 * (1 - Real.cos ψ)) :=
        (neg_mul_eq_neg_mul 2 (1 - Real.cos ψ)).symm
      _ = -d := by
        exact congrArg Neg.neg (show 2 * (1 - Real.cos ψ) = d from rfl)
  have hfield :
      (-d) / d ^ 2 = -1 / d :=
    Real.neg_div_sq_eq_neg_inv hd
  exact Eq.trans
    (congrArg₂ Div.div hneg (congrArg (fun r : ℝ => r ^ 2) (show 2 * (1 - Real.cos ψ) = d from rfl)))
    hfield

/-- Scalar simplification of the raw inverse-chord derivative formula. -/
theorem Real.inverseChord_imCoordFormula_deriv_raw_simplifies
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    (deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ *
          deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ) /
      (2 * (1 - Real.cos ψ)) ^ 2 =
      -1 / (2 * (1 - Real.cos ψ)) := by
  have hnumerator :
      deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        -2 * (1 - Real.cos ψ) :=
    Real.inverseChord_deriv_raw_numerator_eq ψ
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hquotient :
      (-2 * (1 - Real.cos ψ)) / (2 * (1 - Real.cos ψ)) ^ 2 =
        -1 / (2 * (1 - Real.cos ψ)) :=
    Real.inverseChord_deriv_raw_quotient_eq hone_sub_cos_ne
  exact Eq.trans
    (congrArg
      (fun numerator : ℝ =>
        numerator / (2 * (1 - Real.cos ψ)) ^ 2)
      hnumerator)
    hquotient

/-- Derivative formula for the inverse-chord imaginary coordinate. -/
theorem Real.inverseChord_imCoordFormula_deriv_eq
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
      -1 / (2 * (1 - Real.cos ψ)) := by
  exact Eq.trans
    (Real.inverseChord_imCoordFormula_deriv_raw hψ_mem hψ_ne)
    (Real.inverseChord_imCoordFormula_deriv_raw_simplifies hψ_mem hψ_ne)

/-- The inverse-chord imaginary-coordinate derivative is nonpositive on the
punctured reduced arc. -/
theorem Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  have hderiv :
      deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
        -1 / (2 * (1 - Real.cos ψ)) :=
    Real.inverseChord_imCoordFormula_deriv_eq hψ_mem hψ_ne
  have hden_pos : 0 < 2 * (1 - Real.cos ψ) :=
    Real.inverseChord_denominator_pos_of_mem_reducedArc hψ_mem hψ_ne
  have hinv_pos : 0 < (2 * (1 - Real.cos ψ))⁻¹ :=
    inv_pos.mpr hden_pos
  have hone_mul_inv_nonneg :
      0 ≤ 1 * (2 * (1 - Real.cos ψ))⁻¹ :=
    mul_nonneg zero_le_one hinv_pos.le
  have hneg_nonpos : -(1 * (2 * (1 - Real.cos ψ))⁻¹) ≤ 0 :=
    neg_nonpos.mpr hone_mul_inv_nonneg
  have hquot :
      -1 / (2 * (1 - Real.cos ψ)) =
        -(1 * (2 * (1 - Real.cos ψ))⁻¹) := by
    calc
      -1 / (2 * (1 - Real.cos ψ)) =
          (-1) * (2 * (1 - Real.cos ψ))⁻¹ :=
        div_eq_mul_inv (-1) (2 * (1 - Real.cos ψ))
      _ = -(1 * (2 * (1 - Real.cos ψ))⁻¹) :=
        (neg_mul_eq_neg_mul 1 (2 * (1 - Real.cos ψ))⁻¹).symm
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 0)
    hderiv.symm
    (Eq.subst
      (motive := fun r : ℝ => r ≤ 0)
      hquot.symm
      hneg_nonpos)

/-- The real inverse-chord imaginary coordinate formula is antitone on the
positive reduced arc. -/
theorem Real.inverseChord_imCoordFormula_continuousOn_pos :
    ContinuousOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioc (0 : ℝ) Real.pi) := by
  have hnum :
      ContinuousOn Real.sin (Set.Ioc (0 : ℝ) Real.pi) :=
    Real.continuous_sin.continuousOn
  have hcos :
      ContinuousOn Real.cos (Set.Ioc (0 : ℝ) Real.pi) :=
    Real.continuous_cos.continuousOn
  have hden_base :
      ContinuousOn
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (Set.Ioc (0 : ℝ) Real.pi) :=
    continuousOn_const.sub hcos
  have hden :
      ContinuousOn
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (Set.Ioc (0 : ℝ) Real.pi) :=
    continuousOn_const.mul hden_base
  exact hnum.div hden Real.inverseChord_denominator_ne_zero_on_pos

theorem Real.inverseChord_imCoordFormula_differentiableOn_pos :
    DifferentiableOn ℝ
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (interior (Set.Ioc (0 : ℝ) Real.pi)) := by
  have hnum :
      DifferentiableOn ℝ Real.sin (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    Real.differentiable_sin.differentiableOn
  have hcos :
      DifferentiableOn ℝ Real.cos (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    Real.differentiable_cos.differentiableOn
  have hden_base :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    (differentiableOn_const 1).sub hcos
  have hden :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    (differentiableOn_const 2).mul hden_base
  have hden_ne :
      ∀ ψ : ℝ,
        ψ ∈ interior (Set.Ioc (0 : ℝ) Real.pi) →
          2 * (1 - Real.cos ψ) ≠ 0 := by
    intro ψ hψ
    exact Real.inverseChord_denominator_ne_zero_on_pos ψ (interior_subset hψ)
  exact hnum.div hden hden_ne

theorem Real.inverseChord_imCoordFormula_deriv_nonpos_pos :
    ∀ ψ : ℝ,
      ψ ∈ interior (Set.Ioc (0 : ℝ) Real.pi) →
        deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  intro ψ hψ
  have hψ_side : ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    interior_subset hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ_side.1, hψ_side.2⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_gt hψ_side.1
  exact
    Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
      hψ_mem hψ_ne

theorem Real.inverseChord_imCoordFormula_antitoneOn_pos :
    AntitoneOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioc (0 : ℝ) Real.pi) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Ioc (0 : ℝ) Real.pi)
    Real.inverseChord_imCoordFormula_continuousOn_pos
    Real.inverseChord_imCoordFormula_differentiableOn_pos
    Real.inverseChord_imCoordFormula_deriv_nonpos_pos

/-- The real inverse-chord imaginary coordinate formula is antitone on the
negative reduced arc. -/
theorem Real.inverseChord_imCoordFormula_continuousOn_neg :
    ContinuousOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hnum :
      ContinuousOn Real.sin (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    Real.continuous_sin.continuousOn
  have hcos :
      ContinuousOn Real.cos (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    Real.continuous_cos.continuousOn
  have hden_base :
      ContinuousOn
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    continuousOn_const.sub hcos
  have hden :
      ContinuousOn
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    continuousOn_const.mul hden_base
  exact hnum.div hden Real.inverseChord_denominator_ne_zero_on_neg

theorem Real.inverseChord_imCoordFormula_differentiableOn_neg :
    DifferentiableOn ℝ
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (interior (Set.Ioo (-Real.pi) (0 : ℝ))) := by
  have hnum :
      DifferentiableOn ℝ Real.sin (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    Real.differentiable_sin.differentiableOn
  have hcos :
      DifferentiableOn ℝ Real.cos (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    Real.differentiable_cos.differentiableOn
  have hden_base :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    (differentiableOn_const 1).sub hcos
  have hden :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    (differentiableOn_const 2).mul hden_base
  have hden_ne :
      ∀ ψ : ℝ,
        ψ ∈ interior (Set.Ioo (-Real.pi) (0 : ℝ)) →
          2 * (1 - Real.cos ψ) ≠ 0 := by
    intro ψ hψ
    exact Real.inverseChord_denominator_ne_zero_on_neg ψ (interior_subset hψ)
  exact hnum.div hden hden_ne

theorem Real.inverseChord_imCoordFormula_deriv_nonpos_neg :
    ∀ ψ : ℝ,
      ψ ∈ interior (Set.Ioo (-Real.pi) (0 : ℝ)) →
        deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  intro ψ hψ
  have hψ_side : ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    interior_subset hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hψ_side.1, le_of_lt (lt_trans hψ_side.2 Real.pi_pos)⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_lt hψ_side.2
  exact
    Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
      hψ_mem hψ_ne

theorem Real.inverseChord_imCoordFormula_antitoneOn_neg :
    AntitoneOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Ioo (-Real.pi) (0 : ℝ))
    Real.inverseChord_imCoordFormula_continuousOn_neg
    Real.inverseChord_imCoordFormula_differentiableOn_neg
    Real.inverseChord_imCoordFormula_deriv_nonpos_neg

/-- On the positive reduced arc the inverse chord imaginary coordinate is
antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos :
    AntitoneOn
      Complex.reducedArc_inverseGeometricDenominator_imCoord
      (Set.Ioc (0 : ℝ) Real.pi) := by
  intro x hx y hy hxy
  have hx_mem : x ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) hx.1.le, hx.2⟩
  have hy_mem : y ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) hy.1.le, hy.2⟩
  have hx_ne : x ≠ 0 :=
    ne_of_gt hx.1
  have hy_ne : y ≠ 0 :=
    ne_of_gt hy.1
  have hformula_x :
      Complex.reducedArc_inverseGeometricDenominator_imCoord x =
        Real.sin x / (2 * (1 - Real.cos x)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hx_mem hx_ne
  have hformula_y :
      Complex.reducedArc_inverseGeometricDenominator_imCoord y =
        Real.sin y / (2 * (1 - Real.cos y)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hy_mem hy_ne
  exact Eq.subst
    (motive := fun target : ℝ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord y ≤ target)
    hformula_x.symm
    (Eq.subst
      (motive := fun source : ℝ =>
        source ≤ Real.sin x / (2 * (1 - Real.cos x)))
      hformula_y.symm
      (Real.inverseChord_imCoordFormula_antitoneOn_pos hx hy hxy))

/-- On the negative reduced arc the inverse chord imaginary coordinate is
antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg :
    AntitoneOn
      Complex.reducedArc_inverseGeometricDenominator_imCoord
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx_mem : x ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hx.1, le_of_lt (lt_trans hx.2 Real.pi_pos)⟩
  have hy_mem : y ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hy.1, le_of_lt (lt_trans hy.2 Real.pi_pos)⟩
  have hx_ne : x ≠ 0 :=
    ne_of_lt hx.2
  have hy_ne : y ≠ 0 :=
    ne_of_lt hy.2
  have hformula_x :
      Complex.reducedArc_inverseGeometricDenominator_imCoord x =
        Real.sin x / (2 * (1 - Real.cos x)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hx_mem hx_ne
  have hformula_y :
      Complex.reducedArc_inverseGeometricDenominator_imCoord y =
        Real.sin y / (2 * (1 - Real.cos y)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hy_mem hy_ne
  exact Eq.subst
    (motive := fun target : ℝ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord y ≤ target)
    hformula_x.symm
    (Eq.subst
      (motive := fun source : ℝ =>
        source ≤ Real.sin x / (2 * (1 - Real.cos x)))
      hformula_y.symm
      (Real.inverseChord_imCoordFormula_antitoneOn_neg hx hy hxy))

end

end LFunctions
end Boundary

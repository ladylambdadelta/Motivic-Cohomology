import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeThreeComponentBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDirectPoissonArithmetic

/-!
# Arithmetic closure for the quantitative logarithmic B-process

This file owns the numerical target comparison after the three analytic
components have been bounded.  The analytic estimates remain in their packet
owners; only addition, denominator comparison, and cast transport belong here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseQuantitativeNormTarget
    (t : ℝ) (b : ℤ) : ℝ :=
  ((b : ℝ) + 1) / ‖t‖ + Real.sqrt (1 + ‖t‖)

def Real.logarithmicPhaseQuantitativeSqrtTarget
    (t : ℝ) (b : ℤ) : ℝ :=
  ((b : ℝ) + 1) / Real.sqrt ‖t‖ + Real.sqrt (1 + ‖t‖)

theorem Real.logarithmicPhaseQuantitativeNormTarget_eq_directPoissonTarget
    (t : ℝ) (b : ℤ) :
    Real.logarithmicPhaseQuantitativeNormTarget t b =
      Real.logarithmicPhaseDirectPoissonTarget t b := by
  rfl

theorem Real.logarithmicPhaseQuantitativeNormTarget_nonneg
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    0 ≤ Real.logarithmicPhaseQuantitativeNormTarget t b := by
  unfold Real.logarithmicPhaseQuantitativeNormTarget
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  have hnumerator : (0 : ℝ) ≤ (b : ℝ) + 1 :=
    add_nonneg hbReal zero_le_one
  have hnorm : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t
  have hquotient : (0 : ℝ) ≤ ((b : ℝ) + 1) / ‖t‖ :=
    div_nonneg hnumerator hnorm
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg _
  exact add_nonneg hquotient hsqrt

theorem Real.logarithmicPhaseQuantitativeSqrtTarget_nonneg
    (t : ℝ) (b : ℤ)
    (hb : 0 ≤ b) :
    0 ≤ Real.logarithmicPhaseQuantitativeSqrtTarget t b := by
  unfold Real.logarithmicPhaseQuantitativeSqrtTarget
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  have hnumerator : (0 : ℝ) ≤ (b : ℝ) + 1 :=
    add_nonneg hbReal zero_le_one
  have hsqrtNorm : (0 : ℝ) ≤ Real.sqrt ‖t‖ := Real.sqrt_nonneg _
  have hquotient : (0 : ℝ) ≤ ((b : ℝ) + 1) / Real.sqrt ‖t‖ :=
    div_nonneg hnumerator hsqrtNorm
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg _
  exact add_nonneg hquotient hsqrt

theorem Real.sqrt_norm_pos_of_one_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    0 < Real.sqrt ‖t‖ := by
  have hnormPos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  exact Real.sqrt_pos.2 hnormPos

theorem Real.sqrt_norm_le_norm_of_one_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Real.sqrt ‖t‖ ≤ ‖t‖ := by
  have hnormNonneg : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t
  have hsquareLower : Real.sqrt ‖t‖ ^ 2 = ‖t‖ :=
    Real.sq_sqrt hnormNonneg
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt ‖t‖ := by
    have hsqrtMonotone : Real.sqrt 1 ≤ Real.sqrt ‖t‖ :=
      Real.sqrt_le_sqrt ht
    exact le_trans (le_of_eq Real.sqrt_one.symm) hsqrtMonotone
  have hmul :
      Real.sqrt ‖t‖ * 1 ≤
        Real.sqrt ‖t‖ * Real.sqrt ‖t‖ :=
    mul_le_mul_of_nonneg_left hsqrtOne (Real.sqrt_nonneg _)
  have hleft : Real.sqrt ‖t‖ * 1 = Real.sqrt ‖t‖ := mul_one _
  have hright :
      Real.sqrt ‖t‖ * Real.sqrt ‖t‖ = Real.sqrt ‖t‖ ^ 2 :=
    (pow_two (Real.sqrt ‖t‖)).symm
  exact le_trans (le_of_eq hleft.symm)
    (le_trans hmul (le_of_eq (hright.trans hsquareLower)))

theorem Real.inv_norm_le_inv_sqrt_norm_of_one_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖t‖⁻¹ ≤ (Real.sqrt ‖t‖)⁻¹ := by
  have hsqrtPos := Real.sqrt_norm_pos_of_one_le t ht
  have hnormPos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  exact (inv_le_inv₀ hsqrtPos hnormPos).mpr
    (Real.sqrt_norm_le_norm_of_one_le t ht)

theorem Real.endpoint_div_norm_le_endpoint_div_sqrt_norm
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    ((b : ℝ) + 1) / ‖t‖ ≤
      ((b : ℝ) + 1) / Real.sqrt ‖t‖ := by
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  have hnumerator : (0 : ℝ) ≤ (b : ℝ) + 1 :=
    add_nonneg hbReal zero_le_one
  have hinverse :=
    Real.inv_norm_le_inv_sqrt_norm_of_one_le t ht
  have hmul := mul_le_mul_of_nonneg_left hinverse hnumerator
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ ((b : ℝ) + 1) / Real.sqrt ‖t‖)
    (div_eq_mul_inv ((b : ℝ) + 1) ‖t‖).symm
    (Eq.subst
      (motive := fun right : ℝ =>
        ((b : ℝ) + 1) * ‖t‖⁻¹ ≤ right)
      (div_eq_mul_inv ((b : ℝ) + 1) (Real.sqrt ‖t‖)).symm
      hmul)

theorem Real.logarithmicPhaseQuantitativeNormTarget_le_sqrtTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    Real.logarithmicPhaseQuantitativeNormTarget t b ≤
      Real.logarithmicPhaseQuantitativeSqrtTarget t b := by
  unfold Real.logarithmicPhaseQuantitativeNormTarget
  unfold Real.logarithmicPhaseQuantitativeSqrtTarget
  exact add_le_add_right
    (Real.endpoint_div_norm_le_endpoint_div_sqrt_norm t b ht hb)
    (Real.sqrt (1 + ‖t‖))

theorem Real.twenty_twenty_forty_mul_target_le_eighty
    (target : ℝ) :
    20 * target + 20 * target + 40 * target ≤ 80 * target := by
  exact Real.logarithmicPhase_twenty_twenty_forty_targets_le_eighty target

theorem Real.eighty_mul_normTarget_le_eighty_mul_sqrtTarget
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    80 * Real.logarithmicPhaseQuantitativeNormTarget t b ≤
      80 * Real.logarithmicPhaseQuantitativeSqrtTarget t b := by
  exact mul_le_mul_of_nonneg_left
    (Real.logarithmicPhaseQuantitativeNormTarget_le_sqrtTarget t b ht hb)
    (Nat.cast_nonneg 80)

theorem Complex.logarithmicPhaseQuantitativeThreeComponentBudget_le_eightyNormTarget
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hactive :
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcrossing :
      Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcomplement :
      Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b ≤
        40 * Real.logarithmicPhaseQuantitativeNormTarget t b) :
    Complex.logarithmicPhaseQuantitativeThreeComponentBudget t a b radius ≤
      80 * Real.logarithmicPhaseQuantitativeNormTarget t b := by
  unfold Complex.logarithmicPhaseQuantitativeThreeComponentBudget
  have hcomponents := add_le_add
    (add_le_add hactive hcrossing) hcomplement
  exact le_trans hcomponents
    (Real.twenty_twenty_forty_mul_target_le_eighty
      (Real.logarithmicPhaseQuantitativeNormTarget t b))

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_eightyNormTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hactive :
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcrossing :
      Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcomplement :
      Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b ≤
        40 * Real.logarithmicPhaseQuantitativeNormTarget t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseQuantitativeNormTarget t b := by
  have hblock :=
    Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_threeComponentBudget
      t ht htNonneg a b ha hab radius hradius
  have harithmetic :=
    Complex.logarithmicPhaseQuantitativeThreeComponentBudget_le_eightyNormTarget
      t a b radius hactive hcrossing hcomplement
  exact le_trans hblock harithmetic

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_eightySqrtTarget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hb : 0 ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hactive :
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcrossing :
      Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius ≤
        20 * Real.logarithmicPhaseQuantitativeNormTarget t b)
    (hcomplement :
      Complex.logarithmicPhaseQuantitativeComplementTailBudget t a b ≤
        40 * Real.logarithmicPhaseQuantitativeNormTarget t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseQuantitativeSqrtTarget t b := by
  have hnormTarget :=
    Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_eightyNormTarget
      t ht htNonneg a b ha hab radius hradius
      hactive hcrossing hcomplement
  have htarget :=
    Real.eighty_mul_normTarget_le_eighty_mul_sqrtTarget t b ht hb
  exact le_trans hnormTarget htarget

end
end LFunctions
end Boundary

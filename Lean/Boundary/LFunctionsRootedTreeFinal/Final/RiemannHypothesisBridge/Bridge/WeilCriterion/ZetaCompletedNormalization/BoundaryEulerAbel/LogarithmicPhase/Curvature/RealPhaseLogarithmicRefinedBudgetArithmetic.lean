import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeRefinedBProcessBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDirectPoissonArithmetic

/-!
# Arithmetic for the refined logarithmic B-process budget

This owner performs the numerical assembly for the exact four-family packet
decomposition.  Fixed collar constants are absorbed by the square-root term,
while endpoint-length terms are absorbed by the quotient term.  All cast and
coefficient transports are named so the eventual unconditional long theorem
is a thin composition of analytic estimates and this arithmetic owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logarithmicPhaseRefinedScale
    (t : ℝ) (b : ℤ) : ℝ :=
  ((b : ℝ) + 1) / ‖t‖ + Real.sqrt (1 + ‖t‖)

theorem Real.logarithmicPhaseRefinedScale_eq_directScale
    (t : ℝ) (b : ℤ) :
    Real.logarithmicPhaseRefinedScale t b =
      Real.logarithmicPhaseDirectPoissonTarget t b := by
  rfl

theorem Real.logarithmicPhaseRefinedScale_nonneg
    (t : ℝ) (b : ℤ)
    (hb : 0 ≤ b) :
    0 ≤ Real.logarithmicPhaseRefinedScale t b := by
  unfold Real.logarithmicPhaseRefinedScale
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  have hnumerator : (0 : ℝ) ≤ (b : ℝ) + 1 :=
    add_nonneg hbReal zero_le_one
  have hquotient : (0 : ℝ) ≤ ((b : ℝ) + 1) / ‖t‖ :=
    div_nonneg hnumerator (norm_nonneg t)
  have hsquareRoot : (0 : ℝ) ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg _
  exact add_nonneg hquotient hsquareRoot

theorem Real.one_le_logarithmicPhaseRefinedScale
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    (1 : ℝ) ≤ Real.logarithmicPhaseRefinedScale t b := by
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  have hdirect :=
    Real.one_le_logarithmicPhaseDirectPoissonTarget t b ht hbReal
  exact Eq.subst
    (motive := fun scale : ℝ => 1 ≤ scale)
    (Real.logarithmicPhaseRefinedScale_eq_directScale t b).symm
    hdirect

theorem Real.constant_le_constant_mul_logarithmicPhaseRefinedScale
    (t : ℝ) (b : ℤ) (C : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b)
    (hC : 0 ≤ C) :
    C ≤ C * Real.logarithmicPhaseRefinedScale t b := by
  have hone := Real.one_le_logarithmicPhaseRefinedScale t b ht hb
  have hmul := mul_le_mul_of_nonneg_left hone hC
  exact le_trans (le_of_eq (mul_one C).symm) hmul

theorem Real.two_thirds_le_refinedScale
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    (2 : ℝ) / 3 ≤ Real.logarithmicPhaseRefinedScale t b := by
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have htwoLeThree : (2 : ℝ) ≤ 3 := by
    have honeNonneg : (0 : ℝ) ≤ 1 := zero_le_one
    have hstep : (2 : ℝ) ≤ 2 + 1 := le_add_of_nonneg_right honeNonneg
    have hsum : (2 : ℝ) + 1 = 3 := by
      exact Eq.trans
        (Nat.cast_add 2 1).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ))
            (show (2 + 1 : ℕ) = 3 from rfl))
          Nat.cast_ofNat)
    exact hstep.trans_eq hsum
  have hfraction : (2 : ℝ) / 3 ≤ 1 :=
    (div_le_one hthreePos).mpr htwoLeThree
  exact le_trans hfraction
    (Real.one_le_logarithmicPhaseRefinedScale t b ht hb)

theorem Real.four_thirds_le_two_refinedScale
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    (4 : ℝ) / 3 ≤ 2 * Real.logarithmicPhaseRefinedScale t b := by
  have hdirect :=
    Real.four_div_three_le_two_mul_logarithmicPhaseDirectPoissonTarget
      t b ht (Int.cast_nonneg.mpr hb)
  exact Eq.subst
    (motive := fun scale : ℝ => (4 : ℝ) / 3 ≤ 2 * scale)
    (Real.logarithmicPhaseRefinedScale_eq_directScale t b).symm
    hdirect

theorem Real.eight_thirds_le_four_refinedScale
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    (8 : ℝ) / 3 ≤ 4 * Real.logarithmicPhaseRefinedScale t b := by
  have hdirect :=
    Real.eight_div_three_le_four_mul_logarithmicPhaseDirectPoissonTarget
      t b ht (Int.cast_nonneg.mpr hb)
  exact Eq.subst
    (motive := fun scale : ℝ => (8 : ℝ) / 3 ≤ 4 * scale)
    (Real.logarithmicPhaseRefinedScale_eq_directScale t b).symm
    hdirect

theorem Real.sixteen_thirds_le_eight_refinedScale
    (t : ℝ) (b : ℤ)
    (ht : 1 ≤ ‖t‖)
    (hb : 0 ≤ b) :
    (16 : ℝ) / 3 ≤ 8 * Real.logarithmicPhaseRefinedScale t b := by
  have hbase := Real.eight_thirds_le_four_refinedScale t b ht hb
  have hdouble := mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg 2)
  have hleft : 2 * ((8 : ℝ) / 3) = (16 : ℝ) / 3 := by
    calc
      2 * ((8 : ℝ) / 3) = (2 * 8 : ℝ) / 3 :=
        (mul_div_assoc 2 8 3).symm
      _ = (16 : ℝ) / 3 :=
        congrArg (fun numerator : ℝ => numerator / 3)
          (show (2 : ℝ) * 8 = 16 from rfl)
  have hright :
      2 * (4 * Real.logarithmicPhaseRefinedScale t b) =
        8 * Real.logarithmicPhaseRefinedScale t b := by
    calc
      2 * (4 * Real.logarithmicPhaseRefinedScale t b) =
          (2 * 4) * Real.logarithmicPhaseRefinedScale t b :=
        (mul_assoc 2 4 _).symm
      _ = 8 * Real.logarithmicPhaseRefinedScale t b :=
        congrArg
          (fun coefficient : ℝ =>
            coefficient * Real.logarithmicPhaseRefinedScale t b)
          (show (2 : ℝ) * 4 = 8 from rfl)
  exact le_trans (le_of_eq hleft.symm)
    (le_trans hdouble (le_of_eq hright))

theorem Real.endpoint_add_one_pos
    (b : ℤ)
    (hb : 0 ≤ b) :
    0 < (b : ℝ) + 1 := by
  have hbReal : (0 : ℝ) ≤ (b : ℝ) := Int.cast_nonneg.mpr hb
  exact add_pos_of_nonneg_of_pos hbReal zero_lt_one

theorem Real.endpoint_div_norm_nonneg
    (t : ℝ) (b : ℤ)
    (hb : 0 ≤ b) :
    0 ≤ ((b : ℝ) + 1) / ‖t‖ := by
  have hnumerator := (Real.endpoint_add_one_pos b hb).le
  exact div_nonneg hnumerator (norm_nonneg t)

theorem Real.endpoint_div_norm_le_refinedScale
    (t : ℝ) (b : ℤ) :
    ((b : ℝ) + 1) / ‖t‖ ≤
      Real.logarithmicPhaseRefinedScale t b := by
  unfold Real.logarithmicPhaseRefinedScale
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)

theorem Real.sqrt_scale_le_refinedScale
    (t : ℝ) (b : ℤ)
    (hb : 0 ≤ b) :
    Real.sqrt (1 + ‖t‖) ≤ Real.logarithmicPhaseRefinedScale t b := by
  unfold Real.logarithmicPhaseRefinedScale
  have hquotient := Real.endpoint_div_norm_nonneg t b hb
  exact le_add_of_nonneg_left hquotient

theorem Real.coefficient_endpoint_div_norm_le_refined
    (t : ℝ) (b : ℤ) (C : ℝ)
    (hC : 0 ≤ C) :
    C * (((b : ℝ) + 1) / ‖t‖) ≤
      C * Real.logarithmicPhaseRefinedScale t b := by
  exact mul_le_mul_of_nonneg_left
    (Real.endpoint_div_norm_le_refinedScale t b) hC

theorem Real.coefficient_sqrt_scale_le_refined
    (t : ℝ) (b : ℤ) (C : ℝ)
    (hb : 0 ≤ b)
    (hC : 0 ≤ C) :
    C * Real.sqrt (1 + ‖t‖) ≤
      C * Real.logarithmicPhaseRefinedScale t b := by
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_scale_le_refinedScale t b hb) hC

theorem Real.refined_component_coefficients_eq_eighty
    (scale : ℝ) :
    20 * scale + 20 * scale + (20 * scale + 20 * scale) =
      80 * scale := by
  have hfirst : 20 * scale + 20 * scale = 40 * scale := by
    calc
      20 * scale + 20 * scale = (20 + 20) * scale :=
        (add_mul 20 20 scale).symm
      _ = 40 * scale :=
        congrArg (fun coefficient : ℝ => coefficient * scale)
          (show (20 : ℝ) + 20 = 40 from rfl)
  have hsecond :
      40 * scale + 40 * scale = 80 * scale := by
    calc
      40 * scale + 40 * scale = (40 + 40) * scale :=
        (add_mul 40 40 scale).symm
      _ = 80 * scale :=
        congrArg (fun coefficient : ℝ => coefficient * scale)
          (show (40 : ℝ) + 40 = 80 from rfl)
  calc
    20 * scale + 20 * scale + (20 * scale + 20 * scale) =
        40 * scale + 40 * scale :=
      congrArg₂ (fun first second : ℝ => first + second) hfirst hfirst
    _ = 80 * scale := hsecond

theorem Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget_le_eighty
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hactive :
      Complex.logarithmicPhaseQuantitativeRefinedActiveBudget t a b radius ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (hendpoint :
      Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget t a b radius ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (houtside :
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b ≤
        20 * Real.logarithmicPhaseRefinedScale t b) :
    Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget t a b radius ≤
      80 * Real.logarithmicPhaseRefinedScale t b := by
  have hcomponents :=
    Complex.logarithmicPhaseQuantitativeRefinedBudget_upper_of_components
      t a b radius
      (20 * Real.logarithmicPhaseRefinedScale t b)
      (20 * Real.logarithmicPhaseRefinedScale t b)
      (20 * Real.logarithmicPhaseRefinedScale t b)
      (20 * Real.logarithmicPhaseRefinedScale t b)
      hactive hendpoint hinactive houtside
  have harithmetic :=
    Real.refined_component_coefficients_eq_eighty
      (Real.logarithmicPhaseRefinedScale t b)
  exact le_trans hcomponents (le_of_eq harithmetic)

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_eighty_refined
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hactive :
      Complex.logarithmicPhaseQuantitativeRefinedActiveBudget t a b radius ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (hendpoint :
      Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget t a b radius ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
        20 * Real.logarithmicPhaseRefinedScale t b)
    (houtside :
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b ≤
        20 * Real.logarithmicPhaseRefinedScale t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseRefinedScale t b := by
  have hblock :=
    Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_refined_budget
      t ht htNonneg a b ha hab radius hradius
  have harithmetic :=
    Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget_le_eighty
      t a b radius hactive hendpoint hinactive houtside
  exact le_trans hblock harithmetic

end
end LFunctions
end Boundary

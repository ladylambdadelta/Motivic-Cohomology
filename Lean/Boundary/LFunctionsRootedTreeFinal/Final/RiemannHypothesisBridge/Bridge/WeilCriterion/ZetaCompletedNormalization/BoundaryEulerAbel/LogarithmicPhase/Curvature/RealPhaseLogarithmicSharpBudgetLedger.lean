import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpBProcessBudget

/-!
# Exact coefficient ledger for the sharp B-process budget

This file records the presently proved arithmetic constants without rounding
them into the desired final constant.  The resulting ledger identifies the
remaining saving that must be supplied by sharper active/finite interaction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.four_ledger_terms_reassociate
    (a b c d : ℝ) :
    a + ((b + c) + d) = a + b + c + d := by
  exact Eq.trans
    (congrArg (fun value : ℝ => a + value) (add_assoc b c d))
    (Eq.trans (add_assoc a b (c + d)).symm
      (congrArg (fun value : ℝ => value + d)
        (add_assoc a b c).symm))

def Complex.logarithmicPhaseSharpActiveLedger
    (t : ℝ) : ℝ :=
  56 * Complex.logarithmicPhaseBProcessScale t

def Complex.logarithmicPhaseSharpFiniteLedger
    (t : ℝ) : ℝ :=
  (37 / 2 : ℝ) * Complex.logarithmicPhaseBProcessScale t

def Complex.logarithmicPhaseSharpZeroLedger
    (t : ℝ) (b : ℕ) : ℝ :=
  (11 / 3 : ℝ) * Real.logarithmicPhaseRefinedScale t (b : ℤ)

def Complex.logarithmicPhaseSharpInfiniteTailLedger
    (t : ℝ) (b : ℕ) : ℝ :=
  19 * Real.logarithmicPhaseRefinedScale t (b : ℤ)

def Complex.logarithmicPhaseSharpTotalLedger
    (t : ℝ) (b : ℕ) : ℝ :=
  Complex.logarithmicPhaseSharpActiveLedger t +
    Complex.logarithmicPhaseSharpFiniteLedger t +
      Complex.logarithmicPhaseSharpZeroLedger t b +
        Complex.logarithmicPhaseSharpInfiniteTailLedger t b

def Complex.logarithmicPhaseSharpLedgerSavingRequired : ℝ :=
  103 / 6

theorem Real.BProcessScale_le_refinedScale
    (t : ℝ) (b : ℕ) :
    Complex.logarithmicPhaseBProcessScale t ≤
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessScale
  unfold Real.logarithmicPhaseRefinedScale
  have hnormPos : 0 ≤ ‖t‖ := norm_nonneg t
  have hnumerator : 0 ≤ ((b : ℤ) : ℝ) + 1 := by
    exact add_nonneg (Int.cast_nonneg.mpr (Int.ofNat_zero_le b)) zero_le_one
  have hquotient : 0 ≤ (((b : ℤ) : ℝ) + 1) / ‖t‖ :=
    div_nonneg hnumerator hnormPos
  exact le_add_of_nonneg_left hquotient

theorem Complex.logarithmicPhaseSharpActiveBudget_le_ledger
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessCompleteActiveBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpActiveLedger t := by
  unfold Complex.logarithmicPhaseSharpActiveLedger
  exact
    Complex.logarithmicPhaseBProcessCompleteActiveBudget_le_fifty_six_scale
      ht hgeometry

theorem Complex.logarithmicPhaseSharpFiniteBudget_le_ledger
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpFiniteLedger t := by
  unfold Complex.logarithmicPhaseSharpFiniteLedger
  exact
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_thirty_seven_halves_scale
      t ht ht_nonneg a b hgeometry

theorem Complex.logarithmicPhaseSharpZeroBudget_le_ledger
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseQuantitativeZeroModeBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpZeroLedger t b := by
  unfold Complex.logarithmicPhaseSharpZeroLedger
  exact
    Complex.logarithmicPhaseQuantitativeZeroModeBudget_le_eleven_thirds_refined
      t a b ht
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)

theorem Complex.logarithmicPhaseSharpInfiniteTailBudget_le_ledger
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpOutsideTailBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpInfiniteTailLedger t b := by
  unfold Complex.logarithmicPhaseSharpOutsideTailBudget
  unfold Complex.logarithmicPhaseSharpInfiniteTailLedger
  exact
    Complex.logarithmicPhaseInfiniteTailBudget_le_nineteen_refined
      t a b ht hgeometry

theorem Complex.logarithmicPhaseSharpBProcessBudget_le_totalLedger
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpTotalLedger t b := by
  have hactive :=
    Complex.logarithmicPhaseSharpActiveBudget_le_ledger ht hgeometry
  have hfinite :=
    Complex.logarithmicPhaseSharpFiniteBudget_le_ledger
      ht ht_nonneg hgeometry
  have hzero :=
    Complex.logarithmicPhaseSharpZeroBudget_le_ledger ht hgeometry
  have htail :=
    Complex.logarithmicPhaseSharpInfiniteTailBudget_le_ledger ht hgeometry
  unfold Complex.logarithmicPhaseSharpBProcessBudget
  unfold Complex.logarithmicPhaseSharpComplementBudget
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  unfold Complex.logarithmicPhaseSharpTotalLedger
  have hsum := add_le_add hactive
    (add_le_add (add_le_add hfinite hzero) htail)
  exact le_trans hsum
    (le_of_eq (Real.four_ledger_terms_reassociate
      (Complex.logarithmicPhaseSharpActiveLedger t)
      (Complex.logarithmicPhaseSharpFiniteLedger t)
      (Complex.logarithmicPhaseSharpZeroLedger t b)
      (Complex.logarithmicPhaseSharpInfiniteTailLedger t b)))

theorem Real.sharpLedger_coefficient_eq_five_hundred_eighty_three_sixths :
    (56 : ℝ) + 37 / 2 + 11 / 3 + 19 = 583 / 6 := by
  rfl

theorem Real.sharpLedger_saving_identity :
    (583 / 6 : ℝ) = 80 + 103 / 6 := by
  rfl

theorem Complex.logarithmicPhaseSharpTotalLedger_le_five_hundred_eighty_three_sixths_refined
    (t : ℝ) (b : ℕ) :
    Complex.logarithmicPhaseSharpTotalLedger t b ≤
      (583 / 6 : ℝ) * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hscale := Real.BProcessScale_le_refinedScale t b
  have hactive := mul_le_mul_of_nonneg_left hscale (OfNat.zero_le 56)
  have hfinite := mul_le_mul_of_nonneg_left hscale
    (div_nonneg (OfNat.zero_le 37) (OfNat.zero_le 2))
  unfold Complex.logarithmicPhaseSharpTotalLedger
  unfold Complex.logarithmicPhaseSharpActiveLedger
  unfold Complex.logarithmicPhaseSharpFiniteLedger
  unfold Complex.logarithmicPhaseSharpZeroLedger
  unfold Complex.logarithmicPhaseSharpInfiniteTailLedger
  have hsum := add_le_add
    (add_le_add (add_le_add hactive hfinite) (le_refl _)) (le_refl _)
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (Real.four_weighted_terms_eq_sum_coeff_mul
          56 (37 / 2) (11 / 3) 19
          (Real.logarithmicPhaseRefinedScale t (b : ℤ)))
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Real.logarithmicPhaseRefinedScale t (b : ℤ))
          Real.sharpLedger_coefficient_eq_five_hundred_eighty_three_sixths)))

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactInfiniteTailLedger

/-!
# Exact sharp-budget coefficient ledger

This owner replaces the rounded `19R` infinite-tail entry by the exact
negative and positive majorants and records the resulting rational deficit
against the authoritative coefficient `80`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseExactTailRefinedCoefficient : ℝ :=
  5 + Complex.logarithmicPhaseExactPositiveTailConstant

def Complex.logarithmicPhaseExactSharpLedgerCoefficient : ℝ :=
  56 + 37 / 2 + 11 / 3 +
    Complex.logarithmicPhaseExactTailRefinedCoefficient

def Complex.logarithmicPhaseExactSharpLedgerSavingRequired : ℝ :=
  Complex.logarithmicPhaseExactSharpLedgerCoefficient - 80

def Complex.logarithmicPhaseExactSharpTotalLedger
    (t : ℝ) (b : ℕ) : ℝ :=
  Complex.logarithmicPhaseSharpActiveLedger t +
    Complex.logarithmicPhaseSharpFiniteLedger t +
      Complex.logarithmicPhaseSharpZeroLedger t b +
        Complex.logarithmicPhaseExactInfiniteTailMajorant t

theorem Complex.logarithmicPhaseExactTailRefinedCoefficient_nonneg :
    0 ≤ Complex.logarithmicPhaseExactTailRefinedCoefficient := by
  unfold Complex.logarithmicPhaseExactTailRefinedCoefficient
  exact add_nonneg (Nat.cast_nonneg 5)
    Complex.logarithmicPhaseExactPositiveTailConstant_nonneg

theorem Real.four_le_four_mul_refinedScale
    (t : ℝ) (b : ℕ) (ht : 1 ≤ ‖t‖) :
    (4 : ℝ) ≤ 4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hone := Real.one_le_logarithmicPhaseRefinedScale
    t (b : ℤ) ht (Int.ofNat_zero_le b)
  have hmul := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg 4)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    (mul_one (4 : ℝ)) hmul

theorem Real.sqrt_le_refinedScale_nat
    (t : ℝ) (b : ℕ) :
    Real.sqrt (1 + ‖t‖) ≤
      Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  exact Real.sqrt_scale_le_refinedScale t (b : ℤ)
    (Int.ofNat_zero_le b)

theorem Complex.logarithmicPhaseExactPositiveTailConstant_le_constant_mul_refined
    (t : ℝ) (b : ℕ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseExactPositiveTailConstant ≤
      Complex.logarithmicPhaseExactPositiveTailConstant *
        Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  exact Real.constant_le_constant_mul_logarithmicPhaseRefinedScale
    t (b : ℤ) Complex.logarithmicPhaseExactPositiveTailConstant
    ht (Int.ofNat_zero_le b)
    Complex.logarithmicPhaseExactPositiveTailConstant_nonneg

theorem Complex.logarithmicPhaseExactInfiniteTailMajorant_le_exactCoefficient_refined
    (t : ℝ) (b : ℕ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseExactInfiniteTailMajorant t ≤
      Complex.logarithmicPhaseExactTailRefinedCoefficient *
        Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hfour := Real.four_le_four_mul_refinedScale t b ht
  have hsqrt := Real.sqrt_le_refinedScale_nat t b
  have hpositive :=
    Complex.logarithmicPhaseExactPositiveTailConstant_le_constant_mul_refined
      t b ht
  unfold Complex.logarithmicPhaseExactInfiniteTailMajorant
  unfold Complex.logarithmicPhaseExactNegativeTailMajorant
  unfold Complex.logarithmicPhaseExactTailRefinedCoefficient
  have hsum := add_le_add (add_le_add hfour hsqrt) hpositive
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (congrArg
          (fun value : ℝ => value +
            Complex.logarithmicPhaseExactPositiveTailConstant *
              Real.logarithmicPhaseRefinedScale t (b : ℤ))
          (Eq.trans
            (congrArg
              (fun value : ℝ =>
                4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) + value)
              (one_mul
                (Real.logarithmicPhaseRefinedScale t (b : ℤ))).symm)
            (add_mul 4 1
              (Real.logarithmicPhaseRefinedScale t (b : ℤ))).symm))
        (add_mul 5 Complex.logarithmicPhaseExactPositiveTailConstant
          (Real.logarithmicPhaseRefinedScale t (b : ℤ))).symm))

theorem Complex.logarithmicPhaseSharpBProcessBudget_le_exactTotalLedger
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpBProcessBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseExactSharpTotalLedger t b := by
  have hactive :=
    Complex.logarithmicPhaseSharpActiveBudget_le_ledger ht hgeometry
  have hfinite :=
    Complex.logarithmicPhaseSharpFiniteBudget_le_ledger
      ht ht_nonneg hgeometry
  have hzero :=
    Complex.logarithmicPhaseSharpZeroBudget_le_ledger ht hgeometry
  have htail :=
    Complex.logarithmicPhaseSharpOutsideTailBudget_le_exactMajorant
      t a b ht hgeometry
  unfold Complex.logarithmicPhaseSharpBProcessBudget
  unfold Complex.logarithmicPhaseSharpComplementBudget
  unfold Complex.logarithmicPhaseSharpFiniteComplementBudget
  unfold Complex.logarithmicPhaseExactSharpTotalLedger
  have hsum := add_le_add hactive
    (add_le_add (add_le_add hfinite hzero) htail)
  exact le_trans hsum
    (le_of_eq
      (Real.four_ledger_terms_reassociate
        (Complex.logarithmicPhaseSharpActiveLedger t)
        (Complex.logarithmicPhaseSharpFiniteLedger t)
        (Complex.logarithmicPhaseSharpZeroLedger t b)
        (Complex.logarithmicPhaseExactInfiniteTailMajorant t)))

theorem Real.exactSharpLedger_coefficient_fraction :
    (56 : ℝ) + 37 / 2 + 11 / 3 + (5 + 61683 / 4608) =
      1334745 / 13824 := by
  have hdenominatorNonzero : (13824 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 13823))
  have hdenominatorTwo : (13824 : ℝ) = 2 * 6912 := by
    have hnat : (13824 : ℕ) = 2 * 6912 := rfl
    exact Eq.trans Nat.cast_ofNat.symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 2 6912))
  have hdenominatorThree : (13824 : ℝ) = 3 * 4608 := by
    have hnat : (13824 : ℕ) = 3 * 4608 := rfl
    exact Eq.trans Nat.cast_ofNat.symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 3 4608))
  have hdenominatorPositiveTail : (13824 : ℝ) = 4608 * 3 := by
    exact Eq.trans hdenominatorThree (mul_comm (3 : ℝ) 4608)
  have hfiftySix : (56 : ℝ) * 13824 = 774144 := by
    have hnat : (56 * 13824 : ℕ) = 774144 := rfl
    exact Eq.trans (Nat.cast_mul 56 13824).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hthirtySevenProduct : (37 : ℝ) * 6912 = 255744 := by
    have hnat : (37 * 6912 : ℕ) = 255744 := rfl
    exact Eq.trans (Nat.cast_mul 37 6912).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hthirtySeven : (37 / 2 : ℝ) * 13824 = 255744 := by
    have htwoNonzero : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
    have hcancel : (37 / 2 : ℝ) * 2 = 37 :=
      div_mul_cancel₀ 37 htwoNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (37 / 2 : ℝ) * value)
        hdenominatorTwo)
      (Eq.trans
        (mul_assoc (37 / 2 : ℝ) 2 6912).symm
        (Eq.trans
          (congrArg (fun value : ℝ => value * 6912) hcancel)
          hthirtySevenProduct))
  have helevenProduct : (11 : ℝ) * 4608 = 50688 := by
    have hnat : (11 * 4608 : ℕ) = 50688 := rfl
    exact Eq.trans (Nat.cast_mul 11 4608).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have heleven : (11 / 3 : ℝ) * 13824 = 50688 := by
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hcancel : (11 / 3 : ℝ) * 3 = 11 :=
      div_mul_cancel₀ 11 hthreeNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (11 / 3 : ℝ) * value)
        hdenominatorThree)
      (Eq.trans
        (mul_assoc (11 / 3 : ℝ) 3 4608).symm
        (Eq.trans
          (congrArg (fun value : ℝ => value * 4608) hcancel)
          helevenProduct))
  have hfive : (5 : ℝ) * 13824 = 69120 := by
    have hnat : (5 * 13824 : ℕ) = 69120 := rfl
    exact Eq.trans (Nat.cast_mul 5 13824).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hpositiveProduct : (61683 : ℝ) * 3 = 185049 := by
    have hnat : (61683 * 3 : ℕ) = 185049 := rfl
    exact Eq.trans (Nat.cast_mul 61683 3).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hpositive : (61683 / 4608 : ℝ) * 13824 = 185049 := by
    have hdenominatorNonzero : (4608 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 4607))
    have hcancel : (61683 / 4608 : ℝ) * 4608 = 61683 :=
      div_mul_cancel₀ 61683 hdenominatorNonzero
    exact Eq.trans
      (congrArg (fun value : ℝ => (61683 / 4608 : ℝ) * value)
        hdenominatorPositiveTail)
      (Eq.trans
        (mul_assoc (61683 / 4608 : ℝ) 4608 3).symm
        (Eq.trans
          (congrArg (fun value : ℝ => value * 3) hcancel)
          hpositiveProduct))
  have hfirstPair :
      ((56 : ℝ) + 37 / 2) * 13824 =
        56 * 13824 + (37 / 2) * 13824 :=
    add_mul 56 (37 / 2) 13824
  have hfirstThree :
      ((56 : ℝ) + 37 / 2 + 11 / 3) * 13824 =
        56 * 13824 + (37 / 2) * 13824 + (11 / 3) * 13824 := by
    exact Eq.trans
      (add_mul ((56 : ℝ) + 37 / 2) (11 / 3) 13824)
      (congrArg (fun value : ℝ => value + (11 / 3) * 13824)
        hfirstPair)
  have hfinalPair :
      ((5 : ℝ) + 61683 / 4608) * 13824 =
        5 * 13824 + (61683 / 4608) * 13824 :=
    add_mul 5 (61683 / 4608) 13824
  have hdistributed :
      ((56 : ℝ) + 37 / 2 + 11 / 3 + (5 + 61683 / 4608)) * 13824 =
        (56 * 13824 + (37 / 2) * 13824 + (11 / 3) * 13824) +
          (5 * 13824 + (61683 / 4608) * 13824) := by
    exact Eq.trans
      (add_mul ((56 : ℝ) + 37 / 2 + 11 / 3)
        (5 + 61683 / 4608) 13824)
      (congrArg₂ (fun left right : ℝ => left + right)
        hfirstThree hfinalPair)
  have hnormalized :
      (56 * 13824 + (37 / 2 : ℝ) * 13824 + (11 / 3) * 13824) +
          (5 * 13824 + (61683 / 4608) * 13824) =
        (774144 : ℝ) + 255744 + 50688 + (69120 + 185049) := by
    exact congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          hfiftySix hthirtySeven)
        heleven)
      (congrArg₂ (fun left right : ℝ => left + right) hfive hpositive)
  have hleftPair :
      (774144 : ℝ) + 255744 = ((774144 + 255744 : ℕ) : ℝ) :=
    (Nat.cast_add 774144 255744).symm
  have hleftThree :
      (774144 : ℝ) + 255744 + 50688 =
        ((774144 + 255744 + 50688 : ℕ) : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 50688) hleftPair)
      (Nat.cast_add (774144 + 255744) 50688).symm
  have hrightPair :
      (69120 : ℝ) + 185049 = ((69120 + 185049 : ℕ) : ℝ) :=
    (Nat.cast_add 69120 185049).symm
  have hcastSum :
      (774144 : ℝ) + 255744 + 50688 + (69120 + 185049) =
        ((774144 + 255744 + 50688 + (69120 + 185049) : ℕ) : ℝ) := by
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        hleftThree hrightPair)
      (Nat.cast_add (774144 + 255744 + 50688) (69120 + 185049)).symm
  have hnatSum :
      (774144 + 255744 + 50688 + (69120 + 185049) : ℕ) = 1334745 := rfl
  have hsum :
      (774144 : ℝ) + 255744 + 50688 + (69120 + 185049) = 1334745 := by
    exact Eq.trans hcastSum
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnatSum)
        Nat.cast_ofNat)
  have hscaled := Eq.trans hdistributed (Eq.trans hnormalized hsum)
  exact (eq_div_iff hdenominatorNonzero).mpr hscaled

theorem Real.exactSharpLedger_saving_fraction :
    (1334745 / 13824 : ℝ) - 80 = 228825 / 13824 := by
  have hdenominatorNonzero : (13824 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 13823))
  have hquotient : (1334745 / 13824 : ℝ) * 13824 = 1334745 :=
    div_mul_cancel₀ 1334745 hdenominatorNonzero
  have heighty : (80 : ℝ) * 13824 = 1105920 := by
    have hnat : (80 * 13824 : ℕ) = 1105920 := rfl
    exact Eq.trans (Nat.cast_mul 80 13824).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hdistributed :
      ((1334745 / 13824 : ℝ) - 80) * 13824 =
        (1334745 / 13824) * 13824 - 80 * 13824 :=
    sub_mul (1334745 / 13824 : ℝ) 80 13824
  have hnormalized :
      (1334745 / 13824 : ℝ) * 13824 - 80 * 13824 =
        1334745 - 1105920 :=
    congrArg₂ (fun left right : ℝ => left - right) hquotient heighty
  have hadd : (228825 : ℝ) + 1105920 = 1334745 := by
    have hnat : (228825 + 1105920 : ℕ) = 1334745 := rfl
    exact Eq.trans (Nat.cast_add 228825 1105920).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hdifference : (1334745 : ℝ) - 1105920 = 228825 :=
    (eq_sub_of_add_eq hadd).symm
  have hscaled := Eq.trans hdistributed
    (Eq.trans hnormalized hdifference)
  exact (eq_div_iff hdenominatorNonzero).mpr hscaled

theorem Complex.logarithmicPhaseExactSharpLedgerCoefficient_eq_fraction :
    Complex.logarithmicPhaseExactSharpLedgerCoefficient =
      1334745 / 13824 := by
  unfold Complex.logarithmicPhaseExactSharpLedgerCoefficient
  unfold Complex.logarithmicPhaseExactTailRefinedCoefficient
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  exact Real.exactSharpLedger_coefficient_fraction

theorem Complex.logarithmicPhaseExactSharpLedgerSavingRequired_eq_fraction :
    Complex.logarithmicPhaseExactSharpLedgerSavingRequired =
      228825 / 13824 := by
  unfold Complex.logarithmicPhaseExactSharpLedgerSavingRequired
  exact Eq.trans
    (congrArg (fun value : ℝ => value - 80)
      Complex.logarithmicPhaseExactSharpLedgerCoefficient_eq_fraction)
    Real.exactSharpLedger_saving_fraction

theorem Complex.logarithmicPhaseExactSharpTotalLedger_le_exactCoefficient_refined
    (t : ℝ) (b : ℕ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseExactSharpTotalLedger t b ≤
      Complex.logarithmicPhaseExactSharpLedgerCoefficient *
        Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hscale := Real.BProcessScale_le_refinedScale t b
  have hactive := mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg 56)
  have hfinite := mul_le_mul_of_nonneg_left hscale
    (div_nonneg (Nat.cast_nonneg 37) (Nat.cast_nonneg 2))
  have htail :=
    Complex.logarithmicPhaseExactInfiniteTailMajorant_le_exactCoefficient_refined
      t b ht
  unfold Complex.logarithmicPhaseExactSharpTotalLedger
  unfold Complex.logarithmicPhaseSharpActiveLedger
  unfold Complex.logarithmicPhaseSharpFiniteLedger
  unfold Complex.logarithmicPhaseSharpZeroLedger
  unfold Complex.logarithmicPhaseExactSharpLedgerCoefficient
  have hsum := add_le_add
    (add_le_add (add_le_add hactive hfinite) (le_refl _)) htail
  exact le_trans hsum
    (le_of_eq
      (Real.four_weighted_terms_eq_sum_coeff_mul
        56 (37 / 2) (11 / 3)
        Complex.logarithmicPhaseExactTailRefinedCoefficient
        (Real.logarithmicPhaseRefinedScale t (b : ℤ))))

end

end LFunctions
end Boundary

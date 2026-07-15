import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.DyadicComparison
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDyadicPrefixBudget

/-!
# High-frequency logarithmic canonical prefix

The canonical prefix is not a comparable curvature block.  This file obtains
its logarithmic loss by aggregating the unconditional estimate on the exact
canonical dyadic partition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The canonical cutoff is positive. -/
theorem Complex.logarithmicPhase_canonicalCutoff_pos
    (t : ℝ) :
    0 < ⌊2 + ‖t‖⌋₊ := by
  have hone_le_two : (1 : ℝ) ≤ 2 := one_le_two
  have htwo_le_arg : (2 : ℝ) ≤ 2 + ‖t‖ :=
    le_add_of_nonneg_right (norm_nonneg t)
  exact Nat.floor_pos.mpr (le_trans hone_le_two htwo_le_arg)

/-- The canonical cutoff does not exceed its defining real endpoint. -/
theorem Complex.logarithmicPhase_canonicalCutoff_cast_le
    (t : ℝ) :
    ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ ‖t‖ + 2 := by
  have harg_nonneg : 0 ≤ (2 : ℝ) + ‖t‖ :=
    add_nonneg zero_le_two (norm_nonneg t)
  have hfloor : ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ 2 + ‖t‖ :=
    Nat.floor_le harg_nonneg
  exact Eq.subst
    (motive := fun right : ℝ =>
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ right)
    (add_comm 2 ‖t‖)
    hfloor

/-- Above frequency four, the endpoint part of the dyadic budget is bounded
by `9/2`. -/
theorem Complex.logarithmicPhase_canonicalCutoff_three_mul_div_le_nine_halves
    (t : ℝ)
    (ht4 : 4 < ‖t‖) :
    3 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖ ≤ 9 / 2 := by
  have hT_pos : 0 < ‖t‖ :=
    lt_trans zero_lt_four ht4
  have hC := Complex.logarithmicPhase_canonicalCutoff_cast_le t
  have htwice_C :
      2 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ 2 * (‖t‖ + 2) :=
    mul_le_mul_of_nonneg_left hC zero_le_two
  have hfour_le_T : (4 : ℝ) ≤ ‖t‖ := le_of_lt ht4
  have htwice_add : 2 * (‖t‖ + 2) = 2 * ‖t‖ + 4 := by
    calc
      2 * (‖t‖ + 2) = 2 * ‖t‖ + 2 * 2 :=
        mul_add 2 ‖t‖ 2
      _ = 2 * ‖t‖ + 4 := by
        exact congrArg (fun z : ℝ => 2 * ‖t‖ + z)
          (show (2 : ℝ) * 2 = 4 from
            Eq.trans (Nat.cast_mul 2 2).symm Nat.cast_ofNat)
  have htwo_add_le_three : 2 * ‖t‖ + 4 ≤ 3 * ‖t‖ := by
    have hadd := add_le_add_left hfour_le_T (2 * ‖t‖)
    have hright : 2 * ‖t‖ + ‖t‖ = 3 * ‖t‖ := by
      calc
        2 * ‖t‖ + ‖t‖ = 2 * ‖t‖ + 1 * ‖t‖ :=
          congrArg (fun z : ℝ => 2 * ‖t‖ + z) (one_mul ‖t‖).symm
        _ = (2 + 1) * ‖t‖ :=
          (add_mul 2 1 ‖t‖).symm
        _ = 3 * ‖t‖ :=
          congrArg (fun z : ℝ => z * ‖t‖)
            (calc
              (2 : ℝ) + 1 = ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
                congrArg₂ (fun x y : ℝ => x + y)
                  (Nat.cast_ofNat : ((2 : ℕ) : ℝ) = 2).symm
                  (Nat.cast_one : ((1 : ℕ) : ℝ) = 1).symm
              _ = ((2 + 1 : ℕ) : ℝ) := (Nat.cast_add 2 1).symm
              _ = 3 := congrArg (fun n : ℕ => (n : ℝ)) rfl)
    exact Eq.subst
      (motive := fun right : ℝ => 2 * ‖t‖ + 4 ≤ right)
      hright
      hadd
  have hcross :
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) * 2 ≤ ‖t‖ * 3 := by
    have hleft_commute :
        ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) * 2 =
          2 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
      mul_comm _ 2
    have hright_commute : ‖t‖ * 3 = 3 * ‖t‖ :=
      mul_comm ‖t‖ 3
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ ‖t‖ * 3)
      hleft_commute.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          2 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ right)
        hright_commute.symm
        (le_trans htwice_C
          (Eq.subst
            (motive := fun left : ℝ => left ≤ 3 * ‖t‖)
            htwice_add.symm
            htwo_add_le_three)))
  have hratio :
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖ ≤ 3 / 2 :=
    (div_le_div_iff₀ hT_pos zero_lt_two).mpr
      (Eq.subst
        (motive := fun right : ℝ =>
          ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) * 2 ≤ right)
        (mul_comm ‖t‖ 3)
        hcross)
  have hscaled := mul_le_mul_of_nonneg_left hratio
    (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
  have hright : 3 * (3 / 2 : ℝ) = 9 / 2 := by
    calc
      3 * (3 / 2 : ℝ) = (3 * 3 : ℝ) / 2 :=
        (mul_div_assoc 3 3 2).symm
      _ = 9 / 2 := by
        exact congrArg (fun z : ℝ => z / 2)
          (show (3 : ℝ) * 3 = 9 from
            Eq.trans (Nat.cast_mul 3 3).symm Nat.cast_ofNat)
  have hleft :
      3 * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖) =
        3 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖ :=
    (mul_div_assoc 3 ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ‖t‖).symm
  exact Eq.subst
    (motive := fun left : ℝ => left ≤ 9 / 2)
    hleft
    (Eq.subst
      (motive := fun right : ℝ =>
        3 * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖) ≤ right)
      hright
      hscaled)

/-- High frequency forces the transition square root above two. -/
theorem Complex.logarithmicPhase_two_le_sqrt_one_add_norm_of_four_lt
    (t : ℝ)
    (ht4 : 4 < ‖t‖) :
    2 ≤ Real.sqrt (1 + ‖t‖) := by
  have hfour_le : (4 : ℝ) ≤ 1 + ‖t‖ := by
    have hfive_lt : (5 : ℝ) < 1 + ‖t‖ :=
      Eq.subst
        (motive := fun left : ℝ => left < 1 + ‖t‖)
        (calc
          (1 : ℝ) + 4 = ((1 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) :=
            congrArg₂ (fun x y : ℝ => x + y)
              (Nat.cast_one : ((1 : ℕ) : ℝ) = 1).symm
              (Nat.cast_ofNat : ((4 : ℕ) : ℝ) = 4).symm
          _ = ((1 + 4 : ℕ) : ℝ) := (Nat.cast_add 1 4).symm
          _ = 5 := congrArg (fun n : ℕ => (n : ℝ)) rfl)
        (add_lt_add_left ht4 1)
    have hfour_lt_five : (4 : ℝ) < 5 := by
      exact Nat.cast_lt.mpr (Nat.lt_succ_self 4)
    exact le_of_lt (lt_trans hfour_lt_five hfive_lt)
  have htwo_sq : (2 : ℝ) ^ 2 = 4 := by
    exact Eq.trans (Nat.cast_pow 2 2).symm Nat.cast_ofNat
  exact Real.le_sqrt_of_sq_le
    (Eq.subst (motive := fun left : ℝ => left ≤ 1 + ‖t‖)
      htwo_sq.symm hfour_le)

/-- Above frequency four the canonical cutoff contains at least six samples. -/
theorem Complex.logarithmicPhase_six_le_canonicalCutoff_of_four_lt
    (t : ℝ)
    (ht4 : 4 < ‖t‖) :
    6 ≤ ⌊2 + ‖t‖⌋₊ := by
  have harg_nonneg : 0 ≤ (2 : ℝ) + ‖t‖ :=
    add_nonneg zero_le_two (norm_nonneg t)
  have hsix_lt : (6 : ℝ) < 2 + ‖t‖ := by
    have hadd := add_lt_add_left ht4 2
    have hleft : (2 : ℝ) + 4 = 6 := by
      exact Eq.trans (Nat.cast_add 2 4).symm Nat.cast_ofNat
    exact Eq.subst
      (motive := fun left : ℝ => left < 2 + ‖t‖)
      hleft
      hadd
  exact (Nat.le_floor_iff harg_nonneg).mpr (le_of_lt hsix_lt)

/-- The high-frequency canonical logarithm is at least two. -/
theorem Complex.logarithmicPhase_two_le_log_two_add_canonicalCutoff
    (t : ℝ)
    (ht4 : 4 < ‖t‖) :
    2 ≤ Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hC : 6 ≤ C :=
    Complex.logarithmicPhase_six_le_canonicalCutoff_of_four_lt t ht4
  have harg_le : (8 : ℝ) ≤ 2 + C := by
    have hcast : (6 : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hC
    have hadd := add_le_add_left hcast 2
    have hleft : (2 : ℝ) + 6 = 8 := by
      exact Eq.trans (Nat.cast_add 2 6).symm Nat.cast_ofNat
    exact Eq.subst
      (motive := fun left : ℝ => left ≤ 2 + (C : ℝ))
      hleft
      hadd
  have hlog_eight : (2 : ℝ) ≤ Real.log 8 := by
    have hthree_log :
        (2 : ℝ) ≤ 3 * Real.log (2 : ℝ) := by
      have hscaled := mul_le_mul_of_nonneg_left
        Complex.two_thirds_le_real_log_two
        (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
      have hleft : 3 * (2 / 3 : ℝ) = 2 := by
        calc
          3 * (2 / 3 : ℝ) = (3 * 2 : ℝ) / 3 :=
            (mul_div_assoc 3 2 3).symm
          _ = 6 / 3 := by
            exact congrArg (fun z : ℝ => z / 3)
              (show (3 : ℝ) * 2 = 6 from
                Eq.trans (Nat.cast_mul 3 2).symm Nat.cast_ofNat)
          _ = 2 := by
            exact div_eq_iff (show (3 : ℝ) ≠ 0 from ne_of_gt zero_lt_three) |>.mpr
              (show (6 : ℝ) = 2 * 3 from
                Eq.trans Nat.cast_ofNat.symm (Nat.cast_mul 2 3))
      exact Eq.subst
        (motive := fun left : ℝ => left ≤ 3 * Real.log (2 : ℝ))
        hleft hscaled
    have hlog_pow : Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
      have height : (8 : ℝ) = 2 ^ (3 : ℕ) := by
        exact Eq.trans Nat.cast_ofNat.symm (Nat.cast_pow 2 3)
      exact Eq.trans (congrArg Real.log height)
        (Real.log_pow (2 : ℝ) 3)
    exact Eq.subst
      (motive := fun right : ℝ => (2 : ℝ) ≤ right)
      hlog_pow.symm hthree_log
  have height_pos : (0 : ℝ) < 8 := Nat.cast_pos.mpr (Nat.zero_lt_succ 7)
  exact le_trans hlog_eight (Real.log_le_log height_pos harg_le)

/-- Monotonicity transports `log2 C` to the existing shifted dyadic-log
comparison theorem. -/
theorem Complex.logarithmicPhase_log2_canonicalCutoff_add_one_le_two_log
    (t : ℝ) :
    ((Nat.log2 ⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) ≤
      2 * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hlog_nat : Nat.log2 C ≤ Nat.log2 (C + 1) := by
    have hmono : Nat.log 2 C ≤ Nat.log 2 (C + 1) :=
      Nat.log_mono_right (Nat.le_add_right C 1)
    exact Eq.subst
      (motive := fun left : ℕ => left ≤ Nat.log2 (C + 1))
      Nat.log2_eq_log_two.symm
      (Eq.subst
        (motive := fun right : ℕ => Nat.log 2 C ≤ right)
        Nat.log2_eq_log_two.symm hmono)
  have hadd_nat : Nat.log2 C + 1 ≤ Nat.log2 (C + 1) + 1 :=
    Nat.add_le_add_right hlog_nat 1
  have hcast :
      ((Nat.log2 C + 1 : ℕ) : ℝ) ≤
        ((Nat.log2 (C + 1) + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hadd_nat
  have hshifted :
      ((Nat.log2 (C + 1) : ℝ) + 1) ≤ 2 * Real.log (2 + C) :=
    Complex.nat_log2_add_one_le_two_log C
  have hcast_add :
      ((Nat.log2 (C + 1) + 1 : ℕ) : ℝ) =
        (Nat.log2 (C + 1) : ℝ) + 1 := by
    exact Eq.trans (Nat.cast_add (Nat.log2 (C + 1)) 1)
      (congrArg (fun z : ℝ => (Nat.log2 (C + 1) : ℝ) + z)
        Nat.cast_one)
  exact le_trans hcast
    (Eq.subst
      (motive := fun left : ℝ => left ≤ 2 * Real.log (2 + C))
      hcast_add.symm hshifted)

/-- The endpoint component occupies at most three copies of the public
transition scale in the high-frequency branch. -/
theorem Complex.logarithmicPhase_canonicalEndpoint_le_three_transition
    (t : ℝ)
    (ht4 : 4 < ‖t‖) :
    3 * ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) / ‖t‖ ≤
      3 * Real.sqrt (1 + ‖t‖) *
        Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  have hendpoint :=
    Complex.logarithmicPhase_canonicalCutoff_three_mul_div_le_nine_halves t ht4
  have hsqrt :=
    Complex.logarithmicPhase_two_le_sqrt_one_add_norm_of_four_lt t ht4
  have hlog :=
    Complex.logarithmicPhase_two_le_log_two_add_canonicalCutoff t ht4
  have hproduct :
      (12 : ℝ) ≤
        3 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
    have hthree_sqrt :
        (6 : ℝ) ≤ 3 * Real.sqrt (1 + ‖t‖) := by
      have hscaled := mul_le_mul_of_nonneg_left hsqrt
        (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
      have hleft : (3 : ℝ) * 2 = 6 :=
        Eq.trans (Nat.cast_mul 3 2).symm Nat.cast_ofNat
      exact Eq.subst
        (motive := fun left : ℝ => left ≤ 3 * Real.sqrt (1 + ‖t‖))
        hleft hscaled
    have hscaled := mul_le_mul hthree_sqrt hlog
      (show (0 : ℝ) ≤ 2 from zero_le_two)
      (mul_nonneg (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
        (Real.sqrt_nonneg _))
    have hleft : (6 : ℝ) * 2 = 12 :=
      Eq.trans (Nat.cast_mul 6 2).symm Nat.cast_ofNat
    exact Eq.subst
      (motive := fun left : ℝ => left ≤
        3 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊))
      hleft hscaled
  have hnine_halves_le_twelve : (9 / 2 : ℝ) ≤ 12 := by
    have hnat : (9 : ℕ) ≤ 24 := by
      have hle : 9 ≤ 9 + 15 := Nat.le_add_right 9 15
      exact Eq.subst (motive := fun right : ℕ => 9 ≤ right)
        (show (9 + 15 : ℕ) = 24 from rfl) hle
    have hreal : (9 : ℝ) ≤ 24 := Nat.cast_le.mpr hnat
    have hright : (12 : ℝ) * 2 = 24 :=
      Eq.trans (Nat.cast_mul 12 2).symm Nat.cast_ofNat
    exact (div_le_iff₀ zero_lt_two).mpr
      (Eq.subst (motive := fun right : ℝ => (9 : ℝ) ≤ right)
        hright.symm hreal)
  exact le_trans hendpoint
    (le_trans hnine_halves_le_twelve hproduct)

/-- The block-count component occupies two copies of the public transition
scale. -/
theorem Complex.logarithmicPhase_canonicalBlockCount_le_two_transition
    (t : ℝ) :
    ((Nat.log2 ⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
        Real.sqrt (1 + ‖t‖) ≤
      2 * Real.sqrt (1 + ‖t‖) *
        Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  have hcount :=
    Complex.logarithmicPhase_log2_canonicalCutoff_add_one_le_two_log t
  have hsqrt_nonneg := Real.sqrt_nonneg (1 + ‖t‖)
  have hscaled := mul_le_mul_of_nonneg_right hcount hsqrt_nonneg
  have hright :
      (2 * Real.log (2 + ⌊2 + ‖t‖⌋₊)) *
          Real.sqrt (1 + ‖t‖) =
        2 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
    calc
      (2 * Real.log (2 + ⌊2 + ‖t‖⌋₊)) *
          Real.sqrt (1 + ‖t‖) =
        2 * (Real.log (2 + ⌊2 + ‖t‖⌋₊) *
          Real.sqrt (1 + ‖t‖)) :=
        mul_assoc 2 _ _
      _ = 2 * (Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊)) := by
        exact congrArg (fun z : ℝ => 2 * z) (mul_comm _ _)
      _ = 2 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊) :=
        (mul_assoc 2 _ _).symm
  exact Eq.subst
    (motive := fun right : ℝ =>
      ((Nat.log2 ⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
          Real.sqrt (1 + ‖t‖) ≤ right)
    hright hscaled

/-- High-frequency canonical-prefix estimate obtained by exact dyadic
aggregation of the comparable-block curvature theorem. -/
theorem Complex.logarithmicPhase_canonicalPrefix_norm_le_of_four_lt_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht4 : 4 < ‖t‖) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊‖ ≤
      400 * Real.sqrt (1 + ‖t‖) *
        Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hprefix :=
    Complex.logarithmicPhase_dyadicPrefix_norm_le_budget
      t ht (Complex.logarithmicPhase_canonicalCutoff_pos t)
  have hendpoint :=
    Complex.logarithmicPhase_canonicalEndpoint_le_three_transition t ht4
  have hcount :=
    Complex.logarithmicPhase_canonicalBlockCount_le_two_transition t
  let Q : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + C)
  have hinside :
      3 * (C : ℝ) / ‖t‖ +
          ((Nat.log2 C + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖) ≤
        5 * Q := by
    have hadd := add_le_add hendpoint hcount
    have hright :
        3 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) +
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) =
          5 * Q := by
      calc
        3 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) +
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) =
          3 * Q + 2 * Q :=
            congrArg₂ (fun x y : ℝ => x + y)
              (mul_assoc 3 (Real.sqrt (1 + ‖t‖))
                (Real.log (2 + C)))
              (mul_assoc 2 (Real.sqrt (1 + ‖t‖))
                (Real.log (2 + C)))
        _ = (3 + 2) * Q :=
          (add_mul 3 2 Q).symm
        _ = 5 * Q := by
          exact congrArg (fun z : ℝ => z * Q)
            (show (3 : ℝ) + 2 = 5 from
              Eq.trans (Nat.cast_add 3 2).symm Nat.cast_ofNat)
    exact Eq.subst
      (motive := fun right : ℝ =>
        3 * (C : ℝ) / ‖t‖ +
          ((Nat.log2 C + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖) ≤ right)
      hright hadd
  have hscaled := mul_le_mul_of_nonneg_left hinside
    (show (0 : ℝ) ≤ 80 from Nat.cast_nonneg 80)
  have hconstant : 80 * (5 * Q) = 400 * Q := by
    calc
      80 * (5 * Q) = (80 * 5) * Q :=
        (mul_assoc 80 5 Q).symm
      _ = 400 * Q := by
        exact congrArg (fun z : ℝ => z * Q)
          (show (80 : ℝ) * 5 = 400 from
            Eq.trans (Nat.cast_mul 80 5).symm Nat.cast_ofNat)
  have hQ :
      400 * Q =
        400 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) :=
    (mul_assoc 400 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + C))).symm
  exact le_trans hprefix
    (Eq.subst
      (motive := fun right : ℝ =>
        80 *
          (3 * (C : ℝ) / ‖t‖ +
            ((Nat.log2 C + 1 : ℕ) : ℝ) * Real.sqrt (1 + ‖t‖)) ≤ right)
      (Eq.trans hconstant hQ) hscaled)

end

end LFunctions
end Boundary

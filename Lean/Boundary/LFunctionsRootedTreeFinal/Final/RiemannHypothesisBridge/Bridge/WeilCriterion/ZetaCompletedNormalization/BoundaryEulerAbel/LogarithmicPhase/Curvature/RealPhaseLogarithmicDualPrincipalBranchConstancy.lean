import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCenteredReduction

/-!
# Constancy of the centered branch on principal runs

The branch index can change only when the absolute continuous increment crosses
an odd multiple of `pi`.  Such a crossing is exactly a midpoint branch-cut
cell.  Principal runs contain no such cell, so adjacent indices agree; finite
induction then gives one branch index on the entire run.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.centeredAngularBranchIndex_antitoneOn_negative
    {u v : ℝ} (hu : u < 0) (hv : v < 0) (huv : u ≤ v) :
    Real.centeredAngularBranchIndex v ≤
      Real.centeredAngularBranchIndex u := by
  unfold Real.centeredAngularBranchIndex
  have huAbs : |u| = -u := abs_of_neg hu
  have hvAbs : |v| = -v := abs_of_neg hv
  have habs : |v| ≤ |u| := by
    exact Eq.subst (motive := fun z : ℝ => z ≤ |u|) hvAbs.symm
      (Eq.subst (motive := fun z : ℝ => -v ≤ z) huAbs.symm
        (neg_le_neg huv))
  have hdenom : 0 ≤ 2 * Real.pi := le_of_lt Complex.two_mul_pi_pos
  have hratio : |v| / (2 * Real.pi) ≤ |u| / (2 * Real.pi) :=
    div_le_div_of_nonneg_right habs hdenom
  have hshift :
      |v| / (2 * Real.pi) + 1 / 2 ≤
        |u| / (2 * Real.pi) + 1 / 2 :=
    add_le_add_right hratio (1 / 2)
  exact Nat.floor_mono hshift

theorem Real.branchCutLevel_eq_two_pi_mul_half_shift
    (q : ℕ) :
    Complex.logarithmicPhaseDualBranchCutLevel q =
      (2 * Real.pi) * ((q : ℝ) + 1 / 2) := by
  unfold Complex.logarithmicPhaseDualBranchCutLevel
  calc
    (2 * (q : ℝ) + 1) * Real.pi =
        Real.pi * (2 * (q : ℝ) + 1) := mul_comm _ _
    _ = Real.pi * (2 * ((q : ℝ) + 1 / 2)) := by
      exact congrArg (fun z : ℝ => Real.pi * z) (by exact rfl)
    _ = (Real.pi * 2) * ((q : ℝ) + 1 / 2) := by
      exact mul_assoc Real.pi 2 ((q : ℝ) + 1 / 2)
    _ = (2 * Real.pi) * ((q : ℝ) + 1 / 2) := by
      exact congrArg
        (fun z : ℝ => z * ((q : ℝ) + 1 / 2))
        (mul_comm Real.pi 2)

theorem Real.branchIndex_cast_le_shiftedRatio
    (v : ℝ) :
    ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤
      |v| / (2 * Real.pi) + 1 / 2 :=
  Real.centeredAngularBranchIndex_cast_le v

theorem Real.shiftedRatio_lt_branchIndex_succ
    (v : ℝ) :
    |v| / (2 * Real.pi) + 1 / 2 <
      ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) + 1 :=
  Real.centeredAngularBranchIndex_ratio_lt_succ v

theorem Real.branchCutLevel_le_abs_of_succ_le_branchIndex
    {v : ℝ} {q : ℕ}
    (hq : q + 1 ≤ Real.centeredAngularBranchIndex v) :
    Complex.logarithmicPhaseDualBranchCutLevel q ≤ |v| := by
  have hcast : ((q + 1 : ℕ) : ℝ) ≤
      ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) :=
    Nat.cast_le.mpr hq
  have hfloor := Real.centeredAngularBranchIndex_cast_le v
  have hcombined : ((q + 1 : ℕ) : ℝ) ≤
      |v| / (2 * Real.pi) + 1 / 2 := le_trans hcast hfloor
  have hcastSucc : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 :=
    Nat.cast_add q 1
  have hhalf : (q : ℝ) + 1 / 2 ≤ |v| / (2 * Real.pi) := by
    exact (add_le_add_iff_right (1 / 2 : ℝ)).mp
      (Eq.subst
        (motive := fun z : ℝ => z ≤ |v| / (2 * Real.pi) + 1 / 2)
        hcastSucc hcombined)
  have hscaled := mul_le_mul_of_nonneg_left hhalf
    (le_of_lt Complex.two_mul_pi_pos)
  have hcancel : (2 * Real.pi) * (|v| / (2 * Real.pi)) = |v| :=
    mul_div_cancel₀ |v| (ne_of_gt Complex.two_mul_pi_pos)
  exact Eq.subst (motive := fun z : ℝ => z ≤ |v|)
    (Real.branchCutLevel_eq_two_pi_mul_half_shift q).symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z) hcancel hscaled)

theorem Real.abs_lt_branchCutLevel_of_branchIndex_le
    {v : ℝ} {q : ℕ}
    (hq : Real.centeredAngularBranchIndex v ≤ q) :
    |v| < Complex.logarithmicPhaseDualBranchCutLevel q := by
  have hratio := Real.centeredAngularBranchIndex_ratio_lt_succ v
  have hcast :
      ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) ≤ (q : ℝ) :=
    Nat.cast_le.mpr hq
  have hupper :
      ((Real.centeredAngularBranchIndex v : ℕ) : ℝ) + 1 ≤
        (q : ℝ) + 1 := add_le_add_right hcast 1
  have hshifted :
      |v| / (2 * Real.pi) + 1 / 2 < (q : ℝ) + 1 :=
    lt_of_lt_of_le hratio hupper
  have hhalf : |v| / (2 * Real.pi) < (q : ℝ) + 1 / 2 := by
    exact (add_lt_add_iff_right (1 / 2 : ℝ)).mp
      (Eq.subst
        (motive := fun z : ℝ =>
          |v| / (2 * Real.pi) + 1 / 2 < z)
        (by exact rfl) hshifted)
  have hscaled := mul_lt_mul_of_pos_left hhalf Complex.two_mul_pi_pos
  have hcancel : (2 * Real.pi) * (|v| / (2 * Real.pi)) = |v| :=
    mul_div_cancel₀ |v| (ne_of_gt Complex.two_mul_pi_pos)
  exact Eq.subst (motive := fun z : ℝ => z < _)
    hcancel.symm
    (Eq.subst (motive := fun z : ℝ => _ < z)
      (Real.branchCutLevel_eq_two_pi_mul_half_shift q).symm hscaled)

theorem Complex.continuousOn_abs_logarithmicPhaseDualContinuousIncrement_Icc
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x y : ℝ}
    (hh : 0 < h) (hx : 0 < x) (hxy : x ≤ y) :
    ContinuousOn
      (fun z : ℝ =>
        |Complex.logarithmicPhaseDualContinuousIncrement t h z|)
      (Set.Icc x y) := by
  have hcontinuous :=
    Complex.logarithmicPhaseDualContinuousIncrement_continuousOn_positive
      t ht (le_of_lt hh)
  have hrestricted : ContinuousOn
      (Complex.logarithmicPhaseDualContinuousIncrement t h)
      (Set.Icc x y) := by
    exact hcontinuous.mono
      (fun z hz => lt_of_lt_of_le hx hz.1)
  exact continuous_abs.comp_continuousOn hrestricted

theorem Complex.exists_logarithmicPhaseDualBranchCut_crossing_between
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h : ℕ} (hh : 0 < h) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    {q : ℕ}
    (hleft : Complex.logarithmicPhaseDualBranchCutLevel q ≤
      |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x|)
    (hright :
      |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) y| ≤
        Complex.logarithmicPhaseDualBranchCutLevel q) :
    ∃ z ∈ Set.Icc x y,
      |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) z| =
        Complex.logarithmicPhaseDualBranchCutLevel q := by
  have hcontinuous :=
    Complex.continuousOn_abs_logarithmicPhaseDualContinuousIncrement_Icc
      t ht (Nat.cast_pos.mpr hh) hx hxy
  have hiver := intermediate_value_Icc hxy hcontinuous
  have hbetween :
      Complex.logarithmicPhaseDualBranchCutLevel q ∈
        Set.Icc
          |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) y|
          |Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) x| :=
    And.intro hright hleft
  rcases hiver hbetween with ⟨z, hz, hzEq⟩
  exact Exists.intro z (And.intro hz hzEq)

theorem Complex.logarithmicPhaseDualAdjacentBranchIndex_eq_of_not_cut
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h n : ℕ} (hh : 0 < h) (hn : 0 < n)
    (hnotCut : ∀ q : ℕ,
      q < Complex.logarithmicPhaseDualDiscreteBranchIndex t h n →
        ¬ Complex.logarithmicPhaseDualBranchCutCell t h n q) :
    Complex.logarithmicPhaseDualDiscreteBranchIndex t h n =
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1) := by
  have hnSuccPos : 0 < n + 1 := Nat.zero_lt_succ n
  have hraw :=
    Complex.logarithmicPhaseDualShiftedIncrement_monotone_on_Icc
      t ht hh hn n (Finset.mem_Icc.mpr (And.intro (Nat.le_refl n) (Nat.le_add_right n 1)))
      (n + 1) (Finset.mem_Icc.mpr (And.intro (Nat.le_add_right n 1) (Nat.le_refl _)))
      (Nat.le_add_right n 1)
  have hnNeg := Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hn
  have hnSuccNeg :=
    Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hnSuccPos
  have hindexLe :
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1) ≤
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h n := by
    unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
    exact Real.centeredAngularBranchIndex_antitoneOn_negative
      hnNeg hnSuccNeg hraw
  exact le_antisymm hindexLe
    (by
      by_contra hnotLe
      have hstrict :
          Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1) <
            Complex.logarithmicPhaseDualDiscreteBranchIndex t h n :=
        lt_of_le_of_ne hindexLe
          (fun heq => hnotLe (le_of_eq heq.symm))
      let q := Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1)
      have hsuccLe : q + 1 ≤
          Complex.logarithmicPhaseDualDiscreteBranchIndex t h n :=
        Nat.succ_le_of_lt hstrict
      have hleft := Real.branchCutLevel_le_abs_of_succ_le_branchIndex
        (v := Complex.logarithmicPhaseDualShiftedIncrement t h n)
        (q := q) hsuccLe
      have hrightStrict := Real.abs_lt_branchCutLevel_of_branchIndex_le
        (v := Complex.logarithmicPhaseDualShiftedIncrement t h (n + 1))
        (q := q) (Nat.le_refl q)
      have hright := le_of_lt hrightStrict
      have hleftContinuous := Eq.subst
        (motive := fun z : ℝ =>
          Complex.logarithmicPhaseDualBranchCutLevel q ≤ |z|)
        (Complex.logarithmicPhaseDualContinuousIncrement_nat_eq t h n).symm
        hleft
      have hrightContinuous := Eq.subst
        (motive := fun z : ℝ =>
          |z| ≤ Complex.logarithmicPhaseDualBranchCutLevel q)
        (Complex.logarithmicPhaseDualContinuousIncrement_nat_eq t h (n + 1)).symm
        hright
      rcases Complex.exists_logarithmicPhaseDualBranchCut_crossing_between
        t ht hh (Nat.cast_pos.mpr hn)
        (Nat.cast_le.mpr (Nat.le_add_right n 1))
        hleftContinuous hrightContinuous with ⟨x, hxCell, hxLevel⟩
      exact False.elim (hnotCut q hstrict
        (Exists.intro x
          (And.intro
            (Eq.subst
              (motive := fun upper : ℝ => x ∈ Set.Icc (n : ℝ) upper)
              (Nat.cast_add n 1).symm hxCell)
            hxLevel))))

theorem Complex.logarithmicPhaseDualPrincipalRun_adjacent_branchIndex_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M)
    {n : ℕ} (hnLower : p.1 ≤ n) (hnUpper : n + 1 < p.2) :
    Complex.logarithmicPhaseDualDiscreteBranchIndex t h n =
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1) := by
  have hpBounds := Complex.logarithmicPhaseDualPrincipalRun_bounded
    t h eta K M hp
  have hnRun : n ∈ Finset.Ico p.1 p.2 :=
    Finset.mem_Ico.mpr (And.intro hnLower
      (lt_trans (Nat.lt_succ_self n) hnUpper))
  have hnPos := lt_of_lt_of_le hK
    (le_trans hpBounds.1 (Finset.mem_Ico.mp hnRun).1)
  have hnNotMarked :=
    Complex.logarithmicPhaseDualPrincipalRun_cell_not_branchCut
      t h eta K M hp hnRun
  have hKPos := hK
  have hnSuccPos : 0 < n + 1 := Nat.zero_lt_succ n
  have hKLeNSucc : K ≤ n + 1 :=
    le_trans hpBounds.1
      (le_trans (Finset.mem_Ico.mp hnRun).1 (Nat.le_add_right n 1))
  have hrawKNSucc :=
    Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
      t ht hh hKPos hnSuccPos hKLeNSucc
  have hrawKNeg :=
    Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hKPos
  have hrawNSuccNeg :=
    Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hnSuccPos
  have hindexNSuccLeK :
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h (n + 1) ≤
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h K := by
    unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
    exact Real.centeredAngularBranchIndex_antitoneOn_negative
      hrawKNeg hrawNSuccNeg hrawKNSucc
  have hKIndexEqUpper :
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h K =
        Complex.logarithmicPhaseDualBranchCutUpper t (h : ℝ) (K : ℝ) := by
    unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
    unfold Complex.logarithmicPhaseDualBranchCutUpper
    unfold Real.centeredAngularBranchIndex
    exact congrArg
      (fun z : ℝ => ⌊|z| / (2 * Real.pi) + 1 / 2⌋₊)
      (Complex.logarithmicPhaseDualContinuousIncrement_nat_eq t h K).symm
  have hnNotAny : ∀ q : ℕ,
      q < Complex.logarithmicPhaseDualDiscreteBranchIndex t h n →
        ¬ Complex.logarithmicPhaseDualBranchCutCell t h n q := by
    intro q hqLt hnCut
    have hnBlock : n ∈ Finset.Icc K M := by
      have hnUpper : n ≤ M := by
        have hnLtEnd := (Finset.mem_Ico.mp hnRun).2
        have hend := hpBounds.2.2
        exact Nat.le_of_lt_succ
          (lt_of_lt_of_le hnLtEnd hend)
      exact Finset.mem_Icc.mpr
        (And.intro (le_trans hpBounds.1 (Finset.mem_Ico.mp hnRun).1) hnUpper)
    have hnIndexLeK :
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h n ≤
          Complex.logarithmicPhaseDualDiscreteBranchIndex t h K := by
      have hrawKN :=
        Complex.logarithmicPhaseDualShiftedIncrement_monotoneOn_positive
          t ht hh hKPos hnPos
          (le_trans hpBounds.1 (Finset.mem_Ico.mp hnRun).1)
      have hrawNNeg :=
        Complex.logarithmicPhaseDualShiftedIncrement_neg t ht hh hnPos
      unfold Complex.logarithmicPhaseDualDiscreteBranchIndex
      exact Real.centeredAngularBranchIndex_antitoneOn_negative
        hrawKNeg hrawNNeg hrawKN
    have hqLeKIndex : q ≤
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h K :=
      le_trans (le_of_lt hqLt) hnIndexLeK
    have hqUpper : q ≤
        Complex.logarithmicPhaseDualBranchCutUpper t (h : ℝ) (K : ℝ) :=
      Eq.subst (motive := fun z : ℕ => q ≤ z)
        hKIndexEqUpper hqLeKIndex
    have hqLevel : q ∈ Complex.logarithmicPhaseDualBranchCutLevels
        t (h : ℝ) (K : ℝ) :=
      (Complex.mem_logarithmicPhaseDualBranchCutLevels_iff _ _ _ q).mpr
        (And.intro (Nat.zero_le q) hqUpper)
    exact hnNotMarked
      ((Complex.mem_logarithmicPhaseDualDiscreteBranchCutModes_iff
        t h K M n).mpr
        (And.intro hnBlock (Exists.intro q (And.intro hqLevel hnCut))))
  exact Complex.logarithmicPhaseDualAdjacentBranchIndex_eq_of_not_cut
    t ht hh hnPos hnNotAny

theorem Complex.logarithmicPhaseDualPrincipalRun_branchIndex_eq_start
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2,
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n =
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h p.1 := by
  intro n hn
  have hnData := Finset.mem_Ico.mp hn
  have hproperty : ∀ m : ℕ, p.1 ≤ m → m < p.2 →
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h m =
        Complex.logarithmicPhaseDualDiscreteBranchIndex t h p.1 := by
    intro m hmLower
    exact Nat.le_induction
      (fun hmUpper : p.1 < p.2 => Eq.refl _)
      (fun k hkLower hkProperty hkSuccUpper =>
        have hkUpper : k + 1 < p.2 := hkSuccUpper
        have hadjacent :=
          Complex.logarithmicPhaseDualPrincipalRun_adjacent_branchIndex_eq
            t ht hh hK eta hp hkLower hkUpper
        Eq.trans hadjacent.symm hkProperty)
      m hmLower
  exact hproperty n hnData.1 hnData.2

theorem Complex.logarithmicPhaseDualPrincipalRun_branchIndex_exists
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    ∃ q : ℕ, ∀ n ∈ Finset.Ico p.1 p.2,
      Complex.logarithmicPhaseDualDiscreteBranchIndex t h n = q := by
  exact Exists.intro
    (Complex.logarithmicPhaseDualDiscreteBranchIndex t h p.1)
    (Complex.logarithmicPhaseDualPrincipalRun_branchIndex_eq_start
      t ht hh hK eta hp)

theorem Complex.logarithmicPhaseDualPrincipalRun_reducedIncrement_monotone
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2,
      ∀ m ∈ Finset.Ico p.1 p.2,
        n ≤ m →
          Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n ≤
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  rcases Complex.logarithmicPhaseDualPrincipalRun_branchIndex_exists
    t ht hh hK eta hp with ⟨q, hq⟩
  have hpBounds := Complex.logarithmicPhaseDualPrincipalRun_bounded
    t h eta K M hp
  have hpStartPos := lt_of_lt_of_le hK hpBounds.1
  exact
    Complex.logarithmicPhaseDualDiscreteReducedIncrement_monotone_on_Ico_of_branchIndex_const
      t ht hh hpStartPos hq

theorem Complex.logarithmicPhaseDualPrincipalRun_reducedIncrement_strictMono
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2,
      ∀ m ∈ Finset.Ico p.1 p.2,
        n < m →
          Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n <
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m := by
  rcases Complex.logarithmicPhaseDualPrincipalRun_branchIndex_exists
    t ht hh hK eta hp with ⟨q, hq⟩
  have hpBounds := Complex.logarithmicPhaseDualPrincipalRun_bounded
    t h eta K M hp
  have hpStartPos := lt_of_lt_of_le hK hpBounds.1
  exact
    Complex.logarithmicPhaseDualDiscreteReducedIncrement_strictMono_on_Ico_of_branchIndex_const
      t ht hh hpStartPos hq

theorem Complex.logarithmicPhaseDualPrincipalRun_reducedIncrement_sub_eq_raw_sub
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (eta : ℝ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2,
      ∀ m ∈ Finset.Ico p.1 p.2,
        Complex.logarithmicPhaseDualDiscreteReducedIncrement t h m -
            Complex.logarithmicPhaseDualDiscreteReducedIncrement t h n =
          Complex.logarithmicPhaseDualShiftedIncrement t h m -
            Complex.logarithmicPhaseDualShiftedIncrement t h n := by
  rcases Complex.logarithmicPhaseDualPrincipalRun_branchIndex_exists
    t ht hh hK eta hp with ⟨q, hq⟩
  exact
    Complex.logarithmicPhaseDualDiscreteReducedIncrement_sub_eq_raw_sub_of_branchIndex_const
      t h p.1 p.2 q hq

end

end LFunctions
end Boundary

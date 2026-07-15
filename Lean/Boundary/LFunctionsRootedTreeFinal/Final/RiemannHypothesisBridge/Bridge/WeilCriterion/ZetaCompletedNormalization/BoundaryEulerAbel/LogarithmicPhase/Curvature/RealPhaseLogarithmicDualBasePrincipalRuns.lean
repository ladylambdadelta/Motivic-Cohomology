import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBasePartition

/-!
# Principal-run structure for the base dual action

Adjacent branch equality is iterated over each maximal surviving run.  The
resulting fixed lattice translate gives a centered representative throughout
the run, while resonance deletion gives uniform separation from every angular
lattice point.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseDualBasePrincipalRun_branchIndex_eq_start
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2,
      Complex.logarithmicPhaseDualBaseBranchIndex t n =
        Complex.logarithmicPhaseDualBaseBranchIndex t p.1 := by
  intro n hn
  have hnData := Finset.mem_Ico.mp hn
  have hstep : ∀ m : ℕ, p.1 ≤ m → m < p.2 →
      Complex.logarithmicPhaseDualBaseBranchIndex t m =
        Complex.logarithmicPhaseDualBaseBranchIndex t p.1 := by
    intro m hm
    exact Nat.le_induction
      (fun _ => Eq.refl _)
      (fun k hk hik hkUpper =>
        have hkRun : k ∈ Finset.Ico p.1 p.2 :=
          Finset.mem_Ico.mpr (And.intro hk
            (lt_trans (Nat.lt_succ_self k) hkUpper))
        have hadjacent :=
          Complex.logarithmicPhaseDualBasePrincipalRun_adjacent_branch_eq
            t eta K M hp hkRun
        Eq.trans hadjacent.symm hik)
      m hm
  exact hstep n hnData.1 hnData.2

theorem Complex.logarithmicPhaseDualBasePrincipalRun_branchIndex_exists
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    ∃ q : ℤ, ∀ n ∈ Finset.Ico p.1 p.2,
      Complex.logarithmicPhaseDualBaseBranchIndex t n = q := by
  exact Exists.intro
    (Complex.logarithmicPhaseDualBaseBranchIndex t p.1)
    (Complex.logarithmicPhaseDualBasePrincipalRun_branchIndex_eq_start
      t eta K M hp)

theorem Complex.logarithmicPhaseDualBaseReducedIncrement_eq_fixed_branch
    (t : ℝ) {n : ℕ} {q : ℤ}
    (hq : Complex.logarithmicPhaseDualBaseBranchIndex t n = q) :
    Complex.logarithmicPhaseDualBaseReducedIncrement t n =
      Complex.logarithmicPhaseDualBaseIncrementNat t n - q • (2 * Real.pi) := by
  have hraw :=
    Complex.logarithmicPhaseDualBaseReducedIncrement_add_branch_eq_raw t n
  have hbranch :
      Complex.logarithmicPhaseDualBaseBranchIndex t n • (2 * Real.pi) =
        q • (2 * Real.pi) :=
    congrArg (fun k : ℤ => k • (2 * Real.pi)) hq
  exact (eq_sub_iff_add_eq).mpr
    (Eq.subst
      (motive := fun z : ℝ =>
        Complex.logarithmicPhaseDualBaseReducedIncrement t n + z =
          Complex.logarithmicPhaseDualBaseIncrementNat t n)
      hbranch hraw)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_rawIncrement_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} {K M : ℕ}
    (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    AntitoneOn
      (Complex.logarithmicPhaseDualBaseIncrementNat t)
      (Finset.Ico p.1 p.2 : Set ℕ) := by
  intro n hn m hm hnm
  have hpBounds := Complex.logarithmicPhaseDualBasePrincipalRun_bounded
    t eta K M hp
  have hnPos := lt_of_lt_of_le hK
    (le_trans hpBounds.1 (Finset.mem_Ico.mp hn).1)
  exact Complex.logarithmicPhaseDualBaseIncrementNat_antitone
    t ht hnPos hnm

theorem Complex.logarithmicPhaseDualBasePrincipalRun_latticeSeparated
    (t : ℝ) {eta : ℝ} {K M : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    ∀ n ∈ Finset.Ico p.1 p.2, ∀ k : ℤ,
      eta ≤ ‖Complex.logarithmicPhaseDualBaseIncrementNat t n -
        2 * Real.pi * (k : ℝ)‖ := by
  intro n hn k
  have hnot := Complex.logarithmicPhaseDualBasePrincipalRun_not_resonant
    t eta K M hp hn
  unfold Complex.logarithmicPhaseDualBaseResonant at hnot
  exact le_of_not_gt
    (fun hlt => hnot (Exists.intro k hlt))

theorem Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseIncrement_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} {K M : ℕ}
    (hK : 0 < K) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    AntitoneOn
      (fun n : ℕ => Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseDualBaseAction t) n)
      (Finset.Ico p.1 p.2 : Set ℕ) := by
  intro n hn m hm hnm
  have hanti :=
    Complex.logarithmicPhaseDualBasePrincipalRun_rawIncrement_antitone
      t ht hK hp hn hm hnm
  exact Eq.subst (motive := fun z : ℝ => _ ≤ z)
    (Complex.logarithmicPhaseDualBaseAction_integerIncrement_eq t n).symm
    (Eq.subst (motive := fun z : ℝ => z ≤ _)
      (Complex.logarithmicPhaseDualBaseAction_integerIncrement_eq t m).symm
      hanti)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseSeparated
    (t : ℝ) {eta : ℝ} {K M : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    Complex.realPhase_integerIncrementSeparatedOn
      (Complex.logarithmicPhaseDualBaseAction t) p.1 p.2 eta := by
  intro n hn k
  have hsep :=
    Complex.logarithmicPhaseDualBasePrincipalRun_latticeSeparated
      t hp n hn k
  exact Eq.subst
    (motive := fun z : ℝ =>
      eta ≤ ‖z - 2 * Real.pi * (k : ℝ)‖)
    (Complex.logarithmicPhaseDualBaseAction_integerIncrement_eq t n).symm
    hsep

theorem Complex.logarithmicPhaseDualBaseReducedIncrement_eq_realPhase
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseReducedIncrement t n =
      Complex.realPhase_reducedIntegerIncrement
        (Complex.logarithmicPhaseDualBaseAction t) n := by
  unfold Complex.logarithmicPhaseDualBaseReducedIncrement
  unfold Complex.realPhase_reducedIntegerIncrement
  exact congrArg (toIocMod Real.two_pi_pos (-Real.pi))
    (Complex.logarithmicPhaseDualBaseAction_integerIncrement_eq t n).symm

theorem Complex.logarithmicPhaseDualBasePrincipalRun_reducedIncrement_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} {K M : ℕ} (hK : 0 < K)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    AntitoneOn
      (Complex.logarithmicPhaseDualBaseReducedIncrement t)
      (Finset.Ico p.1 p.2 : Set ℕ) := by
  rcases Complex.logarithmicPhaseDualBasePrincipalRun_branchIndex_exists
    t eta K M hp with ⟨q, hq⟩
  intro n hn m hm hnm
  have hnFixed :=
    Complex.logarithmicPhaseDualBaseReducedIncrement_eq_fixed_branch
      t (hq n hn)
  have hmFixed :=
    Complex.logarithmicPhaseDualBaseReducedIncrement_eq_fixed_branch
      t (hq m hm)
  have hpBounds := Complex.logarithmicPhaseDualBasePrincipalRun_bounded
    t eta K M hp
  have hnPos : 0 < n := lt_of_lt_of_le hK
    (le_trans hpBounds.1
    (Finset.mem_Ico.mp hn).1
    )
  have hraw :=
    Complex.logarithmicPhaseDualBaseIncrementNat_antitone
      t ht hnPos hnm
  have htranslated := sub_le_sub_right hraw (q • (2 * Real.pi))
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    hmFixed.symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z)
      hnFixed.symm htranslated)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_realPhaseReducedMonotone
    (t : ℝ) (ht : 1 ≤ ‖t‖) {eta : ℝ} {K M : ℕ} (hK : 0 < K)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    Complex.realPhase_reducedIntegerIncrementMonotoneOn
      (Complex.logarithmicPhaseDualBaseAction t) p.1 p.2 := by
  exact Or.inr
    (fun n hn m hm hnm =>
      have hanti :=
        Complex.logarithmicPhaseDualBasePrincipalRun_reducedIncrement_antitone
          t ht hK hp hn hm hnm
      Eq.subst (motive := fun z : ℝ => z ≤ _)
        (Complex.logarithmicPhaseDualBaseReducedIncrement_eq_realPhase
          t m).symm
        (Eq.subst (motive := fun z : ℝ => _ ≤ z)
          (Complex.logarithmicPhaseDualBaseReducedIncrement_eq_realPhase
            t n).symm hanti))

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBranchCuts

/-!
# Principal runs after resonance and midpoint deletion

The maximal-run construction is applied to the union of resonance-collar cells
and centered-reduction midpoint-cut cells.  Surviving runs retain the full
resonance separation proved earlier and, additionally, contain no unit cell in
which the continuous increment meets a midpoint branch cut.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualPrincipalSeparatedModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Finset.Icc K M \
    Complex.logarithmicPhaseDualDeletedModes t h eta K M

def Complex.logarithmicPhaseDualPrincipalRuns
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset (ℕ × ℕ) :=
  Nat.finiteDeletedIntervalRuns K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M)

def Complex.logarithmicPhaseDualPrincipalRunUnion
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Nat.finiteDeletedIntervalRunUnion K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M)

theorem Complex.mem_logarithmicPhaseDualPrincipalSeparatedModes_iff
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualPrincipalSeparatedModes t h eta K M ↔
      n ∈ Finset.Icc K M ∧
        n ∉ Complex.logarithmicPhaseDualDeletedModes t h eta K M := by
  exact Finset.mem_sdiff

theorem Complex.logarithmicPhaseDualPrincipalSeparatedModes_subset_resonanceSeparated
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualPrincipalSeparatedModes t h eta K M ⊆
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M := by
  intro n hn
  have hnMembership :=
    (Complex.mem_logarithmicPhaseDualPrincipalSeparatedModes_iff
      t h eta K M n).mp hn
  have hnNotCollar :
      n ∉ Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M := by
    intro hnCollar
    exact hnMembership.2
      (Complex.logarithmicPhaseDualDiscreteCollarModes_subset_deleted
        t h eta K M hnCollar)
  exact
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mpr
      (And.intro hnMembership.1 hnNotCollar)

theorem Complex.logarithmicPhaseDualPrincipalSeparatedModes_disjoint_branchCuts
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseDualPrincipalSeparatedModes t h eta K M)
      (Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M) := by
  exact Finset.disjoint_left.mpr
    (fun n hnSurvive hnCut =>
      have hnMembership :=
        (Complex.mem_logarithmicPhaseDualPrincipalSeparatedModes_iff
          t h eta K M n).mp hnSurvive
      hnMembership.2
        (Complex.logarithmicPhaseDualDiscreteBranchCutModes_subset_deleted
          t h eta K M hnCut))

theorem Complex.logarithmicPhaseDualPrincipalRunUnion_eq_separated
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualPrincipalRunUnion t h eta K M =
      Complex.logarithmicPhaseDualPrincipalSeparatedModes t h eta K M := by
  unfold Complex.logarithmicPhaseDualPrincipalRunUnion
  unfold Complex.logarithmicPhaseDualPrincipalSeparatedModes
  exact Nat.finiteDeletedIntervalRunUnion_eq_sdiff K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M)
    (Complex.logarithmicPhaseDualDeletedModes_subset_block t h eta K M)

theorem Complex.logarithmicPhaseDualPrincipalRuns_card_le_deleted_add_one
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualPrincipalRuns t h eta K M).card ≤
      (Complex.logarithmicPhaseDualDeletedModes t h eta K M).card + 1 := by
  unfold Complex.logarithmicPhaseDualPrincipalRuns
  exact Nat.finiteDeletedIntervalRuns_card_le_deleted_add_one K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M)

theorem Complex.logarithmicPhaseDualPrincipalRuns_card_le_collar_add_branch_add_one
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualPrincipalRuns t h eta K M).card ≤
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M).card +
        (Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M).card + 1 := by
  have hruns :=
    Complex.logarithmicPhaseDualPrincipalRuns_card_le_deleted_add_one
      t h eta K M
  have hdeleted :=
    Complex.logarithmicPhaseDualDeletedModes_card_le_add
      t h eta K M
  exact le_trans hruns (Nat.add_le_add_right hdeleted 1)

theorem Complex.logarithmicPhaseDualPrincipalRun_bounded
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M) :
    K ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ M + 1 := by
  unfold Complex.logarithmicPhaseDualPrincipalRuns at hp
  rcases (Nat.mem_finiteDeletedIntervalRuns_iff K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M) p).mp hp with
    ⟨s, hs, hpEq⟩
  have hsBlock := Nat.finiteDeletedIntervalRunStart_mem_block hs
  have hsubset :=
    Complex.logarithmicPhaseDualDeletedModes_subset_block t h eta K M
  have hsEnd := Nat.finiteDeletedIntervalRunStart_le_nextDeleted hsubset hs
  have hend := Nat.finiteDeletedIntervalNextDeleted_le_M_add_one hsubset s
  exact Eq.subst
    (motive := fun pair : ℕ × ℕ =>
      K ≤ pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.2 ≤ M + 1)
    hpEq.symm
    (And.intro (Finset.mem_Icc.mp hsBlock).1 (And.intro hsEnd hend))

theorem Complex.logarithmicPhaseDualPrincipalRuns_pairwise_disjoint
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ∀ p₁ ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M,
      ∀ p₂ ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M,
        p₁ ≠ p₂ →
          Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2) := by
  unfold Complex.logarithmicPhaseDualPrincipalRuns
  exact Nat.finiteDeletedIntervalRuns_pairwise_disjoint K M
    (Complex.logarithmicPhaseDualDeletedModes t h eta K M)

theorem Complex.logarithmicPhaseDualPrincipalRun_cell_not_branchCut
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualPrincipalRuns t h eta K M)
    {n : ℕ} (hn : n ∈ Finset.Ico p.1 p.2) :
    n ∉ Complex.logarithmicPhaseDualDiscreteBranchCutModes t h K M := by
  have hnUnion : n ∈ Complex.logarithmicPhaseDualPrincipalRunUnion
      t h eta K M := by
    unfold Complex.logarithmicPhaseDualPrincipalRunUnion
    exact Finset.mem_biUnion.mpr (Exists.intro p (And.intro hp hn))
  have hnSeparated : n ∈
      Complex.logarithmicPhaseDualPrincipalSeparatedModes t h eta K M :=
    Eq.subst (motive := fun S : Finset ℕ => n ∈ S)
      (Complex.logarithmicPhaseDualPrincipalRunUnion_eq_separated
        t h eta K M) hnUnion
  exact Finset.disjoint_left.mp
    (Complex.logarithmicPhaseDualPrincipalSeparatedModes_disjoint_branchCuts
      t h eta K M) hnSeparated

end

end LFunctions
end Boundary

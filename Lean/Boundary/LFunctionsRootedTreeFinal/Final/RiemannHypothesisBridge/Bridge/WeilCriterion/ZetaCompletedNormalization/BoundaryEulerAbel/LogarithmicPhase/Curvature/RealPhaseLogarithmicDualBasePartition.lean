import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBaseAction

/-!
# Exact discrete partition for the base dual action

The base dual phase has increment `D₁(n)`.  This owner deletes precisely two
classes of cells: resonance cells, where `D₁(n)` approaches the angular
lattice, and branch-boundary cells, where the canonical centered index changes
between consecutive samples.  The complement is decomposed into maximal
half-open runs by the generic finite-deletion construction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualBaseResonant
    (t eta : ℝ) (n : ℕ) : Prop :=
  ∃ k : ℤ,
    ‖Complex.logarithmicPhaseDualBaseIncrementNat t n -
      2 * Real.pi * (k : ℝ)‖ < eta

def Complex.logarithmicPhaseDualBaseResonanceModes
    (t eta : ℝ) (K M : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (Complex.logarithmicPhaseDualBaseResonant t eta)

def Complex.logarithmicPhaseDualBaseBranchBoundaryModes
    (t : ℝ) (K M : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ =>
      Complex.logarithmicPhaseDualBaseBranchIndex t n ≠
        Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1))

def Complex.logarithmicPhaseDualBaseDeletedModes
    (t eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Complex.logarithmicPhaseDualBaseResonanceModes t eta K M ∪
    Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M

def Complex.logarithmicPhaseDualBaseSurvivingModes
    (t eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Finset.Icc K M \
    Complex.logarithmicPhaseDualBaseDeletedModes t eta K M

def Complex.logarithmicPhaseDualBasePrincipalRuns
    (t eta : ℝ) (K M : ℕ) : Finset (ℕ × ℕ) :=
  Nat.finiteDeletedIntervalRuns K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M)

def Complex.logarithmicPhaseDualBasePrincipalRunUnion
    (t eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Nat.finiteDeletedIntervalRunUnion K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M)

theorem Complex.mem_logarithmicPhaseDualBaseResonanceModes_iff
    (t eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualBaseResonanceModes t eta K M ↔
      n ∈ Finset.Icc K M ∧
        ∃ k : ℤ,
          ‖Complex.logarithmicPhaseDualBaseIncrementNat t n -
            2 * Real.pi * (k : ℝ)‖ < eta := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseDualBaseBranchBoundaryModes_iff
    (t : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M ↔
      n ∈ Finset.Icc K M ∧
        Complex.logarithmicPhaseDualBaseBranchIndex t n ≠
          Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1) := by
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhaseDualBaseDeletedModes_iff
    (t eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualBaseDeletedModes t eta K M ↔
      n ∈ Complex.logarithmicPhaseDualBaseResonanceModes t eta K M ∨
      n ∈ Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M := by
  exact Finset.mem_union

theorem Complex.mem_logarithmicPhaseDualBaseSurvivingModes_iff
    (t eta : ℝ) (K M n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualBaseSurvivingModes t eta K M ↔
      n ∈ Finset.Icc K M ∧
        n ∉ Complex.logarithmicPhaseDualBaseDeletedModes t eta K M := by
  exact Finset.mem_sdiff

theorem Complex.logarithmicPhaseDualBaseResonanceModes_subset_block
    (t eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualBaseResonanceModes t eta K M ⊆
      Finset.Icc K M := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhaseDualBaseBranchBoundaryModes_subset_block
    (t : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M ⊆
      Finset.Icc K M := by
  exact Finset.filter_subset _ _

theorem Complex.logarithmicPhaseDualBaseDeletedModes_subset_block
    (t eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualBaseDeletedModes t eta K M ⊆
      Finset.Icc K M := by
  intro n hn
  match Finset.mem_union.mp hn with
  | Or.inl hres =>
      exact Complex.logarithmicPhaseDualBaseResonanceModes_subset_block
        t eta K M hres
  | Or.inr hbranch =>
      exact Complex.logarithmicPhaseDualBaseBranchBoundaryModes_subset_block
        t K M hbranch

theorem Complex.logarithmicPhaseDualBaseDeletedModes_card_le
    (t eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M).card ≤
      (Complex.logarithmicPhaseDualBaseResonanceModes t eta K M).card +
        (Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card := by
  unfold Complex.logarithmicPhaseDualBaseDeletedModes
  exact Finset.card_union_le _ _

theorem Complex.logarithmicPhaseDualBasePrincipalRunUnion_eq_surviving
    (t eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualBasePrincipalRunUnion t eta K M =
      Complex.logarithmicPhaseDualBaseSurvivingModes t eta K M := by
  unfold Complex.logarithmicPhaseDualBasePrincipalRunUnion
  unfold Complex.logarithmicPhaseDualBaseSurvivingModes
  exact Nat.finiteDeletedIntervalRunUnion_eq_sdiff K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M)
    (Complex.logarithmicPhaseDualBaseDeletedModes_subset_block t eta K M)

theorem Complex.logarithmicPhaseDualBasePrincipalRuns_card_le_deleted_add_one
    (t eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M).card ≤
      (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M).card + 1 := by
  unfold Complex.logarithmicPhaseDualBasePrincipalRuns
  exact Nat.finiteDeletedIntervalRuns_card_le_deleted_add_one K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M)

theorem Complex.logarithmicPhaseDualBasePrincipalRuns_card_le_components_add_one
    (t eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M).card ≤
      (Complex.logarithmicPhaseDualBaseResonanceModes t eta K M).card +
        (Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M).card + 1 := by
  exact le_trans
    (Complex.logarithmicPhaseDualBasePrincipalRuns_card_le_deleted_add_one
      t eta K M)
    (Nat.add_le_add_right
      (Complex.logarithmicPhaseDualBaseDeletedModes_card_le t eta K M) 1)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_bounded
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M) :
    K ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ M + 1 := by
  unfold Complex.logarithmicPhaseDualBasePrincipalRuns at hp
  rcases (Nat.mem_finiteDeletedIntervalRuns_iff K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M) p).mp hp with
    ⟨s, hs, hpEq⟩
  have hsBlock := Nat.finiteDeletedIntervalRunStart_mem_block hs
  have hsubset := Complex.logarithmicPhaseDualBaseDeletedModes_subset_block
    t eta K M
  have hsEnd := Nat.finiteDeletedIntervalRunStart_le_nextDeleted hsubset hs
  have hend := Nat.finiteDeletedIntervalNextDeleted_le_M_add_one hsubset s
  exact Eq.subst
    (motive := fun pair : ℕ × ℕ =>
      K ≤ pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.2 ≤ M + 1)
    hpEq.symm
    (And.intro (Finset.mem_Icc.mp hsBlock).1 (And.intro hsEnd hend))

theorem Complex.logarithmicPhaseDualBasePrincipalRuns_pairwise_disjoint
    (t eta : ℝ) (K M : ℕ) :
    ∀ p₁ ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M,
      ∀ p₂ ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M,
        p₁ ≠ p₂ →
          Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2) := by
  unfold Complex.logarithmicPhaseDualBasePrincipalRuns
  exact Nat.finiteDeletedIntervalRuns_pairwise_disjoint K M
    (Complex.logarithmicPhaseDualBaseDeletedModes t eta K M)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_cell_survives
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    {n : ℕ} (hn : n ∈ Finset.Ico p.1 p.2) :
    n ∈ Complex.logarithmicPhaseDualBaseSurvivingModes t eta K M := by
  have hnUnion : n ∈ Complex.logarithmicPhaseDualBasePrincipalRunUnion
      t eta K M := by
    unfold Complex.logarithmicPhaseDualBasePrincipalRunUnion
    exact Finset.mem_biUnion.mpr (Exists.intro p (And.intro hp hn))
  exact Eq.subst (motive := fun S : Finset ℕ => n ∈ S)
    (Complex.logarithmicPhaseDualBasePrincipalRunUnion_eq_surviving
      t eta K M) hnUnion

theorem Complex.logarithmicPhaseDualBasePrincipalRun_not_resonant
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    {n : ℕ} (hn : n ∈ Finset.Ico p.1 p.2) :
    ¬ Complex.logarithmicPhaseDualBaseResonant t eta n := by
  have hsurvive := Complex.logarithmicPhaseDualBasePrincipalRun_cell_survives
    t eta K M hp hn
  have hdata :=
    (Complex.mem_logarithmicPhaseDualBaseSurvivingModes_iff
      t eta K M n).mp hsurvive
  intro hres
  have hresMode : n ∈
      Complex.logarithmicPhaseDualBaseResonanceModes t eta K M :=
    (Complex.mem_logarithmicPhaseDualBaseResonanceModes_iff
      t eta K M n).mpr (And.intro hdata.1 hres)
  exact hdata.2 (Finset.mem_union_left _ hresMode)

theorem Complex.logarithmicPhaseDualBasePrincipalRun_adjacent_branch_eq
    (t eta : ℝ) (K M : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualBasePrincipalRuns t eta K M)
    {n : ℕ} (hn : n ∈ Finset.Ico p.1 p.2) :
    Complex.logarithmicPhaseDualBaseBranchIndex t n =
      Complex.logarithmicPhaseDualBaseBranchIndex t (n + 1) := by
  have hsurvive := Complex.logarithmicPhaseDualBasePrincipalRun_cell_survives
    t eta K M hp hn
  have hdata :=
    (Complex.mem_logarithmicPhaseDualBaseSurvivingModes_iff
      t eta K M n).mp hsurvive
  have hnotBoundary : n ∉
      Complex.logarithmicPhaseDualBaseBranchBoundaryModes t K M := by
    intro hboundary
    exact hdata.2 (Finset.mem_union_right _ hboundary)
  have hfilter :=
    (Complex.mem_logarithmicPhaseDualBaseBranchBoundaryModes_iff
      t K M n)
  by_contra hneq
  exact hnotBoundary (hfilter.mpr (And.intro hdata.1 hneq))

end

end LFunctions
end Boundary

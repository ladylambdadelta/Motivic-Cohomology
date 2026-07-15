import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseFiniteDeletedIntervalRuns

/-!
# Consecutive separated runs for the dual collar partition

The general deleted-interval construction is specialized to the discrete dual
collar family.  The resulting half-open intervals are bounded by `[K,M+1]`,
are pairwise disjoint, and number at most one more than the collar cardinality.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualSeparatedRunStarts
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset ℕ :=
  Nat.finiteDeletedIntervalRunStarts K M
    (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)

def Complex.logarithmicPhaseDualSeparatedRunEnd
    (t : ℝ) (h : ℕ) (eta : ℝ) (M s : ℕ) : ℕ :=
  Nat.finiteDeletedIntervalNextDeleted M
    (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta 0 M) s

def Complex.logarithmicPhaseDualSeparatedRuns
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) : Finset (ℕ × ℕ) :=
  Nat.finiteDeletedIntervalRuns K M
    (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_bounded
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ∀ n ∈ Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M,
      K ≤ n ∧ n ≤ M := by
  intro n hn
  exact Finset.mem_Icc.mp
    (Complex.logarithmicPhaseDualDiscreteCollarModes_subset_block
      t h eta K M hn)

theorem Complex.logarithmicPhaseDualSeparatedRunStarts_eq
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualSeparatedRunStarts t h eta K M =
      Nat.finiteDeletedIntervalRunStarts K M
        (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M) :=
  rfl

theorem Complex.logarithmicPhaseDualSeparatedRuns_eq
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualSeparatedRuns t h eta K M =
      Nat.finiteDeletedIntervalRuns K M
        (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M) :=
  rfl

theorem Complex.logarithmicPhaseDualSeparatedRunStarts_card_le_collar_add_one
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualSeparatedRunStarts t h eta K M).card ≤
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M).card + 1 := by
  unfold Complex.logarithmicPhaseDualSeparatedRunStarts
  exact Nat.finiteDeletedIntervalRunStarts_card_le_deleted_add_one
    K M (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)

theorem Complex.logarithmicPhaseDualSeparatedRuns_card_le_collar_add_one
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    (Complex.logarithmicPhaseDualSeparatedRuns t h eta K M).card ≤
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M).card + 1 := by
  unfold Complex.logarithmicPhaseDualSeparatedRuns
  exact Nat.finiteDeletedIntervalRuns_card_le_deleted_add_one
    K M (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M)

theorem Nat.finiteDeletedIntervalNextDeleted_le_M_add_one
    {K M : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (s : ℕ) :
    Nat.finiteDeletedIntervalNextDeleted M C s ≤ M + 1 := by
  unfold Nat.finiteDeletedIntervalNextDeleted
  let after := C.filter (fun n : ℕ => s ≤ n)
  split_ifs with hafter
  · have hminMem := Finset.min'_mem after hafter
    have hminC : after.min' hafter ∈ C := (Finset.mem_filter.mp hminMem).1
    have hminM := (Finset.mem_Icc.mp (hC hminC)).2
    exact le_trans hminM (Nat.le_succ M)
  · exact Nat.le_refl (M + 1)

theorem Nat.finiteDeletedIntervalRunStart_le_nextDeleted
    {K M : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    {s : ℕ}
    (hs : s ∈ Nat.finiteDeletedIntervalRunStarts K M C) :
    s ≤ Nat.finiteDeletedIntervalNextDeleted M C s := by
  unfold Nat.finiteDeletedIntervalNextDeleted
  let after := C.filter (fun n : ℕ => s ≤ n)
  split_ifs with hafter
  · have hminMem := Finset.min'_mem after hafter
    exact (Finset.mem_filter.mp hminMem).2
  · have hsM := (Finset.mem_Icc.mp
      (Nat.finiteDeletedIntervalRunStart_mem_block hs)).2
    exact le_trans hsM (Nat.le_succ M)

theorem Complex.logarithmicPhaseDualSeparatedRun_bounded
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ)
    {p : ℕ × ℕ}
    (hp : p ∈ Complex.logarithmicPhaseDualSeparatedRuns t h eta K M) :
    K ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ M + 1 := by
  have hpMembership :=
    (Nat.mem_finiteDeletedIntervalRuns_iff K M
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M) p).mp hp
  rcases hpMembership with ⟨s, hs, hpEq⟩
  have hsBlock := Nat.finiteDeletedIntervalRunStart_mem_block hs
  have hC :=
    Complex.logarithmicPhaseDualDiscreteCollarModes_subset_block
      t h eta K M
  have hsEnd := Nat.finiteDeletedIntervalRunStart_le_nextDeleted hC hs
  have hend := Nat.finiteDeletedIntervalNextDeleted_le_M_add_one hC s
  exact Eq.subst
    (motive := fun pair : ℕ × ℕ =>
      K ≤ pair.1 ∧ pair.1 ≤ pair.2 ∧ pair.2 ≤ M + 1)
    hpEq.symm
    (And.intro (Finset.mem_Icc.mp hsBlock).1
      (And.intro hsEnd hend))

theorem Nat.distinct_runStarts_ordered_by_intervening_deleted
    {K M : ℕ} {C : Finset ℕ} {s₁ s₂ : ℕ}
    (hs₁ : s₁ ∈ Nat.finiteDeletedIntervalRunStarts K M C)
    (hs₂ : s₂ ∈ Nat.finiteDeletedIntervalRunStarts K M C)
    (hneq : s₁ ≠ s₂)
    (horder : s₁ < s₂) :
    Nat.finiteDeletedIntervalNextDeleted M C s₁ ≤ s₂ := by
  have hs₂Cases := Nat.finiteDeletedIntervalRunStart_eq_left_or_pred_deleted hs₂
  match hs₂Cases with
  | Or.inl hs₂K =>
      have hs₁Lower := (Finset.mem_Icc.mp
        (Nat.finiteDeletedIntervalRunStart_mem_block hs₁)).1
      exact False.elim (not_lt_of_ge
        (Eq.subst (motive := fun z : ℕ => z ≤ s₁) hs₂K.symm hs₁Lower) horder)
  | Or.inr hpred =>
      have hs₂Pos : 0 < s₂ := lt_of_le_of_lt (Nat.zero_le s₁) horder
      have hs₁Pred : s₁ ≤ s₂ - 1 := Nat.le_sub_one_of_lt horder
      exact le_trans
        (Nat.nextDeleted_le_of_deleted_after hpred hs₁Pred)
        (Nat.sub_le s₂ 1)

theorem Complex.logarithmicPhaseDualSeparatedRuns_pairwise_disjoint
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ∀ p₁ ∈ Complex.logarithmicPhaseDualSeparatedRuns t h eta K M,
      ∀ p₂ ∈ Complex.logarithmicPhaseDualSeparatedRuns t h eta K M,
        p₁ ≠ p₂ →
          Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2) := by
  intro p₁ hp₁ p₂ hp₂ hpNe
  have hp₁Membership :=
    (Nat.mem_finiteDeletedIntervalRuns_iff K M
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M) p₁).mp hp₁
  have hp₂Membership :=
    (Nat.mem_finiteDeletedIntervalRuns_iff K M
      (Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M) p₂).mp hp₂
  rcases hp₁Membership with ⟨s₁, hs₁, hp₁Eq⟩
  rcases hp₂Membership with ⟨s₂, hs₂, hp₂Eq⟩
  have hsNe : s₁ ≠ s₂ := by
    intro hsEq
    exact hpNe
      (Eq.trans hp₁Eq
        (Eq.trans
          (congrArg
            (fun s : ℕ =>
              (s, Nat.finiteDeletedIntervalNextDeleted M
                (Complex.logarithmicPhaseDualDiscreteCollarModes
                  t h eta K M) s)) hsEq)
          hp₂Eq.symm))
  match lt_or_gt_of_ne hsNe with
  | Or.inl hsOrder =>
      have hend := Nat.distinct_runStarts_ordered_by_intervening_deleted
        hs₁ hs₂ hsNe hsOrder
      exact Finset.disjoint_left.mpr (fun n hn₁ hn₂ =>
        have hn₁Bounds := Finset.mem_Ico.mp hn₁
        have hn₂Bounds := Finset.mem_Ico.mp hn₂
        (not_lt_of_ge (le_trans hend hn₂Bounds.1)) hn₁Bounds.2)
  | Or.inr hsOrder =>
      have hend := Nat.distinct_runStarts_ordered_by_intervening_deleted
        hs₂ hs₁ hsNe.symm hsOrder
      exact Finset.disjoint_left.mpr (fun n hn₁ hn₂ =>
        have hn₁Bounds := Finset.mem_Ico.mp hn₁
        have hn₂Bounds := Finset.mem_Ico.mp hn₂
        (not_lt_of_ge (le_trans hend hn₁Bounds.1)) hn₂Bounds.2)

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualCollarCardinalityBound

/-!
# Runs in a finite interval after deleting collar indices

This general finite owner decomposes `Icc K M \ C` into maximal consecutive
runs without introducing a record of prerequisites.  A run starts at `K` when
`K` survives, or immediately after a deleted index.  Therefore the number of
runs is at most `C.card + 1`.  The construction is later specialized to the
dual separated family.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Nat.finiteDeletedIntervalRunStarts
    (K M : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ =>
      n ∉ C ∧ (n = K ∨ n - 1 ∈ C))

def Nat.finiteDeletedIntervalNextDeleted
    (M : ℕ) (C : Finset ℕ) (s : ℕ) : ℕ :=
  let after := C.filter (fun n : ℕ => s ≤ n)
  if hafter : after.Nonempty then after.min' hafter else M + 1

def Nat.finiteDeletedIntervalRun
    (M : ℕ) (C : Finset ℕ) (s : ℕ) : Finset ℕ :=
  Finset.Ico s (Nat.finiteDeletedIntervalNextDeleted M C s)

def Nat.finiteDeletedIntervalRuns
    (K M : ℕ) (C : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Nat.finiteDeletedIntervalRunStarts K M C).image
    (fun s : ℕ =>
      (s, Nat.finiteDeletedIntervalNextDeleted M C s))

theorem Nat.mem_finiteDeletedIntervalRunStarts_iff
    (K M : ℕ) (C : Finset ℕ) (s : ℕ) :
    s ∈ Nat.finiteDeletedIntervalRunStarts K M C ↔
      s ∈ Finset.Icc K M ∧
        s ∉ C ∧ (s = K ∨ s - 1 ∈ C) := by
  exact Finset.mem_filter

theorem Nat.finiteDeletedIntervalRunStart_mem_block
    {K M : ℕ} {C : Finset ℕ} {s : ℕ}
    (hs : s ∈ Nat.finiteDeletedIntervalRunStarts K M C) :
    s ∈ Finset.Icc K M := by
  exact
    ((Nat.mem_finiteDeletedIntervalRunStarts_iff K M C s).mp hs).1

theorem Nat.finiteDeletedIntervalRunStart_not_deleted
    {K M : ℕ} {C : Finset ℕ} {s : ℕ}
    (hs : s ∈ Nat.finiteDeletedIntervalRunStarts K M C) :
    s ∉ C := by
  exact
    ((Nat.mem_finiteDeletedIntervalRunStarts_iff K M C s).mp hs).2.1

theorem Nat.finiteDeletedIntervalRunStart_eq_left_or_pred_deleted
    {K M : ℕ} {C : Finset ℕ} {s : ℕ}
    (hs : s ∈ Nat.finiteDeletedIntervalRunStarts K M C) :
    s = K ∨ s - 1 ∈ C := by
  exact
    ((Nat.mem_finiteDeletedIntervalRunStarts_iff K M C s).mp hs).2.2

theorem Nat.finiteDeletedIntervalRunStart_pos_of_left_pos
    {K M : ℕ} {C : Finset ℕ} {s : ℕ}
    (hK : 0 < K)
    (hs : s ∈ Nat.finiteDeletedIntervalRunStarts K M C) :
    0 < s := by
  have hsBlock := Nat.finiteDeletedIntervalRunStart_mem_block hs
  exact lt_of_lt_of_le hK (Finset.mem_Icc.mp hsBlock).1

theorem Nat.pred_injective_on_nonleft_runStarts
    (K M : ℕ) (C : Finset ℕ) :
    Set.InjOn
      (fun s : ℕ => s - 1)
      {s : ℕ |
        s ∈ Nat.finiteDeletedIntervalRunStarts K M C ∧ s ≠ K} := by
  intro x hx y hy hpred
  have hxBlock := Nat.finiteDeletedIntervalRunStart_mem_block hx.1
  have hyBlock := Nat.finiteDeletedIntervalRunStart_mem_block hy.1
  have hxLower := (Finset.mem_Icc.mp hxBlock).1
  have hyLower := (Finset.mem_Icc.mp hyBlock).1
  have hxPos : 0 < x := by
    match eq_or_lt_of_le hxLower with
    | Or.inl hxEq => exact False.elim (hx.2 hxEq)
    | Or.inr hxLt => exact lt_of_le_of_lt (Nat.zero_le K) hxLt
  have hyPos : 0 < y := by
    match eq_or_lt_of_le hyLower with
    | Or.inl hyEq => exact False.elim (hy.2 hyEq)
    | Or.inr hyLt => exact lt_of_le_of_lt (Nat.zero_le K) hyLt
  exact Nat.sub_one_inj.mp
    (And.intro hxPos (And.intro hyPos hpred))

def Nat.finiteDeletedIntervalNonleftRunStarts
    (K M : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Nat.finiteDeletedIntervalRunStarts K M C).erase K

theorem Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff
    (K M : ℕ) (C : Finset ℕ) (s : ℕ) :
    s ∈ Nat.finiteDeletedIntervalNonleftRunStarts K M C ↔
      s ∈ Nat.finiteDeletedIntervalRunStarts K M C ∧ s ≠ K := by
  unfold Nat.finiteDeletedIntervalNonleftRunStarts
  exact Finset.mem_erase

theorem Nat.pred_maps_nonleft_runStarts_into_deleted
    (K M : ℕ) (C : Finset ℕ) :
    ∀ s ∈ Nat.finiteDeletedIntervalNonleftRunStarts K M C,
      s - 1 ∈ C := by
  intro s hs
  have hsMembership :=
    (Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff K M C s).mp hs
  match Nat.finiteDeletedIntervalRunStart_eq_left_or_pred_deleted hsMembership.1 with
  | Or.inl hsLeft => exact False.elim (hsMembership.2 hsLeft)
  | Or.inr hpred => exact hpred

theorem Nat.finiteDeletedIntervalNonleftRunStarts_card_le_deleted
    (K M : ℕ) (C : Finset ℕ) :
    (Nat.finiteDeletedIntervalNonleftRunStarts K M C).card ≤ C.card := by
  let f : ℕ → ℕ := fun s : ℕ => s - 1
  have hmap := Nat.pred_maps_nonleft_runStarts_into_deleted K M C
  have hinjective :
      Set.InjOn f
        (Nat.finiteDeletedIntervalNonleftRunStarts K M C : Set ℕ) := by
    intro x hx y hy hxy
    exact Nat.pred_injective_on_nonleft_runStarts K M C
      (And.intro
        ((Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff K M C x).mp hx).1
        ((Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff K M C x).mp hx).2)
      (And.intro
        ((Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff K M C y).mp hy).1
        ((Nat.mem_finiteDeletedIntervalNonleftRunStarts_iff K M C y).mp hy).2)
      hxy
  exact Finset.card_le_card_of_injOn f hmap hinjective

theorem Nat.finiteDeletedIntervalRunStarts_card_le_deleted_add_one
    (K M : ℕ) (C : Finset ℕ) :
    (Nat.finiteDeletedIntervalRunStarts K M C).card ≤ C.card + 1 := by
  let S := Nat.finiteDeletedIntervalRunStarts K M C
  let S' := Nat.finiteDeletedIntervalNonleftRunStarts K M C
  have heraseCard : S.card ≤ S'.card + 1 := by
    unfold S'
    exact Finset.card_le_card_erase_add_one S K
  have hnonleft :=
    Nat.finiteDeletedIntervalNonleftRunStarts_card_le_deleted K M C
  exact le_trans heraseCard (Nat.add_le_add_right hnonleft 1)

theorem Nat.mem_finiteDeletedIntervalRuns_iff
    (K M : ℕ) (C : Finset ℕ) (p : ℕ × ℕ) :
    p ∈ Nat.finiteDeletedIntervalRuns K M C ↔
      ∃ s ∈ Nat.finiteDeletedIntervalRunStarts K M C,
        p = (s, Nat.finiteDeletedIntervalNextDeleted M C s) := by
  unfold Nat.finiteDeletedIntervalRuns
  exact Finset.mem_image

theorem Nat.finiteDeletedIntervalRuns_card_le_runStarts
    (K M : ℕ) (C : Finset ℕ) :
    (Nat.finiteDeletedIntervalRuns K M C).card ≤
      (Nat.finiteDeletedIntervalRunStarts K M C).card := by
  unfold Nat.finiteDeletedIntervalRuns
  exact Finset.card_image_le

theorem Nat.finiteDeletedIntervalRuns_card_le_deleted_add_one
    (K M : ℕ) (C : Finset ℕ) :
    (Nat.finiteDeletedIntervalRuns K M C).card ≤ C.card + 1 := by
  exact le_trans
    (Nat.finiteDeletedIntervalRuns_card_le_runStarts K M C)
    (Nat.finiteDeletedIntervalRunStarts_card_le_deleted_add_one K M C)

theorem Nat.nextDeleted_le_of_deleted_after
    {M : ℕ} {C : Finset ℕ} {s d : ℕ}
    (hdC : d ∈ C) (hsd : s ≤ d) :
    Nat.finiteDeletedIntervalNextDeleted M C s ≤ d := by
  unfold Nat.finiteDeletedIntervalNextDeleted
  let after := C.filter (fun n : ℕ => s ≤ n)
  have hdAfter : d ∈ after := Finset.mem_filter.mpr (And.intro hdC hsd)
  have hafter : after.Nonempty := Exists.intro d hdAfter
  split_ifs with hnonempty
  · exact Finset.min'_le after d hdAfter
  · exact False.elim (hnonempty hafter)

theorem Nat.finiteDeletedIntervalRuns_pairwise_disjoint
    (K M : ℕ) (C : Finset ℕ) :
    ∀ p₁ ∈ Nat.finiteDeletedIntervalRuns K M C,
      ∀ p₂ ∈ Nat.finiteDeletedIntervalRuns K M C,
        p₁ ≠ p₂ →
          Disjoint (Finset.Ico p₁.1 p₁.2) (Finset.Ico p₂.1 p₂.2) := by
  intro p₁ hp₁ p₂ hp₂ hpNe
  rcases (Nat.mem_finiteDeletedIntervalRuns_iff K M C p₁).mp hp₁ with
    ⟨s₁, hs₁, hp₁Eq⟩
  rcases (Nat.mem_finiteDeletedIntervalRuns_iff K M C p₂).mp hp₂ with
    ⟨s₂, hs₂, hp₂Eq⟩
  have hsNe : s₁ ≠ s₂ := by
    intro hsEq
    exact hpNe
      (Eq.trans hp₁Eq
        (Eq.trans
          (congrArg
            (fun s : ℕ =>
              (s, Nat.finiteDeletedIntervalNextDeleted M C s)) hsEq)
          hp₂Eq.symm))
  match lt_or_gt_of_ne hsNe with
  | Or.inl hsOrder =>
      have hs₂Cases := Nat.finiteDeletedIntervalRunStart_eq_left_or_pred_deleted hs₂
      have hend : Nat.finiteDeletedIntervalNextDeleted M C s₁ ≤ s₂ := by
        match hs₂Cases with
        | Or.inl hs₂K =>
            have hs₁Lower := (Finset.mem_Icc.mp
              (Nat.finiteDeletedIntervalRunStart_mem_block hs₁)).1
            exact False.elim
              ((not_lt_of_ge
                (Eq.subst (motive := fun z : ℕ => z ≤ s₁) hs₂K.symm hs₁Lower))
                hsOrder)
        | Or.inr hpred =>
            have hs₁Pred : s₁ ≤ s₂ - 1 := Nat.le_sub_one_of_lt hsOrder
            exact le_trans
              (Nat.nextDeleted_le_of_deleted_after hpred hs₁Pred)
              (Nat.sub_le s₂ 1)
      exact Finset.disjoint_left.mpr (fun n hn₁ hn₂ =>
        have hn₁Bounds := Finset.mem_Ico.mp
          (Eq.subst (motive := fun p : ℕ × ℕ => n ∈ Finset.Ico p.1 p.2)
            hp₁Eq hn₁)
        have hn₂Bounds := Finset.mem_Ico.mp
          (Eq.subst (motive := fun p : ℕ × ℕ => n ∈ Finset.Ico p.1 p.2)
            hp₂Eq hn₂)
        (not_lt_of_ge (le_trans hend hn₂Bounds.1)) hn₁Bounds.2)
  | Or.inr hsOrder =>
      have hs₁Cases := Nat.finiteDeletedIntervalRunStart_eq_left_or_pred_deleted hs₁
      have hend : Nat.finiteDeletedIntervalNextDeleted M C s₂ ≤ s₁ := by
        match hs₁Cases with
        | Or.inl hs₁K =>
            have hs₂Lower := (Finset.mem_Icc.mp
              (Nat.finiteDeletedIntervalRunStart_mem_block hs₂)).1
            exact False.elim
              ((not_lt_of_ge
                (Eq.subst (motive := fun z : ℕ => z ≤ s₂) hs₁K.symm hs₂Lower))
                hsOrder)
        | Or.inr hpred =>
            have hs₂Pred : s₂ ≤ s₁ - 1 := Nat.le_sub_one_of_lt hsOrder
            exact le_trans
              (Nat.nextDeleted_le_of_deleted_after hpred hs₂Pred)
              (Nat.sub_le s₁ 1)
      exact Finset.disjoint_left.mpr (fun n hn₁ hn₂ =>
        have hn₁Bounds := Finset.mem_Ico.mp
          (Eq.subst (motive := fun p : ℕ × ℕ => n ∈ Finset.Ico p.1 p.2)
            hp₁Eq hn₁)
        have hn₂Bounds := Finset.mem_Ico.mp
          (Eq.subst (motive := fun p : ℕ × ℕ => n ∈ Finset.Ico p.1 p.2)
            hp₂Eq hn₂)
        (not_lt_of_ge (le_trans hend hn₁Bounds.1)) hn₂Bounds.2)

end

end LFunctions
end Boundary

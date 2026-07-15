import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualDiscreteCollarPartition

/-!
# Cardinality of discrete dual crossing collars

The discrete collar is refined by principal level.  A finite natural set whose
real diameter is at most `D` has real cardinality at most `D+1`; this owner
proves that fact through the set's minimum and maximum.  Applying it levelwise
and summing over the canonical represented-level range gives the collar-count
ledger used by the shifted-correlation bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualDiscreteLevelCollarModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M q : ℕ) : Finset ℕ :=
  (Finset.Icc K M).filter
    (fun n : ℕ =>
      ∃ x : ℝ,
        x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∧
          x ∈ Complex.logarithmicPhaseDualCrossingCollar
            t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ) q)

theorem Complex.mem_logarithmicPhaseDualDiscreteLevelCollarModes_iff
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M q n : ℕ) :
    n ∈ Complex.logarithmicPhaseDualDiscreteLevelCollarModes
        t h eta K M q ↔
      n ∈ Finset.Icc K M ∧
        ∃ x : ℝ,
          x ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ) ∧
            x ∈ Complex.logarithmicPhaseDualCrossingCollar
              t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ) q := by
  exact Finset.mem_filter

theorem Complex.logarithmicPhaseDualDiscreteLevelCollarModes_subset_collarModes
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ)
    {q : ℕ}
    (hq : q ∈ Complex.logarithmicPhaseDualCrossingLevels
      t (h : ℝ) eta (K : ℝ)) :
    Complex.logarithmicPhaseDualDiscreteLevelCollarModes t h eta K M q ⊆
      Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M := by
  intro n hn
  have hnLevel :=
    (Complex.mem_logarithmicPhaseDualDiscreteLevelCollarModes_iff
      t h eta K M q n).mp hn
  rcases hnLevel.2 with ⟨x, hxCell, hxLevel⟩
  have hnUnion :=
    (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
      t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
      (Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ)) x).mpr
      (Exists.intro q (And.intro hq hxLevel))
  exact
    (Complex.mem_logarithmicPhaseDualDiscreteCollarModes_iff
      t h eta K M n).mpr
      (And.intro hnLevel.1
        (Exists.intro x (And.intro hxCell hnUnion)))

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_eq_biUnion_levels
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M =
      (Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ)).biUnion
        (fun q : ℕ =>
          Complex.logarithmicPhaseDualDiscreteLevelCollarModes
            t h eta K M q) := by
  exact Finset.Subset.antisymm
    (fun n hn =>
      have hnMembership :=
        (Complex.mem_logarithmicPhaseDualDiscreteCollarModes_iff
          t h eta K M n).mp hn
      rcases hnMembership.2 with ⟨x, hxCell, hxUnionCell⟩
      have hxUnion :=
        (Complex.mem_logarithmicPhaseDualCrossingCollarUnion_iff
          t (h : ℝ) eta (K : ℝ) ((M + 1 : ℕ) : ℝ)
          (Complex.logarithmicPhaseDualCrossingLevels
            t (h : ℝ) eta (K : ℝ)) x).mp hxUnionCell
      rcases hxUnion with ⟨q, hq, hxLevel⟩
      Finset.mem_biUnion.mpr
        (Exists.intro q
          (And.intro hq
            ((Complex.mem_logarithmicPhaseDualDiscreteLevelCollarModes_iff
              t h eta K M q n).mpr
              (And.intro hnMembership.1
                (Exists.intro x (And.intro hxCell hxLevel))))))
    (fun n hn =>
      have hnUnion := Finset.mem_biUnion.mp hn
      match hnUnion with
      | ⟨q, hq, hnLevel⟩ =>
          Complex.logarithmicPhaseDualDiscreteLevelCollarModes_subset_collarModes
            t h eta K M hq hnLevel)

theorem Finset.card_biUnion_le_sum_card
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : α → Finset β) :
    (S.biUnion F).card ≤ ∑ a ∈ S, (F a).card := by
  induction S using Finset.induction_on with
  | empty =>
      have hunion : (∅ : Finset α).biUnion F = ∅ := Finset.biUnion_empty
      exact Eq.subst (motive := fun n : ℕ => n ≤ 0)
        (congrArg Finset.card hunion).symm (Nat.le_refl 0)
  | @insert a S ha ih =>
      have hunion : (insert a S).biUnion F = F a ∪ S.biUnion F :=
        Finset.biUnion_insert
      have hcardUnion := Finset.card_union_le (F a) (S.biUnion F)
      have hsum := Nat.add_le_add_left ih (F a).card
      have hsumInsert := Finset.sum_insert ha
        (fun x : α => (F x).card)
      exact Eq.subst (motive := fun n : ℕ => n ≤ _)
        (congrArg Finset.card hunion).symm
        (le_trans hcardUnion
          (Eq.subst (motive := fun n : ℕ => _ ≤ n)
            hsumInsert.symm hsum))

theorem Finset.card_real_le_sum_card_real_biUnion
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (F : α → Finset β) :
    (((S.biUnion F).card : ℕ) : ℝ) ≤
      ∑ a ∈ S, (((F a).card : ℕ) : ℝ) := by
  have hnat := Finset.card_biUnion_le_sum_card S F
  have hcast := Nat.cast_le.mpr hnat
  have hsumCast :
      (((∑ a ∈ S, (F a).card : ℕ) : ℕ) : ℝ) =
        ∑ a ∈ S, (((F a).card : ℕ) : ℝ) := by
    exact Nat.cast_sum
  exact Eq.subst (motive := fun z : ℝ => _ ≤ z)
    hsumCast.symm hcast

theorem Finset.card_le_Icc_min_max
    (S : Finset ℕ) (hS : S.Nonempty) :
    S.card ≤ (Finset.Icc (S.min' hS) (S.max' hS)).card := by
  exact Finset.card_le_card
    (fun n hn => Finset.mem_Icc.mpr
      (And.intro (Finset.min'_le S n hn) (Finset.le_max' S n hn)))

theorem Finset.card_real_le_diameter_add_one
    (S : Finset ℕ) (D : ℝ)
    (hD : 0 ≤ D)
    (hdiameter : ∀ x ∈ S, ∀ y ∈ S,
      |(x : ℝ) - (y : ℝ)| ≤ D) :
    (S.card : ℝ) ≤ D + 1 := by
  match S.eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hcard : (S.card : ℝ) = 0 := by
        exact Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ))
            (congrArg Finset.card hempty))
          Nat.cast_zero
      exact Eq.subst (motive := fun z : ℝ => z ≤ D + 1)
        hcard.symm (add_nonneg hD zero_le_one)
  | Or.inr hnonempty =>
      let lo := S.min' hnonempty
      let hi := S.max' hnonempty
      have hlo := Finset.min'_mem S hnonempty
      have hhi := Finset.max'_mem S hnonempty
      have hlohi : lo ≤ hi := Finset.min'_le S hi hhi
      have hcard := Finset.card_le_Icc_min_max S hnonempty
      have hcardIcc := Nat.card_Icc lo hi
      have hcastSub : (((hi + 1 - lo : ℕ) : ℝ)) =
          ((hi + 1 : ℕ) : ℝ) - (lo : ℝ) :=
        Nat.cast_sub (Nat.le_add_left lo 1 |>.trans (Nat.add_le_add_right hlohi 1))
      have hdiam := hdiameter hi hhi lo hlo
      have habs : |(hi : ℝ) - (lo : ℝ)| = (hi : ℝ) - (lo : ℝ) :=
        abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr hlohi))
      have hwidth : ((hi + 1 : ℕ) : ℝ) - (lo : ℝ) ≤ D + 1 := by
        have hcastSucc : ((hi + 1 : ℕ) : ℝ) = (hi : ℝ) + 1 :=
          Nat.cast_add hi 1
        have hbase : (hi : ℝ) - (lo : ℝ) ≤ D :=
          Eq.subst (motive := fun z : ℝ => z ≤ D) habs.symm hdiam
        exact Eq.subst (motive := fun z : ℝ => z - (lo : ℝ) ≤ D + 1)
          hcastSucc.symm
          (Eq.trans
            (add_sub_assoc (hi : ℝ) 1 (lo : ℝ))
            (add_le_add_right hbase 1))
      have hcastCard := Nat.cast_le.mpr hcard
      exact le_trans hcastCard
        (Eq.subst (motive := fun z : ℝ => z ≤ D + 1)
          (Eq.trans (congrArg (fun n : ℕ => (n : ℝ)) hcardIcc) hcastSub).symm
          hwidth)

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_card_real_le_level_sum
    (t : ℝ) (h : ℕ) (eta : ℝ) (K M : ℕ) :
    ((Complex.logarithmicPhaseDualDiscreteCollarModes t h eta K M).card : ℝ) ≤
      ∑ q ∈ Complex.logarithmicPhaseDualCrossingLevels
          t (h : ℝ) eta (K : ℝ),
        ((Complex.logarithmicPhaseDualDiscreteLevelCollarModes
          t h eta K M q).card : ℝ) := by
  have heq :=
    Complex.logarithmicPhaseDualDiscreteCollarModes_eq_biUnion_levels
      t h eta K M
  exact Eq.subst (motive := fun z : Finset ℕ => (z.card : ℝ) ≤ _)
    heq.symm
    (Finset.card_real_le_sum_card_real_biUnion
      (Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ))
      (fun q : ℕ =>
        Complex.logarithmicPhaseDualDiscreteLevelCollarModes
          t h eta K M q))

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseFiniteDeletedIntervalRunCover

/-!
# Exact coverage of a finite deleted interval by maximal runs

The containing start selected from the greatest prior deletion has no deleted
point between itself and the surviving point.  Therefore the next deleted
index lies strictly after the point, and the point belongs to the corresponding
half-open run.  The union of all maximal runs is exactly `Icc K M \ C`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Nat.finiteDeletedIntervalRunUnion
    (K M : ℕ) (C : Finset ℕ) : Finset ℕ :=
  (Nat.finiteDeletedIntervalRuns K M C).biUnion
    (fun p : ℕ × ℕ => Finset.Ico p.1 p.2)

theorem Nat.no_deleted_between_containingStart_and_point
    {K M n d : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hdC : d ∈ C)
    (hstartD : Nat.finiteDeletedIntervalContainingRunStart K C n ≤ d)
    (hdn : d < n) : False := by
  match (Nat.finiteDeletedBefore C n).eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hdBefore : d ∈ Nat.finiteDeletedBefore C n :=
        (Nat.mem_finiteDeletedBefore_iff C n d).mpr (And.intro hdC hdn)
      exact Finset.not_mem_empty d
        (Eq.subst (motive := fun S : Finset ℕ => d ∈ S) hempty hdBefore)
  | Or.inr hbefore =>
      let dmax := (Nat.finiteDeletedBefore C n).max' hbefore
      have hdBefore : d ∈ Nat.finiteDeletedBefore C n :=
        (Nat.mem_finiteDeletedBefore_iff C n d).mpr (And.intro hdC hdn)
      have hdLeMax := Finset.le_max'
        (Nat.finiteDeletedBefore C n) d hdBefore
      have hstartEq :=
        Nat.finiteDeletedIntervalContainingRunStart_eq_max_add_one
          K C n hbefore
      have hsuccLeD : dmax + 1 ≤ d :=
        Eq.subst (motive := fun s : ℕ => s ≤ d) hstartEq hstartD
      exact (not_succ_le_self dmax) (le_trans hsuccLeD hdLeMax)

theorem Nat.point_lt_nextDeleted_of_containingStart
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hnNot : n ∉ C) :
    n < Nat.finiteDeletedIntervalNextDeleted M C
      (Nat.finiteDeletedIntervalContainingRunStart K C n) := by
  let s := Nat.finiteDeletedIntervalContainingRunStart K C n
  unfold Nat.finiteDeletedIntervalNextDeleted
  let after := C.filter (fun d : ℕ => s ≤ d)
  split_ifs with hafter
  · let d := after.min' hafter
    have hdAfter := Finset.min'_mem after hafter
    have hdProperties := Finset.mem_filter.mp hdAfter
    have hnotLe : ¬ d ≤ n := by
      intro hdn
      match Nat.lt_or_eq_of_le hdn with
      | Or.inl hdLt =>
          exact Nat.no_deleted_between_containingStart_and_point
            hC hnBlock hdProperties.1 hdProperties.2 hdLt
      | Or.inr hdEq =>
          exact hnNot
            (Eq.subst (motive := fun z : ℕ => z ∈ C) hdEq.symm hdProperties.1)
    exact lt_of_not_ge hnotLe
  · have hnM := (Finset.mem_Icc.mp hnBlock).2
    exact lt_of_le_of_lt hnM (Nat.lt_succ_self M)

theorem Nat.surviving_point_mem_containing_run
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hnNot : n ∉ C) :
    n ∈ Nat.finiteDeletedIntervalRun M C
      (Nat.finiteDeletedIntervalContainingRunStart K C n) := by
  unfold Nat.finiteDeletedIntervalRun
  exact Finset.mem_Ico.mpr
    (And.intro
      (Nat.finiteDeletedIntervalContainingRunStart_le_point
        K C (Finset.mem_Icc.mp hnBlock).1)
      (Nat.point_lt_nextDeleted_of_containingStart hC hnBlock hnNot))

theorem Nat.surviving_point_mem_runUnion
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hnNot : n ∉ C) :
    n ∈ Nat.finiteDeletedIntervalRunUnion K M C := by
  let s := Nat.finiteDeletedIntervalContainingRunStart K C n
  have hsStart :=
    Nat.finiteDeletedIntervalContainingRunStart_is_runStart
      hC hnBlock hnNot
  let p := (s, Nat.finiteDeletedIntervalNextDeleted M C s)
  have hpRuns : p ∈ Nat.finiteDeletedIntervalRuns K M C := by
    exact (Nat.mem_finiteDeletedIntervalRuns_iff K M C p).mpr
      (Exists.intro s (And.intro hsStart rfl))
  have hnRun := Nat.surviving_point_mem_containing_run hC hnBlock hnNot
  unfold Nat.finiteDeletedIntervalRunUnion
  exact Finset.mem_biUnion.mpr
    (Exists.intro p
      (And.intro hpRuns
        (Eq.subst (motive := fun S : Finset ℕ => n ∈ S) rfl hnRun)))

theorem Nat.run_point_mem_block
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hn : n ∈ Nat.finiteDeletedIntervalRunUnion K M C) :
    n ∈ Finset.Icc K M := by
  unfold Nat.finiteDeletedIntervalRunUnion at hn
  have hnUnion := Finset.mem_biUnion.mp hn
  rcases hnUnion with ⟨p, hp, hnRun⟩
  have hpMembership :=
    (Nat.mem_finiteDeletedIntervalRuns_iff K M C p).mp hp
  rcases hpMembership with ⟨s, hs, hpEq⟩
  have hsBlock := Nat.finiteDeletedIntervalRunStart_mem_block hs
  have hend := Nat.finiteDeletedIntervalNextDeleted_le_M_add_one hC s
  have hnBounds := Finset.mem_Ico.mp hnRun
  have hnLower : K ≤ n := le_trans
    (Finset.mem_Icc.mp hsBlock).1
    (Eq.subst (motive := fun z : ℕ => z ≤ n)
      (congrArg Prod.fst hpEq).symm hnBounds.1)
  have hnUpper : n ≤ M := by
    have hnSucc : n < M + 1 := lt_of_lt_of_le hnBounds.2
      (Eq.subst (motive := fun z : ℕ => z ≤ M + 1)
        (congrArg Prod.snd hpEq).symm hend)
    exact Nat.lt_succ_iff.mp hnSucc
  exact Finset.mem_Icc.mpr (And.intro hnLower hnUpper)

theorem Nat.run_point_not_deleted
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hn : n ∈ Nat.finiteDeletedIntervalRunUnion K M C) :
    n ∉ C := by
  unfold Nat.finiteDeletedIntervalRunUnion at hn
  rcases Finset.mem_biUnion.mp hn with ⟨p, hp, hnRun⟩
  rcases (Nat.mem_finiteDeletedIntervalRuns_iff K M C p).mp hp with
    ⟨s, hs, hpEq⟩
  have hnBounds := Finset.mem_Ico.mp hnRun
  intro hnC
  have hnextLe := Nat.nextDeleted_le_of_deleted_after hnC
    (Eq.subst (motive := fun z : ℕ => z ≤ n)
      (congrArg Prod.fst hpEq).symm hnBounds.1)
  have hnNext : n < Nat.finiteDeletedIntervalNextDeleted M C s :=
    Eq.subst (motive := fun z : ℕ => n < z)
      (congrArg Prod.snd hpEq).symm hnBounds.2
  exact (not_lt_of_ge hnextLe) hnNext

theorem Nat.finiteDeletedIntervalRunUnion_eq_sdiff
    (K M : ℕ) (C : Finset ℕ)
    (hC : C ⊆ Finset.Icc K M) :
    Nat.finiteDeletedIntervalRunUnion K M C = Finset.Icc K M \ C := by
  exact Finset.Subset.antisymm
    (fun n hn => Finset.mem_sdiff.mpr
      (And.intro (Nat.run_point_mem_block hC hn)
        (Nat.run_point_not_deleted hC hn)))
    (fun n hn =>
      have hnMembership := Finset.mem_sdiff.mp hn
      Nat.surviving_point_mem_runUnion hC hnMembership.1 hnMembership.2)

end

end LFunctions
end Boundary

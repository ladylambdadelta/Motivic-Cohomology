import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualSeparatedRuns

/-!
# Exact cover by finite deleted-interval runs

For a surviving point `n`, take the greatest deleted point strictly below it.
If it exists, its successor is the run start containing `n`; otherwise the run
starts at the left endpoint.  This owner proves that the maximal runs cover
exactly the undeleted portion of the finite interval.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Nat.finiteDeletedBefore
    (C : Finset ℕ) (n : ℕ) : Finset ℕ :=
  C.filter (fun d : ℕ => d < n)

def Nat.finiteDeletedIntervalContainingRunStart
    (K : ℕ) (C : Finset ℕ) (n : ℕ) : ℕ :=
  let before := Nat.finiteDeletedBefore C n
  if hbefore : before.Nonempty then before.max' hbefore + 1 else K

theorem Nat.mem_finiteDeletedBefore_iff
    (C : Finset ℕ) (n d : ℕ) :
    d ∈ Nat.finiteDeletedBefore C n ↔ d ∈ C ∧ d < n := by
  exact Finset.mem_filter

theorem Nat.finiteDeletedIntervalContainingRunStart_eq_left_of_empty
    (K : ℕ) (C : Finset ℕ) (n : ℕ)
    (hempty : (Nat.finiteDeletedBefore C n).Nonempty → False) :
    Nat.finiteDeletedIntervalContainingRunStart K C n = K := by
  unfold Nat.finiteDeletedIntervalContainingRunStart
  split_ifs with hbefore
  · exact False.elim (hempty hbefore)
  · exact rfl

theorem Nat.finiteDeletedIntervalContainingRunStart_eq_max_add_one
    (K : ℕ) (C : Finset ℕ) (n : ℕ)
    (hbefore : (Nat.finiteDeletedBefore C n).Nonempty) :
    Nat.finiteDeletedIntervalContainingRunStart K C n =
      (Nat.finiteDeletedBefore C n).max' hbefore + 1 := by
  unfold Nat.finiteDeletedIntervalContainingRunStart
  split_ifs with h
  · exact rfl
  · exact False.elim (h hbefore)

theorem Nat.finiteDeletedIntervalContainingRunStart_le_point
    (K : ℕ) (C : Finset ℕ) {n : ℕ}
    (hK : K ≤ n) :
    Nat.finiteDeletedIntervalContainingRunStart K C n ≤ n := by
  match (Nat.finiteDeletedBefore C n).eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hnone : (Nat.finiteDeletedBefore C n).Nonempty → False := by
        intro hnonempty
        rcases hnonempty with ⟨d, hd⟩
        exact Finset.not_mem_empty d
          (Eq.subst (motive := fun S : Finset ℕ => d ∈ S) hempty hd)
      exact Eq.subst (motive := fun s : ℕ => s ≤ n)
        (Nat.finiteDeletedIntervalContainingRunStart_eq_left_of_empty
          K C n hnone).symm hK
  | Or.inr hbefore =>
      have hmaxMem := Finset.max'_mem
        (Nat.finiteDeletedBefore C n) hbefore
      have hmaxLt :=
        ((Nat.mem_finiteDeletedBefore_iff C n
          ((Nat.finiteDeletedBefore C n).max' hbefore)).mp hmaxMem).2
      have hsuccLe := Nat.succ_le_of_lt hmaxLt
      exact Eq.subst (motive := fun s : ℕ => s ≤ n)
        (Nat.finiteDeletedIntervalContainingRunStart_eq_max_add_one
          K C n hbefore).symm hsuccLe

theorem Nat.finiteDeletedIntervalContainingRunStart_not_deleted
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hnNot : n ∉ C) :
    Nat.finiteDeletedIntervalContainingRunStart K C n ∉ C := by
  match (Nat.finiteDeletedBefore C n).eq_empty_or_nonempty with
  | Or.inl hempty =>
      have hnone : (Nat.finiteDeletedBefore C n).Nonempty → False := by
        intro hnonempty
        rcases hnonempty with ⟨d, hd⟩
        exact Finset.not_mem_empty d
          (Eq.subst (motive := fun S : Finset ℕ => d ∈ S) hempty hd)
      have hstart :=
        Nat.finiteDeletedIntervalContainingRunStart_eq_left_of_empty
          K C n hnone
      intro hstartC
      have hKC : K ∈ C := Eq.subst (motive := fun s : ℕ => s ∈ C)
        hstart hstartC
      have hKBefore : K ∈ Nat.finiteDeletedBefore C n := by
        exact (Nat.mem_finiteDeletedBefore_iff C n K).mpr
          (And.intro hKC
            (lt_of_le_of_ne (Finset.mem_Icc.mp hnBlock).1
              (fun hEq => hnNot (Eq.subst (motive := fun z : ℕ => z ∈ C)
                hEq.symm hKC))))
      exact hnone (Exists.intro K hKBefore)
  | Or.inr hbefore =>
      let d := (Nat.finiteDeletedBefore C n).max' hbefore
      have hdMem := Finset.max'_mem (Nat.finiteDeletedBefore C n) hbefore
      have hdProperties :=
        (Nat.mem_finiteDeletedBefore_iff C n d).mp hdMem
      have hstart :=
        Nat.finiteDeletedIntervalContainingRunStart_eq_max_add_one
          K C n hbefore
      intro hstartC
      have hsuccC : d + 1 ∈ C :=
        Eq.subst (motive := fun s : ℕ => s ∈ C) hstart hstartC
      have hsuccLtOrEq : d + 1 < n ∨ d + 1 = n :=
        Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hdProperties.2)
      match hsuccLtOrEq with
      | Or.inl hsuccLt =>
          have hsuccBefore : d + 1 ∈ Nat.finiteDeletedBefore C n :=
            (Nat.mem_finiteDeletedBefore_iff C n (d + 1)).mpr
              (And.intro hsuccC hsuccLt)
          have hmaxGe := Finset.le_max'
            (Nat.finiteDeletedBefore C n) (d + 1) hsuccBefore
          exact (not_succ_le_self d) hmaxGe
      | Or.inr hsuccEq =>
          exact hnNot
            (Eq.subst (motive := fun s : ℕ => s ∈ C) hsuccEq hsuccC)

theorem Nat.finiteDeletedIntervalContainingRunStart_is_runStart
    {K M n : ℕ} {C : Finset ℕ}
    (hC : C ⊆ Finset.Icc K M)
    (hnBlock : n ∈ Finset.Icc K M)
    (hnNot : n ∉ C) :
    Nat.finiteDeletedIntervalContainingRunStart K C n ∈
      Nat.finiteDeletedIntervalRunStarts K M C := by
  let s := Nat.finiteDeletedIntervalContainingRunStart K C n
  have hsLeN := Nat.finiteDeletedIntervalContainingRunStart_le_point
    K C (Finset.mem_Icc.mp hnBlock).1
  have hsLower : K ≤ s := by
    match (Nat.finiteDeletedBefore C n).eq_empty_or_nonempty with
    | Or.inl hempty =>
        have hnone : (Nat.finiteDeletedBefore C n).Nonempty → False := by
          intro hnonempty
          rcases hnonempty with ⟨d, hd⟩
          exact Finset.not_mem_empty d
            (Eq.subst (motive := fun S : Finset ℕ => d ∈ S) hempty hd)
        exact le_of_eq
          (Nat.finiteDeletedIntervalContainingRunStart_eq_left_of_empty
            K C n hnone).symm
    | Or.inr hbefore =>
        let d := (Nat.finiteDeletedBefore C n).max' hbefore
        have hdC := ((Nat.mem_finiteDeletedBefore_iff C n d).mp
          (Finset.max'_mem (Nat.finiteDeletedBefore C n) hbefore)).1
        have hKd := (Finset.mem_Icc.mp (hC hdC)).1
        exact le_trans hKd (Nat.le_succ d)
  have hsUpper : s ≤ M := le_trans hsLeN (Finset.mem_Icc.mp hnBlock).2
  have hsNot := Nat.finiteDeletedIntervalContainingRunStart_not_deleted
    hC hnBlock hnNot
  have hsCase : s = K ∨ s - 1 ∈ C := by
    match (Nat.finiteDeletedBefore C n).eq_empty_or_nonempty with
    | Or.inl hempty =>
        have hnone : (Nat.finiteDeletedBefore C n).Nonempty → False := by
          intro hnonempty
          rcases hnonempty with ⟨d, hd⟩
          exact Finset.not_mem_empty d
            (Eq.subst (motive := fun S : Finset ℕ => d ∈ S) hempty hd)
        exact Or.inl
          (Nat.finiteDeletedIntervalContainingRunStart_eq_left_of_empty
            K C n hnone)
    | Or.inr hbefore =>
        let d := (Nat.finiteDeletedBefore C n).max' hbefore
        have hdC := ((Nat.mem_finiteDeletedBefore_iff C n d).mp
          (Finset.max'_mem (Nat.finiteDeletedBefore C n) hbefore)).1
        have hsEq :=
          Nat.finiteDeletedIntervalContainingRunStart_eq_max_add_one
            K C n hbefore
        exact Or.inr
          (Eq.subst (motive := fun z : ℕ => z ∈ C)
            (Eq.trans
              (congrArg (fun z : ℕ => z - 1) hsEq)
              (Nat.add_sub_cancel_right d 1)).symm hdC)
  exact
    (Nat.mem_finiteDeletedIntervalRunStarts_iff K M C s).mpr
      (And.intro (Finset.mem_Icc.mpr (And.intro hsLower hsUpper))
        (And.intro hsNot hsCase))

end

end LFunctions
end Boundary

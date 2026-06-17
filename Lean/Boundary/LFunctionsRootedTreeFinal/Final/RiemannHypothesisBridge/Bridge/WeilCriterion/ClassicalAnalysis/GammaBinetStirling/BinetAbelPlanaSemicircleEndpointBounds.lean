import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleEndpointCore

/-!
# Endpoint-defect bounds for right-semicircle staircase approximation

This file owns the endpoint-defect definition, endpoint-defect bounds, graph
probe grid, and finite algebra helpers used by the horizontal sample layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

theorem Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_suffix_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    (∑ t in Finset.range (m - (m + 1) / 2),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m
        (((m + 1) / 2) + 1 + t)|) ≤ ρ := by
  let j : ℕ := (m + 1) / 2
  let start : ℕ := j + 1
  let r : ℕ → ℝ := fun k =>
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  have hjm : j ≤ m := by
    show (m + 1) / 2 ≤ m
    exact nat_staircase_midpoint_le m
  have hend_index : start + (m - j) = m + 1 := by
    show j + 1 + (m - j) = m + 1
    exact nat_succ_add_sub_eq_succ hjm
  have hterm :
      ∀ t ∈ Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)| =
          |r ((start + t) + 1) - r (start + t)| := by
    intro t _ht
    have hj_lt_index : j < start + t := by
      show j < j + 1 + t
      exact nat_lt_succ_add j t
    have hdrop :
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)| =
          r (start + t) - r ((start + t) + 1) := by
      show
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)| =
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (start + t)) -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m ((start + t) + 1))
      exact
          Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_eq_graph_drop_of_midpoint_lt
            hρ (m := m) (k := start + t) hj_lt_index
    have hdrop_abs :
        |r ((start + t) + 1) - r (start + t)| =
          r (start + t) - r ((start + t) + 1) := by
      have hmid_lt_index : j < start + t := hj_lt_index
      have hindex_pos : 0 < start + t :=
        lt_of_le_of_lt (Nat.zero_le j) hmid_lt_index
      have hmid_le_pred : j ≤ start + t - 1 :=
        Nat.le_pred_of_lt hmid_lt_index
      have hpred_succ : (start + t - 1) + 1 = start + t :=
        Nat.sub_add_cancel hindex_pos
      have hy_nonneg :
          0 ≤ Complex.rightSemicircleStaircaseY ρ m (start + t) := by
        exact
          Eq.subst
            (motive := fun n : ℕ =>
              0 ≤ Complex.rightSemicircleStaircaseY ρ m n)
            hpred_succ
            (Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
              hρ hmid_le_pred)
      have hy_le :
          Complex.rightSemicircleStaircaseY ρ m (start + t) ≤
            Complex.rightSemicircleStaircaseY ρ m ((start + t) + 1) :=
        Complex.rightSemicircleStaircaseY_le_succ hρ m (start + t)
      have hanti :
          r ((start + t) + 1) ≤ r (start + t) :=
        Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
      exact
        Eq.trans
          (abs_of_nonpos (sub_nonpos.mpr hanti))
          (neg_sub (r ((start + t) + 1)) (r (start + t)))
    exact Eq.trans hdrop (Eq.symm hdrop_abs)
  have hsum_eq :
      (∑ t in Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|) =
      ∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)| := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hterm t ht
  have hanti :
      ∀ t : ℕ, t < m - j → r ((start + t) + 1) ≤ r (start + t) := by
    intro t _ht
    have hj_lt_index : j < start + t := by
      show j < j + 1 + t
      exact nat_lt_succ_add j t
    have hindex_pos : 0 < start + t :=
      lt_of_le_of_lt (Nat.zero_le j) hj_lt_index
    have hmid_le_pred : j ≤ start + t - 1 :=
      Nat.le_pred_of_lt hj_lt_index
    have hpred_succ : (start + t - 1) + 1 = start + t :=
      Nat.sub_add_cancel hindex_pos
    have hy_nonneg :
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (start + t) := by
      exact
        Eq.subst
          (motive := fun n : ℕ =>
            0 ≤ Complex.rightSemicircleStaircaseY ρ m n)
          hpred_succ
          (Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
            hρ hmid_le_pred)
    have hy_le :
        Complex.rightSemicircleStaircaseY ρ m (start + t) ≤
          Complex.rightSemicircleStaircaseY ρ m ((start + t) + 1) :=
      Complex.rightSemicircleStaircaseY_le_succ hρ m (start + t)
    exact Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
  have htel :
      (∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)|) =
        r start - r (start + (m - j)) :=
    sum_abs_adjacent_of_antitone_suffix r start (m - j) hanti
  have hstart_range : start ∈ Finset.range (m + 2) := by
    show j + 1 ∈ Finset.range (m + 2)
    exact Finset.mem_range.mpr (Nat.succ_lt_succ (Nat.lt_succ_iff.mpr hjm))
  have hystart :
      Complex.rightSemicircleStaircaseY ρ m start ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m start hstart_range
  have hrstart_le : r start ≤ ρ := by
    show
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m start) ≤ ρ
    exact Complex.rightSemicircleGraphRe_le_radius hρ hystart
  have hrend : r (start + (m - j)) = 0 := by
    show
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (start + (m - j))) = 0
    exact
      Eq.trans
        (congrArg
          (fun n : ℕ =>
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m n))
          hend_index)
        (Eq.trans
          (congrArg
            (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
            (Complex.rightSemicircleStaircaseY_last ρ m))
          (Complex.rightSemicircleGraphRe_top (ρ := ρ)))
  calc
    (∑ t in Finset.range (m - (m + 1) / 2),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m
        (((m + 1) / 2) + 1 + t)|)
        =
      (∑ t in Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|) := by
        show
          (∑ t in Finset.range (m - j),
            |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|)
            =
          (∑ t in Finset.range (m - j),
            |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|)
        exact rfl
    _ =
      ∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)| := hsum_eq
    _ = r start - r (start + (m - j)) := htel
    _ ≤ ρ := by
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ ρ)
          (Eq.symm (Eq.trans (congrArg (fun x : ℝ => r start - x) hrend) (sub_zero (r start))))
          hrstart_le

/-- Graph probe on the uniform staircase height grid. -/
noncomputable def Complex.rightSemicircleGraphProbeGrid
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  f (Complex.rightSemicircleGraphPoint c ρ
      (Complex.rightSemicircleStaircaseY ρ m k))

/-- The previous safe endpoint error is zero at the bottom and otherwise is
the preceding safe endpoint defect. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_sub_graphRe_eq_zero_or_endpointDefect
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) =
      if k = 0 then
        0
      else
        Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (k - 1) := by
  match em (k = 0) with
  | Or.inl hk =>
    subst k
    have hprev :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 :=
      Complex.rightSemicircleStaircasePrevSafeRe_zero_owner ρ m
    have hgraph :
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m 0) = 0 :=
      Eq.trans
        (congrArg
          (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
          (Complex.rightSemicircleStaircaseY_zero ρ m))
        (Complex.rightSemicircleGraphRe_bottom (ρ := ρ))
    have hleft :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m 0) = 0 :=
      Eq.trans
        (congrArg₂ HSub.hSub hprev hgraph)
        (sub_zero 0)
    exact Eq.trans hleft (Eq.symm (if_pos rfl))
  | Or.inr hk =>
    have hsucc : (k - 1) + 1 = k :=
      Complex.staircase_pred_succ_of_ne_zero hk
    have hprev :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
          Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
      Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero
        ρ m k hk
    have hleft :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k) =
          Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)) :=
      Eq.trans
        (congrArg
          (fun x : ℝ =>
            x -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k))
          hprev)
        (congrArg
          (fun n : ℕ =>
            Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m n))
          (Eq.symm hsucc))
    have hdef :
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)) =
          Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (k - 1) :=
      rfl
    exact Eq.trans (Eq.trans hleft hdef) (Eq.symm (if_neg hk))

/-- The finite sum of shifted predecessor errors drops the zero term and
reindexes by one. -/
theorem finset_sum_succ_shift_of_zero_or_prev
    (m : ℕ)
    (g : ℕ → ℂ)
    (e : ℕ → ℂ) :
    (∑ k in Finset.range (m + 1),
        g k * (if k = 0 then 0 else e (k - 1))) =
      ∑ k in Finset.range m, g (k + 1) * e k := by
  let F : ℕ → ℂ := fun k => g k * (if k = 0 then 0 else e (k - 1))
  have hsplit :
      (∑ k in Finset.range (m + 1), F k) =
        F 0 + ∑ k in Finset.range m, F (k + 1) :=
    Eq.trans
      (Finset.sum_range_succ' F m)
      (add_comm (∑ k in Finset.range m, F (k + 1)) (F 0))
  have hzero : F 0 = 0 := by
    show g 0 * (if 0 = 0 then 0 else e (0 - 1)) = 0
    exact
      Eq.trans
        (congrArg (fun z : ℂ => g 0 * z) (if_pos rfl))
        (mul_zero (g 0))
  have hshift :
      (∑ k in Finset.range m, F (k + 1)) =
        ∑ k in Finset.range m, g (k + 1) * e k := by
    exact
      Finset.sum_congr rfl
        (fun k _hk => by
          show
            g (k + 1) *
                (if k + 1 = 0 then 0 else e ((k + 1) - 1)) =
              g (k + 1) * e k
          have hnot : k + 1 ≠ 0 := Nat.succ_ne_zero k
          exact
            Eq.trans
              (congrArg
                (fun z : ℂ => g (k + 1) * z)
                (if_neg hnot))
              (congrArg
                (fun n : ℕ => g (k + 1) * e n)
                (Nat.succ_sub_one k)))
  calc
    (∑ k in Finset.range (m + 1),
        g k * (if k = 0 then 0 else e (k - 1)))
        = ∑ k in Finset.range (m + 1), F k := rfl
    _ = F 0 + ∑ k in Finset.range m, F (k + 1) := hsplit
    _ = 0 + ∑ k in Finset.range m, F (k + 1) :=
        congrArg (fun z : ℂ => z + ∑ k in Finset.range m, F (k + 1)) hzero
    _ = ∑ k in Finset.range m, F (k + 1) :=
        zero_add (∑ k in Finset.range m, F (k + 1))
    _ = ∑ k in Finset.range m, g (k + 1) * e k := hshift

/-- Endpoint-defect summation by parts with the top connector tail still
present as a named term. -/
theorem endpoint_defect_summation_by_parts_with_tail
    (m : ℕ)
    (g e p : ℕ → ℂ)
    (tail : ℂ)
    (hshift :
      (∑ k in Finset.range (m + 1), g k * p k) =
        ∑ k in Finset.range m, g (k + 1) * e k)
    (htail : tail = -(g (m + 1) * e m)) :
    (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) + tail =
      ∑ k in Finset.range (m + 1), (g k - g (k + 1)) * e k := by
  have hsplit :
      (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) =
        (∑ k in Finset.range (m + 1), g k * e k) -
          ∑ k in Finset.range (m + 1), g k * p k :=
    Finset.sum_sub_distrib
      (s := Finset.range (m + 1))
      (f := fun k => g k * e k)
      (g := fun k => g k * p k)
  have htail_transport :
      (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) + tail =
        (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) +
          -(g (m + 1) * e m) :=
    congrArg
      (fun z : ℂ =>
        (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) + z)
      htail
  have hadd_to_sub :
      (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) +
          -(g (m + 1) * e m) =
        (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) -
          g (m + 1) * e m :=
    Eq.symm
      (sub_eq_add_neg
        (∑ k in Finset.range (m + 1), (g k * e k - g k * p k))
        (g (m + 1) * e m))
  have hsplit_transport :
      (∑ k in Finset.range (m + 1), (g k * e k - g k * p k)) -
          g (m + 1) * e m =
        ((∑ k in Finset.range (m + 1), g k * e k) -
          ∑ k in Finset.range (m + 1), g k * p k) -
          g (m + 1) * e m :=
    congrArg
      (fun z : ℂ => z - g (m + 1) * e m)
      hsplit
  have hshift_transport :
      ((∑ k in Finset.range (m + 1), g k * e k) -
          ∑ k in Finset.range (m + 1), g k * p k) -
          g (m + 1) * e m =
        ((∑ k in Finset.range (m + 1), g k * e k) -
          ∑ k in Finset.range m, g (k + 1) * e k) -
          g (m + 1) * e m :=
    congrArg
      (fun z : ℂ =>
        ((∑ k in Finset.range (m + 1), g k * e k) - z) -
          g (m + 1) * e m)
      hshift
  exact
    Eq.trans htail_transport
      (Eq.trans hadd_to_sub
        (Eq.trans hsplit_transport
          (Eq.trans hshift_transport
            (endpoint_defect_summation_by_parts_algebra m g e))))

/-- Splitting a range at an index `j ≤ m` separates the prefix, crossing
index, and suffix. -/
theorem finset_sum_range_split_at_index
    {α : Type*}
    [AddCommMonoid α]
    (e : ℕ → α)
    (m j : ℕ)
    (hjm : j ≤ m) :
    (∑ k in Finset.range (m + 1), e k) =
      (∑ k in Finset.range j, e k) + e j +
        ∑ t in Finset.range (m - j), e (j + 1 + t) := by
  have hlen : j + (1 + (m - j)) = m + 1 := by
    calc
      j + (1 + (m - j)) = j + 1 + (m - j) :=
        (Nat.add_assoc j 1 (m - j)).symm
      _ = m + 1 := nat_succ_add_sub_eq_succ hjm
  have hfirst :
      (∑ k in Finset.range (m + 1), e k) =
        ∑ k in Finset.range (j + (1 + (m - j))), e k :=
    congrArg (fun n : ℕ => ∑ k in Finset.range n, e k) (Eq.symm hlen)
  have hsplit :
      (∑ k in Finset.range (j + (1 + (m - j))), e k) =
        (∑ k in Finset.range j, e k) +
          ∑ t in Finset.range (1 + (m - j)), e (j + t) :=
    Finset.sum_range_add e j (1 + (m - j))
  have hsucc :
      (∑ t in Finset.range (1 + (m - j)), e (j + t)) =
        e j + ∑ t in Finset.range (m - j), e (j + 1 + t) := by
    have hrange :
        (∑ t in Finset.range (1 + (m - j)), e (j + t)) =
          (∑ t in Finset.range ((m - j) + 1), e (j + t)) :=
      congrArg (fun n : ℕ => ∑ t in Finset.range n, e (j + t))
        (nat_one_add_eq_add_one (m - j))
    have hsplit_succ :
        (∑ t in Finset.range ((m - j) + 1), e (j + t)) =
          e (j + 0) + ∑ t in Finset.range (m - j), e (j + (t + 1)) :=
      Eq.trans
        (Finset.sum_range_succ' (fun t => e (j + t)) (m - j))
        (add_comm
          (∑ t in Finset.range (m - j), e (j + (t + 1)))
          (e (j + 0)))
    have hhead : e (j + 0) = e j :=
      congrArg e (Nat.add_zero j)
    have htail :
        (∑ t in Finset.range (m - j), e (j + (t + 1))) =
          ∑ t in Finset.range (m - j), e (j + 1 + t) :=
      Finset.sum_congr rfl
        (fun t _ht =>
          congrArg e (nat_midpoint_suffix_index_assoc j t))
    exact
      Eq.trans hrange
        (Eq.trans hsplit_succ
          (Eq.trans
            (congrArg₂ HAdd.hAdd hhead htail)
            rfl))
  calc
    (∑ k in Finset.range (m + 1), e k)
        = ∑ k in Finset.range (j + (1 + (m - j))), e k := hfirst
    _ =
        (∑ k in Finset.range j, e k) +
          ∑ t in Finset.range (1 + (m - j)), e (j + t) := hsplit
    _ =
        (∑ k in Finset.range j, e k) +
          (e j + ∑ t in Finset.range (m - j), e (j + 1 + t)) :=
      congrArg
        (fun z : α => (∑ k in Finset.range j, e k) + z)
        hsucc
    _ =
        (∑ k in Finset.range j, e k) + e j +
          ∑ t in Finset.range (m - j), e (j + 1 + t) :=
      (add_assoc
        (∑ k in Finset.range j, e k)
        (e j)
        (∑ t in Finset.range (m - j), e (j + 1 + t))).symm

end
end LFunctions
end Boundary

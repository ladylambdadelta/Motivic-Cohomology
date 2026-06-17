import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleAngle

/-!
# Endpoint-defect core for right-semicircle staircase approximation

This file owns the endpoint-defect definition and pointwise endpoint-defect
identities for the right-semicircle staircase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

theorem Complex.ofReal_if_nat_zero
    (e : ℕ → ℝ)
    (k : ℕ) :
    (((if k = 0 then 0 else e (k - 1) : ℝ) : ℂ)) =
      if k = 0 then 0 else ((e (k - 1) : ℝ) : ℂ) := by
  match em (k = 0) with
  | Or.inl hk =>
      exact
        Eq.trans
          (congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (if_pos hk))
          (Eq.symm (if_pos hk))
  | Or.inr hk =>
      exact
        Eq.trans
          (congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (if_neg hk))
          (Eq.symm (if_neg hk))


noncomputable def Complex.rightSemicircleStaircaseSafeEndpointDefect
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  Complex.rightSemicircleStaircaseSafeRe ρ m k -
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m (k + 1))

/-- Cells strictly below the midpoint have no endpoint defect: the safe
coordinate is already the right endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeEndpointDefect_eq_zero_of_lt_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k < (m + 1) / 2) :
    Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k = 0 := by
  have hk_succ_le_mid : k + 1 ≤ (m + 1) / 2 :=
    Nat.succ_le_of_lt hk
  have hy_succ_nonpos :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0 :=
    Complex.rightSemicircleStaircaseY_nonpos_of_le_midpoint
      hρ hk_succ_le_mid
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos
      hρ m k hy_succ_nonpos
  show
    Complex.rightSemicircleStaircaseSafeRe ρ m k -
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) = 0
  exact
    Eq.trans
      (congrArg
        (fun x : ℝ =>
          x -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)))
        hsafe)
      (sub_self
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))))

/-- Every individual endpoint defect is bounded by the radius. -/
theorem Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| ≤ ρ := by
  have hsafe_mem :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ m k hk
  have hk_succ_range : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy_succ_mem :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m (k + 1) hk_succ_range
  have hgraph_mem :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleGraphRe_mem_radius_uIcc_of_height_mem hρ hy_succ_mem
  show
    |Complex.rightSemicircleStaircaseSafeRe ρ m k -
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1))| ≤ ρ
  exact abs_sub_le_radius_of_mem_radius_uIcc hρ hsafe_mem hgraph_mem

/-- If a grid index lies strictly above the midpoint, its predecessor is at or
above the midpoint. -/
theorem Complex.midpoint_le_pred_of_midpoint_lt
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    (m + 1) / 2 ≤ k - 1 :=
  Nat.le_pred_of_lt hk

/-- A grid index strictly above the midpoint is nonzero. -/
theorem Complex.ne_zero_of_midpoint_lt
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    k ≠ 0 :=
  Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le ((m + 1) / 2)) hk)

/-- Strictly above the midpoint, the lower endpoint height is nonnegative. -/
theorem Complex.rightSemicircleStaircaseY_nonneg_of_midpoint_lt
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    0 ≤ Complex.rightSemicircleStaircaseY ρ m k := by
  have hmid_le_pred : (m + 1) / 2 ≤ k - 1 :=
    Complex.midpoint_le_pred_of_midpoint_lt hk
  have hpred_succ : (k - 1) + 1 = k :=
    Complex.staircase_pred_succ_of_ne_zero
      (Complex.ne_zero_of_midpoint_lt hk)
  exact
    Eq.subst
      (motive := fun n : ℕ =>
        0 ≤ Complex.rightSemicircleStaircaseY ρ m n)
      hpred_succ
      (Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
        hρ hmid_le_pred)

/-- Strictly above the crossing cell, the endpoint defect is the drop of the
right semicircle graph between adjacent grid points. -/
theorem Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_eq_graph_drop_of_midpoint_lt
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hy_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseY_nonneg_of_midpoint_lt hρ hk
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
      hρ m k hy_nonneg
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  have hgraph_drop :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
  have hdrop_nonneg :
      0 ≤
        Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    sub_nonneg.mpr hgraph_drop
  show
    |Complex.rightSemicircleStaircaseSafeRe ρ m k -
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1))| =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))
  exact
    Eq.trans
      (congrArg
        (fun x : ℝ =>
          |x -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1))|)
        hsafe)
      (abs_of_nonneg hdrop_nonneg)

end
end LFunctions
end Boundary

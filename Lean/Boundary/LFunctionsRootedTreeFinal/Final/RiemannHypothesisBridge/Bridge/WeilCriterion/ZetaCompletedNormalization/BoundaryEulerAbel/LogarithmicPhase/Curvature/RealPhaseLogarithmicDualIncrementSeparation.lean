import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseFiniteDeletedIntervalRunCoverage

/-!
# Increment separation on dual surviving cells

The mean-value theorem identifies the shifted phase increment across one unit
cell with the shifted derivative at an interior point.  Since surviving cells
are disjoint from every derivative-value collar, the discrete increment is
separated from all represented principal levels by the same parameter `eta`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualShiftedIncrement
    (t : ℝ) (h n : ℕ) : ℝ :=
  Complex.logarithmicPhaseDualShiftedDifference
      t (h : ℝ) ((n + 1 : ℕ) : ℝ) -
    Complex.logarithmicPhaseDualShiftedDifference
      t (h : ℝ) (n : ℝ)

theorem Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseDualShiftedDifference t h)
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x) x := by
  have hclosed :=
    Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceClosed
      t h hx hh
  have heq :
      Complex.logarithmicPhaseDualShiftedDifference t h =
        Complex.logarithmicPhaseDualShiftedDifferenceClosed t h := by
    funext y
    exact Complex.logarithmicPhaseDualShiftedDifference_eq_closed t h y
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      HasDerivAt f
        (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x) x)
    heq.symm hclosed

theorem Complex.logarithmicPhaseDualShiftedDifference_continuousOn_cell
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} {n : ℕ}
    (hh : 0 < h) (hn : 0 < n) :
    ContinuousOn
      (Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ))
      (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
  intro x hx
  have hxPos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) hx.1
  exact
    (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
      t ht (le_of_lt (Nat.cast_pos.mpr hh)) hxPos).continuousAt.continuousWithinAt

theorem Complex.logarithmicPhaseDualShiftedDifference_differentiableOn_cellInterior
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℕ} {n : ℕ}
    (hh : 0 < h) (hn : 0 < n) :
    DifferentiableOn ℝ
      (Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ))
      (Set.Ioo (n : ℝ) ((n + 1 : ℕ) : ℝ)) := by
  intro x hx
  have hxPos := lt_of_lt_of_le (Nat.cast_pos.mpr hn) (le_of_lt hx.1)
  exact
    (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
      t ht (le_of_lt (Nat.cast_pos.mpr hh)) hxPos).differentiableAt.differentiableWithinAt

theorem Complex.exists_dualShiftDerivative_eq_increment
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h n : ℕ}
    (hh : 0 < h) (hn : 0 < n) :
    ∃ c ∈ Set.Ioo (n : ℝ) ((n + 1 : ℕ) : ℝ),
      Complex.logarithmicPhaseDualShiftedDifferenceDerivative t (h : ℝ) c =
        Complex.logarithmicPhaseDualShiftedIncrement t h n := by
  have hleftRight : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact Nat.cast_lt.mpr (Nat.lt_succ_self n)
  have hcontinuous :=
    Complex.logarithmicPhaseDualShiftedDifference_continuousOn_cell
      t ht hh hn
  have hdifferentiable :=
    Complex.logarithmicPhaseDualShiftedDifference_differentiableOn_cellInterior
      t ht hh hn
  have hmean := exists_deriv_eq_slope
    (Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ))
    hleftRight hcontinuous hdifferentiable
  rcases hmean with ⟨c, hc, hderiv⟩
  have hderivEq :=
    Complex.deriv_logarithmicPhaseDualShiftDerivative_eq_curvature
  have hactual :
      deriv (Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ)) c =
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative t (h : ℝ) c := by
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
        t ht (le_of_lt (Nat.cast_pos.mpr hh))
        (lt_of_lt_of_le (Nat.cast_pos.mpr hn) (le_of_lt hc.1))).deriv
  have hdenom : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := Nat.cast_add n 1
    exact Eq.trans (congrArg (fun z : ℝ => z - (n : ℝ)) hcast)
      (add_sub_cancel_left (n : ℝ) 1)
  have hslope :
      (Complex.logarithmicPhaseDualShiftedDifference
          t (h : ℝ) ((n + 1 : ℕ) : ℝ) -
        Complex.logarithmicPhaseDualShiftedDifference
          t (h : ℝ) (n : ℝ)) /
          (((n + 1 : ℕ) : ℝ) - (n : ℝ)) =
        Complex.logarithmicPhaseDualShiftedIncrement t h n := by
    unfold Complex.logarithmicPhaseDualShiftedIncrement
    exact Eq.trans
      (congrArg
        (fun denominator : ℝ =>
          (Complex.logarithmicPhaseDualShiftedDifference
              t (h : ℝ) ((n + 1 : ℕ) : ℝ) -
            Complex.logarithmicPhaseDualShiftedDifference
              t (h : ℝ) (n : ℝ)) / denominator) hdenom)
      (div_one _)
  exact Exists.intro c
    (And.intro hc
      (Eq.trans hactual.symm (Eq.trans hderiv hslope)))

theorem Complex.logarithmicPhaseDualSeparated_increment_gap
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ}
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M) :
    ∀ q ∈ Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ),
      eta <
        | |Complex.logarithmicPhaseDualShiftedIncrement t h n| -
            Complex.logarithmicPhaseDualPrincipalLevel q | := by
  have hnBlock :=
    (Complex.mem_logarithmicPhaseDualDiscreteSeparatedModes_iff
      t h eta K M n).mp hn
  have hnPos : 0 < n := lt_of_lt_of_le hK (Finset.mem_Icc.mp hnBlock.1).1
  rcases Complex.exists_dualShiftDerivative_eq_increment t ht hh hnPos with
    ⟨c, hc, hderiv⟩
  have hcell :=
    Complex.logarithmicPhaseDualDiscreteSeparated_cellwise_gap
      t hh hK hn c (And.intro (le_of_lt hc.1) (le_of_lt hc.2))
  intro q hq
  exact Eq.subst
    (motive := fun value : ℝ =>
      eta < | |value| - Complex.logarithmicPhaseDualPrincipalLevel q |)
    hderiv (hcell q hq)

theorem Complex.logarithmicPhaseDualSeparated_increment_abs_ge_eta
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M n : ℕ} (hh : 0 < h) (hK : 0 < K)
    {eta : ℝ}
    (hn : n ∈
      Complex.logarithmicPhaseDualDiscreteSeparatedModes t h eta K M)
    (hzero : 0 ∈ Complex.logarithmicPhaseDualCrossingLevels
      t (h : ℝ) eta (K : ℝ)) :
    eta < |Complex.logarithmicPhaseDualShiftedIncrement t h n| := by
  have hgap :=
    Complex.logarithmicPhaseDualSeparated_increment_gap
      t ht hh hK hn 0 hzero
  unfold Complex.logarithmicPhaseDualPrincipalLevel at hgap
  have hlevelZero : 2 * Real.pi * ((0 : ℕ) : ℝ) = 0 := by exact rfl
  exact Eq.subst (motive := fun z : ℝ => eta < z)
    (Eq.trans
      (congrArg abs
        (Eq.trans
          (congrArg
            (fun level : ℝ =>
              |Complex.logarithmicPhaseDualShiftedIncrement t h n| - level)
            hlevelZero)
          (sub_zero _)))
      (abs_abs _)).symm hgap

end

end LFunctions
end Boundary

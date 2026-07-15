import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualIncrementMonotonicity

/-!
# Continuous start-variable increment of the dual shifted phase

The discrete increment extends naturally to

`J(x) = D_h(x+1) - D_h(x)`.

Its derivative is `g(x+1)-g(x)`, where `g=D_h'`.  Since `g` is strictly
increasing on the positive half-line, `J` is strictly increasing there.  The
continuous increment is the connected-image object used to prove principal
branch constancy on a maximal collar-free run.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualContinuousIncrement
    (t h x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualShiftedDifference t h (x + 1) -
    Complex.logarithmicPhaseDualShiftedDifference t h x

def Complex.logarithmicPhaseDualContinuousIncrementDerivative
    (t h x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h (x + 1) -
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x

theorem Complex.logarithmicPhaseDualContinuousIncrement_nat_eq
    (t : ℝ) (h n : ℕ) :
    Complex.logarithmicPhaseDualContinuousIncrement t (h : ℝ) (n : ℝ) =
      Complex.logarithmicPhaseDualShiftedIncrement t h n := by
  unfold Complex.logarithmicPhaseDualContinuousIncrement
  unfold Complex.logarithmicPhaseDualShiftedIncrement
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) :=
    (Nat.cast_add n 1).symm
  exact congrArg
    (fun z : ℝ =>
      Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ) z -
        Complex.logarithmicPhaseDualShiftedDifference t (h : ℝ) (n : ℝ))
    hcast

theorem Complex.hasDerivAt_logarithmicPhaseDualContinuousIncrement
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseDualContinuousIncrement t h)
      (Complex.logarithmicPhaseDualContinuousIncrementDerivative t h x) x := by
  have hxOne : 0 < x + 1 := add_pos_of_pos_of_nonneg hx zero_le_one
  have hbaseRight :=
    Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference t ht hh hxOne
  have hinner : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have hright := hbaseRight.comp x hinner
  have hleft :=
    Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference t ht hh hx
  have hdifference := hright.sub hleft
  unfold Complex.logarithmicPhaseDualContinuousIncrement
  unfold Complex.logarithmicPhaseDualContinuousIncrementDerivative
  have honeMul :
      Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h (x + 1) * 1 =
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h (x + 1) :=
    mul_one _
  exact Eq.subst
    (motive := fun z : ℝ =>
      HasDerivAt
        (fun y : ℝ =>
          Complex.logarithmicPhaseDualShiftedDifference t h (y + 1) -
            Complex.logarithmicPhaseDualShiftedDifference t h y) z x)
    (congrArg
      (fun z : ℝ =>
        z - Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x)
      honeMul).symm hdifference

theorem Complex.logarithmicPhaseDualContinuousIncrementDerivative_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    0 < Complex.logarithmicPhaseDualContinuousIncrementDerivative t h x := by
  unfold Complex.logarithmicPhaseDualContinuousIncrementDerivative
  have hxOne : 0 < x + 1 := add_pos_of_pos_of_nonneg hx zero_le_one
  have hstrict :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_strictMonoOn
      t ht hh hx hxOne (lt_add_of_pos_right x zero_lt_one)
  exact sub_pos.mpr hstrict

theorem Complex.logarithmicPhaseDualContinuousIncrement_strictMonoOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 < h) :
    StrictMonoOn
      (Complex.logarithmicPhaseDualContinuousIncrement t h)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hcontinuous :
      ContinuousOn
        (Complex.logarithmicPhaseDualContinuousIncrement t h)
        (Set.Icc x y) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx hz.1
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualContinuousIncrement
        t ht (le_of_lt hh) hzPos).continuousAt.continuousWithinAt
  have hdifferentiable :
      DifferentiableOn ℝ
        (Complex.logarithmicPhaseDualContinuousIncrement t h)
        (Set.Ioo x y) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx (le_of_lt hz.1)
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualContinuousIncrement
        t ht (le_of_lt hh) hzPos).differentiableAt.differentiableWithinAt
  have hpositive :
      ∀ z ∈ Set.Ioo x y,
        0 < deriv (Complex.logarithmicPhaseDualContinuousIncrement t h) z := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx (le_of_lt hz.1)
    have hderiv :=
      (Complex.hasDerivAt_logarithmicPhaseDualContinuousIncrement
        t ht (le_of_lt hh) hzPos).deriv
    exact Eq.subst (motive := fun value : ℝ => 0 < value)
      hderiv.symm
      (Complex.logarithmicPhaseDualContinuousIncrementDerivative_pos
        t ht hh hzPos)
  have hgrowth :=
    (convex_Icc x y).mul_sub_lt_image_sub_of_lt_deriv
      hcontinuous hdifferentiable hpositive x (Set.left_mem_Icc.mpr (le_of_lt hxy))
      y (Set.right_mem_Icc.mpr (le_of_lt hxy)) hxy
  have hzero : (0 : ℝ) * (y - x) = 0 := zero_mul _
  have hdifference :
      0 <
        Complex.logarithmicPhaseDualContinuousIncrement t h y -
          Complex.logarithmicPhaseDualContinuousIncrement t h x :=
    Eq.subst (motive := fun z : ℝ => z < _)
      hzero.symm hgrowth
  exact sub_pos.mp hdifference

theorem Complex.logarithmicPhaseDualContinuousIncrement_continuousOn_positive
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 ≤ h) :
    ContinuousOn
      (Complex.logarithmicPhaseDualContinuousIncrement t h)
      (Set.Ioi 0) := by
  intro x hx
  exact
    (Complex.hasDerivAt_logarithmicPhaseDualContinuousIncrement
      t ht hh hx).continuousAt.continuousWithinAt

theorem Complex.logarithmicPhaseDualContinuousIncrement_neg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    Complex.logarithmicPhaseDualContinuousIncrement t h x < 0 := by
  have hphaseDerivativeNeg :
      ∀ z ∈ Set.Icc x (x + 1),
        deriv (Complex.logarithmicPhaseDualShiftedDifference t h) z < 0 := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx hz.1
    have hderiv :=
      (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
        t ht (le_of_lt hh) hzPos).deriv
    exact Eq.subst (motive := fun value : ℝ => value < 0)
      hderiv.symm
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
        t ht hh hzPos)
  have hcontinuous :
      ContinuousOn
        (Complex.logarithmicPhaseDualShiftedDifference t h)
        (Set.Icc x (x + 1)) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx hz.1
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
        t ht (le_of_lt hh) hzPos).continuousAt.continuousWithinAt
  have hdifferentiable :
      DifferentiableOn ℝ
        (Complex.logarithmicPhaseDualShiftedDifference t h)
        (Set.Ioo x (x + 1)) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx (le_of_lt hz.1)
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifference
        t ht (le_of_lt hh) hzPos).differentiableAt.differentiableWithinAt
  have hdecrease :=
    (convex_Icc x (x + 1)).image_sub_lt_mul_sub_of_deriv_lt
      hcontinuous hdifferentiable
      (fun z hz => hphaseDerivativeNeg z (interior_subset hz))
      x (Set.left_mem_Icc.mpr (le_add_of_nonneg_right zero_le_one))
      (x + 1) (Set.right_mem_Icc.mpr (le_add_of_nonneg_right zero_le_one))
      (lt_add_of_pos_right x zero_lt_one)
  unfold Complex.logarithmicPhaseDualContinuousIncrement
  exact sub_neg.mpr (lt_of_sub_pos hdecrease)

end

end LFunctions
end Boundary

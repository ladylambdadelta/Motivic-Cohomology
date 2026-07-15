import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualPrincipalBranchConstancy

/-!
# Base-action increment geometry for the dual oscillation

The dual stationary oscillation is sampled from the real phase
`A_t(u)`.  Its finite increment is

`A_t(n+1)-A_t(n)=D_1(n)`.

This is distinct from the second finite difference
`D_h(n+1)-D_h(n)` used for shifted-correlation estimates.  This owner records
that distinction in the API and supplies the exact derivative, monotonicity,
and exponential transports needed by the base dual partial-sum estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualBaseAction
    (t x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualStationaryActionClosed t x

def Complex.logarithmicPhaseDualBaseIncrement
    (t x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualBaseAction t (x + 1) -
    Complex.logarithmicPhaseDualBaseAction t x

def Complex.logarithmicPhaseDualBaseIncrementNat
    (t : ℝ) (n : ℕ) : ℝ :=
  Complex.logarithmicPhaseDualBaseAction t ((n + 1 : ℕ) : ℝ) -
    Complex.logarithmicPhaseDualBaseAction t (n : ℝ)

def Complex.logarithmicPhaseDualBaseIncrementDerivative
    (t x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualShiftedDifferenceDerivative t 1 x

def Complex.logarithmicPhaseDualBaseBranchIndex
    (t : ℝ) (n : ℕ) : ℤ :=
  toIocDiv Real.two_pi_pos (-Real.pi)
    (Complex.logarithmicPhaseDualBaseIncrementNat t n)

def Complex.logarithmicPhaseDualBaseReducedIncrement
    (t : ℝ) (n : ℕ) : ℝ :=
  toIocMod Real.two_pi_pos (-Real.pi)
    (Complex.logarithmicPhaseDualBaseIncrementNat t n)

theorem Complex.logarithmicPhaseDualBaseReducedIncrement_mem_centered
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseReducedIncrement t n ∈
      Set.Ioc (-Real.pi) Real.pi := by
  unfold Complex.logarithmicPhaseDualBaseReducedIncrement
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi)
    (Complex.logarithmicPhaseDualBaseIncrementNat t n)
  have hright : -Real.pi + 2 * Real.pi = Real.pi := by
    exact Eq.trans
      (congrArg (fun z : ℝ => -Real.pi + z) (two_mul Real.pi).symm)
      (neg_add_cancel_left Real.pi Real.pi)
  exact Eq.subst
    (motive := fun z : ℝ =>
      toIocMod Real.two_pi_pos (-Real.pi)
          (Complex.logarithmicPhaseDualBaseIncrementNat t n) ∈
        Set.Ioc (-Real.pi) z)
    hright hmem

theorem Complex.logarithmicPhaseDualBaseReducedIncrement_add_branch_eq_raw
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseReducedIncrement t n +
        Complex.logarithmicPhaseDualBaseBranchIndex t n • (2 * Real.pi) =
      Complex.logarithmicPhaseDualBaseIncrementNat t n := by
  unfold Complex.logarithmicPhaseDualBaseReducedIncrement
  unfold Complex.logarithmicPhaseDualBaseBranchIndex
  exact toIocMod_add_toIocDiv_zsmul Real.two_pi_pos
    (-Real.pi) (Complex.logarithmicPhaseDualBaseIncrementNat t n)

theorem Complex.logarithmicPhaseDualBaseAction_eq_stationaryAction
    (t x : ℝ) :
    Complex.logarithmicPhaseDualBaseAction t x =
      Complex.logarithmicPhaseDualStationaryActionClosed t x := by
  rfl

theorem Complex.logarithmicPhaseDualBaseIncrement_eq_shiftedDifference_one
    (t x : ℝ) :
    Complex.logarithmicPhaseDualBaseIncrement t x =
      Complex.logarithmicPhaseDualShiftedDifference t 1 x := by
  unfold Complex.logarithmicPhaseDualBaseIncrement
  unfold Complex.logarithmicPhaseDualBaseAction
  unfold Complex.logarithmicPhaseDualShiftedDifference
  exact congrArg
    (fun z : ℝ =>
      Complex.logarithmicPhaseDualStationaryActionClosed t z -
        Complex.logarithmicPhaseDualStationaryActionClosed t x)
    (add_comm x 1)

theorem Complex.logarithmicPhaseDualBaseIncrementNat_eq_continuous
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseIncrementNat t n =
      Complex.logarithmicPhaseDualBaseIncrement t (n : ℝ) := by
  unfold Complex.logarithmicPhaseDualBaseIncrementNat
  unfold Complex.logarithmicPhaseDualBaseIncrement
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 :=
    Nat.cast_add n 1
  exact congrArg
    (fun z : ℝ =>
      Complex.logarithmicPhaseDualBaseAction t z -
        Complex.logarithmicPhaseDualBaseAction t (n : ℝ)) hcast

theorem Complex.logarithmicPhaseDualBaseIncrementNat_eq_shiftedDifference_one
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualBaseIncrementNat t n =
      Complex.logarithmicPhaseDualShiftedDifference t 1 (n : ℝ) := by
  exact Eq.trans
    (Complex.logarithmicPhaseDualBaseIncrementNat_eq_continuous t n)
    (Complex.logarithmicPhaseDualBaseIncrement_eq_shiftedDifference_one
      t (n : ℝ))

theorem Complex.logarithmicPhaseDualBaseIncrement_eq_closed
    (t x : ℝ) :
    Complex.logarithmicPhaseDualBaseIncrement t x =
      ‖t‖ * (Real.log (x + 1) - Real.log x) := by
  exact Eq.trans
    (Complex.logarithmicPhaseDualBaseIncrement_eq_shiftedDifference_one t x)
    (Complex.logarithmicPhaseDualShiftedDifference_eq_closed t 1 x)

theorem Complex.hasDerivAt_logarithmicPhaseDualBaseIncrement
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseDualBaseIncrement t)
      (Complex.logarithmicPhaseDualBaseIncrementDerivative t x) x := by
  have hshift :=
    Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceClosed
      t 1 hx zero_le_one
  have heq :
      Complex.logarithmicPhaseDualBaseIncrement t =
        Complex.logarithmicPhaseDualShiftedDifferenceClosed t 1 := by
    funext y
    exact Eq.trans
      (Complex.logarithmicPhaseDualBaseIncrement_eq_shiftedDifference_one t y)
      (Complex.logarithmicPhaseDualShiftedDifference_eq_closed t 1 y)
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      HasDerivAt f
        (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t 1 x) x)
    heq.symm hshift

theorem Complex.deriv_logarithmicPhaseDualBaseIncrement
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (Complex.logarithmicPhaseDualBaseIncrement t) x =
      Complex.logarithmicPhaseDualBaseIncrementDerivative t x := by
  exact (Complex.hasDerivAt_logarithmicPhaseDualBaseIncrement t hx).deriv

theorem Complex.logarithmicPhaseDualBaseIncrementDerivative_eq
    (t x : ℝ) :
    Complex.logarithmicPhaseDualBaseIncrementDerivative t x =
      -‖t‖ / (x * (x + 1)) := by
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  unfold Complex.logarithmicPhaseDualShiftedDifferenceDerivative
  exact congrArg
    (fun z : ℝ => z / (x * (x + 1)))
    (mul_one (-‖t‖))

theorem Complex.logarithmicPhaseDualBaseIncrementDerivative_neg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {x : ℝ} (hx : 0 < x) :
    Complex.logarithmicPhaseDualBaseIncrementDerivative t x < 0 := by
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  exact Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
    t ht zero_lt_one hx

theorem Complex.logarithmicPhaseDualBaseIncrementDerivative_abs_eq
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    |Complex.logarithmicPhaseDualBaseIncrementDerivative t x| =
      ‖t‖ / (x * (x + 1)) := by
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  have hformula :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t zero_le_one hx
  have hone : ‖t‖ * 1 = ‖t‖ := mul_one _
  exact Eq.trans hformula
    (congrArg
      (fun z : ℝ => z / (x * (x + 1))) hone)

theorem Complex.logarithmicPhaseDualBaseIncrementDerivative_abs_antitoneOn
    (t : ℝ) :
    AntitoneOn
      (fun x : ℝ =>
        |Complex.logarithmicPhaseDualBaseIncrementDerivative t x|)
      (Set.Ioi 0) := by
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  exact
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t zero_le_one

theorem Complex.logarithmicPhaseDualBaseIncrementDerivative_strictMonoOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictMonoOn
      (Complex.logarithmicPhaseDualBaseIncrementDerivative t)
      (Set.Ioi 0) := by
  unfold Complex.logarithmicPhaseDualBaseIncrementDerivative
  exact
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_strictMonoOn
      t ht zero_lt_one

theorem Complex.logarithmicPhaseDualBaseIncrement_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {x : ℝ} (hx : 0 < x) :
    0 < Complex.logarithmicPhaseDualBaseIncrement t x := by
  have hclosed :=
    Complex.logarithmicPhaseDualBaseIncrement_eq_closed t x
  have hxOne : x < x + 1 := lt_add_of_pos_right x zero_lt_one
  have hlog := Real.strictMonoOn_log hx
    (add_pos_of_pos_of_nonneg hx zero_le_one) hxOne
  have hlogDifference : 0 < Real.log (x + 1) - Real.log x :=
    sub_pos.mpr hlog
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  exact Eq.subst (motive := fun z : ℝ => 0 < z)
    hclosed.symm (mul_pos hnorm hlogDifference)

theorem Complex.logarithmicPhaseDualBaseIncrementNat_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {n : ℕ} (hn : 0 < n) :
    0 < Complex.logarithmicPhaseDualBaseIncrementNat t n := by
  exact Eq.subst (motive := fun z : ℝ => 0 < z)
    (Complex.logarithmicPhaseDualBaseIncrementNat_eq_continuous t n).symm
    (Complex.logarithmicPhaseDualBaseIncrement_pos
      t ht (Nat.cast_pos.mpr hn))

theorem Complex.logarithmicPhaseDualBaseIncrement_strictAntiOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictAntiOn
      (Complex.logarithmicPhaseDualBaseIncrement t)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hcontinuous : ContinuousOn
      (Complex.logarithmicPhaseDualBaseIncrement t) (Set.Icc x y) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx hz.1
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualBaseIncrement t hzPos).continuousAt.continuousWithinAt
  have hdifferentiable : DifferentiableOn ℝ
      (Complex.logarithmicPhaseDualBaseIncrement t) (Set.Ioo x y) := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx (le_of_lt hz.1)
    exact
      (Complex.hasDerivAt_logarithmicPhaseDualBaseIncrement t hzPos).differentiableAt.differentiableWithinAt
  have hnegative : ∀ z ∈ Set.Ioo x y,
      deriv (Complex.logarithmicPhaseDualBaseIncrement t) z < 0 := by
    intro z hz
    have hzPos := lt_of_lt_of_le hx (le_of_lt hz.1)
    exact Eq.subst (motive := fun value : ℝ => value < 0)
      (Complex.deriv_logarithmicPhaseDualBaseIncrement t hzPos).symm
      (Complex.logarithmicPhaseDualBaseIncrementDerivative_neg t ht hzPos)
  have hdecrease :=
    (convex_Icc x y).image_sub_lt_mul_sub_of_deriv_lt
      hcontinuous hdifferentiable
      (fun z hz => hnegative z (interior_subset hz))
      x (Set.left_mem_Icc.mpr (le_of_lt hxy))
      y (Set.right_mem_Icc.mpr (le_of_lt hxy)) hxy
  have hzero : (0 : ℝ) * (y - x) = 0 := zero_mul _
  have hdifference :
      Complex.logarithmicPhaseDualBaseIncrement t y -
          Complex.logarithmicPhaseDualBaseIncrement t x < 0 :=
    Eq.subst (motive := fun z : ℝ => _ < z)
      hzero.symm hdecrease
  exact sub_neg.mp hdifference

theorem Complex.logarithmicPhaseDualBaseIncrementNat_strictAnti
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hnm : n < m) :
    Complex.logarithmicPhaseDualBaseIncrementNat t m <
      Complex.logarithmicPhaseDualBaseIncrementNat t n := by
  have hreal :=
    Complex.logarithmicPhaseDualBaseIncrement_strictAntiOn t ht
      (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hm) (Nat.cast_lt.mpr hnm)
  exact Eq.subst (motive := fun z : ℝ => z < _)
    (Complex.logarithmicPhaseDualBaseIncrementNat_eq_continuous t m).symm
    (Eq.subst (motive := fun z : ℝ => _ < z)
      (Complex.logarithmicPhaseDualBaseIncrementNat_eq_continuous t n).symm
      hreal)

theorem Complex.logarithmicPhaseDualBaseIncrementNat_antitone
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    Complex.logarithmicPhaseDualBaseIncrementNat t m ≤
      Complex.logarithmicPhaseDualBaseIncrementNat t n := by
  match eq_or_lt_of_le hnm with
  | Or.inl heq =>
      exact le_of_eq (congrArg
        (Complex.logarithmicPhaseDualBaseIncrementNat t) heq.symm)
  | Or.inr hlt =>
      exact le_of_lt
        (Complex.logarithmicPhaseDualBaseIncrementNat_strictAnti
          t ht hn (lt_of_lt_of_le hn hnm) hlt)

theorem Complex.logarithmicPhaseDualOscillationNat_eq_baseAction_exp
    (t : ℝ) (n : ℕ) :
    Complex.logarithmicPhaseDualOscillationNat t n =
      Complex.exp
        (Complex.I *
          (Complex.logarithmicPhaseDualBaseAction t (n : ℝ) : ℂ)) := by
  rfl

theorem Complex.logarithmicPhaseDualBaseAction_integerIncrement_eq
    (t : ℝ) (n : ℕ) :
    Complex.realPhase_integerIncrement
        (Complex.logarithmicPhaseDualBaseAction t) n =
      Complex.logarithmicPhaseDualBaseIncrementNat t n := by
  unfold Complex.realPhase_integerIncrement
  unfold Complex.logarithmicPhaseDualBaseIncrementNat
  exact congrArg
    (fun z : ℝ =>
      Complex.logarithmicPhaseDualBaseAction t z -
        Complex.logarithmicPhaseDualBaseAction t (n : ℝ))
    (Nat.cast_add n 1).symm

end

end LFunctions
end Boundary

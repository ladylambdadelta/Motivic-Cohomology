import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCanonicalReciprocalGap

/-!
# Dual stationary phase for logarithmic Poisson modes

Absolute summation of canonical stationary packets is too expensive on a long
prefix.  The packet centers themselves oscillate as the negative Fourier mode
varies.  This owner constructs that dual phase on the positive mode coordinate
`u = -m` and proves its first three derivatives explicitly.

For `T = ‖t‖` and `u > 0`, the stationary center is

`x(u) = T / (2*pi*u)`.

Evaluating `-T log x + 2*pi*u*x` at `x(u)` gives the stationary action

`A(u) = -T log (T/(2*pi*u)) + T`.

Its derivatives are `T/u`, `-T/u^2`, and `2T/u^3`.  Thus the dual phase has
strictly monotone derivative and a quantitative second-derivative gap on every
finite positive mode interval.  These are the owner facts needed to sum the
stationary packets with cancellation rather than by their absolute values.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Positive mode-coordinate version of the logarithmic stationary center. -/
def Complex.logarithmicPhaseDualStationaryCenter
    (t u : ℝ) : ℝ :=
  ‖t‖ / (2 * Real.pi * u)

/-- The logarithmic twisted phase written in a positive frequency coordinate. -/
def Complex.logarithmicPhasePositiveFrequencyTwistedPhase
    (t u x : ℝ) : ℝ :=
  -‖t‖ * Real.log x + 2 * Real.pi * u * x

/-- Stationary action as an evaluation of the positive-frequency phase. -/
def Complex.logarithmicPhaseDualStationaryAction
    (t u : ℝ) : ℝ :=
  Complex.logarithmicPhasePositiveFrequencyTwistedPhase t u
    (Complex.logarithmicPhaseDualStationaryCenter t u)

/-- Closed form of the stationary action. -/
def Complex.logarithmicPhaseDualStationaryActionClosed
    (t u : ℝ) : ℝ :=
  ‖t‖ * Real.log u +
    (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)

def Complex.logarithmicPhaseDualStationaryActionDerivative
    (t u : ℝ) : ℝ :=
  ‖t‖ / u

def Complex.logarithmicPhaseDualStationaryActionSecondDerivative
    (t u : ℝ) : ℝ :=
  -‖t‖ / u ^ 2

def Complex.logarithmicPhaseDualStationaryActionThirdDerivative
    (t u : ℝ) : ℝ :=
  2 * ‖t‖ / u ^ 3

theorem Real.two_pi_mul_pos
    {u : ℝ} (hu : 0 < u) :
    0 < 2 * Real.pi * u := by
  exact mul_pos Complex.two_mul_pi_pos hu

theorem Complex.logarithmicPhaseDualStationaryCenter_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    0 < Complex.logarithmicPhaseDualStationaryCenter t u := by
  unfold Complex.logarithmicPhaseDualStationaryCenter
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  exact div_pos hnorm (Real.two_pi_mul_pos hu)

theorem Complex.logarithmicPhaseDualStationaryCenter_angular_mul
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    (2 * Real.pi * u) *
        Complex.logarithmicPhaseDualStationaryCenter t u = ‖t‖ := by
  unfold Complex.logarithmicPhaseDualStationaryCenter
  exact mul_div_cancel₀ ‖t‖ (ne_of_gt (Real.two_pi_mul_pos hu))

theorem Real.norm_div_twoPi_mul_eq_norm_div_twoPi_div
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ‖t‖ / (2 * Real.pi * u) = (‖t‖ / (2 * Real.pi)) / u := by
  exact div_mul_eq_div_mul_one_div ‖t‖ (2 * Real.pi) u

theorem Complex.logarithmicPhaseDualStationaryAction_eq_closed
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    Complex.logarithmicPhaseDualStationaryAction t u =
      Complex.logarithmicPhaseDualStationaryActionClosed t u := by
  unfold Complex.logarithmicPhaseDualStationaryAction
  unfold Complex.logarithmicPhasePositiveFrequencyTwistedPhase
  unfold Complex.logarithmicPhaseDualStationaryActionClosed
  have hproduct :=
    Complex.logarithmicPhaseDualStationaryCenter_angular_mul t hu
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have htwoPi : 0 < 2 * Real.pi := Complex.two_mul_pi_pos
  have hbase : 0 < ‖t‖ / (2 * Real.pi) := div_pos hnorm htwoPi
  have hassoc := Real.norm_div_twoPi_mul_eq_norm_div_twoPi_div t hu.ne'
  have hlog :
      Real.log (‖t‖ / (2 * Real.pi * u)) =
        Real.log (‖t‖ / (2 * Real.pi)) - Real.log u :=
    Eq.trans (congrArg Real.log hassoc)
      (Real.log_div hbase.ne' hu.ne')
  unfold Complex.logarithmicPhaseDualStationaryCenter
  exact Eq.trans
    (congrArg
      (fun z : ℝ => -‖t‖ * Real.log (‖t‖ / (2 * Real.pi * u)) + z)
      hproduct)
    (Eq.trans
      (congrArg
        (fun z : ℝ => -‖t‖ * z + ‖t‖)
        hlog)
      (by
        calc
          -‖t‖ *
                (Real.log (‖t‖ / (2 * Real.pi)) - Real.log u) + ‖t‖ =
              (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) +
                ‖t‖ * Real.log u) + ‖t‖ := by
                  exact congrArg (fun z : ℝ => z + ‖t‖)
                    (Eq.trans
                      (mul_sub (-‖t‖)
                        (Real.log (‖t‖ / (2 * Real.pi)))
                        (Real.log u))
                      (congrArg₂ (fun x y : ℝ => x - y) rfl
                        (neg_mul_neg_eq_mul ‖t‖ (Real.log u))))
          _ = ‖t‖ * Real.log u +
                (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖) := by
                  exact Eq.trans
                    (add_assoc
                      (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)))
                      (‖t‖ * Real.log u) ‖t‖)
                    (Eq.trans
                      (congrArg
                        (fun z : ℝ => z + ‖t‖)
                        (add_comm
                          (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)))
                          (‖t‖ * Real.log u)))
                      (add_assoc
                        (‖t‖ * Real.log u)
                        (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)))
                        ‖t‖).symm)))

theorem Real.log_norm_div_twoPi_div
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    Real.log (‖t‖ / (2 * Real.pi * u)) =
      Real.log (‖t‖ / (2 * Real.pi)) - Real.log u := by
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have htwoPi : 0 < 2 * Real.pi := Complex.two_mul_pi_pos
  have hbase : 0 < ‖t‖ / (2 * Real.pi) := div_pos hnorm htwoPi
  have hdivision := Real.log_div hbase.ne' hu.ne'
  have hassoc := Real.norm_div_twoPi_mul_eq_norm_div_twoPi_div t hu.ne'
  exact Eq.trans (congrArg Real.log hassoc) hdivision

/-- Additive normal form of the dual stationary action. -/
theorem Complex.logarithmicPhaseDualStationaryActionClosed_eq_log_mode_add_constant
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    Complex.logarithmicPhaseDualStationaryActionClosed t u =
      ‖t‖ * Real.log u +
        (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖) := by
  rfl

theorem Complex.hasDerivAt_logarithmicPhaseDualStationaryActionClosed
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    HasDerivAt
      (Complex.logarithmicPhaseDualStationaryActionClosed t)
      (Complex.logarithmicPhaseDualStationaryActionDerivative t u) u := by
  have hlog : HasDerivAt Real.log u⁻¹ u := Real.hasDerivAt_log hu.ne'
  have hscaled := hlog.const_mul ‖t‖
  have hconstant :
      HasDerivAt
        (fun _ : ℝ =>
          -‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)
        0 u := hasDerivAt_const u _
  have hadd := hscaled.add hconstant
  unfold Complex.logarithmicPhaseDualStationaryActionClosed
  have hderivative :
      ‖t‖ * u⁻¹ + 0 =
        Complex.logarithmicPhaseDualStationaryActionDerivative t u := by
    unfold Complex.logarithmicPhaseDualStationaryActionDerivative
    exact Eq.trans (add_zero _) (div_eq_mul_inv ‖t‖ u).symm
  exact Eq.subst
    (motive := fun z : ℝ =>
      HasDerivAt
        (fun y : ℝ =>
          ‖t‖ * Real.log y +
            (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)) z u)
    hderivative.symm hadd

theorem Complex.hasDerivAt_logarithmicPhaseDualStationaryActionDerivative
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt
      (Complex.logarithmicPhaseDualStationaryActionDerivative t)
      (Complex.logarithmicPhaseDualStationaryActionSecondDerivative t u) u := by
  unfold Complex.logarithmicPhaseDualStationaryActionDerivative
  unfold Complex.logarithmicPhaseDualStationaryActionSecondDerivative
  have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-u⁻¹ ^ 2) u :=
    hasDerivAt_inv hu
  have hscaled := hinv.const_mul ‖t‖
  have hnormalize :
      ‖t‖ * (-u⁻¹ ^ 2) = -‖t‖ / u ^ 2 := by
    exact Eq.trans
      (mul_neg ‖t‖ (u⁻¹ ^ 2))
      (congrArg Neg.neg
        (Eq.trans
          (div_eq_mul_inv ‖t‖ (u ^ 2)).symm
          (congrArg (fun z : ℝ => ‖t‖ * z) (inv_pow u 2).symm)))
  exact Eq.subst (motive := fun z : ℝ =>
    HasDerivAt (fun y : ℝ => ‖t‖ * y⁻¹) z u)
    hnormalize.symm hscaled

theorem Complex.hasDerivAt_logarithmicPhaseDualStationaryActionSecondDerivative
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt
      (Complex.logarithmicPhaseDualStationaryActionSecondDerivative t)
      (Complex.logarithmicPhaseDualStationaryActionThirdDerivative t u) u := by
  unfold Complex.logarithmicPhaseDualStationaryActionSecondDerivative
  unfold Complex.logarithmicPhaseDualStationaryActionThirdDerivative
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * u) u := by
    exact hasDerivAt_pow 2 u
  have hinv := hpow.inv (pow_ne_zero 2 hu)
  have hscaled := hinv.const_mul (-‖t‖)
  have hnormalize :
      -‖t‖ * (-(2 * u) / (u ^ 2) ^ 2) = 2 * ‖t‖ / u ^ 3 := by
    have hleft :
        -‖t‖ * (-(2 * u) / (u ^ 2) ^ 2) =
          (2 * ‖t‖ * u) / u ^ 4 := by
      have hpowFour : (u ^ 2) ^ 2 = u ^ 4 := by
        exact (pow_mul u 2 2).symm
      exact Eq.trans
        (mul_div_assoc (-‖t‖) (-(2 * u)) ((u ^ 2) ^ 2)).symm
        (Eq.trans
          (congrArg
            (fun z : ℝ => z / ((u ^ 2) ^ 2))
            (Eq.trans
              (mul_neg (-‖t‖) (2 * u))
              (Eq.trans
                (neg_neg (‖t‖ * (2 * u)))
                (Eq.trans
                  (mul_assoc ‖t‖ 2 u)
                  (congrArg (fun z : ℝ => z * u)
                    (mul_comm ‖t‖ 2))))))
          (congrArg (fun z : ℝ => (2 * ‖t‖ * u) / z) hpowFour))
    have hcancel : (2 * ‖t‖ * u) / u ^ 4 = 2 * ‖t‖ / u ^ 3 := by
      have hu3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
      have hu4 : u ^ 4 = u * u ^ 3 := by
        exact pow_succ u 3
      exact (div_eq_iff (pow_ne_zero 4 hu)).mpr
        (Eq.trans
          (congrArg (fun z : ℝ => (2 * ‖t‖ / u ^ 3) * z) hu4)
          (Eq.trans
            (mul_assoc (2 * ‖t‖ / u ^ 3) u (u ^ 3))
            (Eq.trans
              (congrArg (fun z : ℝ => z * u ^ 3)
                (Eq.trans
                  (mul_comm (2 * ‖t‖ / u ^ 3) u)
                  (mul_div_assoc u (2 * ‖t‖) (u ^ 3))))
              (Eq.trans
                (mul_assoc u (2 * ‖t‖) (u ^ 3)⁻¹)
                (Eq.trans
                  (congrArg (fun z : ℝ => u * (2 * ‖t‖ * z))
                    (inv_mul_cancel₀ hu3))
                  (Eq.trans
                    (congrArg (fun z : ℝ => u * z) (mul_one (2 * ‖t‖)))
                    (mul_comm u (2 * ‖t‖))))))))
    exact Eq.trans hleft hcancel
  exact Eq.subst (motive := fun z : ℝ =>
    HasDerivAt
      (fun y : ℝ => -‖t‖ * (y ^ 2)⁻¹) z u)
    hnormalize.symm hscaled

theorem Complex.logarithmicPhaseDualStationaryActionSecondDerivative_neg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    Complex.logarithmicPhaseDualStationaryActionSecondDerivative t u < 0 := by
  unfold Complex.logarithmicPhaseDualStationaryActionSecondDerivative
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hsquare : 0 < u ^ 2 := sq_pos_of_pos hu
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnorm) hsquare

theorem Complex.logarithmicPhaseDualStationaryActionThirdDerivative_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    0 < Complex.logarithmicPhaseDualStationaryActionThirdDerivative t u := by
  unfold Complex.logarithmicPhaseDualStationaryActionThirdDerivative
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hnumerator : 0 < 2 * ‖t‖ := mul_pos zero_lt_two hnorm
  have hcube : 0 < u ^ 3 := pow_pos hu 3
  exact div_pos hnumerator hcube

theorem Complex.logarithmicPhaseDualStationaryActionDerivative_strictAntiOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictAntiOn
      (Complex.logarithmicPhaseDualStationaryActionDerivative t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualStationaryActionDerivative
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hinv := one_div_strictAnti₀ hu hv huv
  exact mul_lt_mul_of_pos_left hinv hnorm

theorem Complex.logarithmicPhaseDualStationaryActionSecondDerivative_abs_eq
    (t : ℝ) {u : ℝ} (hu : 0 < u) :
    |Complex.logarithmicPhaseDualStationaryActionSecondDerivative t u| =
      ‖t‖ / u ^ 2 := by
  unfold Complex.logarithmicPhaseDualStationaryActionSecondDerivative
  have hquotient : 0 ≤ ‖t‖ / u ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg u)
  exact Eq.trans (abs_neg (‖t‖ / u ^ 2)) (abs_of_nonneg hquotient)

theorem Complex.logarithmicPhaseDualStationaryActionSecondDerivative_abs_lower
    (t : ℝ) {U u : ℝ} (hU : 0 < U) (hu : u ∈ Set.Ioc 0 U) :
    ‖t‖ / U ^ 2 ≤
      |Complex.logarithmicPhaseDualStationaryActionSecondDerivative t u| := by
  have huPos : 0 < u := hu.1
  have huU : u ≤ U := hu.2
  have hsquare := sq_le_sq₀ (le_of_lt huPos) huU
  have hnorm := norm_nonneg t
  have hdivision := div_le_div_of_nonneg_left hnorm
    (sq_pos_of_pos hU) hsquare
  exact le_trans hdivision
    (le_of_eq
      (Complex.logarithmicPhaseDualStationaryActionSecondDerivative_abs_eq
        t huPos).symm)

theorem Complex.logarithmicPhaseDualStationaryActionSecondDerivative_abs_upper
    (t : ℝ) {L u : ℝ} (hL : 0 < L) (hu : u ∈ Set.Ici L) :
    |Complex.logarithmicPhaseDualStationaryActionSecondDerivative t u| ≤
      ‖t‖ / L ^ 2 := by
  have huPos : 0 < u := lt_of_lt_of_le hL hu
  have hsquare := sq_le_sq₀ (le_of_lt hL) hu
  have hnorm := norm_nonneg t
  have hdivision := div_le_div_of_nonneg_left hnorm
    (sq_pos_of_pos hL) hsquare
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Complex.logarithmicPhaseDualStationaryActionSecondDerivative_abs_eq
      t huPos).symm hdivision

/-- Integer negative modes evaluate the dual center at their natural positive
index. -/
theorem Complex.logarithmicPhaseDualStationaryCenter_modeIndex_eq
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseDualStationaryCenter t
        (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) =
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhaseDualStationaryCenter
  exact
    Complex.logarithmicPhase_stationaryCenter_eq_norm_div_modeIndex_raw
      t hm

/-- The modewise stationary phase is the dual action evaluated at `natAbs m`. -/
theorem Complex.logarithmicPhasePositiveFrequencyTwistedPhase_at_modeCenter_eq_dualAction
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhasePositiveFrequencyTwistedPhase t
        (Complex.logarithmicPhaseNegativeModeIndex m : ℝ)
        (Complex.logarithmicPhaseFourierStationaryPoint t m) =
      Complex.logarithmicPhaseDualStationaryAction t
        (Complex.logarithmicPhaseNegativeModeIndex m : ℝ) := by
  unfold Complex.logarithmicPhaseDualStationaryAction
  exact congrArg
    (Complex.logarithmicPhasePositiveFrequencyTwistedPhase t
      (Complex.logarithmicPhaseNegativeModeIndex m : ℝ))
    (Complex.logarithmicPhaseDualStationaryCenter_modeIndex_eq t hm).symm

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualAbel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessPacketArithmetic

/-!
# Balanced dual amplitude for logarithmic stationary packets

The correct B-process amplitude is not the square-root canonical radius.  It
is the balanced radius

`W(u) = x(u) / sqrt (1 + ‖t‖)`.

Since `x(u) = ‖t‖/(2*pi*u)`, this is a constant multiple of `1/u`.  It is
positive, antitone, and has total variation bounded by its first value.  On a
negative integer Fourier mode it is definitionally the existing balanced
B-process radius.  This owner supplies the weight used by the dual Abel sum.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualBProcessAmplitude
    (t u : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualStationaryCenter t u /
    Complex.logarithmicPhaseBProcessScale t

def Complex.logarithmicPhaseDualBProcessAmplitudeNat
    (t : ℝ) (k : ℕ) : ℝ :=
  Complex.logarithmicPhaseDualBProcessAmplitude t (k : ℝ)

def Complex.logarithmicPhaseDualBProcessWeightedTerm
    (t : ℝ) (k : ℕ) : ℂ :=
  (Complex.logarithmicPhaseDualBProcessAmplitudeNat t k : ℂ) *
    Complex.logarithmicPhaseDualOscillationNat t k

theorem Complex.logarithmicPhaseDualBProcessAmplitude_nonneg
    (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ Complex.logarithmicPhaseDualBProcessAmplitude t u := by
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  unfold Complex.logarithmicPhaseDualStationaryCenter
  have hdenom : 0 ≤ 2 * Real.pi * u :=
    mul_nonneg (le_of_lt Complex.two_mul_pi_pos) hu
  have hcenter := div_nonneg (norm_nonneg t) hdenom
  exact div_nonneg hcenter
    (le_of_lt (Complex.logarithmicPhaseBProcessScale_pos t))

theorem Complex.logarithmicPhaseDualBProcessAmplitude_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 0 < u) :
    0 < Complex.logarithmicPhaseDualBProcessAmplitude t u := by
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  exact div_pos
    (Complex.logarithmicPhaseDualStationaryCenter_pos t ht hu)
    (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseDualBProcessAmplitude_eq_norm_div_scale_twoPi_mul
    (t u : ℝ) :
    Complex.logarithmicPhaseDualBProcessAmplitude t u =
      ‖t‖ /
        (Complex.logarithmicPhaseBProcessScale t *
          (2 * Real.pi * u)) := by
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  unfold Complex.logarithmicPhaseDualStationaryCenter
  exact div_div ‖t‖ (2 * Real.pi * u)
    (Complex.logarithmicPhaseBProcessScale t)

theorem Complex.logarithmicPhaseDualBProcessAmplitude_eq_coefficient_mul_inv
    (t : ℝ) {u : ℝ} (hu : u ≠ 0) :
    Complex.logarithmicPhaseDualBProcessAmplitude t u =
      (‖t‖ /
        (Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi))) * u⁻¹ := by
  have hbase :=
    Complex.logarithmicPhaseDualBProcessAmplitude_eq_norm_div_scale_twoPi_mul
      t u
  have hassoc :
      Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi * u) =
        (Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi)) * u :=
    (mul_assoc _ _ _).symm
  exact Eq.trans hbase
    (Eq.trans
      (congrArg (fun denominator : ℝ => ‖t‖ / denominator) hassoc)
      (Eq.trans
        (div_mul_eq_div_mul_one_div ‖t‖
          (Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi)) u)
        (congrArg
          (fun z : ℝ =>
            (‖t‖ /
              (Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi))) * z)
          (one_div u))))

theorem Complex.logarithmicPhaseDualBProcessAmplitude_antitoneOn :
    AntitoneOn
      (Complex.logarithmicPhaseDualBProcessAmplitude t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  have hcenter :=
    Complex.logarithmicPhaseDualStationaryCenter_antitoneOn hu hv huv
  have hscale := le_of_lt (Complex.logarithmicPhaseBProcessScale_pos t)
  exact div_le_div_of_nonneg_right hcenter hscale

theorem Complex.logarithmicPhaseDualBProcessAmplitude_strictAntiOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    StrictAntiOn
      (Complex.logarithmicPhaseDualBProcessAmplitude t)
      (Set.Ioi 0) := by
  intro u hu v hv huv
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  have hcenter :=
    Complex.logarithmicPhaseDualStationaryCenter_strictAntiOn
      t ht hu hv huv
  exact div_lt_div_of_pos_right hcenter
    (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseDualBProcessAmplitudeNat_antitone
    (t : ℝ) {j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    Complex.logarithmicPhaseDualBProcessAmplitudeNat t k ≤
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t j := by
  unfold Complex.logarithmicPhaseDualBProcessAmplitudeNat
  have hjReal : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj
  have hk : 0 < k := lt_of_lt_of_le hj hjk
  have hkReal : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hjkReal : (j : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hjk
  exact Complex.logarithmicPhaseDualBProcessAmplitude_antitoneOn
    hjReal hkReal hjkReal

theorem Complex.logarithmicPhaseDualBProcessAmplitudeNat_succ_le
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    Complex.logarithmicPhaseDualBProcessAmplitudeNat t (k + 1) ≤
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t k := by
  exact Complex.logarithmicPhaseDualBProcessAmplitudeNat_antitone
    t hk (Nat.le_add_right k 1)

theorem Complex.logarithmicPhaseDualBProcessAmplitudeNat_difference_nonneg
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    0 ≤ Complex.logarithmicPhaseDualBProcessAmplitudeNat t k -
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t (k + 1) := by
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseDualBProcessAmplitudeNat_succ_le t hk)

theorem Complex.logarithmicPhaseDualBProcessWeightedTerm_norm
    (t : ℝ) {k : ℕ} (hk : 0 < k) :
    ‖Complex.logarithmicPhaseDualBProcessWeightedTerm t k‖ =
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t k := by
  unfold Complex.logarithmicPhaseDualBProcessWeightedTerm
  have hamp :
      0 ≤ Complex.logarithmicPhaseDualBProcessAmplitudeNat t k :=
    Complex.logarithmicPhaseDualBProcessAmplitude_nonneg t
      (Nat.cast_nonneg k)
  have hcast :
      ‖(Complex.logarithmicPhaseDualBProcessAmplitudeNat t k : ℂ)‖ =
        Complex.logarithmicPhaseDualBProcessAmplitudeNat t k :=
    Complex.norm_real_of_nonneg hamp
  exact Eq.trans
    (norm_mul
      (Complex.logarithmicPhaseDualBProcessAmplitudeNat t k : ℂ)
      (Complex.logarithmicPhaseDualOscillationNat t k))
    (Eq.trans
      (congrArg₂ (fun x y : ℝ => x * y) hcast
        (Complex.logarithmicPhaseDualOscillationNat_norm t k))
      (mul_one _))

theorem Complex.logarithmicPhaseDualBProcessAmplitudeNat_totalVariation_eq_drop
    (t : ℝ) (K N : ℕ) :
    (∑ j ∈ Finset.Ico K (K + N),
      (Complex.logarithmicPhaseDualBProcessAmplitudeNat t j -
        Complex.logarithmicPhaseDualBProcessAmplitudeNat t (j + 1))) =
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t K -
        Complex.logarithmicPhaseDualBProcessAmplitudeNat t (K + N) := by
  exact Finset.sum_Ico_shifted_forwardDifference
    (Complex.logarithmicPhaseDualBProcessAmplitudeNat t) K N

theorem Complex.logarithmicPhaseDualBProcessAmplitudeNat_totalVariation_le_initial
    (t : ℝ) (K N : ℕ) :
    (∑ j ∈ Finset.Ico K (K + N),
      (Complex.logarithmicPhaseDualBProcessAmplitudeNat t j -
        Complex.logarithmicPhaseDualBProcessAmplitudeNat t (j + 1))) ≤
      Complex.logarithmicPhaseDualBProcessAmplitudeNat t K := by
  have hfinal :=
    Complex.logarithmicPhaseDualBProcessAmplitude_nonneg t
      (Nat.cast_nonneg (K + N))
  have hdrop := sub_le_self
    (Complex.logarithmicPhaseDualBProcessAmplitudeNat t K) hfinal
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Complex.logarithmicPhaseDualBProcessAmplitudeNat_totalVariation_eq_drop
      t K N).symm hdrop

theorem Complex.logarithmicPhaseDualBProcessAmplitude_modeIndex_eq_radius
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseDualBProcessAmplitudeNat t
        (Complex.logarithmicPhaseNegativeModeIndex m) =
      Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseDualBProcessAmplitudeNat
  unfold Complex.logarithmicPhaseDualBProcessAmplitude
  unfold Complex.logarithmicPhaseBProcessRadius
  exact congrArg
    (fun center : ℝ => center /
      Complex.logarithmicPhaseBProcessScale t)
    (Complex.logarithmicPhaseDualStationaryCenter_modeIndex_eq t hm)

theorem Complex.logarithmicPhaseDualBProcessAmplitude_le_scale_div_mode
    (t : ℝ) (ht : 1 ≤ ‖t‖) {u : ℝ} (hu : 1 ≤ u) :
    Complex.logarithmicPhaseDualBProcessAmplitude t u ≤
      Complex.logarithmicPhaseBProcessScale t / u := by
  have hscaleSq := Complex.logarithmicPhaseBProcessScale_sq t
  have hnormLe : ‖t‖ ≤
      Complex.logarithmicPhaseBProcessScale t *
        Complex.logarithmicPhaseBProcessScale t := by
    exact le_trans (le_add_of_nonneg_left zero_le_one)
      (le_of_eq hscaleSq.symm)
  have htwoPiOne : (1 : ℝ) ≤ 2 * Real.pi := Real.one_le_two_pi
  have hdenom :
      Complex.logarithmicPhaseBProcessScale t * u ≤
        Complex.logarithmicPhaseBProcessScale t * (2 * Real.pi * u) := by
    have hangular := mul_le_mul_of_nonneg_right htwoPiOne
      (le_trans zero_le_one hu)
    exact mul_le_mul_of_nonneg_left hangular
      (le_of_lt (Complex.logarithmicPhaseBProcessScale_pos t))
  have hcross :
      ‖t‖ * u ≤
        Complex.logarithmicPhaseBProcessScale t *
          (Complex.logarithmicPhaseBProcessScale t *
            (2 * Real.pi * u)) := by
    have hscaled := mul_le_mul_of_nonneg_right hnormLe
      (le_trans zero_le_one hu)
    exact le_trans hscaled
      (mul_le_mul_of_nonneg_left hdenom
        (le_of_lt (Complex.logarithmicPhaseBProcessScale_pos t)))
  have huPos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hbigDenom :
      0 < Complex.logarithmicPhaseBProcessScale t *
        (2 * Real.pi * u) :=
    mul_pos (Complex.logarithmicPhaseBProcessScale_pos t)
      (Real.two_pi_mul_pos huPos)
  have hdivision :
      ‖t‖ /
          (Complex.logarithmicPhaseBProcessScale t *
            (2 * Real.pi * u)) ≤
        Complex.logarithmicPhaseBProcessScale t / u := by
    exact (div_le_div_iff₀ hbigDenom huPos).mpr hcross
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Complex.logarithmicPhaseDualBProcessAmplitude_eq_norm_div_scale_twoPi_mul
      t u).symm hdivision

theorem Complex.logarithmicPhaseDualBProcessWeightedRangeSum_le_two_initial_mul
    (t : ℝ) (K N : ℕ) (hK : 0 < K) {B : ℝ}
    (hpartial : ∀ j ≤ N,
      ‖Complex.shiftedInclusivePartialSum
          (Complex.logarithmicPhaseDualOscillationNat t) K j‖ ≤ B)
    (hB : 0 ≤ B) :
    ‖Complex.shiftedWeightedRangeSum
        (Complex.logarithmicPhaseDualBProcessAmplitudeNat t)
        (Complex.logarithmicPhaseDualOscillationNat t) K (N + 1)‖ ≤
      2 *
        (Complex.logarithmicPhaseDualBProcessAmplitudeNat t K * B) := by
  let w := Complex.logarithmicPhaseDualBProcessAmplitudeNat t
  let z := Complex.logarithmicPhaseDualOscillationNat t
  have hweight : 0 ≤ w (K + N) :=
    Complex.logarithmicPhaseDualBProcessAmplitude_nonneg t
      (Nat.cast_nonneg (K + N))
  have hdrop : ∀ j < N, 0 ≤ w (K + j) - w (K + j + 1) := by
    intro j hj
    have hKj : 0 < K + j := lt_of_lt_of_le hK (Nat.le_add_right K j)
    exact
      Complex.logarithmicPhaseDualBProcessAmplitudeNat_difference_nonneg
        t hKj
  have habel :=
    Complex.norm_shiftedWeightedRangeSum_succ_le_abel
      w z K N hweight hdrop hpartial
  have hvariationEq := Finset.sum_range_forwardDifference
    (fun j : ℕ => w (K + j)) N
  have hterminal := Complex.logarithmicPhaseDualBProcessAmplitudeNat_antitone
    t hK (Nat.le_add_right K N)
  have hfinalNonneg :=
    Complex.logarithmicPhaseDualBProcessAmplitude_nonneg t
      (Nat.cast_nonneg (K + N))
  have hvariation :
      (∑ j ∈ Finset.range N,
        (w (K + j) - w (K + j + 1))) ≤ w K := by
    exact Eq.subst (motive := fun z : ℝ => z ≤ w K)
      hvariationEq.symm (sub_le_self (w K) hfinalNonneg)
  have hscaledTerminal := mul_le_mul_of_nonneg_right hterminal hB
  have hscaledVariation := mul_le_mul_of_nonneg_right hvariation hB
  have hcombined := add_le_add hscaledTerminal hscaledVariation
  exact le_trans habel
    (le_trans hcombined
      (le_of_eq (two_mul (w K * B)).symm))

end

end LFunctions
end Boundary

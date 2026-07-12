import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryMajorantMonotonicity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedMajorantIntegral

/-!
# Closed density comparison for phase-adapted packets

The variable phase curvature is bounded at the positive left support endpoint,
and the variable derivative denominator is replaced by a uniform positive gap.
Only the cutoff, its first derivative, and its second derivative remain under
the integral.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseAdaptedClosedDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ) (x : ℝ) : ℝ :=
  Complex.nonstationarySecondTransformMajorant
    |Real.quantitativeLogarithmicBlockCutoff a b x|
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|
    |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x|
    (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    gap

theorem Complex.logarithmicPhaseAdaptedClosedDensity_nonneg
    (t : ℝ) (a b : ℤ) (gap x : ℝ)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap : 0 ≤ gap) :
    0 ≤ Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x := by
  unfold Complex.logarithmicPhaseAdaptedClosedDensity
  unfold Complex.nonstationarySecondTransformMajorant
  have hA : 0 ≤ |Real.quantitativeLogarithmicBlockCutoff a b x| := abs_nonneg _
  have hA₁ : 0 ≤
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| := abs_nonneg _
  have hA₂ : 0 ≤
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| := abs_nonneg _
  have hv := Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hw :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  have hg₂ : 0 ≤ gap ^ 2 := pow_nonneg hgap 2
  have hg₃ : 0 ≤ gap ^ 3 := pow_nonneg hgap 3
  have hg₄ : 0 ≤ gap ^ 4 := pow_nonneg hgap 4
  have hfirst := div_nonneg hA₂ hg₂
  have hsecondNumerator :
      0 ≤ 3 * |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (Real.mul_three_nonneg hA₁) hv
  have hsecond := div_nonneg hsecondNumerator hg₃
  have hthirdNumerator :
      0 ≤ |Real.quantitativeLogarithmicBlockCutoff a b x| *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg hA hw
  have hthird := div_nonneg hthirdNumerator hg₃
  have hfourthNumerator :
      0 ≤ 3 * |Real.quantitativeLogarithmicBlockCutoff a b x| *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    mul_nonneg (Real.mul_three_nonneg hA) (sq_nonneg _)
  have hfourth := div_nonneg hfourthNumerator hg₄
  exact add_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthird) hfourth

theorem Complex.logarithmicPhaseAdaptedPointwiseMajorant_le_closedDensity
    (t : ℝ) (a b m : ℤ) (gap x : ℝ)
    (hleft : 0 < Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hleftx : Complex.logarithmicPhaseQuantitativeSupportLeft a ≤ x)
    (hgap : 0 < gap)
    (hderivative : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    Complex.logarithmicPhaseAdaptedPointwiseMajorant t a b m x ≤
      Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x := by
  unfold Complex.logarithmicPhaseAdaptedPointwiseMajorant
  unfold Complex.logarithmicPhaseAdaptedClosedDensity
  have hA : 0 ≤ |Real.quantitativeLogarithmicBlockCutoff a b x| := abs_nonneg _
  have hA₁ : 0 ≤
      |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| := abs_nonneg _
  have hA₂ : 0 ≤
      |Real.quantitativeLogarithmicBlockCutoffSecondDerivative a b x| := abs_nonneg _
  have hv₀ : 0 ≤ ‖t‖ / x ^ 2 :=
    div_nonneg (norm_nonneg t) (sq_nonneg x)
  have hw₀ : 0 ≤ 2 * ‖t‖ / x ^ 3 := by
    have hx : 0 < x := lt_of_lt_of_le hleft hleftx
    exact div_nonneg
      (mul_nonneg (by exact OfNat.zero_le 2) (norm_nonneg t))
      (pow_nonneg hx.le 3)
  have hv :=
    Complex.logarithmicPhaseAdaptedCurvature_le_left t _ x hleft hleftx
  have hw :=
    Complex.logarithmicPhaseAdaptedThirdDerivative_le_left t _ x hleft hleftx
  exact Complex.nonstationarySecondTransformMajorant_mono
    hA hA₁ hA₂ hv₀ hw₀ hgap
    (le_refl _) (le_refl _) (le_refl _) hv hw hderivative

theorem Complex.continuousAt_logarithmicPhaseAdaptedClosedDensity
    (t : ℝ) (a b : ℤ) (gap x : ℝ)
    (hgap : gap ≠ 0) :
    ContinuousAt
      (Complex.logarithmicPhaseAdaptedClosedDensity t a b gap) x := by
  unfold Complex.logarithmicPhaseAdaptedClosedDensity
  have hA :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoff a b x
  have hA₁ :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffDerivative a b x
  have hA₂ :=
    Complex.continuousAt_abs_quantitativeLogarithmicBlockCutoffSecondDerivative
      a b x
  exact Complex.continuousAt_nonstationarySecondTransformMajorant_comp
    hA hA₁ hA₂ continuousAt_const continuousAt_const continuousAt_const hgap

theorem Complex.continuous_logarithmicPhaseAdaptedClosedDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hgap : gap ≠ 0) :
    Continuous (Complex.logarithmicPhaseAdaptedClosedDensity t a b gap) := by
  exact continuous_iff_continuousAt.mpr
    (fun x => Complex.continuousAt_logarithmicPhaseAdaptedClosedDensity
      t a b gap x hgap)

theorem Complex.intervalIntegrable_logarithmicPhaseAdaptedClosedDensity
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hgap : gap ≠ 0) :
    IntervalIntegrable
      (Complex.logarithmicPhaseAdaptedClosedDensity t a b gap)
      volume
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  exact (Complex.continuous_logarithmicPhaseAdaptedClosedDensity
    t a b gap hgap).intervalIntegrable _ _

theorem Complex.norm_logarithmicPhaseAdaptedPacket_le_closedDensityIntegral
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedClosedDensity t a b gap x := by
  have hpacket :=
    Complex.norm_logarithmicPhaseAdaptedPacket_le_pointwiseMajorantIntegral
      t a b m gap ha hab hgap hlower
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hleftPos :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hpointwiseIntegrable :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedPointwiseMajorant
      t a b m gap ha hab hgap hlower
  have hclosedIntegrable :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedClosedDensity
      t a b gap (ne_of_gt hgap)
  have hmono := intervalIntegral.integral_mono_on hleftRight
    hpointwiseIntegrable hclosedIntegrable
    (fun x hx =>
      Complex.logarithmicPhaseAdaptedPointwiseMajorant_le_closedDensity
        t a b m gap x hleftPos hx.1 hgap
        (hlower x ((Set.uIcc_of_le hleftRight).mpr hx)))
  exact le_trans hpacket hmono

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedIntegrability

/-!
# Two-step packet estimate for the phase-adapted logarithmic phase

This owner applies the generic twice-integrated nonstationary theorem to the
actual quantitative Poisson packet.  Every analytic side condition is derived
from the cutoff construction, support positivity, and a uniform phase gap.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseAdaptedSecondTransform
    (t : ℝ) (a b m : ℤ) : ℝ → ℂ :=
  Complex.nonstationarySecondTransformedAmplitude
    (Complex.nonstationaryFirstTransformedDerivativeExplicit
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b)
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
      (Complex.realPhaseIntegrationCoefficientSecondDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t)))
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
    (Complex.realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
    (Complex.realPhaseIntegrationCoefficientDerivative
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))

theorem Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_adaptedInterval
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m =
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x *
          Complex.logarithmicPhaseAdaptedOscillator t m x := by
  unfold Complex.logarithmicPhaseQuantitativeBlockFourierPacket
  have hsupport :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_amplitude_linear_interval
      t a b m ha hab
  have hpointwise : ∀ x : ℝ,
      Complex.phaseCutoffFrequencyTwistIntegrand
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) m x =
        Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x *
          Complex.logarithmicPhaseAdaptedOscillator t m x :=
    fun x => Complex.logarithmicPhaseAdaptedPacketIntegrand_eq t a b m x
  have hintegral := intervalIntegral.integral_congr
    (fun x hx => hpointwise x)
  exact Eq.trans hsupport (Eq.trans
    (intervalIntegral.integral_congr
      (fun x hx =>
        Complex.logarithmicPhaseAdaptedPacketIntegrand_eq t a b m x))
    rfl)

theorem Complex.norm_logarithmicPhaseAdaptedPacket_le_secondTransform
    (t : ℝ) (a b m : ℤ) (gap : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hgap : 0 < gap)
    (hlower : ∀ x ∈ [[Complex.logarithmicPhaseQuantitativeSupportLeft a,
        Complex.logarithmicPhaseQuantitativeSupportRight b]],
      gap ≤ ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        ‖Complex.logarithmicPhaseAdaptedSecondTransform t a b m x‖ := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  let amplitude := Complex.logarithmicPhaseAdaptedCutoffAmplitude a b
  let amplitudeDerivative :=
    Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b
  let amplitudeSecondDerivative :=
    Complex.logarithmicPhaseAdaptedCutoffAmplitudeSecondDerivative a b
  let phase := Complex.logarithmicPhaseAdaptedTwistedPhase t m
  let phaseDerivative :=
    Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m
  let phaseSecondDerivative :=
    Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t
  let phaseThirdDerivative :=
    Complex.logarithmicPhaseAdaptedTwistedPhaseThirdDerivative t
  let coefficient := Complex.realPhaseIntegrationCoefficient phaseDerivative
  let coefficientDerivative :=
    Complex.realPhaseIntegrationCoefficientDerivative
      phaseDerivative phaseSecondDerivative
  let coefficientSecondDerivative :=
    Complex.realPhaseIntegrationCoefficientSecondDerivative
      phaseDerivative phaseSecondDerivative phaseThirdDerivative
  let firstDerivative :=
    Complex.nonstationaryFirstTransformedDerivativeExplicit
      amplitude amplitudeDerivative amplitudeSecondDerivative
      coefficient coefficientDerivative coefficientSecondDerivative
  let oscillator := Complex.logarithmicPhaseAdaptedOscillator t m
  let oscillatorDerivative :=
    Complex.logarithmicPhaseAdaptedOscillatorDerivative t m
  have hleftRight : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hamplitude : ∀ x ∈ [[left, right]],
      HasDerivAt amplitude (amplitudeDerivative x) x :=
    fun x hx => Complex.hasDerivAt_logarithmicPhaseAdaptedCutoffAmplitude a b x
  have hcoefficient : ∀ x ∈ [[left, right]],
      HasDerivAt coefficient (coefficientDerivative x) x := by
    intro x hx
    have hxPos :=
      Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
    exact Complex.hasDerivAt_logarithmicPhaseAdaptedCoefficient_of_gap
      t m hxPos hgap (hlower x hx)
  have hfirst : ∀ x ∈ [[left, right]],
      HasDerivAt
        (Complex.nonstationaryFirstTransformedAmplitude
          amplitude amplitudeDerivative coefficient coefficientDerivative)
        (firstDerivative x) x := by
    intro x hx
    have hxPos :=
      Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
    exact Complex.hasDerivAt_logarithmicPhaseAdaptedFirstTransform_of_gap
      t a b m hxPos hgap (hlower x hx)
  have hoscillator : ∀ x ∈ [[left, right]],
      HasDerivAt oscillator (oscillatorDerivative x) x := by
    intro x hx
    have hxPos :=
      Complex.logarithmicPhaseQuantitativeSupport_mem_positive a b ha hab hx
    exact Complex.hasDerivAt_logarithmicPhaseAdaptedOscillator t m hxPos
  have hfirstIntegrable : IntervalIntegrable
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative coefficient coefficientDerivative)
      volume left right :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedFirstTransform
      t a b m gap ha hab hgap hlower
  have hsecondIntegrable : IntervalIntegrable
      (Complex.nonstationarySecondTransformedAmplitude
        firstDerivative amplitude amplitudeDerivative
        coefficient coefficientDerivative) volume left right :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedSecondTransform
      t a b m gap ha hab hgap hlower
  have hoscillatorDerivativeIntegrable :
      IntervalIntegrable oscillatorDerivative volume left right :=
    Complex.intervalIntegrable_logarithmicPhaseAdaptedOscillatorDerivative
      t a b m ha hab
  have hcancellation : ∀ x ∈ [[left, right]],
      coefficient x * oscillatorDerivative x = oscillator x := by
    intro x hx
    exact Complex.logarithmicPhaseAdaptedCoefficient_cancellation_of_gap
      t m x gap hgap (hlower x hx)
  have hfirstLeft :
      Complex.nonstationaryFirstCoefficient amplitude coefficient left = 0 :=
    Complex.logarithmicPhaseAdaptedFirstCoefficient_supportLeft_eq_zero t a b m
  have hfirstRight :
      Complex.nonstationaryFirstCoefficient amplitude coefficient right = 0 :=
    Complex.logarithmicPhaseAdaptedFirstCoefficient_supportRight_eq_zero t a b m
  have hsecondLeft :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        coefficient coefficientDerivative left = 0 :=
    Complex.logarithmicPhaseAdaptedSecondCoefficient_supportLeft_eq_zero t a b m
  have hsecondRight :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        coefficient coefficientDerivative right = 0 :=
    Complex.logarithmicPhaseAdaptedSecondCoefficient_supportRight_eq_zero t a b m
  have hoscillatorNorm : ∀ x : ℝ, ‖oscillator x‖ = 1 :=
    fun x => Complex.norm_logarithmicPhaseAdaptedOscillator t m x
  have hbound :=
    Complex.norm_intervalIntegral_amplitude_oscillator_le_second_transform
      amplitude amplitudeDerivative coefficient coefficientDerivative
      firstDerivative oscillator oscillatorDerivative left right
      hleftRight hamplitude hcoefficient hfirst hoscillator
      hfirstIntegrable hsecondIntegrable hoscillatorDerivativeIntegrable
      hcancellation hfirstLeft hfirstRight hsecondLeft hsecondRight
      hoscillatorNorm
  have hpacket :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_adaptedInterval
      t a b m ha hab
  unfold Complex.logarithmicPhaseAdaptedSecondTransform
  exact le_trans (le_of_eq (congrArg norm hpacket)) hbound

end
end LFunctions
end Boundary

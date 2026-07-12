import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedOscillator
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePacketDecay

/-!
# Endpoint cancellation for phase-adapted logarithmic packets

Only the cutoff and its first derivative enter the boundary coefficients.
Both vanish at the fixed support endpoints, so two integrations by parts have
no boundary contribution independently of the logarithmic parameter or mode.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportLeft_eq_zero
    (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedCutoffAmplitude a b
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitude
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have hreal := Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_left a b
    (le_refl ((a : ℝ) - 1 / 3))
  have hcast := congrArg (fun value : ℝ => (value : ℂ)) hreal
  exact Eq.trans hcast Complex.ofReal_zero

theorem Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportRight_eq_zero
    (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedCutoffAmplitude a b
      (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitude
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have hreal := Real.quantitativeLogarithmicBlockCutoff_eq_zero_of_right a b
    (le_refl ((b : ℝ) + 1 / 3))
  have hcast := congrArg (fun value : ℝ => (value : ℂ)) hreal
  exact Eq.trans hcast Complex.ofReal_zero

theorem Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative_supportLeft_eq_zero
    (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have hreal := Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportLeft a b
  have hcast := congrArg (fun value : ℝ => (value : ℂ)) hreal
  exact Eq.trans hcast Complex.ofReal_zero

theorem Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative_supportRight_eq_zero
    (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b
      (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have hreal := Real.quantitativeLogarithmicBlockCutoffDerivative_at_supportRight a b
  have hcast := congrArg (fun value : ℝ => (value : ℂ)) hreal
  exact Eq.trans hcast Complex.ofReal_zero

theorem Complex.nonstationaryFirstCoefficient_eq_zero_of_amplitude_eq_zero
    (amplitude phaseCoefficient : ℝ → ℂ) (x : ℝ)
    (hamplitude : amplitude x = 0) :
    Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient x = 0 := by
  unfold Complex.nonstationaryFirstCoefficient
  exact Eq.trans
    (congrArg (fun value : ℂ => value * phaseCoefficient x) hamplitude)
    (zero_mul _)

theorem Complex.nonstationarySecondCoefficient_eq_zero_of_amplitudes_eq_zero
    (amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative : ℝ → ℂ)
    (x : ℝ)
    (hamplitude : amplitude x = 0)
    (hamplitudeDerivative : amplitudeDerivative x = 0) :
    Complex.nonstationarySecondCoefficient
      amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative x = 0 := by
  unfold Complex.nonstationarySecondCoefficient
  unfold Complex.nonstationaryFirstTransformedAmplitude
  have hfirst : amplitudeDerivative x * phaseCoefficient x = 0 :=
    Eq.trans
      (congrArg (fun value : ℂ => value * phaseCoefficient x)
        hamplitudeDerivative)
      (zero_mul _)
  have hsecond : amplitude x * phaseCoefficientDerivative x = 0 :=
    Eq.trans
      (congrArg (fun value : ℂ => value * phaseCoefficientDerivative x)
        hamplitude)
      (zero_mul _)
  exact Eq.trans
    (congrArg (fun value : ℂ => value * phaseCoefficient x)
      (Eq.trans (congrArg₂ (fun first second : ℂ => first + second)
        hfirst hsecond) (zero_add 0)))
    (zero_mul _)

theorem Complex.logarithmicPhaseAdaptedFirstCoefficient_supportLeft_eq_zero
    (t : ℝ) (a b m : ℤ) :
    Complex.nonstationaryFirstCoefficient
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  exact Complex.nonstationaryFirstCoefficient_eq_zero_of_amplitude_eq_zero
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
    (Complex.realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
    (Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportLeft_eq_zero a b)

theorem Complex.logarithmicPhaseAdaptedFirstCoefficient_supportRight_eq_zero
    (t : ℝ) (a b m : ℤ) :
    Complex.nonstationaryFirstCoefficient
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  exact Complex.nonstationaryFirstCoefficient_eq_zero_of_amplitude_eq_zero
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
    (Complex.realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
    (Complex.logarithmicPhaseQuantitativeSupportRight b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportRight_eq_zero a b)

theorem Complex.logarithmicPhaseAdaptedSecondCoefficient_supportLeft_eq_zero
    (t : ℝ) (a b m : ℤ) :
    Complex.nonstationarySecondCoefficient
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 0 := by
  exact Complex.nonstationarySecondCoefficient_eq_zero_of_amplitudes_eq_zero
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
    (Complex.realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
    (Complex.realPhaseIntegrationCoefficientDerivative
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
    (Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportLeft_eq_zero a b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative_supportLeft_eq_zero a b)

theorem Complex.logarithmicPhaseAdaptedSecondCoefficient_supportRight_eq_zero
    (t : ℝ) (a b m : ℤ) :
    Complex.nonstationarySecondCoefficient
      (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
      (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
      (Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
      (Complex.realPhaseIntegrationCoefficientDerivative
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
        (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
      (Complex.logarithmicPhaseQuantitativeSupportRight b) = 0 := by
  exact Complex.nonstationarySecondCoefficient_eq_zero_of_amplitudes_eq_zero
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude a b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative a b)
    (Complex.realPhaseIntegrationCoefficient
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m))
    (Complex.realPhaseIntegrationCoefficientDerivative
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m)
      (Complex.logarithmicPhaseAdaptedTwistedPhaseSecondDerivative t))
    (Complex.logarithmicPhaseQuantitativeSupportRight b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitude_supportRight_eq_zero a b)
    (Complex.logarithmicPhaseAdaptedCutoffAmplitudeDerivative_supportRight_eq_zero a b)

end
end LFunctions
end Boundary

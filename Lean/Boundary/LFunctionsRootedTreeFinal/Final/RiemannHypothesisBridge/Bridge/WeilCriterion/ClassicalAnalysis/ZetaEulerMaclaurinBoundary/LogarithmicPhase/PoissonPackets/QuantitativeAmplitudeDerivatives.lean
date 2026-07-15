import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.AmplitudeNonstationaryPhase
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeSupport
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Differentiable compact amplitude for quantitative logarithmic packets

The logarithmic oscillation and the fixed cutoff are treated together as one
complex amplitude.  Its derivatives remain compactly supported, so the two
amplitude integrations by parts required for the far Fourier tail have honest
interval and whole-line integrability statements before any numerical bound is
attempted.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped ContDiff Interval

def Complex.logarithmicPhaseQuantitativeAmplitude
    (t : ℝ)
    (a b : ℤ)
    (x : ℝ) : ℂ :=
  Complex.phaseCutoffFunction
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
    (Real.quantitativeLogarithmicBlockCutoff a b)
    x

def Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ) : ℝ → ℂ :=
  deriv (Complex.logarithmicPhaseQuantitativeAmplitude t a b)

def Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ) : ℝ → ℂ :=
  deriv (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)

theorem Complex.logarithmicPhaseQuantitativeAmplitude_eq_phaseCutoffFunction
    (t : ℝ)
    (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativeAmplitude t a b =
      Complex.phaseCutoffFunction
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) :=
  rfl

theorem Complex.contDiff_logarithmicPhaseQuantitativeAmplitude
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    ContDiff ℝ ∞ (Complex.logarithmicPhaseQuantitativeAmplitude t a b) := by
  exact
    Complex.contDiff_logarithmicPhase_quantitativeBlockCutoffFunction
      t a b ha

theorem Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitude
    (t : ℝ)
    (a b : ℤ) :
    HasCompactSupport (Complex.logarithmicPhaseQuantitativeAmplitude t a b) := by
  exact
    Complex.hasCompactSupport_phaseCutoffFunction
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.quantitativeLogarithmicBlockCutoff a b)
      (Real.hasCompactSupport_quantitativeLogarithmicBlockCutoff a b)

theorem Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    ContDiff ℝ ∞
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) := by
  have hamplitude :=
    Complex.contDiff_logarithmicPhaseQuantitativeAmplitude t a b ha
  have hderivative := (contDiff_infty_iff_deriv.mp hamplitude).2
  exact hderivative

theorem Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    ContDiff ℝ ∞
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) := by
  have hfirst :=
    Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b ha
  have hsecond := (contDiff_infty_iff_deriv.mp hfirst).2
  exact hsecond

theorem Complex.continuous_logarithmicPhaseQuantitativeAmplitude
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Continuous (Complex.logarithmicPhaseQuantitativeAmplitude t a b) :=
  (Complex.contDiff_logarithmicPhaseQuantitativeAmplitude t a b ha).continuous

theorem Complex.continuous_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Continuous (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
  (Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b ha).continuous

theorem Complex.continuous_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Continuous (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) :=
  (Complex.contDiff_logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b ha).continuous

theorem Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ) :
    HasCompactSupport
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) := by
  exact
    (Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitude t a b).deriv

theorem Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ) :
    HasCompactSupport
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) := by
  exact
    (Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b).deriv

theorem Complex.integrable_logarithmicPhaseQuantitativeAmplitude
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Integrable (Complex.logarithmicPhaseQuantitativeAmplitude t a b) := by
  have hcontinuous :
      Continuous (Complex.logarithmicPhaseQuantitativeAmplitude t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitude t a b ha
  have hcompact :
      HasCompactSupport (Complex.logarithmicPhaseQuantitativeAmplitude t a b) :=
    Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitude t a b
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem Complex.integrable_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Integrable (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) := by
  have hcontinuous :
      Continuous
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b ha
  have hcompact :
      HasCompactSupport
        (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b) :=
    Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
      t a b
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem Complex.integrable_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a) :
    Integrable (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) := by
  have hcontinuous :
      Continuous
        (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) :=
    Complex.continuous_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
      t a b ha
  have hcompact :
      HasCompactSupport
        (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b) :=
    Complex.hasCompactSupport_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
      t a b
  exact hcontinuous.integrable_of_hasCompactSupport hcompact

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (left right : ℝ) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativeAmplitudeFirstDerivative t a b)
      volume left right :=
  (Complex.integrable_logarithmicPhaseQuantitativeAmplitudeFirstDerivative
    t a b ha).intervalIntegrable

theorem Complex.intervalIntegrable_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    (t : ℝ)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (left right : ℝ) :
    IntervalIntegrable
      (Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b)
      volume left right :=
  (Complex.integrable_logarithmicPhaseQuantitativeAmplitudeSecondDerivative
    t a b ha).intervalIntegrable

end
end LFunctions
end Boundary

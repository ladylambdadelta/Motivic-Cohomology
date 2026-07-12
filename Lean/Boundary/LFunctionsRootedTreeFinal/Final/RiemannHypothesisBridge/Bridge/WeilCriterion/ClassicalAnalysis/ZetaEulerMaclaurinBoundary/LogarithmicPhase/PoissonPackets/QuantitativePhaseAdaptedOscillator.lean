import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedIntegratedMajorant

/-!
# Oscillator bridge for phase-adapted logarithmic packets

This file identifies the quantitative Fourier packet with the generic
amplitude-times-oscillator formalism and proves the differential cancellation
used by both integrations by parts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseAdaptedOscillator
    (t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.realPhaseOscillation
    (Complex.logarithmicPhaseAdaptedTwistedPhase t m) x

def Complex.logarithmicPhaseAdaptedOscillatorDerivative
    (t : ℝ) (m : ℤ) (x : ℝ) : ℂ :=
  Complex.logarithmicPhaseAdaptedOscillator t m x *
    Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x

theorem Complex.hasDerivAt_logarithmicPhaseAdaptedOscillator
    (t : ℝ) (m : ℤ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (Complex.logarithmicPhaseAdaptedOscillator t m)
      (Complex.logarithmicPhaseAdaptedOscillatorDerivative t m x) x := by
  unfold Complex.logarithmicPhaseAdaptedOscillatorDerivative
  unfold Complex.logarithmicPhaseAdaptedOscillator
  exact Complex.hasDerivAt_realPhaseOscillation
    (Complex.hasDerivAt_logarithmicPhaseAdaptedTwistedPhase t m hx)

theorem Complex.norm_logarithmicPhaseAdaptedOscillator
    (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖Complex.logarithmicPhaseAdaptedOscillator t m x‖ = 1 := by
  unfold Complex.logarithmicPhaseAdaptedOscillator
  unfold Complex.realPhaseOscillation
  have himaginary :
      (Complex.I *
        (Complex.logarithmicPhaseAdaptedTwistedPhase t m x : ℂ)).re = 0 := by
    exact Eq.trans Complex.mul_re
      (Eq.trans
        (congrArg₂ (fun first second : ℝ => first - second)
          Complex.I_re
          (congrArg₂ (fun first second : ℝ => first * second)
            Complex.I_im (Complex.ofReal_im _)))
        (sub_zero 0))
  exact Eq.trans Complex.norm_exp
    (Eq.trans (congrArg Real.exp himaginary) Real.exp_zero)

theorem Complex.norm_logarithmicPhaseAdaptedDerivativeDenominator
    (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖Complex.realPhaseDerivativeDenominator
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x‖ =
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  unfold Complex.realPhaseDerivativeDenominator
  have hnorm := norm_mul Complex.I
    (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x : ℂ)
  have hI : ‖Complex.I‖ = 1 := Complex.norm_I
  have hreal :
      ‖(Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x : ℂ)‖ =
        ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ :=
    Complex.norm_real _
  exact Eq.trans hnorm
    (Eq.trans
      (congrArg₂ (fun first second : ℝ => first * second) hI hreal)
      (one_mul _))

theorem Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero
    (t : ℝ) (m : ℤ) (x : ℝ)
    (hphase :
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≠ 0) :
    Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x ≠ 0 := by
  intro hzero
  unfold Complex.realPhaseDerivativeDenominator at hzero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hcast :
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hI
  have hreal :
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x = 0 :=
    Complex.ofReal_eq_zero.mp hcast
  exact hphase hreal

theorem Complex.logarithmicPhaseAdaptedDerivative_ne_zero_of_gap
    (t : ℝ) (m : ℤ) (x gap : ℝ)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≠ 0 := by
  intro hzero
  have hnormZero :
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ = 0 :=
    congrArg norm hzero
  have hgapZero : gap ≤ 0 := le_trans hlower (le_of_eq hnormZero)
  exact (not_le_of_gt hgap) hgapZero

theorem Complex.logarithmicPhaseAdaptedCoefficient_cancels_oscillatorDerivative
    (t : ℝ) (m : ℤ) (x : ℝ)
    (hphase :
      Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x ≠ 0) :
    Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x *
      Complex.logarithmicPhaseAdaptedOscillatorDerivative t m x =
      Complex.logarithmicPhaseAdaptedOscillator t m x := by
  unfold Complex.logarithmicPhaseAdaptedOscillatorDerivative
  unfold Complex.realPhaseIntegrationCoefficient
  have hdenominator :=
    Complex.logarithmicPhaseAdaptedDerivativeDenominator_ne_zero
      t m x hphase
  let D := Complex.realPhaseDerivativeDenominator
    (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x
  let E := Complex.logarithmicPhaseAdaptedOscillator t m x
  have hinverse : D⁻¹ * D = 1 := inv_mul_cancel₀ hdenominator
  calc
    D⁻¹ * (E * D) = D⁻¹ * (D * E) :=
      congrArg (fun value : ℂ => D⁻¹ * value) (mul_comm E D)
    _ = (D⁻¹ * D) * E := (mul_assoc D⁻¹ D E).symm
    _ = 1 * E := congrArg (fun value : ℂ => value * E) hinverse
    _ = E := one_mul E

theorem Complex.logarithmicPhaseAdaptedCoefficient_cancellation_of_gap
    (t : ℝ) (m : ℤ) (x gap : ℝ)
    (hgap : 0 < gap)
    (hlower : gap ≤
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖) :
    Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x *
      Complex.logarithmicPhaseAdaptedOscillatorDerivative t m x =
      Complex.logarithmicPhaseAdaptedOscillator t m x := by
  have hphase :=
    Complex.logarithmicPhaseAdaptedDerivative_ne_zero_of_gap
      t m x gap hgap hlower
  exact Complex.logarithmicPhaseAdaptedCoefficient_cancels_oscillatorDerivative
    t m x hphase

theorem Complex.logarithmicPhaseAdaptedAmplitude_mul_oscillator
    (t : ℝ) (a b m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x *
      Complex.logarithmicPhaseAdaptedOscillator t m x =
      (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
        Complex.exp
          (Complex.I *
            (Complex.logarithmicPhaseAdaptedTwistedPhase t m x : ℂ)) := by
  unfold Complex.logarithmicPhaseAdaptedCutoffAmplitude
  unfold Complex.logarithmicPhaseAdaptedOscillator
  unfold Complex.realPhaseOscillation
  exact rfl

theorem Complex.logarithmicPhaseAdaptedTwistedPhase_eq_frequencyTwist
    (t : ℝ) (m : ℤ) (x : ℝ) :
    Complex.logarithmicPhaseAdaptedTwistedPhase t m x =
      Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m x := by
  unfold Complex.logarithmicPhaseAdaptedTwistedPhase
  unfold Complex.realPhaseFrequencyTwist
  unfold Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
  have hfrequency :
      2 * Real.pi * (m : ℝ) * x = (2 * Real.pi * (m : ℝ)) * x := rfl
  exact congrArg₂ (fun first second : ℝ => first - second) rfl hfrequency

theorem Complex.logarithmicPhaseAdaptedPacketIntegrand_eq
    (t : ℝ) (a b m : ℤ) (x : ℝ) :
    Complex.phaseCutoffFrequencyTwistIntegrand
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        (Real.quantitativeLogarithmicBlockCutoff a b) m x =
      Complex.logarithmicPhaseAdaptedCutoffAmplitude a b x *
        Complex.logarithmicPhaseAdaptedOscillator t m x := by
  unfold Complex.phaseCutoffFrequencyTwistIntegrand
  have hphase :=
    Complex.logarithmicPhaseAdaptedTwistedPhase_eq_frequencyTwist t m x
  have hexponent := congrArg
    (fun value : ℝ => Complex.exp (Complex.I * (value : ℂ))) hphase
  have hscalar :
      Real.quantitativeLogarithmicBlockCutoff a b x •
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m x : ℂ)) =
        (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) *
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                m x : ℂ)) := by
    exact real_smul _ _
  exact Eq.trans hscalar
    (Eq.trans
      (congrArg
        (fun value : ℂ =>
          (Real.quantitativeLogarithmicBlockCutoff a b x : ℂ) * value)
        hexponent.symm)
      (Complex.logarithmicPhaseAdaptedAmplitude_mul_oscillator t a b m x).symm)

theorem Complex.logarithmicPhaseAdaptedOscillatorDerivative_norm
    (t : ℝ) (m : ℤ) (x : ℝ) :
    ‖Complex.logarithmicPhaseAdaptedOscillatorDerivative t m x‖ =
      ‖Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m x‖ := by
  unfold Complex.logarithmicPhaseAdaptedOscillatorDerivative
  have hproduct := norm_mul
    (Complex.logarithmicPhaseAdaptedOscillator t m x)
    (Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseAdaptedTwistedPhaseDerivative t m) x)
  have hoscillator := Complex.norm_logarithmicPhaseAdaptedOscillator t m x
  have hdenominator :=
    Complex.norm_logarithmicPhaseAdaptedDerivativeDenominator t m x
  exact Eq.trans hproduct
    (Eq.trans
      (congrArg₂ (fun first second : ℝ => first * second)
        hoscillator hdenominator)
      (one_mul _))

end
end LFunctions
end Boundary

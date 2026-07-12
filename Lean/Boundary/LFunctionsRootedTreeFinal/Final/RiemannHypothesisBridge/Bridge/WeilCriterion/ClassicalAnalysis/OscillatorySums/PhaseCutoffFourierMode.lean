import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegerBlockCutoff
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.FrequencyTwist

/-!
# Fourier modes of phase-cutoff extensions

This file identifies the abstract Schwartz-space Fourier transform with the
mode integral that is subsequently decomposed into stationary and
nonstationary packets.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped ContDiff FourierTransform

/-- Raw Fourier-mode integrand for a cutoff real phase, in mathlib's
`exp (-2π i x m)` normalization. -/
def Complex.phaseCutoffFourierModeIntegrand
    (phase cutoff : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) : ℂ :=
  Complex.exp
      (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) •
    Complex.phaseCutoffFunction phase cutoff x

/-- Reordering of mathlib's raw Fourier coefficient into the canonical
angular-frequency order. -/
theorem Real.rawFourierModeCoefficient_eq_neg_angularFrequency
    (m : ℤ)
    (x : ℝ) :
    -2 * Real.pi * x * (m : ℝ) =
      -(2 * Real.pi * (m : ℝ) * x) := by
  let base : ℝ := 2 * Real.pi
  calc
    -2 * Real.pi * x * (m : ℝ) =
        (-base) * x * (m : ℝ) :=
      congrArg
        (fun value : ℝ => value * x * (m : ℝ))
        (neg_mul (2 : ℝ) Real.pi)
    _ = (-(base * x)) * (m : ℝ) :=
      congrArg (fun value : ℝ => value * (m : ℝ))
        (neg_mul base x)
    _ = -((base * x) * (m : ℝ)) :=
      neg_mul (base * x) (m : ℝ)
    _ = -(base * (x * (m : ℝ))) :=
      congrArg Neg.neg (mul_assoc base x (m : ℝ))
    _ = -(base * ((m : ℝ) * x)) :=
      congrArg Neg.neg
        (congrArg (fun value : ℝ => base * value)
          (mul_comm x (m : ℝ)))
    _ = -((base * (m : ℝ)) * x) :=
      congrArg Neg.neg (mul_assoc base (m : ℝ) x).symm

/-- The sum of the raw Fourier exponent and the phase exponent is exactly the
canonical frequency-twisted exponent. -/
theorem Complex.rawFourierExponent_add_phaseExponent
    (phase : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) :
    (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) +
        Complex.I * (phase x : ℂ) =
      Complex.I *
        (Complex.realPhaseFrequencyTwist phase m x : ℂ) := by
  let frequency : ℝ := 2 * Real.pi * (m : ℝ) * x
  have hrawReal :
      -2 * Real.pi * x * (m : ℝ) = -frequency :=
    Real.rawFourierModeCoefficient_eq_neg_angularFrequency m x
  have hrawCast :
      ((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) =
        -(frequency : ℂ) :=
    (congrArg (fun value : ℝ => (value : ℂ)) hrawReal).trans
      (Complex.ofReal_neg frequency)
  have htwistCast :
      (Complex.realPhaseFrequencyTwist phase m x : ℂ) =
        (phase x : ℂ) - (frequency : ℂ) :=
    Complex.ofReal_sub (phase x) frequency
  calc
    (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) +
        Complex.I * (phase x : ℂ) =
      (-(frequency : ℂ)) * Complex.I +
        Complex.I * (phase x : ℂ) :=
      congrArg
        (fun value : ℂ =>
          value * Complex.I + Complex.I * (phase x : ℂ))
        hrawCast
    _ = Complex.I * (phase x : ℂ) +
        (-(frequency : ℂ)) * Complex.I :=
      add_comm
        ((-(frequency : ℂ)) * Complex.I)
        (Complex.I * (phase x : ℂ))
    _ = Complex.I * (phase x : ℂ) +
        Complex.I * (-(frequency : ℂ)) :=
      congrArg
        (fun value : ℂ => Complex.I * (phase x : ℂ) + value)
        (mul_comm (-(frequency : ℂ)) Complex.I)
    _ = Complex.I *
        ((phase x : ℂ) + (-(frequency : ℂ))) :=
      (mul_add Complex.I (phase x : ℂ) (-(frequency : ℂ))).symm
    _ = Complex.I * ((phase x : ℂ) - (frequency : ℂ)) :=
      congrArg (fun value : ℂ => Complex.I * value)
        (sub_eq_add_neg (phase x : ℂ) (frequency : ℂ)).symm
    _ = Complex.I *
        (Complex.realPhaseFrequencyTwist phase m x : ℂ) :=
      congrArg (fun value : ℂ => Complex.I * value) htwistCast.symm

/-- Canonical cutoff integrand for the frequency-twisted phase. -/
def Complex.phaseCutoffFrequencyTwistIntegrand
    (phase cutoff : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) : ℂ :=
  cutoff x •
    Complex.exp
      (Complex.I *
        (Complex.realPhaseFrequencyTwist phase m x : ℂ))

/-- The norm of a cutoff frequency-twist integrand is exactly the absolute
value of its real cutoff amplitude. -/
theorem Complex.norm_phaseCutoffFrequencyTwistIntegrand
    (phase cutoff : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) :
    ‖Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x‖ =
      |cutoff x| := by
  have hsmul :
      ‖cutoff x •
          Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist phase m x : ℂ))‖ =
        |cutoff x| *
          ‖Complex.exp
            (Complex.I *
              (Complex.realPhaseFrequencyTwist phase m x : ℂ))‖ :=
    norm_smul (cutoff x)
      (Complex.exp
        (Complex.I *
          (Complex.realPhaseFrequencyTwist phase m x : ℂ)))
  exact
    hsmul.trans
      ((congrArg
        (fun value : ℝ => |cutoff x| * value)
        ((congrArg norm
          (congrArg Complex.exp
            (mul_comm Complex.I
              (Complex.realPhaseFrequencyTwist phase m x : ℂ)))).trans
          (Complex.norm_exp_ofReal_mul_I
            (Complex.realPhaseFrequencyTwist phase m x)))).trans
        (mul_one |cutoff x|))

/-- Pointwise normalization of a raw Fourier mode into the canonical
frequency-twisted oscillation. -/
theorem Complex.phaseCutoffFourierModeIntegrand_eq_frequencyTwistIntegrand
    (phase cutoff : ℝ → ℝ)
    (m : ℤ)
    (x : ℝ) :
    Complex.phaseCutoffFourierModeIntegrand phase cutoff m x =
      Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x := by
  let rawExponent : ℂ :=
    ((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I
  let phaseExponent : ℂ := Complex.I * (phase x : ℂ)
  have hexponent :
      rawExponent + phaseExponent =
        Complex.I *
          (Complex.realPhaseFrequencyTwist phase m x : ℂ) :=
    Complex.rawFourierExponent_add_phaseExponent phase m x
  have hexponentialProduct :
      Complex.exp rawExponent * Complex.exp phaseExponent =
        Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist phase m x : ℂ)) :=
    (Complex.exp_add rawExponent phaseExponent).symm.trans
      (congrArg Complex.exp hexponent)
  have hscalarProduct :
      Complex.exp rawExponent • Complex.exp phaseExponent =
        Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist phase m x : ℂ)) :=
    hexponentialProduct
  calc
    Complex.phaseCutoffFourierModeIntegrand phase cutoff m x =
        Complex.exp rawExponent •
          (cutoff x • Complex.exp phaseExponent) :=
      rfl

    _ = cutoff x •
        (Complex.exp rawExponent • Complex.exp phaseExponent) :=
      smul_comm (Complex.exp rawExponent) (cutoff x)
        (Complex.exp phaseExponent)
    _ = cutoff x •
        Complex.exp
          (Complex.I *
            (Complex.realPhaseFrequencyTwist phase m x : ℂ)) :=
      congrArg (fun value : ℂ => cutoff x • value) hscalarProduct
    _ = Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x :=
      rfl

/-- Smoothness of every Fourier-mode integrand follows from smoothness of the
cutoff oscillatory product; no global smoothness of the bare phase is needed. -/
theorem Complex.contDiff_phaseCutoffFrequencyTwistIntegrand_of_productSmooth
    (phase cutoff : ℝ → ℝ)
    (m : ℤ)
    (hsmooth : ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff)) :
    ContDiff ℝ ∞
      (Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m) := by
  have hcoefficientReal :
      ContDiff ℝ ∞
        (fun x : ℝ => -2 * Real.pi * x * (m : ℝ)) :=
    ((contDiff_const.mul contDiff_id).mul contDiff_const)
  have hcoefficientComplex :
      ContDiff ℝ ∞
        (fun x : ℝ => ((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcoefficientReal
  have hexponent :
      ContDiff ℝ ∞
        (fun x : ℝ =>
          ((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) :=
    hcoefficientComplex.mul contDiff_const
  have hfourierOscillation :
      ContDiff ℝ ∞
        (fun x : ℝ =>
          Complex.exp
            (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I)) :=
    hexponent.cexp
  have hrawProduct :
      ContDiff ℝ ∞
        (fun x : ℝ =>
          Complex.exp
              (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) *
            Complex.phaseCutoffFunction phase cutoff x) :=
    hfourierOscillation.mul hsmooth
  have hrawFunction :
      (fun x : ℝ =>
        Complex.exp
            (((-2 * Real.pi * x * (m : ℝ) : ℝ) : ℂ) * Complex.I) *
          Complex.phaseCutoffFunction phase cutoff x) =
        Complex.phaseCutoffFourierModeIntegrand phase cutoff m :=
    funext (fun _x : ℝ => rfl)
  have hraw :
      ContDiff ℝ ∞
        (Complex.phaseCutoffFourierModeIntegrand phase cutoff m) :=
    Eq.subst
      (motive := fun function : ℝ → ℂ => ContDiff ℝ ∞ function)
      hrawFunction
      hrawProduct
  have hfunctions :
      Complex.phaseCutoffFourierModeIntegrand phase cutoff m =
        Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m :=
    funext
      (fun x : ℝ =>
        Complex.phaseCutoffFourierModeIntegrand_eq_frequencyTwistIntegrand
          phase cutoff m x)
  exact
    Eq.subst
      (motive := fun function : ℝ → ℂ => ContDiff ℝ ∞ function)
      hfunctions
      hraw

/-- Whole-line integral normalization of a raw Fourier mode. -/
theorem Complex.integral_phaseCutoffFourierModeIntegrand_eq_frequencyTwist
    (phase cutoff : ℝ → ℝ)
    (m : ℤ) :
    (∫ x : ℝ,
        Complex.phaseCutoffFourierModeIntegrand phase cutoff m x) =
      ∫ x : ℝ,
        Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x := by
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall
      (fun x : ℝ =>
        Complex.phaseCutoffFourierModeIntegrand_eq_frequencyTwistIntegrand
          phase cutoff m x))

/-- Evaluation of the Schwartz Fourier transform as the raw Fourier-mode
integral. -/
theorem Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_integral
    (phase cutoff : ℝ → ℝ)
    (hsmooth : ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff))
    (hcutoffCompact : HasCompactSupport cutoff)
    (m : ℤ) :
    SchwartzMap.fourierTransformCLM ℝ
        (Complex.phaseCutoffSchwartzOfSmoothProduct
          phase cutoff hsmooth hcutoffCompact)
        (m : ℝ) =
      ∫ x : ℝ,
        Complex.phaseCutoffFourierModeIntegrand phase cutoff m x := by
  let extension : SchwartzMap ℝ ℂ :=
    Complex.phaseCutoffSchwartzOfSmoothProduct
      phase cutoff hsmooth hcutoffCompact
  have htransform :
      SchwartzMap.fourierTransformCLM ℝ extension =
        Real.fourierIntegral extension :=
    SchwartzMap.fourierTransformCLM_apply ℝ extension
  have hevaluation :
      SchwartzMap.fourierTransformCLM ℝ extension (m : ℝ) =
        Real.fourierIntegral extension (m : ℝ) :=
    congrArg (fun transformed : ℝ → ℂ => transformed (m : ℝ)) htransform
  have hintegral :=
    Real.fourierIntegral_real_eq_integral_exp_smul
      (fun x : ℝ => extension x) (m : ℝ)
  exact hevaluation.trans hintegral

/-- Evaluation under the stronger separate smoothness hypotheses. -/
theorem Complex.fourierTransform_phaseCutoffSchwartz_eq_integral
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (m : ℤ) :
    SchwartzMap.fourierTransformCLM ℝ
        (Complex.phaseCutoffSchwartz
          phase cutoff hphase hcutoffSmooth hcutoffCompact)
        (m : ℝ) =
      ∫ x : ℝ,
        Complex.phaseCutoffFourierModeIntegrand phase cutoff m x := by
  exact
    Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_integral
      phase cutoff
      (Complex.contDiff_phaseCutoffFunction
        phase cutoff hphase hcutoffSmooth)
      hcutoffCompact m

/-- The abstract Schwartz Fourier coefficient is the whole-line integral of
the canonical frequency-twisted cutoff oscillation. -/
theorem Complex.fourierTransform_phaseCutoffSchwartz_eq_frequencyTwistIntegral
    (phase cutoff : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (hcutoffSmooth : ContDiff ℝ ∞ cutoff)
    (hcutoffCompact : HasCompactSupport cutoff)
    (m : ℤ) :
    SchwartzMap.fourierTransformCLM ℝ
        (Complex.phaseCutoffSchwartz
          phase cutoff hphase hcutoffSmooth hcutoffCompact)
        (m : ℝ) =
      ∫ x : ℝ,
        Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x := by
  exact
    (Complex.fourierTransform_phaseCutoffSchwartz_eq_integral
      phase cutoff hphase hcutoffSmooth hcutoffCompact m).trans
      (Complex.integral_phaseCutoffFourierModeIntegrand_eq_frequencyTwist
        phase cutoff m)

/-- Product-smooth form of the canonical frequency-twist Fourier integral. -/
theorem Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_frequencyTwistIntegral
    (phase cutoff : ℝ → ℝ)
    (hsmooth : ContDiff ℝ ∞ (Complex.phaseCutoffFunction phase cutoff))
    (hcutoffCompact : HasCompactSupport cutoff)
    (m : ℤ) :
    SchwartzMap.fourierTransformCLM ℝ
        (Complex.phaseCutoffSchwartzOfSmoothProduct
          phase cutoff hsmooth hcutoffCompact)
        (m : ℝ) =
      ∫ x : ℝ,
        Complex.phaseCutoffFrequencyTwistIntegrand phase cutoff m x := by
  exact
    (Complex.fourierTransform_phaseCutoffSchwartzOfSmoothProduct_eq_integral
      phase cutoff hsmooth hcutoffCompact m).trans
      (Complex.integral_phaseCutoffFourierModeIntegrand_eq_frequencyTwist
        phase cutoff m)

end

end LFunctions
end Boundary

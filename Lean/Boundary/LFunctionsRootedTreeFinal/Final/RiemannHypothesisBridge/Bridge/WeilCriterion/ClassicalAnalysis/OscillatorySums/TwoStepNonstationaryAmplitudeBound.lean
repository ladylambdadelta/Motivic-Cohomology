import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryPhaseCoefficient

/-!
# Pointwise bound for the second nonstationary amplitude transform

Differentiating `A'c+Ac'` gives `A''c+2A'c'+Ac''`.  Multiplication by `c`
and addition of the second integration-by-parts product yields the canonical
four-term phase-gap majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.nonstationaryFirstTransformedDerivativeExplicit
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative
      phaseCoefficientSecondDerivative : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  amplitudeSecondDerivative x * phaseCoefficient x +
    2 * amplitudeDerivative x * phaseCoefficientDerivative x +
    amplitude x * phaseCoefficientSecondDerivative x

def Complex.nonstationarySecondTransformMajorant
    (amplitudeNorm amplitudeDerivativeNorm amplitudeSecondDerivativeNorm : ℝ)
    (phaseSecond phaseThird gap : ℝ) : ℝ :=
  amplitudeSecondDerivativeNorm / gap ^ 2 +
    3 * amplitudeDerivativeNorm * phaseSecond / gap ^ 3 +
    amplitudeNorm * phaseThird / gap ^ 3 +
    3 * amplitudeNorm * phaseSecond ^ 2 / gap ^ 4

theorem Complex.hasDerivAt_nonstationaryFirstTransformedAmplitude_explicit
    {amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ}
    {phaseCoefficient phaseCoefficientDerivative
      phaseCoefficientSecondDerivative : ℝ → ℂ}
    {x : ℝ}
    (hamplitude : HasDerivAt amplitude (amplitudeDerivative x) x)
    (hamplitudeDerivative :
      HasDerivAt amplitudeDerivative (amplitudeSecondDerivative x) x)
    (hcoefficient :
      HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x)
    (hcoefficientDerivative :
      HasDerivAt phaseCoefficientDerivative
        (phaseCoefficientSecondDerivative x) x) :
    HasDerivAt
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative)
      (Complex.nonstationaryFirstTransformedDerivativeExplicit
        amplitude amplitudeDerivative amplitudeSecondDerivative
        phaseCoefficient phaseCoefficientDerivative
        phaseCoefficientSecondDerivative x)
      x := by
  unfold Complex.nonstationaryFirstTransformedAmplitude
  unfold Complex.nonstationaryFirstTransformedDerivativeExplicit
  have hfirst := hamplitudeDerivative.mul hcoefficient
  have hsecond := hamplitude.mul hcoefficientDerivative
  have hsum := hfirst.add hsecond
  have hnormalize :
      (amplitudeSecondDerivative x * phaseCoefficient x +
          amplitudeDerivative x * phaseCoefficientDerivative x) +
        (amplitudeDerivative x * phaseCoefficientDerivative x +
          amplitude x * phaseCoefficientSecondDerivative x) =
      amplitudeSecondDerivative x * phaseCoefficient x +
        2 * amplitudeDerivative x * phaseCoefficientDerivative x +
        amplitude x * phaseCoefficientSecondDerivative x := by
    let first := amplitudeSecondDerivative x * phaseCoefficient x
    let middle := amplitudeDerivative x * phaseCoefficientDerivative x
    let last := amplitude x * phaseCoefficientSecondDerivative x
    calc
      (first + middle) + (middle + last) =
          first + (middle + middle) + last := by
        calc
          (first + middle) + (middle + last) =
              first + (middle + (middle + last)) :=
            add_assoc first middle (middle + last)
          _ = first + ((middle + middle) + last) :=
            congrArg (fun value : ℂ => first + value)
              (add_assoc middle middle last).symm
          _ = first + (middle + middle) + last :=
            (add_assoc first (middle + middle) last).symm
      _ = first + 2 * middle + last :=
        congrArg (fun value : ℂ => first + value + last)
          (two_mul middle).symm
      _ = amplitudeSecondDerivative x * phaseCoefficient x +
          2 * amplitudeDerivative x * phaseCoefficientDerivative x +
          amplitude x * phaseCoefficientSecondDerivative x := by
        have hfirst_eq : first =
            amplitudeSecondDerivative x * phaseCoefficient x := by
          rfl
        have hlast_eq : last =
            amplitude x * phaseCoefficientSecondDerivative x := by
          rfl
        have hmiddle_eq : middle =
            amplitudeDerivative x * phaseCoefficientDerivative x := by
          rfl
        have hmiddle_substitution :
            first + 2 * middle + last =
              first +
                2 * (amplitudeDerivative x * phaseCoefficientDerivative x) +
                last :=
          congrArg (fun value : ℂ => first + 2 * value + last) hmiddle_eq
        have hendpoint_substitution :
            first +
                2 * (amplitudeDerivative x * phaseCoefficientDerivative x) +
                last =
              amplitudeSecondDerivative x * phaseCoefficient x +
                2 * (amplitudeDerivative x * phaseCoefficientDerivative x) +
                amplitude x * phaseCoefficientSecondDerivative x :=
          congrArg₂
            (fun firstValue lastValue : ℂ =>
              firstValue +
                2 * (amplitudeDerivative x * phaseCoefficientDerivative x) +
                lastValue)
            hfirst_eq hlast_eq
        have hscalar_reassociate :
            amplitudeSecondDerivative x * phaseCoefficient x +
                2 * (amplitudeDerivative x * phaseCoefficientDerivative x) +
                amplitude x * phaseCoefficientSecondDerivative x =
              amplitudeSecondDerivative x * phaseCoefficient x +
                2 * amplitudeDerivative x * phaseCoefficientDerivative x +
                amplitude x * phaseCoefficientSecondDerivative x :=
          congrArg
            (fun value : ℂ =>
              amplitudeSecondDerivative x * phaseCoefficient x + value +
                amplitude x * phaseCoefficientSecondDerivative x)
            (mul_assoc (2 : ℂ) (amplitudeDerivative x)
              (phaseCoefficientDerivative x)).symm
        exact hmiddle_substitution.trans
          (hendpoint_substitution.trans hscalar_reassociate)
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasDerivAt
        (fun y : ℝ =>
          amplitudeDerivative y * phaseCoefficient y +
            amplitude y * phaseCoefficientDerivative y)
        value x)
    hnormalize
    hsum

theorem Complex.norm_firstTransformedDerivativeExplicit_le
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative
      phaseCoefficientSecondDerivative : ℝ → ℂ)
    (x : ℝ) :
    ‖Complex.nonstationaryFirstTransformedDerivativeExplicit
        amplitude amplitudeDerivative amplitudeSecondDerivative
        phaseCoefficient phaseCoefficientDerivative
        phaseCoefficientSecondDerivative x‖ ≤
      ‖amplitudeSecondDerivative x‖ * ‖phaseCoefficient x‖ +
        2 * ‖amplitudeDerivative x‖ * ‖phaseCoefficientDerivative x‖ +
        ‖amplitude x‖ * ‖phaseCoefficientSecondDerivative x‖ := by
  unfold Complex.nonstationaryFirstTransformedDerivativeExplicit
  have houter := norm_add_le
    (amplitudeSecondDerivative x * phaseCoefficient x +
      2 * amplitudeDerivative x * phaseCoefficientDerivative x)
    (amplitude x * phaseCoefficientSecondDerivative x)
  have hinner := norm_add_le
    (amplitudeSecondDerivative x * phaseCoefficient x)
    (2 * amplitudeDerivative x * phaseCoefficientDerivative x)
  have hfirst := norm_mul (amplitudeSecondDerivative x) (phaseCoefficient x)
  have hmiddle :
      ‖2 * amplitudeDerivative x * phaseCoefficientDerivative x‖ =
        2 * ‖amplitudeDerivative x‖ * ‖phaseCoefficientDerivative x‖ := by
    have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) :=
      (Complex.norm_real 2).trans
        (Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two))
    exact Eq.trans
      (norm_mul (2 * amplitudeDerivative x) (phaseCoefficientDerivative x))
      (congrArg
        (fun value : ℝ => value * ‖phaseCoefficientDerivative x‖)
        ((norm_mul 2 (amplitudeDerivative x)).trans
          (congrArg
            (fun value : ℝ => value * ‖amplitudeDerivative x‖)
            htwo_norm)))
  have hlast := norm_mul (amplitude x) (phaseCoefficientSecondDerivative x)
  exact le_trans houter
    (le_trans (add_le_add_right hinner _)
      (le_of_eq
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            hfirst hmiddle)
          hlast)))

theorem Complex.norm_nonstationarySecondTransformedAmplitude_le_components
    (firstTransformedDerivative amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ)
    (x : ℝ) :
    ‖Complex.nonstationarySecondTransformedAmplitude
        firstTransformedDerivative amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative x‖ ≤
      ‖firstTransformedDerivative x‖ * ‖phaseCoefficient x‖ +
        (‖amplitudeDerivative x‖ * ‖phaseCoefficient x‖ +
          ‖amplitude x‖ * ‖phaseCoefficientDerivative x‖) *
          ‖phaseCoefficientDerivative x‖ := by
  unfold Complex.nonstationarySecondTransformedAmplitude
  unfold Complex.nonstationaryFirstTransformedAmplitude
  have houter := norm_add_le
    (firstTransformedDerivative x * phaseCoefficient x)
    ((amplitudeDerivative x * phaseCoefficient x +
      amplitude x * phaseCoefficientDerivative x) *
      phaseCoefficientDerivative x)
  have hfirst := norm_mul (firstTransformedDerivative x) (phaseCoefficient x)
  have hproduct := norm_mul
    (amplitudeDerivative x * phaseCoefficient x +
      amplitude x * phaseCoefficientDerivative x)
    (phaseCoefficientDerivative x)
  have hsum := norm_add_le
    (amplitudeDerivative x * phaseCoefficient x)
    (amplitude x * phaseCoefficientDerivative x)
  have hsumProducts := add_le_add
    (le_of_eq (norm_mul (amplitudeDerivative x) (phaseCoefficient x)))
    (le_of_eq (norm_mul (amplitude x) (phaseCoefficientDerivative x)))
  have hsumBound := le_trans hsum hsumProducts
  have hscaled := mul_le_mul_of_nonneg_right hsumBound
    (norm_nonneg (phaseCoefficientDerivative x))
  exact le_trans houter
    (le_trans
      (add_le_add (le_of_eq hfirst)
        (le_trans (le_of_eq hproduct) hscaled))
      (le_refl _))

end
end LFunctions
end Boundary

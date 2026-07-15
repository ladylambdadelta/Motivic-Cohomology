import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryAmplitudeBound

/-!
# Raw phase-gap majorant for the second amplitude transform

This owner substitutes the exact norms of `c` and `c'` and the proved upper
bound for `c''` into the componentwise transform estimate.  No coefficient
collection is performed here, so every analytic contribution remains visible.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.nonstationaryFirstDerivativeRawMajorant
    (amplitudeNorm amplitudeDerivativeNorm amplitudeSecondDerivativeNorm : ℝ)
    (phaseSecond phaseThird gap : ℝ) : ℝ :=
  amplitudeSecondDerivativeNorm * gap⁻¹ +
    2 * amplitudeDerivativeNorm * (phaseSecond / gap ^ 2) +
    amplitudeNorm *
      (phaseThird / gap ^ 2 + 2 * phaseSecond ^ 2 / gap ^ 3)

def Complex.nonstationarySecondTransformRawMajorant
    (amplitudeNorm amplitudeDerivativeNorm amplitudeSecondDerivativeNorm : ℝ)
    (phaseSecond phaseThird gap : ℝ) : ℝ :=
  Complex.nonstationaryFirstDerivativeRawMajorant
      amplitudeNorm amplitudeDerivativeNorm amplitudeSecondDerivativeNorm
      phaseSecond phaseThird gap * gap⁻¹ +
    (amplitudeDerivativeNorm * gap⁻¹ +
      amplitudeNorm * (phaseSecond / gap ^ 2)) *
      (phaseSecond / gap ^ 2)

theorem Complex.nonstationaryFirstDerivativeRawMajorant_nonneg
    {A A₁ A₂ v w g : ℝ}
    (hA : 0 ≤ A)
    (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂)
    (hv : 0 ≤ v)
    (hw : 0 ≤ w)
    (hg : 0 ≤ g) :
    0 ≤ Complex.nonstationaryFirstDerivativeRawMajorant A A₁ A₂ v w g := by
  unfold Complex.nonstationaryFirstDerivativeRawMajorant
  have hginv : 0 ≤ g⁻¹ := inv_nonneg.mpr hg
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hg3 : 0 ≤ g ^ 3 := pow_nonneg hg 3
  have hfirst := mul_nonneg hA₂ hginv
  have hsecond := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg 2) hA₁)
    (div_nonneg hv hg2)
  have hthirdInside := add_nonneg
    (div_nonneg hw hg2)
    (div_nonneg
      (mul_nonneg (Nat.cast_nonneg 2) (sq_nonneg v)) hg3)
  have hthird := mul_nonneg hA hthirdInside
  exact add_nonneg (add_nonneg hfirst hsecond) hthird

theorem Complex.nonstationarySecondTransformRawMajorant_nonneg
    {A A₁ A₂ v w g : ℝ}
    (hA : 0 ≤ A)
    (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂)
    (hv : 0 ≤ v)
    (hw : 0 ≤ w)
    (hg : 0 ≤ g) :
    0 ≤ Complex.nonstationarySecondTransformRawMajorant A A₁ A₂ v w g := by
  unfold Complex.nonstationarySecondTransformRawMajorant
  have hginv : 0 ≤ g⁻¹ := inv_nonneg.mpr hg
  have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
  have hfirst := mul_nonneg
    (Complex.nonstationaryFirstDerivativeRawMajorant_nonneg
      hA hA₁ hA₂ hv hw hg)
    hginv
  have hinside := add_nonneg
    (mul_nonneg hA₁ hginv)
    (mul_nonneg hA (div_nonneg hv hg2))
  have hlast := mul_nonneg hinside (div_nonneg hv hg2)
  exact add_nonneg hfirst hlast

theorem Complex.norm_firstTransformedDerivativeExplicit_le_rawMajorant
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (φ' φ'' φ''' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.nonstationaryFirstTransformedDerivativeExplicit
        amplitude amplitudeDerivative amplitudeSecondDerivative
        (Complex.realPhaseIntegrationCoefficient φ')
        (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
        (Complex.realPhaseIntegrationCoefficientSecondDerivative
          φ' φ'' φ''') x‖ ≤
      Complex.nonstationaryFirstDerivativeRawMajorant
        ‖amplitude x‖ ‖amplitudeDerivative x‖
        ‖amplitudeSecondDerivative x‖
        |φ'' x| |φ''' x| ‖φ' x‖ := by
  have hcomponents :=
    Complex.norm_firstTransformedDerivativeExplicit_le
      amplitude amplitudeDerivative amplitudeSecondDerivative
      (Complex.realPhaseIntegrationCoefficient φ')
      (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
      (Complex.realPhaseIntegrationCoefficientSecondDerivative φ' φ'' φ''') x
  have hc := Complex.norm_realPhaseIntegrationCoefficient φ' x
  have hc' := Complex.norm_realPhaseIntegrationCoefficientDerivative φ' φ'' x
  have hc'' :=
    Complex.norm_realPhaseIntegrationCoefficientSecondDerivative_le
      φ' φ'' φ''' x
  unfold Complex.nonstationaryFirstDerivativeRawMajorant
  have hfirst := mul_le_mul_of_nonneg_left (le_of_eq hc)
    (norm_nonneg (amplitudeSecondDerivative x))
  have hsecond := mul_le_mul_of_nonneg_left (le_of_eq hc')
    (mul_nonneg (Nat.cast_nonneg 2) (norm_nonneg (amplitudeDerivative x)))
  have hthird := mul_le_mul_of_nonneg_left hc'' (norm_nonneg (amplitude x))
  exact le_trans hcomponents
    (add_le_add (add_le_add hfirst hsecond) hthird)

theorem Complex.norm_nonstationarySecondTransform_le_rawMajorant
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (φ' φ'' φ''' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.nonstationarySecondTransformedAmplitude
        (Complex.nonstationaryFirstTransformedDerivativeExplicit
          amplitude amplitudeDerivative amplitudeSecondDerivative
          (Complex.realPhaseIntegrationCoefficient φ')
          (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
          (Complex.realPhaseIntegrationCoefficientSecondDerivative
            φ' φ'' φ'''))
        amplitude amplitudeDerivative
        (Complex.realPhaseIntegrationCoefficient φ')
        (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'') x‖ ≤
      Complex.nonstationarySecondTransformRawMajorant
        ‖amplitude x‖ ‖amplitudeDerivative x‖
        ‖amplitudeSecondDerivative x‖
        |φ'' x| |φ''' x| ‖φ' x‖ := by
  let B' := Complex.nonstationaryFirstTransformedDerivativeExplicit
    amplitude amplitudeDerivative amplitudeSecondDerivative
    (Complex.realPhaseIntegrationCoefficient φ')
    (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
    (Complex.realPhaseIntegrationCoefficientSecondDerivative φ' φ'' φ''')
  have hcomponents :=
    Complex.norm_nonstationarySecondTransformedAmplitude_le_components
      B' amplitude amplitudeDerivative
      (Complex.realPhaseIntegrationCoefficient φ')
      (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'') x
  have hB :=
    Complex.norm_firstTransformedDerivativeExplicit_le_rawMajorant
      amplitude amplitudeDerivative amplitudeSecondDerivative φ' φ'' φ''' x
  have hc := Complex.norm_realPhaseIntegrationCoefficient φ' x
  have hc' := Complex.norm_realPhaseIntegrationCoefficientDerivative φ' φ'' x
  have hrawNonneg : 0 ≤
      Complex.nonstationaryFirstDerivativeRawMajorant
        ‖amplitude x‖ ‖amplitudeDerivative x‖
        ‖amplitudeSecondDerivative x‖
        |φ'' x| |φ''' x| ‖φ' x‖ :=
    Complex.nonstationaryFirstDerivativeRawMajorant_nonneg
      (norm_nonneg (amplitude x))
      (norm_nonneg (amplitudeDerivative x))
      (norm_nonneg (amplitudeSecondDerivative x))
      (abs_nonneg (φ'' x))
      (abs_nonneg (φ''' x))
      (norm_nonneg (φ' x))
  unfold Complex.nonstationarySecondTransformRawMajorant
  have hfirst := mul_le_mul hB (le_of_eq hc)
    (norm_nonneg _) hrawNonneg
  have hinside := add_le_add
    (mul_le_mul_of_nonneg_left (le_of_eq hc)
      (norm_nonneg (amplitudeDerivative x)))
    (mul_le_mul_of_nonneg_left (le_of_eq hc')
      (norm_nonneg (amplitude x)))
  have hgapInverse : 0 ≤ ‖φ' x‖⁻¹ :=
    inv_nonneg.mpr (norm_nonneg (φ' x))
  have hphaseQuotient : 0 ≤ |φ'' x| / ‖φ' x‖ ^ 2 :=
    div_nonneg (abs_nonneg (φ'' x)) (sq_nonneg ‖φ' x‖)
  have hinsideUpper : 0 ≤
      ‖amplitudeDerivative x‖ * ‖φ' x‖⁻¹ +
        ‖amplitude x‖ * (|φ'' x| / ‖φ' x‖ ^ 2) :=
    add_nonneg
      (mul_nonneg (norm_nonneg (amplitudeDerivative x)) hgapInverse)
      (mul_nonneg (norm_nonneg (amplitude x)) hphaseQuotient)
  have hlast := mul_le_mul hinside (le_of_eq hc')
    (norm_nonneg _) hinsideUpper
  exact le_trans hcomponents (add_le_add hfirst hlast)

end
end LFunctions
end Boundary

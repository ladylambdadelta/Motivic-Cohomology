import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.NonstationaryPhase

/-!
# Two-step nonstationary integration by parts with amplitude

For a complex amplitude `A`, phase reciprocal coefficient `c`, and oscillator
`u` satisfying `c*u'=u`, define the first transformed amplitude `(A*c)'` and
iterate integration by parts.  When `A*c` and `(A*c)'*c` vanish at both
endpoints, the original oscillatory integral equals the integral of the second
transformed amplitude.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.nonstationaryFirstCoefficient
    (amplitude phaseCoefficient : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  amplitude x * phaseCoefficient x

def Complex.nonstationaryFirstTransformedAmplitude
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  amplitudeDerivative x * phaseCoefficient x +
    amplitude x * phaseCoefficientDerivative x

def Complex.nonstationarySecondCoefficient
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  Complex.nonstationaryFirstTransformedAmplitude
    amplitude amplitudeDerivative phaseCoefficient
    phaseCoefficientDerivative x * phaseCoefficient x

def Complex.nonstationarySecondTransformedAmplitude
    (firstTransformedDerivative : ℝ → ℂ)
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ)
    (x : ℝ) : ℂ :=
  firstTransformedDerivative x * phaseCoefficient x +
    Complex.nonstationaryFirstTransformedAmplitude
      amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative x * phaseCoefficientDerivative x

theorem Complex.hasDerivAt_nonstationaryFirstCoefficient
    {amplitude amplitudeDerivative : ℝ → ℂ}
    {phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ}
    {x : ℝ}
    (hamplitude : HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x) :
    HasDerivAt
      (Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient)
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative x)
      x := by
  unfold Complex.nonstationaryFirstCoefficient
  unfold Complex.nonstationaryFirstTransformedAmplitude
  exact hamplitude.mul hcoefficient

theorem Complex.hasDerivAt_nonstationarySecondCoefficient
    {amplitude amplitudeDerivative : ℝ → ℂ}
    {phaseCoefficient phaseCoefficientDerivative : ℝ → ℂ}
    {firstTransformedDerivative : ℝ → ℂ}
    {x : ℝ}
    (hfirst :
      HasDerivAt
        (Complex.nonstationaryFirstTransformedAmplitude
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative)
        (firstTransformedDerivative x) x)
    (hcoefficient :
      HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x) :
    HasDerivAt
      (Complex.nonstationarySecondCoefficient
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative)
      (Complex.nonstationarySecondTransformedAmplitude
        firstTransformedDerivative amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative x)
      x := by
  unfold Complex.nonstationarySecondCoefficient
  unfold Complex.nonstationarySecondTransformedAmplitude
  exact hfirst.mul hcoefficient

theorem Complex.nonstationaryFirstCoefficient_mul_oscillatorDerivative
    (amplitude phaseCoefficient oscillator oscillatorDerivative : ℝ → ℂ)
    (x : ℝ)
    (hcancellation :
      phaseCoefficient x * oscillatorDerivative x = oscillator x) :
    Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient x *
        oscillatorDerivative x =
      amplitude x * oscillator x := by
  unfold Complex.nonstationaryFirstCoefficient
  exact Eq.trans
    (mul_assoc (amplitude x) (phaseCoefficient x) (oscillatorDerivative x))
    (congrArg (fun value : ℂ => amplitude x * value) hcancellation)

theorem Complex.nonstationarySecondCoefficient_mul_oscillatorDerivative
    (amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative oscillator oscillatorDerivative : ℝ → ℂ)
    (x : ℝ)
    (hcancellation :
      phaseCoefficient x * oscillatorDerivative x = oscillator x) :
    Complex.nonstationarySecondCoefficient
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative x * oscillatorDerivative x =
      Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative x * oscillator x := by
  unfold Complex.nonstationarySecondCoefficient
  exact Eq.trans
    (mul_assoc
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative x)
      (phaseCoefficient x) (oscillatorDerivative x))
    (congrArg
      (fun value : ℂ =>
        Complex.nonstationaryFirstTransformedAmplitude
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative x * value)
      hcancellation)

theorem Complex.intervalIntegral_amplitude_oscillator_eq_first_boundary_sub
    (amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative oscillator oscillatorDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x)
    (hoscillator :
      ∀ x ∈ [[left, right]],
        HasDerivAt oscillator (oscillatorDerivative x) x)
    (hfirstIntegrable : IntervalIntegrable
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative) volume left right)
    (hoscillatorDerivativeIntegrable :
      IntervalIntegrable oscillatorDerivative volume left right)
    (hcancellation :
      ∀ x ∈ [[left, right]],
        phaseCoefficient x * oscillatorDerivative x = oscillator x) :
    (∫ x in left..right, amplitude x * oscillator x) =
      Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient right *
          oscillator right -
        Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient left *
          oscillator left -
        ∫ x in left..right,
          Complex.nonstationaryFirstTransformedAmplitude
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative x * oscillator x := by
  have hfirstCoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient)
          (Complex.nonstationaryFirstTransformedAmplitude
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative x) x :=
    fun x hx => Complex.hasDerivAt_nonstationaryFirstCoefficient
      (hamplitude x hx) (hcoefficient x hx)
  have hintegration := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hfirstCoefficient hoscillator hfirstIntegrable
    hoscillatorDerivativeIntegrable
  have hintegrand :
      (∫ x in left..right,
        Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient x *
          oscillatorDerivative x) =
      ∫ x in left..right, amplitude x * oscillator x :=
    intervalIntegral.integral_congr
      (fun x hx =>
        Complex.nonstationaryFirstCoefficient_mul_oscillatorDerivative
          amplitude phaseCoefficient oscillator oscillatorDerivative
          x (hcancellation x hx))
  exact hintegrand.symm.trans hintegration

theorem Complex.intervalIntegral_amplitude_oscillator_eq_second_remainder
    (amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative firstTransformedDerivative
      oscillator oscillatorDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x)
    (hfirst :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.nonstationaryFirstTransformedAmplitude
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative)
          (firstTransformedDerivative x) x)
    (hoscillator :
      ∀ x ∈ [[left, right]],
        HasDerivAt oscillator (oscillatorDerivative x) x)
    (hfirstIntegrable : IntervalIntegrable
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative) volume left right)
    (hsecondIntegrable : IntervalIntegrable
      (Complex.nonstationarySecondTransformedAmplitude
        firstTransformedDerivative amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative) volume left right)
    (hoscillatorDerivativeIntegrable :
      IntervalIntegrable oscillatorDerivative volume left right)
    (hcancellation :
      ∀ x ∈ [[left, right]],
        phaseCoefficient x * oscillatorDerivative x = oscillator x)
    (hfirstLeft :
      Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient left = 0)
    (hfirstRight :
      Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient right = 0)
    (hsecondLeft :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative left = 0)
    (hsecondRight :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative right = 0) :
    (∫ x in left..right, amplitude x * oscillator x) =
      ∫ x in left..right,
        Complex.nonstationarySecondTransformedAmplitude
          firstTransformedDerivative amplitude amplitudeDerivative
          phaseCoefficient phaseCoefficientDerivative x * oscillator x := by
  have hfirstIdentity :=
    Complex.intervalIntegral_amplitude_oscillator_eq_first_boundary_sub
      amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative oscillator oscillatorDerivative
      left right hamplitude hcoefficient hoscillator hfirstIntegrable
      hoscillatorDerivativeIntegrable hcancellation
  have hsecondCoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
            phaseCoefficient phaseCoefficientDerivative)
          (Complex.nonstationarySecondTransformedAmplitude
            firstTransformedDerivative amplitude amplitudeDerivative
            phaseCoefficient phaseCoefficientDerivative x) x :=
    fun x hx => Complex.hasDerivAt_nonstationarySecondCoefficient
      (hfirst x hx) (hcoefficient x hx)
  have hsecondIdentity :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      hsecondCoefficient hoscillator hsecondIntegrable
      hoscillatorDerivativeIntegrable
  have hsecondIntegrand :
      (∫ x in left..right,
        Complex.nonstationarySecondCoefficient
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative x * oscillatorDerivative x) =
      ∫ x in left..right,
        Complex.nonstationaryFirstTransformedAmplitude
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative x * oscillator x :=
    intervalIntegral.integral_congr
      (fun x hx =>
        Complex.nonstationarySecondCoefficient_mul_oscillatorDerivative
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative oscillator oscillatorDerivative
          x (hcancellation x hx))
  have hsecondNormalized :
      (∫ x in left..right,
        Complex.nonstationaryFirstTransformedAmplitude
          amplitude amplitudeDerivative phaseCoefficient
          phaseCoefficientDerivative x * oscillator x) =
        Complex.nonstationarySecondCoefficient
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative right * oscillator right -
          Complex.nonstationarySecondCoefficient
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative left * oscillator left -
          ∫ x in left..right,
            Complex.nonstationarySecondTransformedAmplitude
              firstTransformedDerivative amplitude amplitudeDerivative
              phaseCoefficient phaseCoefficientDerivative x * oscillator x :=
    hsecondIntegrand.symm.trans hsecondIdentity
  exact Eq.trans hfirstIdentity
    (by
      have hfirstBoundaries :
          Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient right *
              oscillator right -
            Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient left *
              oscillator left = 0 := by
        exact Eq.trans
          (congrArg₂ (fun first second : ℂ =>
            first * oscillator right - second * oscillator left)
            hfirstRight hfirstLeft)
          ((congrArg₂ (fun first second : ℂ => first - second)
            (zero_mul _) (zero_mul _)).trans (sub_self 0))
      have hsecondBoundaries :
          Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
                phaseCoefficient phaseCoefficientDerivative right * oscillator right -
            Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
                phaseCoefficient phaseCoefficientDerivative left * oscillator left = 0 := by
        exact Eq.trans
          (congrArg₂ (fun first second : ℂ =>
            first * oscillator right - second * oscillator left)
            hsecondRight hsecondLeft)
          ((congrArg₂ (fun first second : ℂ => first - second)
            (zero_mul _) (zero_mul _)).trans (sub_self 0))
      exact Eq.trans
        (congrArg (fun boundary : ℂ => boundary -
          (∫ x in left..right,
            Complex.nonstationaryFirstTransformedAmplitude
              amplitude amplitudeDerivative phaseCoefficient
              phaseCoefficientDerivative x * oscillator x))
          hfirstBoundaries)
        (Eq.trans
          (zero_sub _)
          (Eq.trans
            (congrArg Neg.neg hsecondNormalized)
            (Eq.trans
              (congrArg (fun boundary : ℂ =>
                -(boundary -
                  ∫ x in left..right,
                    Complex.nonstationarySecondTransformedAmplitude
                      firstTransformedDerivative amplitude amplitudeDerivative
                      phaseCoefficient phaseCoefficientDerivative x * oscillator x))
                hsecondBoundaries)
              (Eq.trans (congrArg Neg.neg (zero_sub _)) (neg_neg _))))))

theorem Complex.norm_intervalIntegral_amplitude_oscillator_le_second_transform
    (amplitude amplitudeDerivative phaseCoefficient
      phaseCoefficientDerivative firstTransformedDerivative
      oscillator oscillatorDerivative : ℝ → ℂ)
    (left right : ℝ)
    (hleftRight : left ≤ right)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hcoefficient :
      ∀ x ∈ [[left, right]],
        HasDerivAt phaseCoefficient (phaseCoefficientDerivative x) x)
    (hfirst :
      ∀ x ∈ [[left, right]],
        HasDerivAt
          (Complex.nonstationaryFirstTransformedAmplitude
            amplitude amplitudeDerivative phaseCoefficient
            phaseCoefficientDerivative)
          (firstTransformedDerivative x) x)
    (hoscillator :
      ∀ x ∈ [[left, right]],
        HasDerivAt oscillator (oscillatorDerivative x) x)
    (hfirstIntegrable : IntervalIntegrable
      (Complex.nonstationaryFirstTransformedAmplitude
        amplitude amplitudeDerivative phaseCoefficient
        phaseCoefficientDerivative) volume left right)
    (hsecondIntegrable : IntervalIntegrable
      (Complex.nonstationarySecondTransformedAmplitude
        firstTransformedDerivative amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative) volume left right)
    (hoscillatorDerivativeIntegrable :
      IntervalIntegrable oscillatorDerivative volume left right)
    (hcancellation :
      ∀ x ∈ [[left, right]],
        phaseCoefficient x * oscillatorDerivative x = oscillator x)
    (hfirstLeft :
      Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient left = 0)
    (hfirstRight :
      Complex.nonstationaryFirstCoefficient amplitude phaseCoefficient right = 0)
    (hsecondLeft :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative left = 0)
    (hsecondRight :
      Complex.nonstationarySecondCoefficient amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative right = 0)
    (hoscillatorNorm : ∀ x : ℝ, ‖oscillator x‖ = 1) :
    ‖∫ x in left..right, amplitude x * oscillator x‖ ≤
      ∫ x in left..right,
        ‖Complex.nonstationarySecondTransformedAmplitude
          firstTransformedDerivative amplitude amplitudeDerivative
          phaseCoefficient phaseCoefficientDerivative x‖ := by
  have hidentity :=
    Complex.intervalIntegral_amplitude_oscillator_eq_second_remainder
      amplitude amplitudeDerivative phaseCoefficient phaseCoefficientDerivative
      firstTransformedDerivative oscillator oscillatorDerivative left right
      hamplitude hcoefficient hfirst hoscillator hfirstIntegrable
      hsecondIntegrable hoscillatorDerivativeIntegrable hcancellation
      hfirstLeft hfirstRight hsecondLeft hsecondRight
  have hnorm := intervalIntegral.norm_integral_le_integral_norm hleftRight
    (f := fun x =>
      Complex.nonstationarySecondTransformedAmplitude
        firstTransformedDerivative amplitude amplitudeDerivative
        phaseCoefficient phaseCoefficientDerivative x * oscillator x)
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx =>
      Eq.trans
        (norm_mul
          (Complex.nonstationarySecondTransformedAmplitude
            firstTransformedDerivative amplitude amplitudeDerivative
            phaseCoefficient phaseCoefficientDerivative x)
          (oscillator x))
        (Eq.trans
          (congrArg
            (fun value : ℝ =>
              ‖Complex.nonstationarySecondTransformedAmplitude
                firstTransformedDerivative amplitude amplitudeDerivative
                phaseCoefficient phaseCoefficientDerivative x‖ * value)
            (hoscillatorNorm x))
          (mul_one _)))
  exact le_trans (le_of_eq (congrArg norm hidentity))
    (le_trans hnorm (le_of_eq hintegrand))

end
end LFunctions
end Boundary

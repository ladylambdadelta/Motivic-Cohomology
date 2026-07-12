import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.AmplitudeNonstationaryPhase

/-!
# Two-step decay for a linear Fourier phase

This owner isolates the repeated integration-by-parts calculation used by the
far-frequency logarithmic Poisson packets.  The phase is linear, hence its
reciprocal integration coefficient is constant.  Two integrations by parts
therefore move both derivatives onto the amplitude and produce the exact
inverse-square frequency factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.linearFourierPhase (frequency : ℝ) (x : ℝ) : ℝ :=
  frequency * x

def Complex.linearFourierPhaseDerivative (frequency : ℝ) (_x : ℝ) : ℝ :=
  frequency

def Complex.linearFourierOscillationDerivative
    (frequency : ℝ) (x : ℝ) : ℂ :=
  Complex.realPhaseOscillation (Complex.linearFourierPhase frequency) x *
    Complex.realPhaseDerivativeDenominator
      (Complex.linearFourierPhaseDerivative frequency) x

def Complex.linearFourierCoefficient (frequency : ℝ) : ℂ :=
  (Complex.I * (frequency : ℂ))⁻¹

def Complex.linearFourierFirstAmplitude
    (amplitudeDerivative : ℝ → ℂ)
    (frequency : ℝ)
    (x : ℝ) : ℂ :=
  amplitudeDerivative x * Complex.linearFourierCoefficient frequency

def Complex.linearFourierSecondAmplitude
    (amplitudeSecondDerivative : ℝ → ℂ)
    (frequency : ℝ)
    (x : ℝ) : ℂ :=
  amplitudeSecondDerivative x * Complex.linearFourierCoefficient frequency

theorem Complex.linearFourierPhase_hasDerivAt
    (frequency x : ℝ) :
    HasDerivAt
      (Complex.linearFourierPhase frequency)
      (Complex.linearFourierPhaseDerivative frequency x)
      x := by
  exact (hasDerivAt_id x).const_mul frequency

theorem Complex.linearFourierPhaseDerivative_hasDerivAt
    (frequency x : ℝ) :
    HasDerivAt
      (Complex.linearFourierPhaseDerivative frequency)
      0
      x := by
  exact hasDerivAt_const x frequency

theorem Complex.linearFourierCoefficient_eq_integrationCoefficient
    (frequency x : ℝ) :
    Complex.linearFourierCoefficient frequency =
      Complex.realPhaseIntegrationCoefficient
        (Complex.linearFourierPhaseDerivative frequency) x := by
  rfl

theorem Complex.linearFourierCoefficient_hasDerivAt
    (frequency x : ℝ) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient
        (Complex.linearFourierPhaseDerivative frequency))
      0
      x := by
  have hconstant :
      Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) =
        fun _y : ℝ => Complex.linearFourierCoefficient frequency := by
    funext y
    exact
      (Complex.linearFourierCoefficient_eq_integrationCoefficient
        frequency y).symm
  have hderivative :
      HasDerivAt
        (fun _y : ℝ => Complex.linearFourierCoefficient frequency)
        0
        x :=
    hasDerivAt_const x (Complex.linearFourierCoefficient frequency)
  exact Eq.subst (motive := fun f : ℝ → ℂ => HasDerivAt f 0 x)
    hconstant.symm hderivative

theorem Complex.linearFourierOscillation_hasDerivAt
    (frequency x : ℝ) :
    HasDerivAt
      (Complex.realPhaseOscillation
        (Complex.linearFourierPhase frequency))
      (Complex.linearFourierOscillationDerivative frequency x)
      x := by
  exact
    Complex.hasDerivAt_realPhaseOscillation
      (Complex.linearFourierPhase_hasDerivAt frequency x)

theorem Complex.linearFourierOscillationDerivative_eq
    (frequency x : ℝ) :
    Complex.linearFourierOscillationDerivative frequency x =
      Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) x *
        Complex.realPhaseDerivativeDenominator
          (Complex.linearFourierPhaseDerivative frequency) x := by
  rfl

theorem Complex.linearFourierDenominator_ne_zero
    (frequency x : ℝ)
    (hfrequency : frequency ≠ 0) :
    Complex.realPhaseDerivativeDenominator
      (Complex.linearFourierPhaseDerivative frequency) x ≠ 0 := by
  intro hzero
  have hnorm := congrArg norm hzero
  have hfrequencyNorm : ‖frequency‖ = 0 :=
    Eq.trans
      (Complex.norm_realPhaseDerivativeDenominator
        (Complex.linearFourierPhaseDerivative frequency) x).symm
      (Eq.trans hnorm norm_zero)
  have hfrequencyZero : frequency = 0 := norm_eq_zero.mp hfrequencyNorm
  exact hfrequency hfrequencyZero

theorem Complex.linearFourierAmplitudeCoefficient_eq_firstAmplitude
    (amplitude amplitudeDerivative : ℝ → ℂ)
    (frequency x : ℝ) :
    Complex.realPhaseAmplitudeCoefficientDerivative
        amplitude amplitudeDerivative (fun _y : ℝ => 0)
        (Complex.linearFourierPhaseDerivative frequency) x =
      Complex.linearFourierFirstAmplitude amplitudeDerivative frequency x := by
  unfold Complex.realPhaseAmplitudeCoefficientDerivative
  unfold Complex.linearFourierFirstAmplitude
  have hcoefficient :=
    (Complex.linearFourierCoefficient_eq_integrationCoefficient frequency x).symm
  calc
    amplitudeDerivative x *
          Complex.realPhaseIntegrationCoefficient
            (Complex.linearFourierPhaseDerivative frequency) x +
        amplitude x * 0 =
      amplitudeDerivative x *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) x :=
      add_zero _
    _ = amplitudeDerivative x * Complex.linearFourierCoefficient frequency :=
      congrArg (fun value : ℂ => amplitudeDerivative x * value) hcoefficient

theorem Complex.linearFourierFirstAmplitude_hasDerivAt
    (amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (frequency x : ℝ)
    (hamplitude :
      HasDerivAt amplitudeDerivative (amplitudeSecondDerivative x) x) :
    HasDerivAt
      (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
      (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency x)
      x := by
  have hconstant :
      HasDerivAt
        (fun _y : ℝ => Complex.linearFourierCoefficient frequency)
        0
        x :=
    hasDerivAt_const x (Complex.linearFourierCoefficient frequency)
  have hproduct := hamplitude.mul hconstant
  have hvalue :
      amplitudeSecondDerivative x * Complex.linearFourierCoefficient frequency +
          amplitudeDerivative x * 0 =
        Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency x := by
    exact
      (add_zero
        (amplitudeSecondDerivative x *
          Complex.linearFourierCoefficient frequency)).trans rfl
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasDerivAt
        (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
        value x)
    hvalue hproduct

theorem Complex.linearFourierFirstAmplitudeCoefficientDerivative_eq_secondAmplitude
    (amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (frequency x : ℝ) :
    Complex.realPhaseAmplitudeCoefficientDerivative
        (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
        (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
        (fun _y : ℝ => 0)
        (Complex.linearFourierPhaseDerivative frequency) x =
      amplitudeSecondDerivative x *
        (Complex.linearFourierCoefficient frequency) ^ 2 := by
  unfold Complex.realPhaseAmplitudeCoefficientDerivative
  unfold Complex.linearFourierSecondAmplitude
  unfold Complex.linearFourierFirstAmplitude
  have hcoefficient :=
    (Complex.linearFourierCoefficient_eq_integrationCoefficient frequency x).symm
  calc
    amplitudeSecondDerivative x * Complex.linearFourierCoefficient frequency *
          Complex.realPhaseIntegrationCoefficient
            (Complex.linearFourierPhaseDerivative frequency) x +
        amplitudeDerivative x * Complex.linearFourierCoefficient frequency * 0 =
      amplitudeSecondDerivative x * Complex.linearFourierCoefficient frequency *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) x :=
      add_zero _
    _ = amplitudeSecondDerivative x * Complex.linearFourierCoefficient frequency *
        Complex.linearFourierCoefficient frequency :=
      congrArg
        (fun value : ℂ =>
          amplitudeSecondDerivative x *
            Complex.linearFourierCoefficient frequency * value)
        hcoefficient
    _ = amplitudeSecondDerivative x *
        (Complex.linearFourierCoefficient frequency) ^ 2 := by
      exact
        (mul_assoc
          (amplitudeSecondDerivative x)
          (Complex.linearFourierCoefficient frequency)
          (Complex.linearFourierCoefficient frequency)).trans
          (congrArg
            (fun value : ℂ => amplitudeSecondDerivative x * value)
            (pow_two (Complex.linearFourierCoefficient frequency)).symm)

theorem Complex.linearFourierCoefficient_norm
    (frequency : ℝ) :
    ‖Complex.linearFourierCoefficient frequency‖ = ‖frequency‖⁻¹ := by
  have hcoefficient :
      Complex.linearFourierCoefficient frequency =
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) 0 :=
    Complex.linearFourierCoefficient_eq_integrationCoefficient frequency 0
  exact
    (congrArg norm hcoefficient).trans
      (Complex.norm_realPhaseIntegrationCoefficient
        (Complex.linearFourierPhaseDerivative frequency) 0)

theorem Complex.linearFourierCoefficient_sq_norm
    (frequency : ℝ) :
    ‖(Complex.linearFourierCoefficient frequency) ^ 2‖ =
      ‖frequency‖⁻¹ ^ 2 := by
  exact
    (norm_pow (Complex.linearFourierCoefficient frequency) 2).trans
      (congrArg (fun value : ℝ => value ^ 2)
        (Complex.linearFourierCoefficient_norm frequency))

theorem Complex.linearFourier_secondDerivative_integrand_norm
    (amplitudeSecondDerivative : ℝ → ℂ)
    (frequency x : ℝ) :
    ‖amplitudeSecondDerivative x *
        (Complex.linearFourierCoefficient frequency) ^ 2‖ =
      ‖amplitudeSecondDerivative x‖ * ‖frequency‖⁻¹ ^ 2 := by
  exact
    (norm_mul
      (amplitudeSecondDerivative x)
      ((Complex.linearFourierCoefficient frequency) ^ 2)).trans
      (congrArg
        (fun value : ℝ => ‖amplitudeSecondDerivative x‖ * value)
        (Complex.linearFourierCoefficient_sq_norm frequency))

theorem Complex.intervalIntegral_linearFourier_eq_secondDerivative
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (frequency left right : ℝ)
    (hfrequency : frequency ≠ 0)
    (hamplitude :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitude (amplitudeDerivative x) x)
    (hamplitudeDerivative :
      ∀ x ∈ [[left, right]],
        HasDerivAt amplitudeDerivative (amplitudeSecondDerivative x) x)
    (hfirstIntegrable :
      IntervalIntegrable
        (Complex.realPhaseAmplitudeCoefficientDerivative
          amplitude amplitudeDerivative (fun _x : ℝ => 0)
          (Complex.linearFourierPhaseDerivative frequency))
        volume left right)
    (hsecondIntegrable :
      IntervalIntegrable
        (Complex.realPhaseAmplitudeCoefficientDerivative
          (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
          (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
          (fun _x : ℝ => 0)
          (Complex.linearFourierPhaseDerivative frequency))
        volume left right)
    (hoscillationDerivativeIntegrable :
      IntervalIntegrable
        (Complex.linearFourierOscillationDerivative frequency)
        volume left right)
    (hamplitudeLeft : amplitude left = 0)
    (hamplitudeRight : amplitude right = 0)
    (hamplitudeDerivativeLeft : amplitudeDerivative left = 0)
    (hamplitudeDerivativeRight : amplitudeDerivative right = 0) :
    (∫ x in left..right,
        amplitude x *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x) =
      ∫ x in left..right,
        amplitudeSecondDerivative x *
          (Complex.linearFourierCoefficient frequency) ^ 2 *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase frequency) x := by
  have hfirst :=
    Complex.intervalIntegral_realPhaseAmplitudeOscillation_eq_boundary_sub_remainder
      amplitude amplitudeDerivative
      (Complex.linearFourierPhase frequency)
      (Complex.linearFourierPhaseDerivative frequency)
      (fun _x : ℝ => 0)
      (Complex.linearFourierOscillationDerivative frequency)
      left right hamplitude
      (fun x _hx => Complex.linearFourierCoefficient_hasDerivAt frequency x)
      (fun x _hx => Complex.linearFourierOscillation_hasDerivAt frequency x)
      hfirstIntegrable hoscillationDerivativeIntegrable
      (fun x _hx => Complex.linearFourierOscillationDerivative_eq frequency x)
      (fun x _hx => Complex.linearFourierDenominator_ne_zero frequency x hfrequency)
  have hfirstBoundaryRight :
      Complex.realPhaseAmplitudeCoefficient amplitude
          (Complex.linearFourierPhaseDerivative frequency) right = 0 := by
    unfold Complex.realPhaseAmplitudeCoefficient
    exact congrArg
      (fun value : ℂ => value *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) right)
      hamplitudeRight
  have hfirstBoundaryLeft :
      Complex.realPhaseAmplitudeCoefficient amplitude
          (Complex.linearFourierPhaseDerivative frequency) left = 0 := by
    unfold Complex.realPhaseAmplitudeCoefficient
    exact congrArg
      (fun value : ℂ => value *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) left)
      hamplitudeLeft
  have hfirstReduced :
      (∫ x in left..right,
          amplitude x * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x) =
        -∫ x in left..right,
          Complex.linearFourierFirstAmplitude amplitudeDerivative frequency x *
            Complex.realPhaseOscillation
              (Complex.linearFourierPhase frequency) x := by
    exact hfirst.trans <| by
      have hrightProduct :
          Complex.realPhaseAmplitudeCoefficient amplitude
                (Complex.linearFourierPhaseDerivative frequency) right *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) right = 0 :=
        Eq.trans (congrArg
        (fun value : ℂ => value * Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) right)
        hfirstBoundaryRight) (zero_mul _)
      have hleftProduct :
          Complex.realPhaseAmplitudeCoefficient amplitude
                (Complex.linearFourierPhaseDerivative frequency) left *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) left = 0 :=
        Eq.trans (congrArg
        (fun value : ℂ => value * Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) left)
        hfirstBoundaryLeft) (zero_mul _)
      have hintegrand : Set.EqOn
          (Complex.realPhaseAmplitudeCoefficientDerivative amplitude amplitudeDerivative
            (fun _x : ℝ => 0) (Complex.linearFourierPhaseDerivative frequency))
          (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
          [[left, right]] := by
        intro x hx
        exact Complex.linearFourierAmplitudeCoefficient_eq_firstAmplitude
          amplitude amplitudeDerivative frequency x
      have hintegral := intervalIntegral.integral_congr
        (fun x hx => congrArg
          (fun value : ℂ => value * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x)
          (hintegrand x hx))
      calc
        Complex.realPhaseAmplitudeCoefficient amplitude
              (Complex.linearFourierPhaseDerivative frequency) right *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) right -
            Complex.realPhaseAmplitudeCoefficient amplitude
              (Complex.linearFourierPhaseDerivative frequency) left *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) left -
            ∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  amplitude amplitudeDerivative (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x =
          0 - 0 -
            ∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  amplitude amplitudeDerivative (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x :=
            congrArg₂
              (fun first second : ℂ => first - second -
                ∫ x in left..right,
                  Complex.realPhaseAmplitudeCoefficientDerivative
                      amplitude amplitudeDerivative (fun _x : ℝ => 0)
                      (Complex.linearFourierPhaseDerivative frequency) x *
                    Complex.realPhaseOscillation
                      (Complex.linearFourierPhase frequency) x)
              hrightProduct hleftProduct
        _ = -∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  amplitude amplitudeDerivative (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x := by
            exact Eq.trans (zero_sub 0) (zero_sub _)
        _ = -∫ x in left..right,
              Complex.linearFourierFirstAmplitude amplitudeDerivative frequency x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x :=
            congrArg Neg.neg hintegral
  have hsecond :=
    Complex.intervalIntegral_realPhaseAmplitudeOscillation_eq_boundary_sub_remainder
      (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
      (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
      (Complex.linearFourierPhase frequency)
      (Complex.linearFourierPhaseDerivative frequency)
      (fun _x : ℝ => 0)
      (Complex.linearFourierOscillationDerivative frequency)
      left right
      (fun x hx => Complex.linearFourierFirstAmplitude_hasDerivAt
        amplitudeDerivative amplitudeSecondDerivative frequency x
        (hamplitudeDerivative x hx))
      (fun x _hx => Complex.linearFourierCoefficient_hasDerivAt frequency x)
      (fun x _hx => Complex.linearFourierOscillation_hasDerivAt frequency x)
      hsecondIntegrable hoscillationDerivativeIntegrable
      (fun x _hx => Complex.linearFourierOscillationDerivative_eq frequency x)
      (fun x _hx => Complex.linearFourierDenominator_ne_zero frequency x hfrequency)
  have hsecondBoundaryRight :
      Complex.realPhaseAmplitudeCoefficient
          (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
          (Complex.linearFourierPhaseDerivative frequency) right = 0 := by
    unfold Complex.realPhaseAmplitudeCoefficient
    unfold Complex.linearFourierFirstAmplitude
    exact congrArg
      (fun value : ℂ => value * Complex.linearFourierCoefficient frequency *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) right)
      hamplitudeDerivativeRight
  have hsecondBoundaryLeft :
      Complex.realPhaseAmplitudeCoefficient
          (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
          (Complex.linearFourierPhaseDerivative frequency) left = 0 := by
    unfold Complex.realPhaseAmplitudeCoefficient
    unfold Complex.linearFourierFirstAmplitude
    exact congrArg
      (fun value : ℂ => value * Complex.linearFourierCoefficient frequency *
        Complex.realPhaseIntegrationCoefficient
          (Complex.linearFourierPhaseDerivative frequency) left)
      hamplitudeDerivativeLeft
  have hsecondReduced :
      (∫ x in left..right,
          Complex.linearFourierFirstAmplitude amplitudeDerivative frequency x *
            Complex.realPhaseOscillation (Complex.linearFourierPhase frequency) x) =
        -∫ x in left..right,
          amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2 *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) x := by
    exact hsecond.trans <| by
      have hrightProduct :
          Complex.realPhaseAmplitudeCoefficient
                (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                (Complex.linearFourierPhaseDerivative frequency) right *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) right = 0 :=
        Eq.trans
          (congrArg
            (fun value : ℂ => value * Complex.realPhaseOscillation
              (Complex.linearFourierPhase frequency) right)
            hsecondBoundaryRight)
          (zero_mul _)
      have hleftProduct :
          Complex.realPhaseAmplitudeCoefficient
                (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                (Complex.linearFourierPhaseDerivative frequency) left *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) left = 0 :=
        Eq.trans
          (congrArg
            (fun value : ℂ => value * Complex.realPhaseOscillation
              (Complex.linearFourierPhase frequency) left)
            hsecondBoundaryLeft)
          (zero_mul _)
      have hintegrand : Set.EqOn
          (Complex.realPhaseAmplitudeCoefficientDerivative
            (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
            (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
            (fun _x : ℝ => 0) (Complex.linearFourierPhaseDerivative frequency))
          (fun x => amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2)
          [[left, right]] := by
        intro x hx
        exact Complex.linearFourierFirstAmplitudeCoefficientDerivative_eq_secondAmplitude
          amplitudeDerivative amplitudeSecondDerivative frequency x
      have hintegral := intervalIntegral.integral_congr
        (fun x hx => congrArg
          (fun value : ℂ => value * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x)
          (hintegrand x hx))
      calc
        Complex.realPhaseAmplitudeCoefficient
              (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
              (Complex.linearFourierPhaseDerivative frequency) right *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) right -
            Complex.realPhaseAmplitudeCoefficient
              (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
              (Complex.linearFourierPhaseDerivative frequency) left *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) left -
            ∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                  (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
                  (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x =
          0 - 0 -
            ∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                  (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
                  (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x :=
            congrArg₂
              (fun first second : ℂ => first - second -
                ∫ x in left..right,
                  Complex.realPhaseAmplitudeCoefficientDerivative
                      (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                      (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
                      (fun _x : ℝ => 0)
                      (Complex.linearFourierPhaseDerivative frequency) x *
                    Complex.realPhaseOscillation
                      (Complex.linearFourierPhase frequency) x)
              hrightProduct hleftProduct
        _ = -∫ x in left..right,
              Complex.realPhaseAmplitudeCoefficientDerivative
                  (Complex.linearFourierFirstAmplitude amplitudeDerivative frequency)
                  (Complex.linearFourierSecondAmplitude amplitudeSecondDerivative frequency)
                  (fun _x : ℝ => 0)
                  (Complex.linearFourierPhaseDerivative frequency) x *
                Complex.realPhaseOscillation
                  (Complex.linearFourierPhase frequency) x := by
            exact Eq.trans (zero_sub 0) (zero_sub _)
        _ = -∫ x in left..right,
              amplitudeSecondDerivative x *
                (Complex.linearFourierCoefficient frequency) ^ 2 *
                  Complex.realPhaseOscillation
                    (Complex.linearFourierPhase frequency) x :=
            congrArg Neg.neg hintegral
  exact hfirstReduced.trans <| by
    have hnegative := congrArg Neg.neg hsecondReduced
    exact hnegative.trans (neg_neg _)

theorem Complex.linearFourier_twiceIntegrated_integrand_norm
    (amplitudeSecondDerivative : ℝ → ℂ)
    (frequency x : ℝ) :
    ‖amplitudeSecondDerivative x *
          (Complex.linearFourierCoefficient frequency) ^ 2 *
        Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) x‖ =
      ‖amplitudeSecondDerivative x‖ * ‖frequency‖⁻¹ ^ 2 := by
  have hoscillation :
      ‖Complex.realPhaseOscillation
        (Complex.linearFourierPhase frequency) x‖ = 1 :=
    Complex.norm_realPhaseOscillation
      (Complex.linearFourierPhase frequency) x
  exact
    (norm_mul
      (amplitudeSecondDerivative x *
        (Complex.linearFourierCoefficient frequency) ^ 2)
      (Complex.realPhaseOscillation
        (Complex.linearFourierPhase frequency) x)).trans
      ((congrArg₂ (fun first second : ℝ => first * second)
        (Complex.linearFourier_secondDerivative_integrand_norm
          amplitudeSecondDerivative frequency x)
        hoscillation).trans
        (mul_one _))

theorem Complex.norm_intervalIntegral_linearFourier_le_inverseSquare_integral
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (frequency left right : ℝ)
    (hleftRight : left ≤ right)
    (hidentity :
      (∫ x in left..right,
          amplitude x * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x) =
        ∫ x in left..right,
          amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2 *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) x) :
    ‖∫ x in left..right,
        amplitude x * Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) x‖ ≤
      ∫ x in left..right,
        ‖amplitudeSecondDerivative x‖ * ‖frequency‖⁻¹ ^ 2 := by
  have hnorm := intervalIntegral.norm_integral_le_integral_norm
    hleftRight
    (f := fun x : ℝ =>
      amplitudeSecondDerivative x *
        (Complex.linearFourierCoefficient frequency) ^ 2 *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x)
  have hintegrand : Set.EqOn
      (fun x : ℝ =>
        ‖amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2 *
          Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x‖)
      (fun x : ℝ =>
        ‖amplitudeSecondDerivative x‖ * ‖frequency‖⁻¹ ^ 2)
      [[left, right]] := by
    intro x hx
    exact Complex.linearFourier_twiceIntegrated_integrand_norm
      amplitudeSecondDerivative frequency x
  have hintegral := intervalIntegral.integral_congr hintegrand
  have htransported :
      ‖∫ x in left..right,
          amplitude x * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x‖ =
        ‖∫ x in left..right,
          amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2 *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) x‖ :=
    congrArg norm hidentity
  exact le_trans (le_of_eq htransported) (le_trans hnorm (le_of_eq hintegral))

theorem Complex.norm_intervalIntegral_linearFourier_le_inverseSquare_budget
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (frequency left right secondDerivativeBudget : ℝ)
    (hleftRight : left ≤ right)
    (hidentity :
      (∫ x in left..right,
          amplitude x * Complex.realPhaseOscillation
            (Complex.linearFourierPhase frequency) x) =
        ∫ x in left..right,
          amplitudeSecondDerivative x *
            (Complex.linearFourierCoefficient frequency) ^ 2 *
              Complex.realPhaseOscillation
                (Complex.linearFourierPhase frequency) x)
    (hbudget :
      (∫ x in left..right,
          ‖amplitudeSecondDerivative x‖ * ‖frequency‖⁻¹ ^ 2) ≤
        secondDerivativeBudget * ‖frequency‖⁻¹ ^ 2) :
    ‖∫ x in left..right,
        amplitude x * Complex.realPhaseOscillation
          (Complex.linearFourierPhase frequency) x‖ ≤
      secondDerivativeBudget * ‖frequency‖⁻¹ ^ 2 := by
  exact le_trans
    (Complex.norm_intervalIntegral_linearFourier_le_inverseSquare_integral
      amplitude amplitudeDerivative amplitudeSecondDerivative
      frequency left right hleftRight hidentity)
    hbudget

end
end LFunctions
end Boundary

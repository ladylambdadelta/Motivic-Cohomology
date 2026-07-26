import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.NormalizedCorrectionTarget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.ZetaAutocorrelationHilbert.Owner

/-!
# Autocorrelation prime normalization
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The negative-time value of an autocorrelation is the conjugate of its
positive-time value. -/
theorem zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_neg_eq_star
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) (-a) =
      star (zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) := by
  have hnegative :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) (-a) =
        convolutionAutocorrelationKernel f (-a) :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f (-a)
  have hpositive :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a =
        convolutionAutocorrelationKernel f a :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel f a
  have hdagger :
      convolutionAutocorrelationKernel f (-a) =
        star (convolutionAutocorrelationKernel f a) :=
    convolutionAutocorrelationKernel_neg_eq_conj f a
  exact Eq.trans hnegative
    (Eq.trans hdagger (congrArg star hpositive.symm))

/-- A complex number fixed by conjugation is its coerced real part. -/
theorem zetaCompleted_add_star_eq_ofReal_re_add_star
    (value : ℂ) :
    value + star value = ((Complex.re (value + star value) : ℝ) : ℂ) := by
  have him : Complex.im (value + star value) = 0 := by
    calc
      Complex.im (value + star value) =
          Complex.im value + Complex.im (star value) :=
        Complex.add_im value (star value)
      _ = Complex.im value + (-Complex.im value) := by
        exact congrArg (fun x : ℝ => Complex.im value + x)
          (Eq.trans
            (congrArg Complex.im (congrFun Complex.star_def value))
            (Complex.conj_im value))
      _ = 0 := add_neg_cancel (Complex.im value)
  exact Complex.ext
    (Complex.ofReal_re (Complex.re (value + star value))).symm
    (Eq.trans him
      (Complex.ofReal_im (Complex.re (value + star value))).symm)

/-- At one natural index, the raw two-face Mellin sample is `2 pi` times the
negative of the signed time-side summand. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_convolutionAutocorrelation_eq_twoPi_mul_neg_timeSummand
    (f : ZetaAdmissibleFunction) (n : ℕ) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
        (convolutionAutocorrelation f) n =
      explicitFormulaTwoPi *
        (-(zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
          (convolutionAutocorrelation f) n)) := by
  let weight : ℝ := zetaCompletedExplicitFormulaPrimeNaturalWeight n
  let center : ℝ := zetaCompletedExplicitFormulaPrimeNaturalCenter n
  let value : ℂ :=
    zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) center
  have hreflected :
      zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) (-center) =
        star value :=
    zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_neg_eq_star f center
  have hreal : value + star value = ((Complex.re (value + star value) : ℝ) : ℂ) :=
    zetaCompleted_add_star_eq_ofReal_re_add_star value
  have htwoPi_coe :
      (((2 * Real.pi : ℝ) : ℝ) : ℂ) = explicitFormulaTwoPi := by
    unfold explicitFormulaTwoPi
    exact Complex.ofReal_mul 2 Real.pi
  have hsmul (sample : ℂ) :
      (2 * Real.pi : ℝ) • sample = explicitFormulaTwoPi * sample := by
    exact Eq.trans
      (RCLike.real_smul_eq_coe_mul (2 * Real.pi) sample)
      (congrArg (fun scalar : ℂ => scalar * sample) htwoPi_coe)
  calc
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
        (convolutionAutocorrelation f) n =
        (weight : ℂ) * ((2 * Real.pi : ℝ) • value) +
          (weight : ℂ) * ((2 * Real.pi : ℝ) • star value) := by
      unfold zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
      unfold zetaCompletedExplicitFormulaPrimeNaturalOneSidedTimeSample
      unfold zetaCompletedExplicitFormulaPrimeNaturalReflectedTimeBoundarySample
      exact congrArg₂ HAdd.hAdd (Eq.refl _)
        (congrArg (fun sample : ℂ => (weight : ℂ) * ((2 * Real.pi : ℝ) • sample))
          hreflected)
    _ = (weight : ℂ) * (explicitFormulaTwoPi * value) +
          (weight : ℂ) * (explicitFormulaTwoPi * star value) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg (fun sample : ℂ => (weight : ℂ) * sample) (hsmul value))
        (congrArg (fun sample : ℂ => (weight : ℂ) * sample) (hsmul (star value)))
    _ = explicitFormulaTwoPi * ((weight : ℂ) * (value + star value)) := by
      calc
        (weight : ℂ) * (explicitFormulaTwoPi * value) +
            (weight : ℂ) * (explicitFormulaTwoPi * star value) =
            explicitFormulaTwoPi * ((weight : ℂ) * value) +
              explicitFormulaTwoPi * ((weight : ℂ) * star value) := by
          exact congrArg₂ HAdd.hAdd
            (calc
              (weight : ℂ) * (explicitFormulaTwoPi * value) =
                  ((weight : ℂ) * explicitFormulaTwoPi) * value := by
                exact (mul_assoc (weight : ℂ) explicitFormulaTwoPi value).symm
              _ = (explicitFormulaTwoPi * (weight : ℂ)) * value := by
                exact congrArg (fun scalar : ℂ => scalar * value)
                  (mul_comm (weight : ℂ) explicitFormulaTwoPi)
              _ = explicitFormulaTwoPi * ((weight : ℂ) * value) := by
                exact mul_assoc explicitFormulaTwoPi (weight : ℂ) value)
            (calc
              (weight : ℂ) * (explicitFormulaTwoPi * star value) =
                  ((weight : ℂ) * explicitFormulaTwoPi) * star value := by
                exact (mul_assoc (weight : ℂ) explicitFormulaTwoPi (star value)).symm
              _ = (explicitFormulaTwoPi * (weight : ℂ)) * star value := by
                exact congrArg (fun scalar : ℂ => scalar * star value)
                  (mul_comm (weight : ℂ) explicitFormulaTwoPi)
              _ = explicitFormulaTwoPi * ((weight : ℂ) * star value) := by
                exact mul_assoc explicitFormulaTwoPi (weight : ℂ) (star value))
        _ = explicitFormulaTwoPi *
              ((weight : ℂ) * value + (weight : ℂ) * star value) := by
          exact (mul_add explicitFormulaTwoPi
            ((weight : ℂ) * value) ((weight : ℂ) * star value)).symm
        _ = explicitFormulaTwoPi * ((weight : ℂ) * (value + star value)) := by
          exact congrArg (fun sample : ℂ => explicitFormulaTwoPi * sample)
            (mul_add (weight : ℂ) value (star value)).symm
    _ = explicitFormulaTwoPi *
          ((weight : ℂ) * ((Complex.re (value + star value) : ℝ) : ℂ)) := by
      exact congrArg
        (fun sample : ℂ => explicitFormulaTwoPi * ((weight : ℂ) * sample)) hreal
    _ = explicitFormulaTwoPi *
          (-(zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
            (convolutionAutocorrelation f) n)) := by
      unfold zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
      exact congrArg
        (fun sample : ℂ => explicitFormulaTwoPi * sample)
        (neg_neg ((weight : ℂ) * ((Complex.re (value + star value) : ℝ) : ℂ))).symm

/-- Multiplying a summable complex sequence by a fixed scalar preserves its
`HasSum` value on the left. -/
theorem hasSum_complex_left_mul_of_summable
    (a : ℂ) (term : ℕ → ℂ) (hterm : Summable term) :
    HasSum
      (fun n : ℕ => a * term n)
      (a * (∑' n : ℕ, term n)) :=
  HasSum.mul_left a hterm.hasSum

/-- The raw two-face autocorrelation contribution divided by `2 pi` is the
public signed prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_div_twoPi_eq_primeContribution_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f) /
        explicitFormulaTwoPi =
      zetaCompletedExplicitFormulaPrimeContribution
        (convolutionAutocorrelation f) := by
  let timeSummand : ℕ → ℂ := fun n : ℕ =>
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand
      (convolutionAutocorrelation f) n
  have htime : Summable timeSummand :=
    zetaCompletedExplicitFormulaPrimeNaturalTimeSummand_summable
      (convolutionAutocorrelation f)
  have hraw :
      HasSum
        (fun n : ℕ => explicitFormulaTwoPi * (-(timeSummand n)))
        (explicitFormulaTwoPi * (-(∑' n : ℕ, timeSummand n))) := by
    have hrawBase :
        HasSum
          (fun n : ℕ => explicitFormulaTwoPi * (-(timeSummand n)))
          (explicitFormulaTwoPi * (∑' n : ℕ, -(timeSummand n))) :=
      hasSum_complex_left_mul_of_summable
        explicitFormulaTwoPi
        (fun n : ℕ => -(timeSummand n))
        htime.neg
    have hnegTsum :
        (∑' n : ℕ, -(timeSummand n)) =
          -(∑' n : ℕ, timeSummand n) :=
      tsum_neg
    exact Eq.subst
      (motive := fun value : ℂ =>
        HasSum
          (fun n : ℕ => explicitFormulaTwoPi * (-(timeSummand n)))
          (explicitFormulaTwoPi * value))
      hnegTsum
      hrawBase
  have hpoint :
      (fun n : ℕ =>
        zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample
          (convolutionAutocorrelation f) n) =
      (fun n : ℕ => explicitFormulaTwoPi * (-(timeSummand n))) := by
    exact funext (fun n : ℕ =>
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundarySample_convolutionAutocorrelation_eq_twoPi_mul_neg_timeSummand
        f n)
  have hcontribution :
      zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution
          (convolutionAutocorrelation f) =
        explicitFormulaTwoPi * (-(∑' n : ℕ, timeSummand n)) := by
    exact Eq.trans
      (zetaCompletedExplicitFormulaPrimeNaturalTwoFaceBoundaryContribution_eq_tsum
        (convolutionAutocorrelation f))
      (Eq.trans (congrArg tsum hpoint) hraw.tsum_eq)
  have hdivide :
      (explicitFormulaTwoPi * (-(∑' n : ℕ, timeSummand n))) /
          explicitFormulaTwoPi =
        -(∑' n : ℕ, timeSummand n) :=
    mul_div_cancel_left₀ (-(∑' n : ℕ, timeSummand n)) explicitFormulaTwoPi_ne_zero
  have hpublic :
      (∑' n : ℕ, timeSummand n) =
        -zetaCompletedExplicitFormulaPrimeContribution
          (convolutionAutocorrelation f) :=
    Eq.trans
      (zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_tsum
        (convolutionAutocorrelation f)).symm
      (zetaCompletedExplicitFormulaPrimeNaturalSymmetricContribution_eq_primeContribution
        (convolutionAutocorrelation f))
  have hnegPublic :
      -(∑' n : ℕ, timeSummand n) =
        zetaCompletedExplicitFormulaPrimeContribution
          (convolutionAutocorrelation f) := by
    calc
      -(∑' n : ℕ, timeSummand n) =
          -(-zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f)) := by
        exact congrArg Neg.neg hpublic
      _ =
          zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f) := by
        exact neg_neg
          (zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f))
  exact Eq.trans
    (congrArg (fun value : ℂ => value / explicitFormulaTwoPi) hcontribution)
    (Eq.trans hdivide hnegPublic)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

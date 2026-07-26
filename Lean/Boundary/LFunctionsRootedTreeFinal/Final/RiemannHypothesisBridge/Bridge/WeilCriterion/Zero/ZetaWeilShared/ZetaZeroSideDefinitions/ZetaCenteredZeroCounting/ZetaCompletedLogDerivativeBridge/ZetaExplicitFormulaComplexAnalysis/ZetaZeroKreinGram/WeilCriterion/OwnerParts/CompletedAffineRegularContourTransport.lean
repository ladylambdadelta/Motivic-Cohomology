import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedHermitianInverseGamma
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanSeedTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourFinite
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineRegularContourDecay
import Mathlib.Topology.Basic

/-!
# Regular inverse-Gamma contour transport

The inverse-Gamma completion packet is transported as a single regular
channel.  Its archimedean and elementary correction summands are separated
only after this residue-free contour identity has been established.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The inverse-Gamma logarithmic derivative at opposite heights of the
right affine line is conjugate. -/
theorem inverseGammaCompletionLogDeriv_rightAffineLine_neg_eq_star
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    inverseGammaCompletionLogDeriv
        (zetaCompletedExplicitFormulaRightAffineLine family (-t)) =
      star
        (inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine family t)) :=
  let positivePoint : ℂ :=
    zetaCompletedExplicitFormulaRightAffineLine family t
  let negativePoint : ℂ :=
    zetaCompletedExplicitFormulaRightAffineLine family (-t)
  let positiveArchimedean : ℂ :=
    explicitFormulaArchimedeanLogDerivative positivePoint
  let negativeArchimedean : ℂ :=
    explicitFormulaArchimedeanLogDerivative negativePoint
  let positiveCorrection : ℂ :=
    explicitFormulaCorrectionLogDerivative positivePoint
  let negativeCorrection : ℂ :=
    explicitFormulaCorrectionLogDerivative negativePoint
  let positiveArchimedeanFactor :
      positiveArchimedean =
        zetaCompletedAffineArchimedeanRightBinetFactor family t :=
    (zetaCompletedAffineArchimedeanRightBinetFactor_eq_logDerivative
      family t).symm
  let negativeArchimedeanFactor :
      negativeArchimedean =
        zetaCompletedAffineArchimedeanRightBinetFactor family (-t) :=
    (zetaCompletedAffineArchimedeanRightBinetFactor_eq_logDerivative
      family (-t)).symm
  let archimedeanConjugation :
      negativeArchimedean = star positiveArchimedean :=
    Eq.trans negativeArchimedeanFactor
      (Eq.trans
        (zetaCompletedAffineArchimedeanRightBinetFactor_neg_eq_star
          family t)
        (congrArg star positiveArchimedeanFactor.symm))
  let correctionConjugation :
      negativeCorrection = star positiveCorrection :=
    explicitFormulaCorrectionLogDerivative_rightAffineLine_neg_eq_star
      family t
  let negativeSplit :
      inverseGammaCompletionLogDeriv negativePoint =
        negativeArchimedean + negativeCorrection :=
    (sub_add_cancel
      (inverseGammaCompletionLogDeriv negativePoint)
      negativeCorrection).symm
  let positiveSplit :
      inverseGammaCompletionLogDeriv positivePoint =
        positiveArchimedean + positiveCorrection :=
    (sub_add_cancel
      (inverseGammaCompletionLogDeriv positivePoint)
      positiveCorrection).symm
  Eq.trans negativeSplit
    (Eq.trans
      (congrArg₂ HAdd.hAdd archimedeanConjugation correctionConjugation)
      (Eq.trans
        (star_add positiveArchimedean positiveCorrection).symm
        (congrArg star positiveSplit.symm)))

/-- The reflected affine inverse-Gamma kernel is the negative conjugate of
the right one-sided seed kernel. -/
theorem zetaCompletedPrimeLeftReflectedInverseGamma_convolutionAutocorrelation_eq_neg_star_right
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f) family t =
      -star
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f) family t) :=
  let rightPoint : ℂ :=
    zetaCompletedExplicitFormulaRightCenteredAffineLine family t
  let leftPoint : ℂ :=
    zetaCompletedExplicitFormulaLeftCenteredAffineLine family t
  let rightFactor : ℂ :=
    inverseGammaCompletionLogDeriv
      (zetaCompletedExplicitFormulaRightAffineLine family t)
  let rightSeed : ℂ :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform f rightPoint
  let factorConjugation :
      inverseGammaCompletionLogDeriv
          (zetaCompletedExplicitFormulaRightAffineLine family (-t)) =
        star rightFactor :=
    inverseGammaCompletionLogDeriv_rightAffineLine_neg_eq_star family t
  let leftTransform :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) leftPoint =
        star rightSeed :=
    Eq.trans
      (zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f leftPoint)
      (zetaCompletedArchimedeanSeedAutocorrelationTransform_left_eq_star_right
        f family t)
  let rightTransform :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) rightPoint =
        rightSeed :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f rightPoint
  let unfoldLeft :
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
        (convolutionAutocorrelation f) family t =
        (-(star rightFactor)) * star rightSeed :=
    congrArg₂ HMul.hMul
        (congrArg Neg.neg factorConjugation)
        leftTransform
  let moveNeg :
      (-(star rightFactor)) * star rightSeed =
        -(star rightFactor * star rightSeed) :=
    neg_mul (star rightFactor) (star rightSeed)
  let productStar :
      -(star rightFactor * star rightSeed) =
        -star (rightFactor * rightSeed) :=
    congrArg Neg.neg
      (Eq.trans
        (mul_comm (star rightFactor) (star rightSeed))
        (star_mul rightFactor rightSeed).symm)
  let foldRight :
      -star (rightFactor * rightSeed) =
        -star
        (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f) family t) :=
    congrArg (fun value : ℂ => -star value)
      (congrArg₂ HMul.hMul rfl rightTransform.symm)
  Eq.trans unfoldLeft
    (Eq.trans moveNeg
      (Eq.trans productStar foldRight))

/-- The coupled affine inverse-Gamma packet is the Hermitianization of its
right one-sided kernel. -/
theorem zetaCompletedAffineInverseGamma_convolutionAutocorrelation_eq_right_add_star
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        (convolutionAutocorrelation f) family t =
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
          (convolutionAutocorrelation f) family t +
        star
          (zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
            (convolutionAutocorrelation f) family t) :=
  let rightValue : ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      (convolutionAutocorrelation f) family t
  let reflectedValue :
      zetaCompletedExplicitFormulaPrimeLeftReflectedInverseGammaKernel
          (convolutionAutocorrelation f) family t =
        -star rightValue :=
    zetaCompletedPrimeLeftReflectedInverseGamma_convolutionAutocorrelation_eq_neg_star_right
      f family t
  Eq.trans
    (congrArg
      (fun value : ℂ => rightValue - value)
      reflectedValue)
    (sub_neg_eq_add rightValue (star rightValue))

/-- The critical Hermitian inverse-Gamma integrand is the Hermitianization
of its one-sided seed kernel. -/
theorem zetaCompletedHermitianInverseGamma_convolutionAutocorrelation_eq_seed_add_star
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedHermitianInverseGammaIntegrand
        (convolutionAutocorrelation f) t =
      zetaCompletedCriticalInverseGammaSeedKernel f t +
        star (zetaCompletedCriticalInverseGammaSeedKernel f t) :=
  let factor : ℂ :=
    inverseGammaCompletionLogDeriv
      (zetaCompletedCenteredSpectralLine t)
  let seed : ℂ :=
    zetaCompletedArchimedeanSeedAutocorrelationTransform f
      (t * Complex.I)
  let transformEquality :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (t * Complex.I) =
        seed :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f (t * Complex.I)
  let seedStar : star seed = seed :=
    let transform : ℂ :=
      zetaCompletedExplicitFormulaPhi f (t * Complex.I)
    let daggerFixed : -star ((t : ℂ) * Complex.I) = (t : ℂ) * Complex.I :=
      zetaCompletedImaginaryCoordinate_dagger_fixed t
    let unfoldSeed :
        star seed =
          star
            (transform *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-star ((t : ℂ) * Complex.I)))) :=
      rfl
    let distributeStar :
        star
            (transform *
              star
                (zetaCompletedExplicitFormulaPhi f
                  (-star ((t : ℂ) * Complex.I)))) =
        star transform *
        star
          (star
            (zetaCompletedExplicitFormulaPhi f
              (-star ((t : ℂ) * Complex.I)))) :=
      Eq.trans
        (star_mul transform
          (star
            (zetaCompletedExplicitFormulaPhi f
              (-star ((t : ℂ) * Complex.I)))))
        (mul_comm
          (star
            (star
              (zetaCompletedExplicitFormulaPhi f
                (-star ((t : ℂ) * Complex.I)))))
          (star transform))
    let cancelDoubleStar :
        star transform *
          star
            (star
              (zetaCompletedExplicitFormulaPhi f
                (-star ((t : ℂ) * Complex.I)))) =
          star transform *
          zetaCompletedExplicitFormulaPhi f
            (-star ((t : ℂ) * Complex.I)) :=
      congrArg
          (fun value : ℂ => star transform * value)
          (star_star
            (zetaCompletedExplicitFormulaPhi f
              (-star ((t : ℂ) * Complex.I))))
    let applyDaggerFixed :
        star transform *
          zetaCompletedExplicitFormulaPhi f
            (-star ((t : ℂ) * Complex.I)) =
          star transform * transform :=
      congrArg
          (fun value : ℂ => star transform *
            zetaCompletedExplicitFormulaPhi f value)
          daggerFixed
    let commuteProduct :
        star transform * transform = transform * star transform :=
      mul_comm (star transform) transform
    let foldSeed :
        transform * star transform = seed :=
      congrArg
          (fun value : ℂ => transform *
            star (zetaCompletedExplicitFormulaPhi f value))
          daggerFixed.symm
    Eq.trans unfoldSeed
      (Eq.trans distributeStar
        (Eq.trans cancelDoubleStar
          (Eq.trans applyDaggerFixed
            (Eq.trans commuteProduct foldSeed))))
  let conjugateProduct :
      star (factor * seed) = star factor * seed :=
    Eq.trans (star_mul factor seed)
      (Eq.trans
        (congrArg (fun value : ℂ => value * star factor) seedStar)
        (mul_comm seed (star factor)))
  let unfoldLeft :
      zetaCompletedHermitianInverseGammaIntegrand
        (convolutionAutocorrelation f) t =
        (factor + star factor) * seed :=
    congrArg
        (fun value : ℂ => (factor + star factor) * value)
        transformEquality
  let distribute :
      (factor + star factor) * seed =
        factor * seed + star factor * seed :=
    add_mul factor (star factor) seed
  let conjugateTerm :
      factor * seed + star factor * seed =
        factor * seed + star (factor * seed) :=
    congrArg
        (fun value : ℂ => factor * seed + value)
        conjugateProduct.symm
  let foldRight :
      factor * seed + star (factor * seed) =
        zetaCompletedCriticalInverseGammaSeedKernel f t +
          star (zetaCompletedCriticalInverseGammaSeedKernel f t) :=
    rfl
  Eq.trans unfoldLeft
    (Eq.trans distribute
      (Eq.trans conjugateTerm foldRight))

/-- Equality of finite windows up to a vanishing error identifies the two
whole-line integrals. -/
theorem integral_eq_of_symmetric_windows_eq_add_vanishing_error
    (right critical : ℝ → ℂ)
    (error : ℝ → ℂ)
    (rightIntegrable : Integrable right (volume : Measure ℝ))
    (criticalIntegrable : Integrable critical (volume : Measure ℝ))
    (finiteEquality :
      ∀ T : ℝ,
        0 ≤ T →
        (∫ t in Set.Icc (-T) T, right t) =
          (∫ t in Set.Icc (-T) T, critical t) + error T)
    (errorLimit : Filter.Tendsto error Filter.atTop (𝓝 0)) :
    (∫ t : ℝ, right t) = ∫ t : ℝ, critical t :=
  let rightLimit :
      Filter.Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, right t)
        Filter.atTop
        (𝓝 (∫ t : ℝ, right t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      right rightIntegrable
  let criticalLimit :
      Filter.Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, critical t)
        Filter.atTop
        (𝓝 (∫ t : ℝ, critical t)) :=
    explicitFormulaSymmetricIntervalIntegral_tendsto_integral
      critical criticalIntegrable
  let sumLimit :
      Filter.Tendsto
        (fun T : ℝ =>
          (∫ t in Set.Icc (-T) T, critical t) + error T)
        Filter.atTop
        (𝓝 ((∫ t : ℝ, critical t) + 0)) :=
    criticalLimit.add errorLimit
  let transportedRightLimit :
      Filter.Tendsto
        (fun T : ℝ => ∫ t in Set.Icc (-T) T, right t)
        Filter.atTop
        (𝓝 ((∫ t : ℝ, critical t) + 0)) :=
    Filter.Tendsto.congr'
      ((Filter.eventually_ge_atTop (0 : ℝ)).mono
        (fun T : ℝ => fun heightNonnegative : 0 ≤ T =>
          (finiteEquality T heightNonnegative).symm))
      sumLimit
  let uniqueLimit :
      (∫ t : ℝ, right t) = (∫ t : ℝ, critical t) + 0 :=
    tendsto_nhds_unique rightLimit transportedRightLimit
  Eq.trans uniqueLimit (add_zero (∫ t : ℝ, critical t))

/-- The one-sided critical inverse-Gamma seed kernel is integrable. -/
theorem zetaCompletedCriticalInverseGammaSeedKernel_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedCriticalInverseGammaSeedKernel f)
      (volume : Measure ℝ) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let archimedeanKernel : ℝ → ℂ := fun t : ℝ =>
    explicitFormulaArchimedeanLogDerivative
        (zetaCompletedCenteredSpectralLine t) *
      zetaCompletedExplicitFormulaPhi probe (t * Complex.I)
  let correctionKernel : ℝ → ℂ := fun t : ℝ =>
    explicitFormulaCorrectionLogDerivative
        (zetaCompletedCenteredSpectralLine t) *
      zetaCompletedExplicitFormulaPhi probe (t * Complex.I)
  let archimedeanIntegrable :
      Integrable archimedeanKernel (volume : Measure ℝ) :=
    zetaCompletedArchimedeanCenteredIntegrand_integrable probe
  let correctionFactorMeasurable :
      AEStronglyMeasurable
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedCenteredSpectralLine t))
        (volume : Measure ℝ) :=
    let functionEquality :
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative
            (zetaCompletedCenteredSpectralLine t)) =
          fun t : ℝ =>
            (-1 : ℂ) / zetaCompletedCenteredSpectralLine t -
              1 / (zetaCompletedCenteredSpectralLine t - 1) :=
      funext
        (fun t : ℝ =>
          explicitFormulaCorrectionLogDerivative_eq_poleCorrection
            (zetaCompletedCenteredSpectralLine t))
    Eq.subst
      (motive := fun candidate : ℝ → ℂ =>
        AEStronglyMeasurable candidate (volume : Measure ℝ))
      functionEquality.symm
      zetaCompletedCenteredElementaryPoleCorrection_aestronglyMeasurable
  let correctionFactorBound :
      ∀ t : ℝ,
        ‖explicitFormulaCorrectionLogDerivative
            (zetaCompletedCenteredSpectralLine t)‖ ≤
          zetaCompletedCenteredElementaryPoleBoundConstant *
            (1 + ‖t‖) :=
    fun t : ℝ =>
      Eq.subst
        (motive := fun value : ℂ =>
          ‖value‖ ≤
            zetaCompletedCenteredElementaryPoleBoundConstant *
              (1 + ‖t‖))
        (explicitFormulaCorrectionLogDerivative_eq_poleCorrection
          (zetaCompletedCenteredSpectralLine t)).symm
        (zetaCompletedCenteredElementaryPoleCorrection_bound t)
  let correctionIntegrable :
      Integrable correctionKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalLineProduct_integrable_of_linearFactor
      probe
      (fun t : ℝ =>
        explicitFormulaCorrectionLogDerivative
          (zetaCompletedCenteredSpectralLine t))
      zetaCompletedCenteredElementaryPoleBoundConstant
      zetaCompletedCenteredElementaryPoleBoundConstant_nonneg
      correctionFactorMeasurable
      correctionFactorBound
  let sumIntegrable :
      Integrable
        (fun t : ℝ => archimedeanKernel t + correctionKernel t)
        (volume : Measure ℝ) :=
    archimedeanIntegrable.add correctionIntegrable
  let functionEquality :
      zetaCompletedCriticalInverseGammaSeedKernel f =
        fun t : ℝ => archimedeanKernel t + correctionKernel t :=
    funext
      (fun t : ℝ =>
        let inverseGammaSplit :
            inverseGammaCompletionLogDeriv
                (zetaCompletedCenteredSpectralLine t) =
              explicitFormulaArchimedeanLogDerivative
                  (zetaCompletedCenteredSpectralLine t) +
                explicitFormulaCorrectionLogDerivative
                  (zetaCompletedCenteredSpectralLine t) :=
          (sub_add_cancel
            (inverseGammaCompletionLogDeriv
              (zetaCompletedCenteredSpectralLine t))
            (explicitFormulaCorrectionLogDerivative
              (zetaCompletedCenteredSpectralLine t))).symm
        let transformEquality :
            zetaCompletedExplicitFormulaPhi probe (t * Complex.I) =
              zetaCompletedArchimedeanSeedAutocorrelationTransform f
                (t * Complex.I) :=
          zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
            f (t * Complex.I)
        Eq.trans
          (congrArg₂ HMul.hMul inverseGammaSplit transformEquality.symm)
          (add_mul
            (explicitFormulaArchimedeanLogDerivative
              (zetaCompletedCenteredSpectralLine t))
            (explicitFormulaCorrectionLogDerivative
              (zetaCompletedCenteredSpectralLine t))
            (zetaCompletedExplicitFormulaPhi probe (t * Complex.I))))
  Eq.subst
    (motive := fun candidate : ℝ → ℂ =>
      Integrable candidate (volume : Measure ℝ))
    functionEquality.symm
    sumIntegrable

/-- One-sided regular contour transport from the affine right line to the
critical line.  This is the sole analytic strip-shift sink. -/
theorem zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedCriticalInverseGammaSeedKernel f t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let error : ℝ → ℂ :=
    zetaCompletedRegularInverseGammaHorizontalDefect f
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let finiteEquality :
      ∀ T : ℝ,
        0 ≤ T →
        (∫ t in Set.Icc (-T) T, rightKernel t) =
          (∫ t in Set.Icc (-T) T, criticalKernel t) + error T :=
    fun T : ℝ => fun heightNonnegative : 0 ≤ T =>
      zetaCompletedRegularInverseGamma_finiteWindow_eq_critical_add_horizontal
        f hPhi T heightNonnegative
  let errorLimit : Filter.Tendsto error Filter.atTop (𝓝 0) :=
    zetaCompletedRegularInverseGammaHorizontalDefect_tendsto_zero f
  integral_eq_of_symmetric_windows_eq_add_vanishing_error
    rightKernel criticalKernel error
    rightIntegrable criticalIntegrable finiteEquality errorLimit

/-- The regular affine inverse-Gamma packet transports to the Hermitian
critical-line packet without a residue term. -/
theorem zetaCompletedAffineRegularInverseGamma_integral_eq_critical_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
    let family : ExplicitFormulaContourFamily :=
      zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    (∫ t : ℝ,
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
        probe family t) =
      ∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let family : ExplicitFormulaContourFamily :=
    zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let rightKernel : ℝ → ℂ :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel
      probe family
  let criticalKernel : ℝ → ℂ :=
    zetaCompletedCriticalInverseGammaSeedKernel f
  let analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage probe family :=
    CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let rightIntegrable :
      Integrable rightKernel (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaInverseGammaRightAffineKernel_integrable
      probe family analyticPackage
  let rightStarIntegrable :
      Integrable (fun t : ℝ => star (rightKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      rightIntegrable
  let criticalIntegrable :
      Integrable criticalKernel (volume : Measure ℝ) :=
    zetaCompletedCriticalInverseGammaSeedKernel_integrable f
  let criticalStarIntegrable :
      Integrable (fun t : ℝ => star (criticalKernel t))
        (volume : Measure ℝ) :=
    Complex.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      criticalIntegrable
  let affineFunctionEquality :
      zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family =
        fun t : ℝ => rightKernel t + star (rightKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedAffineInverseGamma_convolutionAutocorrelation_eq_right_add_star
          f family t)
  let criticalFunctionEquality :
      zetaCompletedHermitianInverseGammaIntegrand probe =
        fun t : ℝ => criticalKernel t + star (criticalKernel t) :=
    funext
      (fun t : ℝ =>
        zetaCompletedHermitianInverseGamma_convolutionAutocorrelation_eq_seed_add_star
          f t)
  let affineIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedAffineInverseGammaRightReflectedDifferenceKernel
          probe family t) =
        (∫ t : ℝ, rightKernel t) +
          star (∫ t : ℝ, rightKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        affineFunctionEquality)
      (Eq.trans
        (integral_add rightIntegrable rightStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, rightKernel t) + value)
          integral_conj))
  let criticalIntegralEquality :
      (∫ t : ℝ,
        zetaCompletedHermitianInverseGammaIntegrand probe t) =
        (∫ t : ℝ, criticalKernel t) +
          star (∫ t : ℝ, criticalKernel t) :=
    Eq.trans
      (congrArg
        (fun candidate : ℝ → ℂ => ∫ t : ℝ, candidate t)
        criticalFunctionEquality)
      (Eq.trans
        (integral_add criticalIntegrable criticalStarIntegrable)
        (congrArg
          (fun value : ℂ => (∫ t : ℝ, criticalKernel t) + value)
          integral_conj))
  let oneSidedEquality :
      (∫ t : ℝ, rightKernel t) =
        ∫ t : ℝ, criticalKernel t :=
    zetaCompletedAffineInverseGamma_oneSided_integral_eq_critical_owner f
      hPhi hLog
  Eq.trans affineIntegralEquality
    (Eq.trans
      (congrArg₂ HAdd.hAdd oneSidedEquality
        (congrArg star oneSidedEquality))
      criticalIntegralEquality.symm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

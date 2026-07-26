import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffineArchimedeanSeedTransport

/-!
# Hermitian affine-to-critical contour transport

The affine and critical one-sided archimedean integrals are Hermitianized
only after their contour discrepancy has been identified.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- The canonical one-sided right affine archimedean seed kernel. -/
noncomputable def zetaCompletedAffineArchimedeanSeedRightKernel
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanRightAffineKernel
    (convolutionAutocorrelation f) family t

/-- The canonical one-sided critical-line archimedean seed kernel. -/
noncomputable def zetaCompletedArchimedeanSeedCriticalKernel
    (f : ZetaAdmissibleFunction)
    (t : ℝ) : ℂ :=
  zetaCompletedArchimedeanCenteredIntegrand
    (convolutionAutocorrelation f) t

/-- The explicit right seed factor is the canonical one-sided right affine
kernel. -/
theorem zetaCompletedAffineArchimedeanSeedRightKernel_eq_factor_mul_seed
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanSeedRightKernel f family t =
      zetaCompletedAffineArchimedeanRightBinetFactor family t *
        zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) :=
  let scalarEquality :
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaRightAffineLine family t) =
        zetaCompletedAffineArchimedeanRightBinetFactor family t :=
    (zetaCompletedAffineArchimedeanRightBinetFactor_eq_logDerivative
      family t).symm
  let transformEquality :
      zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f)
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) =
        zetaCompletedArchimedeanSeedAutocorrelationTransform f
          (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
      f
      (zetaCompletedExplicitFormulaRightCenteredAffineLine family t)
  congrArg₂ HMul.hMul scalarEquality transformEquality

/-- The Hermitianized right affine kernel is the named Hermitian seed
kernel. -/
theorem zetaCompletedAffineArchimedeanSeedHermitianRightKernel_eq_oneSided
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (t : ℝ) :
    zetaCompletedAffineArchimedeanSeedHermitianRightKernel f family t =
      zetaCompletedAffineArchimedeanSeedRightKernel f family t +
        star (zetaCompletedAffineArchimedeanSeedRightKernel f family t) :=
  let rightEquality :
      zetaCompletedAffineArchimedeanSeedRightKernel f family t =
        zetaCompletedAffineArchimedeanRightBinetFactor family t *
          zetaCompletedArchimedeanSeedAutocorrelationTransform f
            (zetaCompletedExplicitFormulaRightCenteredAffineLine family t) :=
    zetaCompletedAffineArchimedeanSeedRightKernel_eq_factor_mul_seed
      f family t
  congrArg₂ HAdd.hAdd rightEquality.symm
    (congrArg star rightEquality.symm)

/-- The one-sided right affine seed kernel is integrable. -/
theorem zetaCompletedAffineArchimedeanSeedRightKernel_integrable
    (f : ZetaAdmissibleFunction)
    (family : ExplicitFormulaContourFamily)
    (analyticPackage :
      ExplicitFormulaFamilyAnalyticPackage
        (convolutionAutocorrelation f) family) :
    Integrable
      (zetaCompletedAffineArchimedeanSeedRightKernel f family)
      (volume : Measure ℝ) :=
  let probe : ZetaAdmissibleFunction := convolutionAutocorrelation f
  let mainIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
          probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel_integrable
      probe family analyticPackage
  let remainderIntegrable :
      Integrable
        (zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
          probe family)
        (volume : Measure ℝ) :=
    zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel_integrable
      probe family analyticPackage
  let sumIntegrable :
      Integrable
        (fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              probe family t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              probe family t)
        (volume : Measure ℝ) :=
    mainIntegrable.add remainderIntegrable
  let functionEquality :
      zetaCompletedAffineArchimedeanSeedRightKernel f family =
        fun t : ℝ =>
          zetaCompletedExplicitFormulaArchimedeanRightBinetMainKernel
              probe family t +
            zetaCompletedExplicitFormulaArchimedeanRightBinetRemainderKernel
              probe family t :=
    funext
      (fun t : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanRightAffineKernel_eq_binetMain_add_remainder
          probe family t)
  Eq.subst
    (motive := fun candidate : ℝ → ℂ =>
      Integrable candidate (volume : Measure ℝ))
    functionEquality.symm
    sumIntegrable

/-- The one-sided critical seed kernel is integrable. -/
theorem zetaCompletedArchimedeanSeedCriticalKernel_integrable
    (f : ZetaAdmissibleFunction) :
    Integrable
      (zetaCompletedArchimedeanSeedCriticalKernel f)
      (volume : Measure ℝ) :=
  zetaCompletedArchimedeanCenteredIntegrand_integrable
    (convolutionAutocorrelation f)

/-- The critical-line Hermitian seed kernel is the Hermitianization of its
one-sided kernel. -/
theorem zetaCompletedHermitianArchimedeanSeedIntegrand_eq_oneSided
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    zetaCompletedHermitianArchimedeanSeedIntegrand f t =
      zetaCompletedArchimedeanSeedCriticalKernel f t +
        star (zetaCompletedArchimedeanSeedCriticalKernel f t) :=
  let archimedean : ℂ :=
    explicitFormulaArchimedeanLogDerivative
      (zetaCompletedCenteredSpectralLine t)
  let transform : ℂ :=
    zetaCompletedExplicitFormulaPhi f (t * Complex.I)
  let gram : ℂ := transform * star transform
  let gramStar : star gram = gram :=
    Eq.trans
      (star_mul transform (star transform))
      (Eq.trans
        (congrArg
          (fun value : ℂ => star transform * value)
          (star_star transform))
        (mul_comm (star transform) transform))
  let oneSidedEquality :
      zetaCompletedArchimedeanSeedCriticalKernel f t =
        archimedean * gram :=
    zetaCompletedArchimedeanCenteredIntegrand_convolutionAutocorrelation_eq_seed
      f t
  let conjugateProduct :
      star (archimedean * gram) = star archimedean * gram :=
    Eq.trans (star_mul archimedean gram)
      (congrArg (fun value : ℂ => star archimedean * value) gramStar)
  let hermitianExpansion :
      zetaCompletedHermitianArchimedeanSeedIntegrand f t =
        archimedean * gram + star archimedean * gram :=
    add_mul archimedean (star archimedean) gram
  Eq.trans hermitianExpansion
    (congrArg₂ HAdd.hAdd oneSidedEquality.symm
      (Eq.trans conjugateProduct.symm
        (congrArg star oneSidedEquality).symm))

/-- Conjugation preserves integrability of a complex kernel. -/
theorem integrable_star
    (kernel : ℝ → ℂ)
    (kernelIntegrable :
      Integrable kernel (volume : Measure ℝ)) :
    Integrable
      (fun t : ℝ => star (kernel t))
      (volume : Measure ℝ) :=
  Complex.conjLIE.toLinearIsometry.integrable_comp kernelIntegrable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

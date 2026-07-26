import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityNormalizationInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointAbsorptionAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.FinalCommonLimitFromFactorData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledHorizontalBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCarrierDataPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.EndpointPhysicalAbsorption

/-!
# Final boundary-identification positivity

This owner part keeps the final RH positivity route on the reflected physical
boundary lane.  It intentionally does not import the historical contour
assembly owner, whose direct vertical-channel normalization belongs to a
different coordinate system.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- The final completed-Weil positivity reduction: once the reflected physical
autocorrelation boundary identification is proved, endpoint physical absorption
gives raw quadratic Weil positivity. -/
theorem zetaWeilQuadraticPositivity_of_finalBoundaryIdentification_owner
    (boundaryIdentification : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_endpointAbsorbedPhysical_owner
    boundaryIdentification
    (fun f =>
      ZetaAdmissibleFunction.completedWeilEndpointAbsorbedPhysicalScalar_nonnegative_owner
        f)

/-- A common zero-side/physical-boundary contour limit is the exact remaining
input needed by the final completed-Weil positivity route. -/
theorem zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (commonLimit : ZetaCompletedAutocorrelationPoleCorrectedCommonLimit) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalBoundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit_core
      commonLimit)

/-- Physical completed-log-derivative control is the exact analytic input that
still feeds the corrected common-limit route to final completed-Weil
positivity. -/
theorem zetaWeilQuadraticPositivity_of_physicalLogDerivControl_final_owner
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_physicalLogDerivControl_owner
      hLog)

/-- Polynomial scheduled packages plus their physical boundary endpoint are
enough for the final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledBoundaryLimit_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledBoundaryLimit_final_owner
      hPolynomial
      boundaryLimit)

/-- Polynomial scheduled packages plus affine-kernel integrability and value are
enough for the final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffineKernelIntegrableValue_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffineKernelIntegrableValue_final_owner
      hPolynomial
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Polynomial scheduled packages plus affine packet data are enough for the
final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffinePacketData_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledAffinePacketData_final_owner
      hPolynomial
      packetData)

/-- Polynomial scheduled packages plus physical completed-log-derivative control
are enough for the final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledPhysicalLogDerivControl_final_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (hLog :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
          (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledPhysicalLogDerivControl_final_owner
      hPolynomial
      hLog)

/-- Canonical scheduled horizontal polynomial bounds plus the associated
physical boundary endpoint are enough for the final completed-Weil positivity
lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_boundaryLimit_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
              f
              (horizontalBounds f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    ZetaAdmissibleFunction.canonicalScheduledPolynomialPackage_of_horizontalBounds
      horizontalBounds
  zetaWeilQuadraticPositivity_of_polynomialScheduledBoundaryLimit_final_owner
    hPolynomial
    boundaryLimit

/-- Canonical scheduled horizontal polynomial bounds and the corresponding
affine-channel physical endpoint give raw Weil positivity through the final
common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_affineChannelLimit_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds.polynomialPackage
                f
                (horizontalBounds f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineChannelLimit_final_owner
      horizontalBounds
      channelLimit)

/-- Canonical scheduled horizontal polynomial bounds plus affine-kernel
integrability and value give raw Weil positivity through the final common-limit
lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_affineKernelIntegrableValue_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affineKernelIntegrableValue_final_owner
      horizontalBounds
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Canonical scheduled horizontal polynomial bounds plus affine packet data give
raw Weil positivity through the final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_affinePacketData_final_owner
      horizontalBounds
      packetData)

/-- Canonical scheduled horizontal polynomial bounds plus concrete
autocorrelation completed-log-derivative control give raw Weil positivity
through the final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_concreteControl_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_concreteControl_final_owner
      horizontalBounds
      hConcrete)

/-- Canonical scheduled horizontal polynomial bounds plus split autocorrelation
completed-log-derivative factor controls give raw Weil positivity through the
final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_splitControls_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_splitControls_final_owner
      horizontalBounds
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled horizontal polynomial bounds plus global
completed-log-derivative factor controls give raw Weil positivity through the
final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledHorizontalBounds_globalFactorControls_final_owner
    (horizontalBounds :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledPolynomialHorizontalBounds f)
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledHorizontalBounds_globalFactorControls_final_owner
      horizontalBounds
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled Cauchy path data plus the associated physical boundary
endpoint are enough for the final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_boundaryLimit_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
              f
              (K f)
              (zetaData f)
              (gammaData f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
        f
        (K f)
        (zetaData f)
        (gammaData f)
  zetaWeilQuadraticPositivity_of_polynomialScheduledBoundaryLimit_final_owner
    hPolynomial
    boundaryLimit

/-- Canonical scheduled Cauchy path data and the corresponding affine-channel
physical endpoint give raw Weil positivity through the final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineChannelLimit_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
                f (K f) (zetaData f) (gammaData f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineChannelLimit_final_owner
      K
      zetaData
      gammaData
      channelLimit)

/-- Canonical scheduled Cauchy path data plus affine-kernel integrability and
the full-line affine value give raw Weil positivity through the final
common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (rightIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (leftIntegrable :
      ∀ f : ZetaAdmissibleFunction,
        Integrable
          (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f))
          (volume : Measure ℝ))
    (valueEquality :
      ∀ f : ZetaAdmissibleFunction,
        (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) -
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              t) =
            ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_final_owner
      K
      zetaData
      gammaData
      rightIntegrable
      leftIntegrable
      valueEquality)

/-- Canonical scheduled Cauchy path data plus affine packet data give raw Weil
positivity through the final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affinePacketData_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (packetData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ZetaCompletedAutocorrelationAffinePacketData f) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_affinePacketData_final_owner
      K
      zetaData
      gammaData
      packetData)

/-- Canonical scheduled Cauchy path data plus concrete autocorrelation
completed-log-derivative control give raw Weil positivity through the final
common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_concreteControl_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hConcrete :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_concreteControl_final_owner
      K
      zetaData
      gammaData
      hConcrete)

/-- Canonical scheduled Cauchy path data plus split autocorrelation
completed-log-derivative factor controls give raw Weil positivity through the
final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_splitControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_splitControls_final_owner
      K
      zetaData
      gammaData
      hZetaSide
      hInverseGamma)

/-- Canonical scheduled Cauchy path data plus global completed-log-derivative
factor controls give raw Weil positivity through the final common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_globalFactorControls_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (hZetaSide :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivZetaSideControl)
    (hInverseGamma :
      ZetaAdmissibleFunction.CompletedZetaNegLogDerivInverseGammaControl) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCauchyPathData_globalFactorControls_final_owner
      K
      zetaData
      gammaData
      hZetaSide
      hInverseGamma)

/-- Packaged canonical scheduled carrier Cauchy data plus the associated
physical boundary endpoint are enough for the final completed-Weil positivity
lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_boundaryLimit_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
              f
              (K f)
              carrierData.pathData.zetaData f
              carrierData.pathData.gammaData f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_boundaryLimit_final_owner
    K
    carrierData.pathData.zetaData
    carrierData.pathData.gammaData
    boundaryLimit

/-- Packaged canonical scheduled carrier Cauchy data and the corresponding
affine-channel physical endpoint give raw Weil positivity through the final
common-limit lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierCauchyData_affineChannelLimit_final_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (carrierData : CanonicalScheduledCarrierCauchyData K)
    (channelLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
                f
                (K f)
                carrierData.pathData.zetaData f
                carrierData.pathData.gammaData f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineChannelLimit_final_owner
    K
    carrierData.pathData.zetaData
    carrierData.pathData.gammaData
    channelLimit

/-- Canonical scheduled-carrier factor-bound data plus its physical boundary
limit is enough for the final completed-Weil positivity lane. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_boundaryLimit_final_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledFamilyAnalyticPackage_of_carrierFactorData
              f
              ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
                ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
              (factorData f)))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_finalCommonLimit_owner
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_canonicalScheduledCarrierFactorData_boundaryLimit_owner
      factorData
      boundaryLimit)

end
end LFunctions
end Boundary

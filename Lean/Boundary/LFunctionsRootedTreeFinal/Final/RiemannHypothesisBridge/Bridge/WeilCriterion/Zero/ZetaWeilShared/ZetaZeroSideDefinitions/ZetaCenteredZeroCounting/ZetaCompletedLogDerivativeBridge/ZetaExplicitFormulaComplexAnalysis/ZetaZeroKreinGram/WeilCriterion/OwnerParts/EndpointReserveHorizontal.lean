import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.EndpointReservePositivity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalContourBoundaryHorizontal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryHorizontal
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCompletedBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.CarrierFactorData

/-!
# Endpoint reserve positivity with supplied horizontal decay

This owner part connects the explicit-horizontal contour boundary lane to the
endpoint-reserve positivity theorem without using a global scheduled carrier
as a shortcut.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- Completed Weil positivity from scheduled packages with explicit tangent,
horizontal, and boundary endpoint limits. -/
theorem zetaWeilQuadraticPositivity_of_scheduledPackageBoundaryLimit_horizontal_owner
    (hScheduled :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (htangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (zetaAutocorrelationPhysicalProbe f)
              ((hScheduled f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                ((hScheduled f).height_schedule.height u)))
    (hhorizontal :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaScheduledPackageHorizontalSideDifference
              (hScheduled f) u)
          atTop (𝓝 0))
    (boundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalScheduledPackagePoleCorrectedVertical
            f (hScheduled f))
          atTop
          (𝓝
            (zetaCompletedAffinePoleCorrectedBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_scheduledPackageBoundaryLimit_horizontal_owner
      hScheduled
      htangentEventual
      hhorizontal
      boundaryLimit)

/-- Completed Weil positivity from polynomial scheduled project-contour,
horizontal, and boundary endpoint limits. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledProjectContourBoundaryLimits_horizontal_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (projectLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (zetaAutocorrelationPhysicalProbe f))))
    (horizontalLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageHorizontalSideDifference
              (hPolynomial f) u)
          atTop
          (𝓝 (0 : ℂ)))
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_horizontal_owner
      hPolynomial
      projectLimit
      horizontalLimit
      boundaryLimit)

/-- Completed Weil positivity from polynomial scheduled project-contour and
boundary endpoint limits; horizontal decay comes from the polynomial
package itself. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledProjectContourBoundaryLimits_packageHorizontal_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (projectLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
              (zetaAutocorrelationPhysicalProbe f))))
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_packageHorizontal_owner
      hPolynomial
      projectLimit
      boundaryLimit)

/-- Completed Weil positivity from polynomial scheduled packages and the
physical boundary endpoint; project-contour and horizontal endpoints come from
the package owner chain. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledBoundaryLimit_packageHorizontal_owner
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
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledBoundaryLimit_packageHorizontal_owner
      hPolynomial
      boundaryLimit)

/-- Completed Weil positivity from polynomial scheduled packages and an
affine-channel physical boundary limit. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffineChannelLimit_packageHorizontal_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (zetaAutocorrelationPhysicalProbe f)
              (zetaAutocorrelationPhysicalContourFamily f)
              ((hPolynomial f).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f)))) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_boundaryIdentification_owner
    (zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledAffineChannelLimit_packageHorizontal_owner
      hPolynomial
      channelBoundaryLimit)

/-- Completed Weil positivity from polynomial scheduled packages and concrete
affine-kernel integrability/value identification. -/
theorem zetaWeilQuadraticPositivity_of_polynomialScheduledAffineKernelIntegrableValue_packageHorizontal_owner
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
  zetaWeilQuadraticPositivity_of_polynomialScheduledAffineChannelLimit_packageHorizontal_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedScheduledAffineVerticalChannel_tendsto_physical_of_integrable_value
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)
        (hPolynomial f).height_schedule
        (rightIntegrable f)
        (leftIntegrable f)
        (valueEquality f))

/-- Completed Weil positivity from canonical scheduled polynomial path bounds
and concrete affine-kernel integrability/value identification. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_affineKernelIntegrableValue_packageHorizontal_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (C : ZetaAdmissibleFunction → ℝ)
    (C_pos : ∀ f : ZetaAdmissibleFunction, 0 < C f)
    (topBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTopPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (bottomBound :
      ∀ f : ZetaAdmissibleFunction,
        ∀ u x : ℝ,
          x ∈ Set.uIcc
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 -
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
          ‖completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
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
  zetaWeilQuadraticPositivity_of_polynomialScheduledAffineKernelIntegrableValue_packageHorizontal_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
        f
        (K f)
        (C f)
        (C_pos f)
        (topBound f)
        (bottomBound f))
    rightIntegrable
    leftIntegrable
    valueEquality

/-- Completed Weil positivity from canonical scheduled Cauchy path data and
concrete affine-kernel integrability/value identification. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCauchyPathData_affineKernelIntegrableValue_packageHorizontal_owner
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
  zetaWeilQuadraticPositivity_of_canonicalScheduledPolynomialPathBounds_affineKernelIntegrableValue_packageHorizontal_owner
    K
    (fun f =>
      ZetaAdmissibleFunction.canonicalScheduledCauchyPathDataCompletedBoundConstant
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.canonicalScheduledCauchyPathDataCompletedBoundConstant_pos
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.completedZetaNegLogDeriv_top_bound_of_canonicalScheduledCauchyPathData
        (zetaData f)
        (gammaData f))
    (fun f =>
      ZetaAdmissibleFunction.completedZetaNegLogDeriv_bottom_bound_of_canonicalScheduledCauchyPathData
        (zetaData f)
        (gammaData f))
    rightIntegrable
    leftIntegrable
    valueEquality

/-- Completed Weil positivity from canonical scheduled carrier factor data and
concrete affine-kernel integrability/value identification. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_packageHorizontal_owner
    (factorData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.FactorBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
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
  zetaWeilQuadraticPositivity_of_polynomialScheduledAffineKernelIntegrableValue_packageHorizontal_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_carrierFactorData
        f
        ((ZetaAdmissibleFunction.zetaPhiAnalyticControl_autocorrelation_of_concreteControl
          ZetaAdmissibleFunction.zetaPhiAutocorrelationConcreteControl_owner) f)
        (factorData f))
    rightIntegrable
    leftIntegrable
    valueEquality

/-- Completed Weil positivity from canonical scheduled carrier zeta/Gamma bound
data and concrete affine-kernel integrability/value identification. -/
theorem zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierBoundData_affineKernelIntegrableValue_packageHorizontal_owner
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.ZetaSideBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CompletedZetaZeroExcisedStrip.InverseGammaBoundData
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f))
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
  zetaWeilQuadraticPositivity_of_canonicalScheduledCarrierFactorData_affineKernelIntegrableValue_packageHorizontal_owner
    (fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_factorData_of_parts
        f
        (zetaData f)
        (gammaData f))
    rightIntegrable
    leftIntegrable
    valueEquality

end
end LFunctions
end Boundary

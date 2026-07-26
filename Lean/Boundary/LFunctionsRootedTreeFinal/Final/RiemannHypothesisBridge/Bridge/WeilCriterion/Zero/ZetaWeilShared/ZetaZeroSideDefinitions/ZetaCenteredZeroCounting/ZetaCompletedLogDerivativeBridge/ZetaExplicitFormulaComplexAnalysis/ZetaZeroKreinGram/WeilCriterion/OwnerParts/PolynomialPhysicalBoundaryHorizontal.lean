import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransports
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransportsParts.ProjectContourHorizontal

/-!
# Polynomial physical boundary transport with supplied horizontal decay

This owner part exposes the physical specialization of the polynomial
project-contour horizontal split.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Every polynomial scheduled package supplies the explicit horizontal endpoint
required for the horizontal boundary lane. -/
theorem explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero_owner
    {f : ZetaAdmissibleFunction} {F : ZetaAdmissibleFunction.ExplicitFormulaContourFamily}
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        f F) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageHorizontalSideDifference
          h u)
      atTop
      (𝓝 (0 : ℂ)) :=
  ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero
    h

/-- A family of polynomial scheduled packages supplies the horizontal endpoint
family required for the horizontal boundary lane. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledHorizontal_tendsto_zero_family_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)) :
    ∀ f : ZetaAdmissibleFunction,
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageHorizontalSideDifference
            (hPolynomial f) u)
        atTop
        (𝓝 (0 : ℂ)) :=
  fun f =>
    explicitFormulaPolynomialScheduledPackageHorizontalSideDifference_tendsto_zero_owner
      (hPolynomial f)

/-- The selected tangent-residue owner gives the normalized project-contour
zero-side endpoint for a physical polynomial scheduled package. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledProjectContour_tendsto_zeroSide_of_selectedTangent_owner
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          (h.height_schedule.height u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_polynomialScheduledPackage_tangentEventual
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h)
    (summable_zetaZeroSideContribution_owner
      (zetaAutocorrelationPhysicalProbe f))

/-- A family of physical polynomial scheduled packages supplies the normalized
project-contour zero-side endpoint family. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledProjectContour_tendsto_zeroSide_family_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)) :
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
            (zetaAutocorrelationPhysicalProbe f))) :=
  fun f =>
    zetaAutocorrelationPhysicalPolynomialScheduledProjectContour_tendsto_zeroSide_of_selectedTangent_owner
      f (hPolynomial f)

/-- A polynomial scheduled normalized project-contour limit and explicit
horizontal decay give the physical polynomial zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_projectContourLimit_horizontal
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (projectLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            (h.height_schedule.height u))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (zetaAutocorrelationPhysicalProbe f))))
    (horizontalLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageHorizontalSideDifference
            h u)
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_projectContourLimit_horizontal
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    h
    projectLimit
    horizontalLimit

/-- Polynomial scheduled project-contour, horizontal, and boundary endpoints
give the exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_horizontal_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledEndpointLimits_owner
    hPolynomial
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_projectContourLimit_horizontal
        f
        (hPolynomial f)
        (projectLimit f)
        (horizontalLimit f))
    boundaryLimit

/-- Polynomial scheduled project-contour and boundary endpoints give the exact
autocorrelation boundary identification; the horizontal endpoint comes from the
polynomial package itself. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_packageHorizontal_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_horizontal_owner
    hPolynomial
    projectLimit
    (zetaAutocorrelationPhysicalPolynomialScheduledHorizontal_tendsto_zero_family_owner
      hPolynomial)
    boundaryLimit

/-- Polynomial scheduled packages plus the physical boundary endpoint give the
exact autocorrelation boundary identification; project-contour and horizontal
endpoints come from the package owner chain. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledBoundaryLimit_packageHorizontal_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_packageHorizontal_owner
    hPolynomial
    (zetaAutocorrelationPhysicalPolynomialScheduledProjectContour_tendsto_zeroSide_family_owner
      hPolynomial)
    boundaryLimit

/-- Polynomial scheduled packages plus an affine-channel physical limit give the
exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledAffineChannelLimit_packageHorizontal_owner
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
    ZetaWeilAutocorrelationBoundaryIdentification :=
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledBoundaryLimit_packageHorizontal_owner
    hPolynomial
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

end
end LFunctions
end Boundary

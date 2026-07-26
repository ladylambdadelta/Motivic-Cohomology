import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PolynomialPhysicalBoundaryTransportsParts.TangentResidue
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.FactorPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationTransports

/-!
# Polynomial physical boundary transports

This file owns the fixed-degree scheduled physical boundary lane.  It avoids
promoting a polynomial horizontal estimate into a global full strip-control
package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

/-- The polynomial scheduled physical vertical expression with the completed
pole packet removed. -/
noncomputable def zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)) :
    ℝ → ℂ :=
  fun u : ℝ =>
    (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
        (zetaAutocorrelationPhysicalProbe f)
        ((zetaAutocorrelationPhysicalContourFamily f).rectangle
          (h.height_schedule.height u)) -
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
        (zetaAutocorrelationPhysicalProbe f)
        ((zetaAutocorrelationPhysicalContourFamily f).rectangle
          (h.height_schedule.height u))) /
      ZetaAdmissibleFunction.explicitFormulaTwoPi -
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum
      (zetaAutocorrelationPhysicalProbe f)

/-- A polynomial scheduled normalized project-contour limit gives the physical
polynomial scheduled zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_projectContourLimit
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
            (zetaAutocorrelationPhysicalProbe f)))) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  ZetaAdmissibleFunction.explicitFormulaPolynomialScheduledPackageNormalizedPoleCorrectedVerticalDifference_tendsto_zeroSideComplex_of_projectContourLimit
    (zetaAutocorrelationPhysicalProbe f)
    (zetaAutocorrelationPhysicalContourFamily f)
    h
    projectLimit

/-- Polynomial scheduled tangent-residue equality gives the physical polynomial
scheduled zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (tangentEventual :
      ∀ᶠ u in atTop,
        ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
            (zetaAutocorrelationPhysicalProbe f)
            (h.height_schedule.height u) =
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
            (zetaAutocorrelationPhysicalProbe f)
            ((zetaAutocorrelationPhysicalContourFamily f).rectangle
              (h.height_schedule.height u))) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_projectContourLimit
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangleNormalizedPoleCorrectedContourIntegral_tendsto_zeroSideComplex_of_polynomialScheduledPackage_tangentEventual
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      tangentEventual
      (summable_zetaZeroSideContribution_owner
        (zetaAutocorrelationPhysicalProbe f)))

/-- Pointwise raw Cauchy tangent-residue equality gives the physical polynomial
scheduled zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_rawTangentPointwise
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (rawPointwise :
      ∀ u : ℝ,
        0 < h.height_schedule.height u →
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) =
            ZetaAdmissibleFunction.explicitFormulaTwoPiI •
              ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
                (zetaAutocorrelationPhysicalProbe f)
                (h.height_schedule.height u)) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_rawPointwise
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h
      rawPointwise)

/-- The selected-radius polynomial tangent-residue theorem gives the physical
polynomial scheduled zero-side endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_selectedTangentResidue
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
          (zetaAutocorrelationPhysicalProbe f))) :=
  zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
    f
    h
    (ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
      (zetaAutocorrelationPhysicalProbe f)
      (zetaAutocorrelationPhysicalContourFamily f)
      h)

theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_family_of_selectedTangentResidue
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)) :
    ∀ f : ZetaAdmissibleFunction,
      Tendsto
        (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
          f (hPolynomial f))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.zetaCompletedZeroSideComplex
            (zetaAutocorrelationPhysicalProbe f))) :=
  fun f =>
    zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_selectedTangentResidue
      f
      (hPolynomial f)

/-- Polynomial scheduled endpoint limits construct the common-limit surface. -/
theorem zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledEndpointLimits
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
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
    ZetaCompletedAutocorrelationPoleCorrectedCommonLimit :=
  zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_limitFamily
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
        f (hPolynomial f))
    zeroLimit
    boundaryLimit

/-- Polynomial scheduled endpoint limits give the exact autocorrelation boundary
identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledEndpointLimits_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (zeroLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical
            f (hPolynomial f))
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
  zetaWeilAutocorrelationBoundaryIdentification_of_commonLimit
    (zetaCompletedAutocorrelationPoleCorrectedCommonLimit_of_polynomialScheduledEndpointLimits
      hPolynomial
      zeroLimit
      boundaryLimit)

theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledSelectedTangentBoundaryLimit_owner
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
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledEndpointLimits_owner
    hPolynomial
    (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_family_of_selectedTangentResidue
      hPolynomial)
    boundaryLimit

/-- Polynomial scheduled project-contour and boundary endpoint limits give the
exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledProjectContourBoundaryLimits_owner
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
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledEndpointLimits_owner
    hPolynomial
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_projectContourLimit
        f
        (hPolynomial f)
        (projectLimit f))
    boundaryLimit

/-- Polynomial scheduled tangent-residue and boundary endpoint limits give the
exact autocorrelation boundary identification. -/
theorem zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledTangentBoundaryLimits_owner
    (hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f))
    (tangentEventual :
      ∀ f : ZetaAdmissibleFunction,
        ∀ᶠ u in atTop,
          ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum
              (zetaAutocorrelationPhysicalProbe f)
              ((hPolynomial f).height_schedule.height u) =
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaNormalizedTangentContourIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                ((hPolynomial f).height_schedule.height u)))
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
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_zeroSide_of_tangentEventual
        f
        (hPolynomial f)
        (tangentEventual f))
    boundaryLimit

/-- A raw right-minus-left vertical limit gives the polynomial scheduled
pole-corrected physical boundary endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_rawVerticalLimit
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (rawLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  let probe : ZetaAdmissibleFunction := zetaAutocorrelationPhysicalProbe f
  let polePacket : ℂ :=
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum probe
  let boundary : ℂ := zetaCompletedAffinePhysicalBoundaryChannel probe
  let dividedLimit :
      Tendsto
        (fun u : ℝ =>
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
                probe
                ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                  (h.height_schedule.height u)) -
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
                probe
                ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                  (h.height_schedule.height u))) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi)
        atTop
        (𝓝
          ((ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi)) :=
    rawLimit.div_const ZetaAdmissibleFunction.explicitFormulaTwoPi
  let poleLimit :
      Tendsto (fun value : ℝ => polePacket) atTop (𝓝 polePacket) :=
    tendsto_const_nhds
  let correctedLimit :
      Tendsto
        (fun u : ℝ =>
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
                probe
                ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                  (h.height_schedule.height u)) -
              ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
                probe
                ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                  (h.height_schedule.height u))) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi -
          polePacket)
        atTop
        (𝓝
          ((ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
              ZetaAdmissibleFunction.explicitFormulaTwoPi -
            polePacket)) :=
    dividedLimit.sub poleLimit
  let divisionEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        boundary :=
    mul_div_cancel_left₀ boundary
      ZetaAdmissibleFunction.explicitFormulaTwoPi_ne_zero
  let targetEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi -
          polePacket =
        zetaCompletedAffinePoleCorrectedBoundaryChannel probe :=
    Eq.trans
      (congrArg (fun value : ℂ => value - polePacket) divisionEquality)
      (zetaCompletedAffinePoleCorrectedBoundaryChannel_eq probe).symm
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
        atTop
        (𝓝 target))
    targetEquality
    correctedLimit

/-- A polynomial scheduled affine-channel limit gives the physical
pole-corrected boundary endpoint. -/
theorem zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
    (f : ZetaAdmissibleFunction)
    (h :
      ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f))
    (channelLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            (zetaAutocorrelationPhysicalProbe f)
            (zetaAutocorrelationPhysicalContourFamily f)
            (h.height_schedule.height u))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f)))) :
    Tendsto
      (zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical f h)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (zetaAutocorrelationPhysicalProbe f))) :=
  let rawFunctionEquality :
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          (h.height_schedule.height u)) =
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
            (zetaAutocorrelationPhysicalProbe f)
            ((zetaAutocorrelationPhysicalContourFamily f).rectangle
              (h.height_schedule.height u)) -
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
            (zetaAutocorrelationPhysicalProbe f)
            ((zetaAutocorrelationPhysicalContourFamily f).rectangle
              (h.height_schedule.height u))) :=
    funext
      (fun u : ℝ =>
        zetaCompletedAffineVerticalChannel_eq_rightLineIntegral_sub_leftLineIntegral
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f)
          (h.height_schedule.height u))
  let rawLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral
              (zetaAutocorrelationPhysicalProbe f)
              ((zetaAutocorrelationPhysicalContourFamily f).rectangle
                (h.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel
              (zetaAutocorrelationPhysicalProbe f))) :=
    Eq.subst
      (motive := fun values : ℝ → ℂ =>
        Tendsto values atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (zetaAutocorrelationPhysicalProbe f))))
      rawFunctionEquality
      channelLimit
  zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_rawVerticalLimit
    f h rawLimit

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledPolynomialPathBounds_affineChannelLimit_owner
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
          ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv
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
          ‖ZetaAdmissibleFunction.completedZetaNegLogDeriv
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBottomPath
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x)‖ ≤
            C f *
              (1 +
                ‖(ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^
                K f)
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
                f (K f) (C f) (C_pos f) (topBound f) (bottomBound f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_pathBounds
        f (K f) (C f) (C_pos f) (topBound f) (bottomBound f)
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledTangentBoundaryLimits_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)
        (hPolynomial f))
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

theorem zetaWeilAutocorrelationBoundaryIdentification_of_canonicalScheduledCauchyPathData_affineChannelLimit_owner
    (K : ZetaAdmissibleFunction → ℕ)
    (zetaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledZetaSideCauchyPathData
          f (K f))
    (gammaData :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.CanonicalScheduledInverseGammaCauchyPathData
          f (K f))
    (channelBoundaryLimit :
      ∀ f : ZetaAdmissibleFunction,
        Tendsto
          (fun u : ℝ =>
            ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
              (ZetaAdmissibleFunction.convolutionAutocorrelation f)
              (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
              ((ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
                f (K f) (zetaData f) (gammaData f)).height_schedule.height u))
          atTop
          (𝓝
            (ZetaAdmissibleFunction.explicitFormulaTwoPi *
              zetaCompletedAffinePhysicalBoundaryChannel
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)))) :
    ZetaWeilAutocorrelationBoundaryIdentification :=
  let hPolynomial :
      ∀ f : ZetaAdmissibleFunction,
        ZetaAdmissibleFunction.ExplicitFormulaScheduledPolynomialFamilyAnalyticPackage
          (zetaAutocorrelationPhysicalProbe f)
          (zetaAutocorrelationPhysicalContourFamily f) :=
    fun f =>
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationScheduledPolynomialFamilyAnalyticPackage_of_cauchyPathData
        f (K f) (zetaData f) (gammaData f)
  zetaWeilAutocorrelationBoundaryIdentification_of_polynomialScheduledTangentBoundaryLimits_owner
    hPolynomial
    (fun f =>
      ZetaAdmissibleFunction.explicitFormulaRectangle_poleCorrectedResidueSum_eventually_eq_normalizedTangent_of_polynomialScheduledPackage_selected
        (zetaAutocorrelationPhysicalProbe f)
        (zetaAutocorrelationPhysicalContourFamily f)
        (hPolynomial f))
    (fun f =>
      zetaAutocorrelationPhysicalPolynomialScheduledPoleCorrectedVertical_tendsto_boundary_of_affineChannelLimit
        f
        (hPolynomial f)
        (channelBoundaryLimit f))

end
end LFunctions
end Boundary

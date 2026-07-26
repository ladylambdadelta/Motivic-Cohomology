import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SelectedRadiusCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledLogDerivControl

/-!
# Scheduled selected-radius finite-hole Cauchy

This file peels the finite-hole Cauchy input needed by the scheduled residue
assembly away from the full analytic package.  The proofs keep only the local
data actually used by Cauchy-Goursat: transform regularity, boundary regularity,
interior zero-coordinate identification, and closed-radius geometry.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Package-free interior differentiability off the raw finite singular carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_differentiableAt_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_differentiableAt_off_singularSet
    phiControl
    (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
      F hT hinterior (hRInterior z hz) (hROff z hz))

/-- Package-free interior continuity off the raw finite singular carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_continuousAt_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_continuousAt_off_singularSet
    phiControl
    (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
      F hT hinterior (hRInterior z hz) (hROff z hz))

/-- Package-free interior continuity on any off-raw carrier. -/
theorem explicitFormulaRectangleInteriorOffRawSingular_continuousOn_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (R : Set ℂ)
    (hRInterior :
      ∀ z : ℂ, z ∈ R → z ∈ explicitFormulaContourFamilyInterior F T)
    (hROff :
      ∀ z : ℂ, z ∈ R → z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) R :=
  fun z hz =>
    (explicitFormulaRectangleInteriorOffRawSingular_continuousAt_of_phiControl
      f F phiControl hT hinterior R hRInterior hROff hz).continuousWithinAt

/-- Package-free closed-cell continuity from interior-or-boundary location data. -/
theorem explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousAt_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (R : Set ℂ)
    (hRLocation :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T ∨
          z ∈ explicitFormulaContourFamilyBoundary F T)
    (hROff :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T)
    {z : ℂ}
    (hz : z ∈ R) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  match hRLocation z hz with
  | Or.inl hzInterior =>
      completedZetaContourIntegrand_continuousAt_off_singularSet
        phiControl
        (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
          F hT hinterior hzInterior (hROff z hz hzInterior))
  | Or.inr hzBoundary =>
      (hboundary z hzBoundary).1

/-- Package-free closed-cell continuity from interior-or-boundary location data. -/
theorem explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousOn_of_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (R : Set ℂ)
    (hRLocation :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T ∨
          z ∈ explicitFormulaContourFamilyBoundary F T)
    (hROff :
      ∀ z : ℂ, z ∈ R →
        z ∈ explicitFormulaContourFamilyInterior F T →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) R :=
  fun z hz =>
    (explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousAt_of_phiControl
      f F phiControl hT hinterior hboundary R hRLocation hROff hz).continuousWithinAt

/-- Package-free Cauchy-Goursat zero for one half-radius regular grid cell. -/
theorem ExplicitFormulaRectangleRegularGridCell.boundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls_phiControl
    {F : ExplicitFormulaContourFamily} {T epsilon : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T (epsilon / 2))
    (f : ZetaAdmissibleFunction)
    (phiControl : ZetaPhiAnalyticControl f)
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) :
    finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        c.lower c.upper = 0 :=
  let s : Set ℂ := completedZetaContourIntegrandSingularSet
  let hs : s.Countable := completedZetaContourIntegrandSingularSet_countable
  let Hc :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (Set.uIcc c.lower.re c.upper.re ×ℂ
          Set.uIcc c.lower.im c.upper.im) :=
    explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousOn_of_phiControl
      f F phiControl hT hinterior hboundary
      (Set.uIcc c.lower.re c.upper.re ×ℂ
        Set.uIcc c.lower.im c.upper.im)
      (fun z hz =>
        c.closedCell_mem_interior_or_boundary_of_halfRadius_closedRadiusControls
          hT hepsilon hclosed hz)
      (fun z hz hzInterior =>
        c.closedCell_not_mem_rawSingularCoordinates hz)
  let Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min c.lower.re c.upper.re)
                (max c.lower.re c.upper.re) ×ℂ
              Set.Ioo (min c.lower.im c.upper.im)
                (max c.lower.im c.upper.im) \ s →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x :=
    fun x hx =>
      let hxInterior :
          x ∈ explicitFormulaContourFamilyInterior F T :=
        c.openCell_mem_interior_of_halfRadius_closedRadiusControls
          hT hepsilon hclosed hx.1
      let hxOffRaw :
          x ∉ explicitFormulaRectangleRawSingularCoordinates T :=
        c.openCell_not_mem_rawSingularCoordinates hx.1
      completedZetaContourIntegrand_differentiableAt_off_singularSet
        phiControl
        (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
          F hT hinterior hxInterior hxOffRaw)
  finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    c.lower c.upper s hs Hc Hd

/-- Package-free endpoint-data Cauchy-Goursat zero. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.boundary_eq_zero_of_halfRadius_closedRadiusControls_phiControl
    {F : ExplicitFormulaContourFamily} {T epsilon : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2))
    (f : ZetaAdmissibleFunction)
    (phiControl : ZetaPhiAnalyticControl f)
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0 :=
  d.toRegularGridCell.boundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls_phiControl
    f phiControl hT hepsilon hinterior hboundary hclosed

/-- Package-free endpoint-data boundary-sum vanishing. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_halfRadius_closedRadiusControls_phiControl
    {F : ExplicitFormulaContourFamily} {T epsilon : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)))
    (phiControl : ZetaPhiAnalyticControl f)
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data = 0 :=
  explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_forall_mem
    f data
    (fun d _hd =>
      d.boundary_eq_zero_of_halfRadius_closedRadiusControls_phiControl
        f phiControl hT hepsilon hinterior hboundary hclosed)

/-- Package-free half-radius inscribed-square Cauchy-Goursat zero. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointDataBoundarySum_halfRadius_closedRadiusControls_phiControl
    {F : ExplicitFormulaContourFamily} {T epsilon : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)))
    (f : ZetaAdmissibleFunction)
    (phiControl : ZetaPhiAnalyticControl f)
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (epsilon / 2) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (epsilon / 2) = 0 :=
  Eq.trans hsubdivision
    (explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_halfRadius_closedRadiusControls_phiControl
      f data phiControl hT hepsilon hinterior hboundary hclosed)

/-- Package-free subdivision form of half-radius inscribed-square Cauchy. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls_phiControl
    {F : ExplicitFormulaContourFamily} {T epsilon : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (epsilon / 2)))
    (f : ZetaAdmissibleFunction)
    (phiControl : ZetaPhiAnalyticControl f)
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (epsilon / 2) = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointDataBoundarySum_halfRadius_closedRadiusControls_phiControl
    data f phiControl hT hepsilon hinterior hboundary hclosed
    (explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum
      f data hsubdivision)

/-- Package-free continuity on a raw half-annulus. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_continuousOn_of_closedRadiusControls_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ContinuousOn
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Metric.closedBall a epsilon \ Metric.ball a (epsilon / 2)) :=
  explicitFormulaRectangleInteriorOffRawSingular_continuousOn_of_phiControl
    f F phiControl hT hinterior
    (Metric.closedBall a epsilon \ Metric.ball a (epsilon / 2))
    (explicitFormulaRectangleRawSingularHalfAnnulus_subset_interior_of_closedRadiusControls
      F T epsilon hclosed a ha)
    (explicitFormulaRectangleRawSingularHalfAnnulus_offRaw_of_closedRadiusControls
      T epsilon hepsilon hsep a ha)

/-- Package-free differentiability on a raw half-annulus. -/
theorem explicitFormulaRectangleRawSingularHalfAnnulus_differentiableAt_of_closedRadiusControls_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (a : ℂ)
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (z : ℂ)
    (hz : z ∈ Metric.ball a epsilon \ Metric.closedBall a (epsilon / 2)) :
    DifferentiableAt ℂ
      (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  let hzClosed : z ∈ Metric.closedBall a epsilon :=
    Metric.mem_closedBall.mpr
      (le_of_lt (Metric.mem_ball.mp hz.1))
  let hzNotBall : z ∉ Metric.ball a (epsilon / 2) :=
    fun hzBall =>
      hz.2
        (Metric.mem_closedBall.mpr
          (le_of_lt (Metric.mem_ball.mp hzBall)))
  let hzAnnulus :
      z ∈ Metric.closedBall a epsilon \ Metric.ball a (epsilon / 2) :=
    And.intro hzClosed hzNotBall
  explicitFormulaRectangleInteriorOffRawSingular_differentiableAt_of_phiControl
    f F phiControl hT hinterior
    (Metric.closedBall a epsilon \ Metric.ball a (epsilon / 2))
    (explicitFormulaRectangleRawSingularHalfAnnulus_subset_interior_of_closedRadiusControls
      F T epsilon hclosed a ha)
    (explicitFormulaRectangleRawSingularHalfAnnulus_offRaw_of_closedRadiusControls
      T epsilon hepsilon hsep a ha)
    hzAnnulus

/-- Package-free closed-radius transport from half radius to selected radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    {T epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (hhalfZero :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T (epsilon / 2) = 0) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T epsilon = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_annulus_regular_radius_transport
    f F T
    (finiteRectangle_halfRadius_pos hepsilon)
    (finiteRectangle_halfRadius_le_self hepsilon)
    hhalfZero
    (fun _a : ℂ => completedZetaContourIntegrandSingularSet)
    (fun _a _ha => completedZetaContourIntegrandSingularSet_countable)
    (fun a ha =>
      explicitFormulaRectangleRawSingularHalfAnnulus_continuousOn_of_closedRadiusControls_phiControl
        f F phiControl hT hepsilon hinterior hclosed hsep a ha)
    (fun a ha z hz =>
      explicitFormulaRectangleRawSingularHalfAnnulus_differentiableAt_of_closedRadiusControls_phiControl
        f F phiControl hT hepsilon hinterior hclosed hsep a ha z hz.1)

/-- Package-free finite-hole Cauchy at one selected square-side regular radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius_boundaryData_phiControl
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T))
    (hgrid :
      ∀ radius : ℝ,
        0 < radius →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2) (-T) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2) T →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a).im) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a).im) →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2) F.c →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2) (1 - F.c) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a).re) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a).re) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → radius + radius < dist a b) →
            ∃ grid :
                List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (radius / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f grid)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (epsilon / 2) a =
            explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F T epsilon = 0 :=
  match explicitFormulaRectangle_selectedRegularRadius_sideIntegrability_of_boundaryData
      f F phiControl T hT hepsilon hboundaryRegular hboundaryAvoidance hclosed hregular with
  | ⟨hbottom, htop, hbottomHole, htopHole, hright, hleft, hrightHole, hleftHole⟩ =>
      match hgrid epsilon hepsilon hclosed
          hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hseparated with
      | ⟨grid, hsubdivision⟩ =>
          let hsquare :
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                f F T (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls_phiControl
              grid f phiControl hT hepsilon hinterior hboundaryRegular hclosed hsubdivision
          let hhalfZero :
              explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
                f F T (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
              f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2))
              hsquare hdeleted
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls_phiControl
            f F phiControl hT hepsilon hinterior hclosed hseparated hhalfZero

/-- Scheduled finite-hole Cauchy at one selected square-side regular radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_scheduledPackage_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaScheduledFamilyAnalyticPackage f F) {u epsilon : ℝ}
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F (h.height_schedule.height u) epsilon = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius_boundaryData_phiControl
    f F h.phi_control hT hepsilon hinterior hboundaryRegular hboundaryAvoidance hclosed hseparated
    hregular
    (explicitFormulaRectangleComplement_hgrid_noPackage f F hT)
    (explicitFormulaRectangleComplement_circleEqSquare_of_puncturedResidueRegularity
      f (h.height_schedule.height u) epsilon hepsilon
      (fun a ha =>
        explicitFormulaRectangleRawSingular_puncturedResidueRegularity_of_coefficientRegularity
          f h.phi_control a ha
          (explicitFormulaRectangleRawSingular_coefficientRegularity_of_phiControl
            f F h.phi_control hT hinterior epsilon hepsilon hclosed hseparated a ha)))

/- Radius-selection owner: common closed-radius controls are shrunk once more
   away from the finite square-side forbidden set. -/
theorem explicitFormulaRectangle_exists_selectedRegularRadius_of_localControls
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hlocal :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ r : ℝ, 0 < r ∧
            Metric.ball a r ⊆ explicitFormulaContourFamilyInterior F T) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) ∧
      ε ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T) := by
  exact explicitFormulaRectangleRawSingularCoordinates_exists_squareSideRegular_closedRadiusControls
    F T hlocal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

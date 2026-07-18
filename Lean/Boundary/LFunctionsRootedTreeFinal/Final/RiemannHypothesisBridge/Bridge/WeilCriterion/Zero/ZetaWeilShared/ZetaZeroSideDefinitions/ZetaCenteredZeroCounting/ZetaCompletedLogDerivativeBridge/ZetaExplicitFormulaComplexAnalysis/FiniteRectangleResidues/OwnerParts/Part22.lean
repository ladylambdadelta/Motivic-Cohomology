import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part21

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A closed point of a regular grid cell is either in the contour-family interior or on
the contour-family boundary under the selected closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.closedCell_mem_interior_or_boundary_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz : z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
      Set.uIcc c.lower.im c.upper.im)) :
    z ∈ explicitFormulaContourFamilyInterior F T ∨
      z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hbox :
      z ∈ (Set.uIcc F.c (1 - F.c) ×ℂ Set.Icc (-T) T) :=
    c.closedCell_subset_outerClosedCell_of_closedRadiusControls
      hT_nonneg hε hclosed hz
  exact
    explicitFormulaContourFamily_closedBox_mem_interior_or_boundary
      F T hbox.1 hbox.2

/-- Closed-radius controls at radius `ε` give closed-cell location for the regular grid
whose deleted squares have half-width `ε / 2`. -/
theorem ExplicitFormulaRectangleRegularGridCell.closedCell_mem_interior_or_boundary_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz : z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
      Set.uIcc c.lower.im c.upper.im)) :
    z ∈ explicitFormulaContourFamilyInterior F T ∨
      z ∈ explicitFormulaContourFamilyBoundary F T :=
  c.closedCell_mem_interior_or_boundary_of_closedRadiusControls
    (le_of_lt hT)
    (finiteRectangle_halfRadius_nonneg hε)
    (explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hε hclosed)
    hz

/-- Closed-radius controls at radius `ε` put every open cell of the half-radius regular grid
inside the contour interior. -/
theorem ExplicitFormulaRectangleRegularGridCell.openCell_mem_interior_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz :
      z ∈ Set.Ioo (min c.lower.re c.upper.re)
            (max c.lower.re c.upper.re) ×ℂ
          Set.Ioo (min c.lower.im c.upper.im)
            (max c.lower.im c.upper.im)) :
    z ∈ explicitFormulaContourFamilyInterior F T :=
  c.openCell_mem_interior_of_closedRadiusControls
    (le_of_lt hT)
    (finiteRectangle_halfRadius_nonneg hε)
    (explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hε hclosed)
    hz

/-- Closed-radius controls and regular-cell omission give both closed-cell location and
raw-singular avoidance for a half-radius regular grid cell. -/
theorem ExplicitFormulaRectangleRegularGridCell.closedCell_location_and_offRaw_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz : z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
      Set.uIcc c.lower.im c.upper.im)) :
    (z ∈ explicitFormulaContourFamilyInterior F T ∨
        z ∈ explicitFormulaContourFamilyBoundary F T) ∧
      z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  And.intro
    (c.closedCell_mem_interior_or_boundary_of_halfRadius_closedRadiusControls
      hT hε hclosed hz)
    (c.closedCell_not_mem_rawSingularCoordinates hz)

/-- Closed-radius controls give closed-cell location for every cell in a finite family
of half-radius regular grid cells. -/
theorem explicitFormulaRectangleRegularGridCellFamily_closedCell_location_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
          Set.uIcc c.lower.im c.upper.im) →
          z ∈ explicitFormulaContourFamilyInterior F T ∨
            z ∈ explicitFormulaContourFamilyBoundary F T :=
  fun c _hc _z hz =>
    c.closedCell_mem_interior_or_boundary_of_halfRadius_closedRadiusControls
      hT hε hclosed hz

/-- Closed-radius controls give closed-cell location and raw-singular avoidance for every
cell in a finite family of half-radius regular grid cells. -/
theorem explicitFormulaRectangleRegularGridCellFamily_closedCell_location_and_offRaw_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
          Set.uIcc c.lower.im c.upper.im) →
          (z ∈ explicitFormulaContourFamilyInterior F T ∨
              z ∈ explicitFormulaContourFamilyBoundary F T) ∧
            z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  fun c _hc _z hz =>
    c.closedCell_location_and_offRaw_of_halfRadius_closedRadiusControls
      hT hε hclosed hz

/-- Closed-radius controls give open-cell interior membership for every cell in a finite
family of half-radius regular grid cells. -/
theorem explicitFormulaRectangleRegularGridCellFamily_openCell_interior_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ Set.Ioo (min c.lower.re c.upper.re)
              (max c.lower.re c.upper.re) ×ℂ
            Set.Ioo (min c.lower.im c.upper.im)
              (max c.lower.im c.upper.im) →
          z ∈ explicitFormulaContourFamilyInterior F T :=
  fun c _hc _z hz =>
    c.openCell_mem_interior_of_halfRadius_closedRadiusControls
      hT hε hclosed hz

/-- Every closed cell in a finite family of half-radius regular grid cells avoids the raw
singular-coordinate carrier. -/
theorem explicitFormulaRectangleRegularGridCellFamily_closedCell_offRaw_of_halfRadius
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2))) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
          Set.uIcc c.lower.im c.upper.im) →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  fun c _hc _z hz =>
    c.closedCell_not_mem_rawSingularCoordinates hz

/-- Every open cell in a finite family of half-radius regular grid cells avoids the raw
singular-coordinate carrier. -/
theorem explicitFormulaRectangleRegularGridCellFamily_openCell_offRaw_of_halfRadius
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2))) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ Set.Ioo (min c.lower.re c.upper.re)
              (max c.lower.re c.upper.re) ×ℂ
            Set.Ioo (min c.lower.im c.upper.im)
              (max c.lower.im c.upper.im) →
          z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  fun c _hc _z hz =>
    c.openCell_not_mem_rawSingularCoordinates hz

/-- Closed-radius controls give both open-cell interior membership and raw-singular
avoidance for every cell in a finite family of half-radius regular grid cells. -/
theorem explicitFormulaRectangleRegularGridCellFamily_openCell_interior_and_offRaw_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (hT : 0 < T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
      ∀ z : ℂ,
        z ∈ Set.Ioo (min c.lower.re c.upper.re)
              (max c.lower.re c.upper.re) ×ℂ
            Set.Ioo (min c.lower.im c.upper.im)
              (max c.lower.im c.upper.im) →
          z ∈ explicitFormulaContourFamilyInterior F T ∧
            z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  fun c hc z hz =>
    And.intro
      (explicitFormulaRectangleRegularGridCellFamily_openCell_interior_of_halfRadius_closedRadiusControls
        cells hT hε hclosed c hc z hz)
      (explicitFormulaRectangleRegularGridCellFamily_openCell_offRaw_of_halfRadius
        cells c hc z hz)

/-- Cauchy-Goursat zero for one half-radius regular grid cell, using the endpoint-derived
closed-cell location and regular-cell raw-carrier omission facts. -/
theorem ExplicitFormulaRectangleRegularGridCell.boundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        c.lower c.upper = 0 := by
  let s : Set ℂ := completedZetaContourIntegrandSingularSet
  have hs : s.Countable :=
    completedZetaContourIntegrandSingularSet_countable
  have Hc :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (Set.uIcc c.lower.re c.upper.re ×ℂ
          Set.uIcc c.lower.im c.upper.im) :=
    explicitFormulaRectangleInteriorOrBoundaryOffRawSingular_continuousOn
      f F h hT hinterior hboundary
      (Set.uIcc c.lower.re c.upper.re ×ℂ
        Set.uIcc c.lower.im c.upper.im)
      (fun z hz =>
        c.closedCell_mem_interior_or_boundary_of_halfRadius_closedRadiusControls
          hT hε hclosed hz)
      (fun z hz _hzInterior =>
        c.closedCell_not_mem_rawSingularCoordinates hz)
  have Hd :
      ∀ x : ℂ,
        x ∈
            Set.Ioo (min c.lower.re c.upper.re)
                (max c.lower.re c.upper.re) ×ℂ
              Set.Ioo (min c.lower.im c.upper.im)
                (max c.lower.im c.upper.im) \ s →
          DifferentiableAt ℂ
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) x := by
    intro x hx
    have hxInterior :
        x ∈ explicitFormulaContourFamilyInterior F T :=
      c.openCell_mem_interior_of_halfRadius_closedRadiusControls
        hT hε hclosed hx.1
    have hxOffRaw :
        x ∉ explicitFormulaRectangleRawSingularCoordinates T :=
      c.openCell_not_mem_rawSingularCoordinates hx.1
    exact
      completedZetaContourIntegrand_differentiableAt_off_singularSet
        h.phi_control
        (explicitFormulaRectangleInterior_not_mem_singularSet_of_not_mem_rawSingularCoordinates
          F hT hinterior hxInterior hxOffRaw)
  exact
    finiteRectangleSubdivisionCellBoundaryIntegral_eq_zero_of_differentiable_on_off_countable
      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      c.lower c.upper s hs Hc Hd

/-- Cauchy-Goursat zero for one endpoint datum, after converting it to the associated
half-radius regular grid cell. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.boundary_eq_zero_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0 :=
  d.toRegularGridCell.boundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
    f h hT hε hinterior hboundary hclosed

/-- The endpoint-data boundary sum over a list of half-radius regular grid cells vanishes
under the closed-radius controls. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)))
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data = 0 :=
  explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_forall_mem
    f data
    (fun d _hd =>
      d.boundary_eq_zero_of_halfRadius_closedRadiusControls
        f h hT hε hinterior hboundary hclosed)

/-- Cauchy-Goursat zero from a concrete endpoint-data list boundary-sum subdivision at
half radius.  The list is consumed directly, without filtering or quotienting through a
`Finset`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointDataBoundarySum_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T (ε / 2) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
      exact hsubdivision
    _ = 0 := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_halfRadius_closedRadiusControls
          f data h hT hε hinterior hboundary hclosed

/-- A selected regular grid cell is ordered in both coordinate directions. -/
theorem ExplicitFormulaRectangleRegularGridCell.ordered
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    explicitFormulaRectangleGridCellOrdered c.cell :=
  c.regular.1.1

/-- A selected regular grid cell has adjacent horizontal endpoints. -/
theorem ExplicitFormulaRectangleRegularGridCell.noIntermediateX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    explicitFormulaRectangleNoIntermediateXEndpoint F T ε c.cell.1.1 c.cell.1.2 :=
  c.regular.1.2.1

/-- A selected regular grid cell has adjacent vertical endpoints. -/
theorem ExplicitFormulaRectangleRegularGridCell.noIntermediateY
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    explicitFormulaRectangleNoIntermediateYEndpoint T ε c.cell.2.1 c.cell.2.2 :=
  c.regular.1.2.2

/-- A selected regular grid cell omits every raw singular center in at least one
coordinate interval. -/
theorem ExplicitFormulaRectangleRegularGridCell.omitsRaw
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ Set.uIcc c.cell.1.1 c.cell.1.2 ∨
          a.im ∉ Set.uIcc c.cell.2.1 c.cell.2.2 :=
  c.regular.2

/-- A selected regular grid cell has strictly increasing real coordinates after
transporting from the grid-index coordinates to the complex lower and upper corners. -/
theorem ExplicitFormulaRectangleRegularGridCell.lower_re_lt_upper_re
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    c.lower.re < c.upper.re := by
  have hcell : c.cell.1.1 < c.cell.1.2 := c.ordered.1
  have hupper : c.cell.1.1 < c.upper.re :=
    Eq.subst
      (motive := fun x : ℝ => c.cell.1.1 < x)
      (explicitFormulaRectangleGridCellUpper_re c.cell).symm
      hcell
  exact
    Eq.subst
      (motive := fun x : ℝ => x < c.upper.re)
      (explicitFormulaRectangleGridCellLower_re c.cell).symm
      hupper

/-- A selected regular grid cell has strictly increasing imaginary coordinates after
transporting from the grid-index coordinates to the complex lower and upper corners. -/
theorem ExplicitFormulaRectangleRegularGridCell.lower_im_lt_upper_im
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    c.lower.im < c.upper.im := by
  have hcell : c.cell.2.1 < c.cell.2.2 := c.ordered.2
  have hupper : c.cell.2.1 < c.upper.im :=
    Eq.subst
      (motive := fun y : ℝ => c.cell.2.1 < y)
      (explicitFormulaRectangleGridCellUpper_im c.cell).symm
      hcell
  exact
    Eq.subst
      (motive := fun y : ℝ => y < c.upper.im)
      (explicitFormulaRectangleGridCellLower_im c.cell).symm
      hupper

/-- Raw-center omission for a selected regular grid cell, expressed in the lower/upper
corner coordinates used by the analytic cell integrals. -/
theorem ExplicitFormulaRectangleRegularGridCell.omitsRaw_lower_upper
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ Set.uIcc c.lower.re c.upper.re ∨
          a.im ∉ Set.uIcc c.lower.im c.upper.im := by
  intro a ha
  exact explicitFormulaRectangleGridCell_coordinateOmission_transport c.cell a (c.omitsRaw a ha)

/-- Raw-center omission for every selected cell in a finite regular-grid family, in the
coordinate form used by cell-boundary integrals. -/
theorem explicitFormulaRectangleRegularGridCellFamily_omitsRaw_lower_upper
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T ε)) :
    ∀ c : ExplicitFormulaRectangleRegularGridCell F T ε, c ∈ cells →
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ Set.uIcc c.lower.re c.upper.re ∨
            a.im ∉ Set.uIcc c.lower.im c.upper.im :=
  fun c _hc a ha => c.omitsRaw_lower_upper a ha

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

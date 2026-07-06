import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part26

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

/-- The concrete regular-grid half-radius construction supplies the finite-hole Cauchy
function required by the finite rectangle residue theorem.  This theorem is the precise
handoff point between the geometric subdivision layer and the residue assembly layer. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                ∑ c in cells,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    c.lower c.upper ∧
              (∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
                ∀ z : ℂ,
                  z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
                    Set.uIcc c.lower.im c.upper.im) →
                    z ∈ explicitFormulaContourFamilyInterior F T ∨
                      z ∈ explicitFormulaContourFamilyBoundary F T) ∧
              (∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
                ∀ z : ℂ,
                  z ∈ Set.Ioo (min c.lower.re c.upper.re)
                        (max c.lower.re c.upper.re) ×ℂ
                      Set.Ioo (min c.lower.im c.upper.im)
                        (max c.lower.im c.upper.im) →
                    z ∈ explicitFormulaContourFamilyInterior F T) ∧
              (∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  intro ε hε hclosed hsep
  match hgrid ε hε hclosed hsep with
  | ⟨cells, hsubdivision, hcell_location, hcell_open_interior, hdeleted⟩ =>
      exact
        explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellHalfRadius_closedRadiusControls
          cells f h hT hε hinterior hboundary hclosed hsep
          hsubdivision hcell_location hcell_open_interior hdeleted

/-- The concrete regular-grid half-radius construction supplies finite-hole Cauchy without
asking the geometric subdivision layer to separately prove open-cell interior containment:
for regular grid cells, that open-cell condition follows from the selected closed-radius
controls. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_location_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                ∑ c in cells,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    c.lower c.upper ∧
              (∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
                ∀ z : ℂ,
                  z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
                    Set.uIcc c.lower.im c.upper.im) →
                    z ∈ explicitFormulaContourFamilyInterior F T ∨
                      z ∈ explicitFormulaContourFamilyBoundary F T) ∧
              (∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  intro ε hε hclosed hsep
  match hgrid ε hε hclosed hsep with
  | ⟨cells, hsubdivision, hcell_location, hdeleted⟩ =>
      have hcell_open_interior :
          ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
            ∀ z : ℂ,
              z ∈ Set.Ioo (min c.lower.re c.upper.re)
                    (max c.lower.re c.upper.re) ×ℂ
                  Set.Ioo (min c.lower.im c.upper.im)
                    (max c.lower.im c.upper.im) →
                z ∈ explicitFormulaContourFamilyInterior F T :=
        explicitFormulaRectangleRegularGridCellFamily_openCell_interior_of_halfRadius_closedRadiusControls
          cells hT hε hclosed
      exact
        explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellHalfRadius_closedRadiusControls
          cells f h hT hε hinterior hboundary hclosed hsep
          hsubdivision hcell_location hcell_open_interior hdeleted

/-- The regular-grid half-radius construction supplies finite-hole Cauchy once the
subdivision layer has produced only the regular-cell boundary identity and the
circle-to-inscribed-square deleted-boundary replacement.  Closed-cell location and
open-cell interior membership are derived from closed-radius controls. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_subdivision_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                ∑ c in cells,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    c.lower c.upper ∧
              (∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a)) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  intro ε hε hclosed hsep
  match hgrid ε hε hclosed hsep with
  | ⟨cells, hsubdivision, hdeleted⟩ =>
      have hcell_location :
          ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
            ∀ z : ℂ,
              z ∈ (Set.uIcc c.lower.re c.upper.re ×ℂ
                Set.uIcc c.lower.im c.upper.im) →
                z ∈ explicitFormulaContourFamilyInterior F T ∨
                  z ∈ explicitFormulaContourFamilyBoundary F T :=
        explicitFormulaRectangleRegularGridCellFamily_closedCell_location_of_halfRadius_closedRadiusControls
          cells hT hε hclosed
      have hcell_open_interior :
          ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
            ∀ z : ℂ,
              z ∈ Set.Ioo (min c.lower.re c.upper.re)
                    (max c.lower.re c.upper.re) ×ℂ
                  Set.Ioo (min c.lower.im c.upper.im)
                    (max c.lower.im c.upper.im) →
                z ∈ explicitFormulaContourFamilyInterior F T :=
        explicitFormulaRectangleRegularGridCellFamily_openCell_interior_of_halfRadius_closedRadiusControls
          cells hT hε hclosed
      exact
        explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellHalfRadius_closedRadiusControls
          cells f h hT hε hinterior hboundary hclosed hsep
          hsubdivision hcell_location hcell_open_interior hdeleted

/-- The finite-hole Cauchy input follows from a half-radius inscribed-square Cauchy zero
and pointwise transport from deleted circles to the inscribed-square deleted boundary.
This isolates the two geometric obligations left after residue accounting: prove the
square-hole punctured rectangle has zero boundary, and identify the circle and square
deleted-boundary values around each raw singular coordinate. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_inscribedSquareHalfRadiusZero_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
              f F T (ε / 2) = 0)
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  intro ε hε hclosed hsep
  have hhalfZero :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T (ε / 2) = 0 :=
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
      f F T (ε / 2)
      (explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2))
      (hsquare ε hε hclosed hsep)
      (hdeleted ε hε hclosed hsep)
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
      f F h hT hε hinterior hclosed hsep hhalfZero

/-- Finite-hole Cauchy from a half-radius regular-grid subdivision and a separate
circle-to-inscribed-square deleted-boundary transport theorem.  The regular grid is used
only to prove the square-hole Cauchy zero; the circle-square transport remains the local
boundary-value theorem around each raw singular coordinate. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_squareZero_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                ∑ c in cells,
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    c.lower c.upper)
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
              f F T (ε / 2) = 0 := by
    intro ε hε hclosed _hsep
    match hgrid ε hε hclosed _hsep with
    | ⟨cells, hsubdivision⟩ =>
        exact
          explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_subdivision_closedRadiusControls
            cells f h hT hε hinterior hboundary hclosed hsubdivision
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_inscribedSquareHalfRadiusZero_closedRadiusControls
      f F h hT hinterior hsquare hdeleted

/-- Finite-hole Cauchy from a half-radius regular-grid boundary-sum identity and a
separate circle-to-inscribed-square deleted-boundary transport theorem.  This is the
entry point for the edge-cancellation layer once it proves the named regular-cell
boundary-sum equality. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_boundarySum_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                explicitFormulaRectangleRegularGridCellBoundarySum f cells)
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
              f F T (ε / 2) = 0 := by
    intro ε hε hclosed hsep
    match hgrid ε hε hclosed hsep with
    | ⟨cells, hboundarySum⟩ =>
        exact
          explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_boundarySum_closedRadiusControls
            cells f h hT hε hinterior hboundary hclosed hboundarySum
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_inscribedSquareHalfRadiusZero_closedRadiusControls
      f F h hT hinterior hsquare hdeleted

/-- Finite-hole Cauchy from a half-radius regular-grid subdivision whose edge-cancellation
layer supplies an explicit boundary function `B` over the selected cells.  The bridge folds
the supplied finite sum to the named regular-grid boundary-sum consumer theorem. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_suppliedBoundarySum_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              ∃ B : ExplicitFormulaRectangleRegularGridCell F T (ε / 2) → ℂ,
                explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                    f F T (ε / 2) =
                  ∑ c in cells, B c ∧
                ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
                  B c =
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      c.lower c.upper)
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hgridBoundary :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)),
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                  f F T (ε / 2) =
                explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
    intro ε hε hclosed hsep
    match hgrid ε hε hclosed hsep with
    | ⟨cells, B, hsubdivision, hB⟩ =>
        have hboundarySum :
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                f F T (ε / 2) =
              explicitFormulaRectangleRegularGridCellBoundarySum f cells :=
          explicitFormulaRectangleRegularGridCellBoundarySum_fold_supplied_right
            f cells B hsubdivision hB
        exact Exists.intro cells hboundarySum
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_boundarySum_closedRadiusControls
      f F h hT hinterior hboundary hgridBoundary hdeleted

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

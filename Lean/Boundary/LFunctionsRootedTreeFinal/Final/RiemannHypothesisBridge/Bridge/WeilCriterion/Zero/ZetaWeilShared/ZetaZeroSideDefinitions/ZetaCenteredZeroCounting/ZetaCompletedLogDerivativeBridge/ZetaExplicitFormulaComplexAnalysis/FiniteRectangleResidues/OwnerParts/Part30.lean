import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part29

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

/-- Finite-radius tangent punctured-rectangle residue assembly from concrete closed-radius
controls: closed disks lie in the rectangle interior and distinct closed disks are strictly
separated.  This is the form produced by the radius-selection layer before the finite-hole
Cauchy zero is applied. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T ε : ℝ)
    (hT : 0 < T) (hε_pos : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (hcauchy :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T ε = 0)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hgeometry :
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b →
                Disjoint (Metric.closedBall a ε) (Metric.closedBall b ε)) :=
    explicitFormulaRectangleRawClosedDisks_geometry_of_radius_controls
      F T ε hclosed hsep
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_closedRadiusGeometry
      f F h T ε hT hε_pos hinterior hgeometry hcauchy hlocal

/-- Radius-selected tangent punctured-rectangle residue assembly.  The finite raw singular
carrier chooses a single positive radius satisfying closed-disk containment and strict
pairwise separation; once finite-hole Cauchy-Goursat is known for every such chosen radius,
the tangent contour has the pole-corrected residue value. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_radiusLocalInterior_and_finiteHoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hlocalInterior :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ explicitFormulaContourFamilyInterior F T)
    (hfiniteHoleCauchy :
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
              f F T ε = 0)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  match explicitFormulaRectangleRawSingularCoordinates_exists_closedRadiusControls
      F T hlocalInterior with
  | ⟨ε, hε_pos, hcontrols⟩ =>
      exact
        zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteRadiusPuncturedBoundary_and_closedRadiusControls
          f F h T ε hT hε_pos hinterior
          hcontrols.1
          hcontrols.2
          (hfiniteHoleCauchy ε hε_pos hcontrols.1 hcontrols.2)
          hlocal

/-- Tangent contour residue assembly after all radius/local-interior data has been
constructed in the owner layer.  The sole remaining geometric input is the finite-hole
Cauchy-Goursat zero for the selected closed-radius controls. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteHoleCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hfiniteHoleCauchy :
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
              f F T ε = 0)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) *
                zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_radiusLocalInterior_and_finiteHoleCauchy
      f F h T hT hinterior
      (fun a ha =>
        explicitFormulaRectangleRawSingularCoordinates_localInterior_ball F hT hinterior ha)
      hfiniteHoleCauchy
      hlocal

/-- Tangent Cauchy-residue theorem from the named regular-grid boundary-sum finite-hole
construction.  This is the clean handoff for the edge-cancellation layer: it must produce
proof-carrying regular cells, the named boundary-sum equality, and the pointwise
circle-to-inscribed-square deleted-boundary transport. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_regularGridBoundarySum_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteHoleCauchy
      f F h T hT hinterior
      (explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_boundarySum_closedRadiusControls
        f F h hT hinterior hboundary hgrid hdeleted)
      hlocal

/-- Tangent Cauchy-residue theorem from the reduced regular-grid finite-hole construction.
The residue assembly is no longer part of the remaining sink: it is a thin wrapper over
the finite-hole Cauchy theorem, while the geometric layer must still construct the regular
grid cells, prove the subdivision identity, and identify circular and inscribed-square
deleted boundaries. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_regularGridSubdivision_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
                    explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a))
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hgrid_square :
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
                    c.lower c.upper := by
    intro ε hε hclosed hsep
    match hgrid ε hε hclosed hsep with
    | ⟨cells, hsubdivision, _hdeleted⟩ =>
        exact ⟨cells, hsubdivision⟩
  have hdeleted :
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
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a := by
    intro ε hε hclosed hsep a ha
    match hgrid ε hε hclosed hsep with
    | ⟨_cells, _hsubdivision, hdeleted⟩ =>
        exact hdeleted a ha
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteHoleCauchy
      f F h T hT hinterior
      (explicitFormulaRectangle_finiteHoleCauchy_of_regularGridHalfRadius_squareZero_closedRadiusControls
        f F h hT hinterior hboundary hgrid_square hdeleted)
      hlocal

/-- Tangent Cauchy-residue theorem from a concrete endpoint-data subdivision.  This is the
endpoint-data handoff for the constructive finite-rectangle route: the geometric layer
produces the endpoint-data boundary decomposition, and the local deleted-boundary layer
produces the circle-to-inscribed-square transport. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_regularGridEndpointDataSubdivision_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
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
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_finiteHoleCauchy
      f F h T hT hinterior
      (explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls
        f F h hT hinterior hboundary hgrid hdeleted)
      hlocal

/-- Endpoint-data Cauchy-residue theorem with the true remaining deleted-boundary
primitive exposed: pointwise deformation from each half-radius circle to the
corresponding quarter-width deleted square. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_circleSquare_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (hcircle_square :
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
                  explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hdeleted :
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
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a := by
    intro ε hε hclosed hsep
    exact
      explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
        f T ε
        (hcircle_square ε hε hclosed hsep)
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_regularGridEndpointDataSubdivision_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hgrid hdeleted hlocal

/-- Endpoint-data Cauchy-residue theorem from common residue values for the half-radius
circle and quarter-width square boundaries.  This is the construction-output form: the
local boundary layer supplies one common value for the circle and square boundary around
each raw singular coordinate. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_commonValues_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (value : ℝ → ℂ → ℂ)
    (hcircle :
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
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value ε a)
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
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value ε a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hcircle_square :
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
                  explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a := by
    intro ε hε hclosed hsep a ha
    exact
      explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawDeletedSquareBoundary_quarter_of_common_value
        f ε a (value ε a)
        (hcircle ε hε hclosed hsep a ha)
        (hsquare ε hε hclosed hsep a ha)
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_circleSquare_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hgrid hcircle_square hlocal

/-- Endpoint-data Cauchy-residue theorem from common values for the half-radius circle
boundary and the corresponding half-radius inscribed-square boundary.  This is the direct
consumer for square-hole boundary evaluations stated in the same boundary normalization
as the endpoint-data subdivision. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_inscribedSquareCommonValues_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
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
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (value : ℝ → ℂ → ℂ)
    (hcircle :
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
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value ε a)
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
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value ε a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hdeleted :
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
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a := by
    intro ε hε hclosed hsep a ha
    exact Eq.trans
      (hcircle ε hε hclosed hsep a ha)
      (hsquare ε hε hclosed hsep a ha).symm
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_regularGridEndpointDataSubdivision_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hgrid hdeleted hlocal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

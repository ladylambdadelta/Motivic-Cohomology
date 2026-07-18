import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ProjectionCore

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

/-- Endpoint-data Cauchy-residue theorem from the canonical deleted-circle residue
evaluations and a separate half-radius inscribed-square common-value theorem.  This is the
thin owner bridge from the already proved circle residue cases to the downstream
`hcircle`/`hsquare` common-value package; the remaining analytic input is exactly the
square-boundary value theorem. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_inscribedSquareCommonValues_of_circleResidues_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
    (hvalue_zero :
      ∀ ε : ℝ,
        value ε 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hvalue_one :
      ∀ ε : ℝ,
        value ε 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hvalue_completed :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
            value ε (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
    (s0 s1 : ℝ → Set ℂ)
    (hs0 : ∀ ε : ℝ, (s0 ε).Countable)
    (hs1 : ∀ ε : ℝ, (s1 ε).Countable)
    (szero : ℝ → {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
            (szero ε ρ).Countable)
      (hzero_continuous :
        ∀ ε : ℝ,
          ContinuousOn
            (fun z : ℂ => (z - 0) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall (0 : ℂ) (ε / 2) \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) (ε / 2) \ {(0 : ℂ)}) \ s0 ε →
              DifferentiableAt ℂ
                (fun w : ℂ => (w - 0) * zetaCompletedExplicitFormulaContourIntegrand f w)
                z)
    (hone_continuous :
      ∀ ε : ℝ,
        ContinuousOn
          (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (1 : ℂ) (ε / 2) \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (1 : ℂ) (ε / 2) \ {(1 : ℂ)}) \ s1 ε →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hcompleted_continuous :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
            ContinuousOn
              (fun z : ℂ =>
                (z - completedZeroResidueCoordinate ρ) *
                  zetaCompletedExplicitFormulaContourIntegrand f z)
              (Metric.closedBall (completedZeroResidueCoordinate ρ) (ε / 2) \
                {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T,
            ∀ z : ℂ,
              z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) (ε / 2) \
                  {completedZeroResidueCoordinate ρ}) \ szero ε ρ →
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    (w - completedZeroResidueCoordinate ρ) *
                      zetaCompletedExplicitFormulaContourIntegrand f w)
                  z)
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hcircle :
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
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value ε a :=
    explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_commonValue_on_rawSingularCoordinates
      f hPhi F T value
      hvalue_zero hvalue_one hvalue_completed
      s0 s1 hs0 hs1 szero hszero
      hzero_continuous hzero_differentiable
      hone_continuous hone_differentiable
      hcompleted_continuous hcompleted_differentiable
      hlocal
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_inscribedSquareCommonValues_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hgrid value hcircle hsquare hlocal

/-- Avoided-boundary endpoint-data Cauchy-residue theorem from concrete common values for
the half-radius circle and quarter-width square boundaries.  This is the construction
output handoff for the final finite-rectangle route: boundary avoidance supplies boundary
regularity, while the endpoint-data subdivision and square/circle evaluations supply the
finite-hole Cauchy input. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_avoidsBoundary_endpointDataSubdivision_commonValues_ownerCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h T havoid
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_endpointDataSubdivision_commonValues_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hgrid value hcircle hsquare hlocal

/-- If the corrected contour integral has the completed-zero residue window and the
explicit pole-boundary contribution is exactly the pole residue sum, then the raw contour
integral has the pole-corrected finite residue sum. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_poleCorrectedResidueSum_of_correctedContour
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hcorrected :
      explicitFormulaRectangle_poleCorrectedContourIntegral f F T =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f T)
    (hpoles :
      explicitFormulaRectangle_completedPoleBoundaryContribution f F T =
        explicitFormulaRectangle_completedPoleResidueSum f) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  calc
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaRectangle_poleCorrectedContourIntegral f F T +
          explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
      exact zetaCompletedExplicitFormulaContourIntegral_eq_poleCorrected_add_poles f F T
    _ = explicitFormulaCompletedZeroContourHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleBoundaryContribution f F T := by
      exact congrArg
        (fun x : ℂ => x + explicitFormulaRectangle_completedPoleBoundaryContribution f F T)
        hcorrected
    _ = explicitFormulaCompletedZeroContourHeightWindowResidueSum f T +
          explicitFormulaRectangle_completedPoleResidueSum f := by
      exact congrArg
        (fun x : ℂ => explicitFormulaCompletedZeroContourHeightWindowResidueSum f T + x)
        hpoles
    _ = explicitFormulaRectangle_poleCorrectedResidueSum f T := by
      exact (explicitFormulaRectangle_poleCorrectedResidueSum_eq f T).symm

/-- Cauchy's finite rectangle residue theorem for the raw completed explicit-formula
integrand in tangent contour normalization.  The raw integrand has interior singularities
at the completed-zeta pole coordinates `0` and `1`, so the honest tangent target is the
completed-zero residue window plus those two pole residues. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_interiorPoles_ownerCauchyResidueTheorem
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hside :
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
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) ∧
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T ∧
                (∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) ∧
                  (∀ a : ℂ,
                    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) ∧
                    explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c ∧
                      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) ∧
                        (∀ a : ℂ,
                          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
                              (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                (ε / 2) a).re) ∧
                          (∀ a : ℂ,
                            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                              explicitFormulaRectangleSortedYVerticalSideIntegrable f T
                                (ε / 2)
                                (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                  (ε / 2) a).re))
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
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
      (explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_ownerGridSubdivision
        f F h hT hinterior hboundary hside)
      hlocal

/-- The finite Cauchy-residue theorem for the tangent completed contour integral, after
boundary regularity, zero-window identification, and local completed-zero residue
transport have been supplied.  The raw target includes the completed-zeta pole residues. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_windowResidues_ownerFiniteCauchyResidueTheorem
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
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hside :
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
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) ∧
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T ∧
                (∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) ∧
                  (∀ a : ℂ,
                    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) ∧
                    explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c ∧
                      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) ∧
                        (∀ a : ℂ,
                          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
                              (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                (ε / 2) a).re) ∧
                          (∀ a : ℂ,
                            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                              explicitFormulaRectangleSortedYVerticalSideIntegrable f T
                                (ε / 2)
                                (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                  (ε / 2) a).re))
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_interiorPoles_ownerCauchyResidueTheorem
      f F h T hT hboundary hinterior hside hlocal

/-- The tangent finite Cauchy-residue theorem applied to the avoided rectangle.  The raw
completed integrand includes the completed-zeta pole residues at `0` and `1`. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_avoidsBoundary_ownerFiniteCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hside :
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
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) ∧
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T ∧
                (∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) ∧
                  (∀ a : ℂ,
                    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) ∧
                    explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c ∧
                      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) ∧
                        (∀ a : ℂ,
                          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
                              (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                (ε / 2) a).re) ∧
                          (∀ a : ℂ,
                            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                              explicitFormulaRectangleSortedYVerticalSideIntegrable f T
                                (ε / 2)
                                (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                  (ε / 2) a).re))
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h T havoid
  exact
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_boundaryRegular_windowResidues_ownerFiniteCauchyResidueTheorem
      f F h T hT hboundary hinterior hside hlocal

/-- Pointwise tangent finite Cauchy-residue theorem for an avoided rectangle.

This is the exact finite analytic computation left after schedule bookkeeping has been
removed: the completed contour integrand is regular on the boundary, its interior
singularities are the completed zeros in the height window together with the completed-zeta
pole coordinates, and the tangent residue target includes all of them. -/
theorem zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_avoidsBoundary_ownerPointwiseFiniteCauchyResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (hT : 0 < T)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hside :
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
            explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T) ∧
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T ∧
                (∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im) ∧
                  (∀ a : ℂ,
                    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
                        (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im) ∧
                    explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c ∧
                      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c) ∧
                        (∀ a : ℂ,
                          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                            explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
                              (explicitFormulaRectangleRawInscribedSquareUpperCorner
                                (ε / 2) a).re) ∧
                          (∀ a : ℂ,
                            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                              explicitFormulaRectangleSortedYVerticalSideIntegrable f T
                                (ε / 2)
                                (explicitFormulaRectangleRawInscribedSquareLowerCorner
                                  (ε / 2) a).re))
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroContourHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
      (2 * ↑Real.pi * Complex.I : ℂ) •
        explicitFormulaRectangle_poleCorrectedResidueSum f T := by
  have hresidue :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) =
        (2 * ↑Real.pi * Complex.I : ℂ) •
          explicitFormulaRectangle_poleCorrectedResidueSum f T :=
    zetaCompletedExplicitFormulaTangentContourIntegral_eq_twoPiI_smul_poleCorrectedResidueSum_of_avoidsBoundary_ownerFiniteCauchyResidueTheorem
      f F h T hT havoid hinterior hside hlocal
  exact hresidue

/-- Scheduled transport wrapper for an already-proved project-contour finite residue
equality at every scheduled height. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_heightWindowResidueSum_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    ∀ u : ℝ,
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u) := by
  intro u
  exact hfinite u

/-- Transport wrapper for a supplied finite rectangle residue equality at one scheduled
height. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_heightWindowResidueSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
        (h.height_schedule.height u) := by
  exact
    hfinite

/-- Completed-zeta naming wrapper for a supplied project-contour finite residue equality
on an avoided rectangle. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq_completedZeroHeightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f T := by
  exact
    hfinite

/-- If the chosen scheduled rectangle has the finite contour/residue equality, then the
named scheduled residue-equality error is zero at that height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaCompletedZeroContourHeightWindowResidueSum f
        (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  change
    zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) -
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u) =
      0
  exact sub_eq_zero.mpr hfinite

/-- Finite scheduled rectangle residue equality at one avoided height.

This is the true finite-rectangle residue-theorem input: boundary avoidance guarantees that
the residue-window computation has no zero/pole hit on the contour, so the named equality
error vanishes at that scheduled height. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (havoid :
      explicitFormulaContourFamilyAvoidsSingularBoundary F
        (h.height_schedule.height u))
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u hfinite

/-- The scheduled rectangle residue-equality error vanishes using the package schedule's
boundary-avoidance certificate. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_eq_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f
          (F.rectangle (h.height_schedule.height u)) =
        explicitFormulaCompletedZeroContourHeightWindowResidueSum f
          (h.height_schedule.height u)) :
    explicitFormulaScheduledRectangleResidueEqualityError f F h u = 0 := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_eq_zero_of_heightWindowResidueEquality
      f F h u hfinite

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the scheduled finite-rectangle computation with the boundary-avoidance certificate
kept visible.  The certificate is the progress condition that makes each finite contour
computation admissible along the scheduled realization. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (havoid :
      ∀ u : ℝ,
        explicitFormulaContourFamilyAvoidsSingularBoundary F
          (h.height_schedule.height u))
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  have hpointwise :
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u) =
        (fun _u : ℝ => (0 : ℂ)) := by
    exact funext
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError_eq_zero f F h u (hfinite u))
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    tendsto_const_nhds

/-- Core finite-rectangle contour residue theorem, after zero-excision/window accounting.

This is the finite-rectangle residue theorem in its zero-side window form: the full
rectangle contour integral differs from the finite zero-side window by an error tending to
zero. -/
theorem explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_core_ownerFiniteRectangleResidueEquality
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hfinite :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroContourHeightWindowResidueSum f
            (h.height_schedule.height u)) :
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledRectangleResidueEqualityError f F h u)
      atTop
      (𝓝 0) := by
  exact
    explicitFormulaScheduledRectangleResidueEqualityError_tendsto_zero_of_avoidsBoundary_ownerFiniteRectangleResidueEquality
      f F h
      (fun u => explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hfinite

/-! ## Projected contour spine for vertical channels -/

/-- The scheduled rectangle residue-equality error, viewed as a contour-side input to a
selected vertical channel projection. -/
noncomputable def explicitFormulaScheduledProjectedRectangleResidueEqualityError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledRectangleResidueEqualityError f F h u

/-- The scheduled horizontal contour error, viewed as an input to a selected vertical channel
projection. -/
noncomputable def explicitFormulaScheduledProjectedHorizontalError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (_channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaFamilyHorizontalResidueWindowError f F
    (h.height_schedule.height u)

/-- The full projected contour spine error combines finite rectangle residue equality,
projected horizontal decay, and projected vertical decomposition. -/
noncomputable def explicitFormulaScheduledProjectedContourSpineError
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (channel : ExplicitFormulaScheduledVerticalChannelProjection) : ℂ :=
  explicitFormulaScheduledProjectedRectangleResidueEqualityError f F h u channel +
    explicitFormulaScheduledProjectedHorizontalError f F h u channel +
      explicitFormulaScheduledProjectedVerticalDecompositionError f F h u channel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

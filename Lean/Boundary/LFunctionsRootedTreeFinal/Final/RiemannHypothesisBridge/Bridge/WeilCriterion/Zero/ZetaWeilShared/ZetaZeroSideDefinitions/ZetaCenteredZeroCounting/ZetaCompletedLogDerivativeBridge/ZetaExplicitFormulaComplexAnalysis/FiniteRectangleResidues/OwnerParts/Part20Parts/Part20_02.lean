import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_01

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

/-!
## Part20 02: RawAndOuterBoxes
-/

def explicitFormulaRectangleOuterEndpointDataBox
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    ExplicitFormulaRectangleEndpointDataBoxEdge :=
  ((F.c, 1 - F.c), (-T, T))

/-- Full-box label for the raw inscribed square around a singular coordinate. -/
def explicitFormulaRectangleRawInscribedSquareEndpointDataBox
    (ε : ℝ) (a : ℂ) : ExplicitFormulaRectangleEndpointDataBoxEdge :=
  (((explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re,
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re),
    ((explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im,
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im))

/-- Every side of the outer endpoint-data box is one of the corresponding subdivision
endpoints at the selected half-radius grid. -/
theorem explicitFormulaRectangleOuterEndpointDataBox_halfRadius_mem_subdivisionEndpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleOuterEndpointDataBox F T
    box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
      box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
        box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) ∧
          box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) := by
  let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleOuterEndpointDataBox F T
  have hleft :
      box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_left
      F T (ε / 2)
  have hright :
      box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_right
      F T (ε / 2)
  have hbottom :
      box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_lower
      T (ε / 2)
  have htop :
      box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_upper
      T (ε / 2)
  exact And.intro hleft (And.intro hright (And.intro hbottom htop))

/-- The lower corner of the outer endpoint-data box is the named outer lower corner. -/
theorem explicitFormulaRectangleOuterEndpointDataBox_lowerCorner
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleEndpointDataBoxLowerCorner
        (explicitFormulaRectangleOuterEndpointDataBox F T) =
      explicitFormulaRectangleOuterLowerCorner F T := by
  rfl

/-- The upper corner of the outer endpoint-data box is the named outer upper corner. -/
theorem explicitFormulaRectangleOuterEndpointDataBox_upperCorner
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleEndpointDataBoxUpperCorner
        (explicitFormulaRectangleOuterEndpointDataBox F T) =
      explicitFormulaRectangleOuterUpperCorner F T := by
  rfl

/-- The lower corner of a raw inscribed-square endpoint-data box is the named raw lower
corner. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_lowerCorner
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleEndpointDataBoxLowerCorner
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) =
      explicitFormulaRectangleRawInscribedSquareLowerCorner ε a := by
  exact Complex.ext
    (ofReal_add_mul_I_re
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im)
    (ofReal_add_mul_I_im
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im)

/-- The upper corner of a raw inscribed-square endpoint-data box is the named raw upper
corner. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_upperCorner
    (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleEndpointDataBoxUpperCorner
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) =
      explicitFormulaRectangleRawInscribedSquareUpperCorner ε a := by
  exact Complex.ext
    (ofReal_add_mul_I_re
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im)
    (ofReal_add_mul_I_im
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im)

/-- Under the closed-radius control hypotheses used by the selected-grid theorem, every
side of the half-radius raw inscribed-square endpoint-data box is one of the corresponding
subdivision endpoints. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_halfRadius_mem_subdivisionEndpoints_closedRadiusControls
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hε : 0 < ε)
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
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a
    box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
      box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
        box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) ∧
          box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) := by
  let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a
  have hleft :
      box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeLeft
      F T (ε / 2) ha
  have hright :
      box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_holeRight
      F T (ε / 2) ha
  have hbottom :
      box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeBottom
      T (ε / 2) ha
  have htop :
      box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_holeTop
      T (ε / 2) ha
  exact And.intro hleft (And.intro hright (And.intro hbottom htop))

/-- Under the closed-radius controls, the half-radius raw inscribed-square endpoint-data
box is a candidate sorted subdivision cell. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_halfRadius_mem_candidateCells_closedRadiusControls
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hε : 0 < ε)
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
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a ∈
      explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T (ε / 2) := by
  let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a
  have hmem :
      box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
        box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
          box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) ∧
            box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBox_halfRadius_mem_subdivisionEndpoints_closedRadiusControls
      F hε hclosed hsep ha
  exact
    explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_of_endpoints
      F T (ε / 2) hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2

/-- The outer box is grid-aligned and every raw half-radius inscribed-square box is a
candidate box in the same half-radius subdivision grid. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_boundaryBoxes_gridAligned_closedRadiusControls
    (F : ExplicitFormulaContourFamily) {T ε : ℝ} (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    (let box : ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleOuterEndpointDataBox F T
    box.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
      box.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T (ε / 2) ∧
        box.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2) ∧
          box.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T (ε / 2)) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a ∈
            explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T (ε / 2)) := by
  exact
    And.intro
      (explicitFormulaRectangleOuterEndpointDataBox_halfRadius_mem_subdivisionEndpoints
        F T ε)
      (fun a ha =>
        explicitFormulaRectangleRawInscribedSquareEndpointDataBox_halfRadius_mem_candidateCells_closedRadiusControls
          F hε hclosed hsep ha)

/-- A raw inscribed-square endpoint-data box is not selected by the coordinate-omission
predicate for the same raw singular coordinate: the box is contained in its own raw
square. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_coordinateOmission_false
    {T ε : ℝ} (_hε : 0 ≤ ε)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ¬ (∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ¬
            ((explicitFormulaRectangleRawInscribedSquareLowerCorner ε b).re ≤
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a).1.1 ∧
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a).1.2 ≤
                (explicitFormulaRectangleRawInscribedSquareUpperCorner ε b).re ∧
                (explicitFormulaRectangleRawInscribedSquareLowerCorner ε b).im ≤
                  (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a).2.1 ∧
                  (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a).2.2 ≤
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner ε b).im)) := by
  intro homit
  exact
    homit a ha
      (And.intro
        (le_refl _)
        (And.intro
          (le_refl _)
          (And.intro
            (le_refl _)
            (le_refl _))))

/-- Half-radius raw inscribed-square endpoint-data boxes are not selected by the
coordinate-omission predicate for their own raw singular coordinate. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_halfRadius_coordinateOmission_false
    {T ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    ¬ (∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ¬
            ((explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) b).re ≤
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a).1.1 ∧
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a).1.2 ≤
                (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) b).re ∧
                (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) b).im ≤
                  (explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a).2.1 ∧
                  (explicitFormulaRectangleRawInscribedSquareEndpointDataBox (ε / 2) a).2.2 ≤
                    (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) b).im)) := by
  exact
    explicitFormulaRectangleRawInscribedSquareEndpointDataBox_coordinateOmission_false
      (half_nonneg (le_of_lt hε)) ha

/-- The boundary of the outer endpoint-data box is the named outer Cauchy cell boundary. -/
theorem explicitFormulaRectangleOuterEndpointDataBox_boundary_eq_outerCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        [explicitFormulaRectangleOuterEndpointDataBox F T] =
      explicitFormulaRectangleOuterCauchyCellBoundary f F T := by
  calc
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        [explicitFormulaRectangleOuterEndpointDataBox F T] =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleEndpointDataBoxLowerCorner
          (explicitFormulaRectangleOuterEndpointDataBox F T))
        (explicitFormulaRectangleEndpointDataBoxUpperCorner
          (explicitFormulaRectangleOuterEndpointDataBox F T)) + 0 := by
      rfl
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleOuterLowerCorner F T)
        (explicitFormulaRectangleEndpointDataBoxUpperCorner
          (explicitFormulaRectangleOuterEndpointDataBox F T)) + 0 := by
      exact congrArg
        (fun z : ℂ =>
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
            z
            (explicitFormulaRectangleEndpointDataBoxUpperCorner
              (explicitFormulaRectangleOuterEndpointDataBox F T)) + 0)
        (explicitFormulaRectangleOuterEndpointDataBox_lowerCorner F T)
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleOuterLowerCorner F T)
        (explicitFormulaRectangleOuterUpperCorner F T) + 0 := by
      exact congrArg
        (fun z : ℂ =>
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
            (explicitFormulaRectangleOuterLowerCorner F T)
            z + 0)
        (explicitFormulaRectangleOuterEndpointDataBox_upperCorner F T)
    _ = explicitFormulaRectangleOuterCauchyCellBoundary f F T + 0 := by
      rfl
    _ = explicitFormulaRectangleOuterCauchyCellBoundary f F T := by
      exact add_zero (explicitFormulaRectangleOuterCauchyCellBoundary f F T)

/-- The boundary of one raw inscribed-square endpoint-data box is the corresponding raw
inscribed-square cell-boundary integral. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_boundary_eq_cellBoundary
    (f : ZetaAdmissibleFunction) (ε : ℝ) (a : ℂ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        [explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a] =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  calc
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        [explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a] =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleEndpointDataBoxLowerCorner
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))
        (explicitFormulaRectangleEndpointDataBoxUpperCorner
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) + 0 := by
      rfl
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleEndpointDataBoxUpperCorner
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) + 0 := by
      exact congrArg
        (fun z : ℂ =>
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
            z
            (explicitFormulaRectangleEndpointDataBoxUpperCorner
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) + 0)
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_lowerCorner ε a)
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) + 0 := by
      exact congrArg
        (fun z : ℂ =>
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            z + 0)
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox_upperCorner ε a)
    _ =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact add_zero
        (finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a))

/-- Sum of raw inscribed-square endpoint-data box boundaries over the raw singular
coordinate finset. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
      [explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a]

/-- Bottom-side sum over the raw inscribed-square endpoint-data boxes. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    explicitFormulaRectangleBoxBottomEdgeIntegral f
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)

/-- Top-side sum over the raw inscribed-square endpoint-data boxes. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    explicitFormulaRectangleBoxTopEdgeIntegral f
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)

/-- Right-side sum over the raw inscribed-square endpoint-data boxes. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    explicitFormulaRectangleBoxRightEdgeIntegral f
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)

/-- Left-side sum over the raw inscribed-square endpoint-data boxes. -/
noncomputable def explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
    (f : ZetaAdmissibleFunction) (T ε : ℝ) : ℂ :=
  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
    explicitFormulaRectangleBoxLeftEdgeIntegral f
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)

/-- The raw inscribed-square endpoint-data box-boundary finset sum is exactly the
raw inscribed-square cell-boundary finset sum. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum f T ε =
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  exact
    Finset.sum_congr rfl
      (fun a _ha =>
        explicitFormulaRectangleRawInscribedSquareEndpointDataBox_boundary_eq_cellBoundary
          f ε a)

/-- The raw inscribed-square endpoint-data box-boundary finset sum decomposes into the
four raw side sums. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq_edgeSums
    (f : ZetaAdmissibleFunction) (T ε : ℝ) :
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum f T ε =
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε +
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
              f T ε) := by
  let S := explicitFormulaRectangleRawSingularCoordinates T
  let bottom : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε
  let top : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε
  let right : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε
  let left : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ε
  have hpoint :
      ∀ a : ℂ,
        a ∈ S →
          explicitFormulaRectangleEndpointDataBoxBoundarySum f
              [explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a] =
            explicitFormulaRectangleBoxBottomEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) -
              explicitFormulaRectangleBoxTopEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) +
                (explicitFormulaRectangleBoxRightEdgeIntegral f
                    (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) -
                  explicitFormulaRectangleBoxLeftEdgeIntegral f
                    (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) := by
    intro a _ha
    exact
      explicitFormulaRectangleEndpointDataBoxBoundarySum_eq_edgeSums
        f [explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a]
  calc
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum f T ε =
        ∑ a in S,
          (explicitFormulaRectangleBoxBottomEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) -
              explicitFormulaRectangleBoxTopEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) +
                (explicitFormulaRectangleBoxRightEdgeIntegral f
                    (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a) -
                  explicitFormulaRectangleBoxLeftEdgeIntegral f
                    (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))) := by
      exact Finset.sum_congr rfl hpoint
    _ =
        (∑ a in S,
          explicitFormulaRectangleBoxBottomEdgeIntegral f
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) -
          (∑ a in S,
            explicitFormulaRectangleBoxTopEdgeIntegral f
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) +
            ((∑ a in S,
              explicitFormulaRectangleBoxRightEdgeIntegral f
                (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a)) -
              (∑ a in S,
                explicitFormulaRectangleBoxLeftEdgeIntegral f
                  (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))) := by
      exact
        finiteRectangleSubdivisionEndpointBoundary_finsetEdgeAlgebra
          S
          (fun a : ℂ =>
            explicitFormulaRectangleBoxBottomEdgeIntegral f
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))
          (fun a : ℂ =>
            explicitFormulaRectangleBoxTopEdgeIntegral f
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))
          (fun a : ℂ =>
            explicitFormulaRectangleBoxRightEdgeIntegral f
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))
          (fun a : ℂ =>
            explicitFormulaRectangleBoxLeftEdgeIntegral f
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ε a))
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T ε) := by
      rfl

/-- The bottom side of a raw endpoint-data box is the corresponding horizontal
coordinate-label integral. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_bottomEdgeIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (ρ : ℝ) (a : ℂ) :
    explicitFormulaRectangleBoxBottomEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im) := by
  rfl

/-- The top side of a raw endpoint-data box is the corresponding horizontal
coordinate-label integral. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_topEdgeIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (ρ : ℝ) (a : ℂ) :
    explicitFormulaRectangleBoxTopEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re),
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im) := by
  rfl

/-- The right side of a raw endpoint-data box is the corresponding vertical
coordinate-label integral. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_rightEdgeIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (ρ : ℝ) (a : ℂ) :
    explicitFormulaRectangleBoxRightEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re) := by
  rfl

/-- The left side of a raw endpoint-data box is the corresponding vertical
coordinate-label integral. -/
theorem explicitFormulaRectangleRawInscribedSquareEndpointDataBox_leftEdgeIntegral_eq_coordinate
    (f : ZetaAdmissibleFunction) (ρ : ℝ) (a : ℂ) :
    explicitFormulaRectangleBoxLeftEdgeIntegral f
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBox ρ a) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im),
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re) := by
  rfl

/-- The outer left horizontal coordinate is present in the sorted horizontal endpoint
list. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

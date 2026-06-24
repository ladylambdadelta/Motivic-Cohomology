import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedFourCellNormalForm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedBoundarySplits

/-!
# Named edge integrals for the one-pole square-punctured rectangle

This file gives stable names to the concrete edge integrals used in the
square-punctured boundary decomposition.  The names are intentionally geometric:
outer rectangle edges, inner square edges, and the exposed cell segments.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Outer bottom edge of the one-pole rectangle in standard orientation. -/
noncomputable def zetaExplicitFormulaOnePoleOuterBottomEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)

/-- Outer top edge of the one-pole rectangle, before the standard boundary sign. -/
noncomputable def zetaExplicitFormulaOnePoleOuterTopEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)

/-- Outer right vertical edge of the one-pole rectangle with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleOuterRightEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I))

/-- Outer left vertical edge of the one-pole rectangle with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleOuterLeftEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I))

/-- Inner square bottom edge around the pole `1`. -/
noncomputable def zetaExplicitFormulaOnePoleInnerBottomEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I)

/-- Inner square top edge around the pole `1`, before the standard boundary sign. -/
noncomputable def zetaExplicitFormulaOnePoleInnerTopEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I)

/-- Inner square right vertical edge around the pole `1` with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleInnerRightEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))

/-- Inner square left vertical edge around the pole `1` with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleInnerLeftEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I))

/-- Bottom exposed left horizontal segment at the lower side of the puncture. -/
noncomputable def zetaExplicitFormulaOnePoleBottomLeftSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)

/-- Bottom exposed right horizontal segment at the lower side of the puncture. -/
noncomputable def zetaExplicitFormulaOnePoleBottomRightSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)

/-- Top exposed left horizontal segment at the upper side of the puncture. -/
noncomputable def zetaExplicitFormulaOnePoleTopLeftSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)

/-- Top exposed right horizontal segment at the upper side of the puncture. -/
noncomputable def zetaExplicitFormulaOnePoleTopRightSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)

/-- Right outer vertical bottom segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleRightBottomSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I))

/-- Right outer vertical middle segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleRightMiddleSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))

/-- Right outer vertical top segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleRightTopSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in R..T, g (F.c + y * Complex.I))

/-- Left outer vertical bottom segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleLeftBottomSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))

/-- Left outer vertical middle segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleLeftMiddleSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))

/-- Left outer vertical top segment with tangent factor. -/
noncomputable def zetaExplicitFormulaOnePoleLeftTopSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))

/-- The outer standard boundary in named edge-integral form. -/
theorem zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral_eq_namedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T =
      zetaExplicitFormulaOnePoleOuterBottomEdge g F T -
        zetaExplicitFormulaOnePoleOuterTopEdge g F T +
          (zetaExplicitFormulaOnePoleOuterRightEdge g F T -
            zetaExplicitFormulaOnePoleOuterLeftEdge g F T) := by
  rfl

/-- The inner square boundary in named edge-integral form. -/
theorem zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral_eq_namedEdges
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R =
      zetaExplicitFormulaOnePoleInnerBottomEdge g R -
        zetaExplicitFormulaOnePoleInnerTopEdge g R +
          (zetaExplicitFormulaOnePoleInnerRightEdge g R -
            zetaExplicitFormulaOnePoleInnerLeftEdge g R) := by
  rfl

/-- Named exposed boundary normal form for the square-punctured rectangle. -/
noncomputable def zetaExplicitFormulaOnePoleNamedSquareExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
      -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
    (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
      -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
    ((zetaExplicitFormulaOnePoleOuterRightEdge g F T +
        -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
      (zetaExplicitFormulaOnePoleOuterLeftEdge g F T +
        -zetaExplicitFormulaOnePoleInnerLeftEdge g R))

/-- Named four-cell boundary normal form after horizontal subdivision. -/
noncomputable def zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaOnePoleOuterBottomEdge g F T -
      ((zetaExplicitFormulaOnePoleBottomLeftSegment g F R +
        zetaExplicitFormulaOnePoleInnerBottomEdge g R) +
          zetaExplicitFormulaOnePoleBottomRightSegment g F R) +
      zetaExplicitFormulaOnePoleRightBottomSegment g F T R -
        zetaExplicitFormulaOnePoleLeftBottomSegment g F T R) +
    (((zetaExplicitFormulaOnePoleTopLeftSegment g F R +
        zetaExplicitFormulaOnePoleInnerTopEdge g R) +
          zetaExplicitFormulaOnePoleTopRightSegment g F R) -
      zetaExplicitFormulaOnePoleOuterTopEdge g F T +
      zetaExplicitFormulaOnePoleRightTopSegment g F T R -
        zetaExplicitFormulaOnePoleLeftTopSegment g F T R) +
      (zetaExplicitFormulaOnePoleBottomLeftSegment g F R -
        zetaExplicitFormulaOnePoleTopLeftSegment g F R +
        zetaExplicitFormulaOnePoleInnerLeftEdge g R -
          zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
        (zetaExplicitFormulaOnePoleBottomRightSegment g F R -
          zetaExplicitFormulaOnePoleTopRightSegment g F R +
          zetaExplicitFormulaOnePoleRightMiddleSegment g F R -
            zetaExplicitFormulaOnePoleInnerRightEdge g R)

/-- Named exposed boundary normal form with the outer vertical sides already
written as the three vertical cell segments. -/
noncomputable def zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
      -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
    (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
      -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
    ((((zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
        zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
          zetaExplicitFormulaOnePoleRightTopSegment g F T R) +
        -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
      ((((zetaExplicitFormulaOnePoleLeftBottomSegment g F T R +
        zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
          zetaExplicitFormulaOnePoleLeftTopSegment g F T R) +
          -zetaExplicitFormulaOnePoleInnerLeftEdge g R)))

/-- The square-punctured boundary in named outer and inner edge form. -/
theorem zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq_namedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      (zetaExplicitFormulaOnePoleOuterBottomEdge g F T -
          zetaExplicitFormulaOnePoleOuterTopEdge g F T +
            (zetaExplicitFormulaOnePoleOuterRightEdge g F T -
              zetaExplicitFormulaOnePoleOuterLeftEdge g F T)) -
        (zetaExplicitFormulaOnePoleInnerBottomEdge g R -
          zetaExplicitFormulaOnePoleInnerTopEdge g R +
            (zetaExplicitFormulaOnePoleInnerRightEdge g R -
              zetaExplicitFormulaOnePoleInnerLeftEdge g R)) := by
  rfl

/-- The square-punctured boundary in named exposed-edge form. -/
theorem zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq_namedExposedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R := by
  let outerBottom : ℂ := zetaExplicitFormulaOnePoleOuterBottomEdge g F T
  let outerTop : ℂ := zetaExplicitFormulaOnePoleOuterTopEdge g F T
  let outerRight : ℂ := zetaExplicitFormulaOnePoleOuterRightEdge g F T
  let outerLeft : ℂ := zetaExplicitFormulaOnePoleOuterLeftEdge g F T
  let innerBottom : ℂ := zetaExplicitFormulaOnePoleInnerBottomEdge g R
  let innerTop : ℂ := zetaExplicitFormulaOnePoleInnerTopEdge g R
  let innerRight : ℂ := zetaExplicitFormulaOnePoleInnerRightEdge g R
  let innerLeft : ℂ := zetaExplicitFormulaOnePoleInnerLeftEdge g R
  have hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) := by
    rfl
  have halgebra :
      (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) :=
    zetaExplicitFormulaOnePole_outer_sub_inner_four_edges_grouped
      outerBottom outerTop outerRight outerLeft
      innerBottom innerTop innerRight innerLeft
  calc
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) := hboundary
    _ =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) := halgebra
    _ =
      (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
          -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
        (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
          -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
        ((zetaExplicitFormulaOnePoleOuterRightEdge g F T +
            -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
          (zetaExplicitFormulaOnePoleOuterLeftEdge g F T +
            -zetaExplicitFormulaOnePoleInnerLeftEdge g R)) := by
      rfl

/-- Replacing the right and left outer vertical edges in the named exposed
boundary by their three-segment forms gives the vertical-split normal form. -/
theorem zetaExplicitFormulaOnePoleNamedSquareExposedBoundary_eq_verticalSplit
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hright :
      zetaExplicitFormulaOnePoleOuterRightEdge g F T =
        (zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
          zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleRightTopSegment g F T R)
    (hleft :
      zetaExplicitFormulaOnePoleOuterLeftEdge g F T =
        (zetaExplicitFormulaOnePoleLeftBottomSegment g F T R +
          zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleLeftTopSegment g F T R) :
    zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R =
      zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R := by
  calc
    zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R =
        (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
            -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
          (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
            -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
          ((zetaExplicitFormulaOnePoleOuterRightEdge g F T +
              -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
            (zetaExplicitFormulaOnePoleOuterLeftEdge g F T +
              -zetaExplicitFormulaOnePoleInnerLeftEdge g R)) := by
      rfl
    _ =
        (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
            -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
          (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
            -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
          ((((zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
              zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
                zetaExplicitFormulaOnePoleRightTopSegment g F T R) +
              -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
            (zetaExplicitFormulaOnePoleOuterLeftEdge g F T +
              -zetaExplicitFormulaOnePoleInnerLeftEdge g R)) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
              -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
            (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
              -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
            ((z + -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
              (zetaExplicitFormulaOnePoleOuterLeftEdge g F T +
                -zetaExplicitFormulaOnePoleInnerLeftEdge g R)))
        hright
    _ =
        (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
            -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
          (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
            -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
          ((((zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
              zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
                zetaExplicitFormulaOnePoleRightTopSegment g F T R) +
              -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
            ((((zetaExplicitFormulaOnePoleLeftBottomSegment g F T R +
              zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
                zetaExplicitFormulaOnePoleLeftTopSegment g F T R) +
                -zetaExplicitFormulaOnePoleInnerLeftEdge g R))) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaOnePoleOuterBottomEdge g F T +
              -zetaExplicitFormulaOnePoleInnerBottomEdge g R) -
            (zetaExplicitFormulaOnePoleOuterTopEdge g F T +
              -zetaExplicitFormulaOnePoleInnerTopEdge g R) +
            ((((zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
                zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
                  zetaExplicitFormulaOnePoleRightTopSegment g F T R) +
                -zetaExplicitFormulaOnePoleInnerRightEdge g R) -
              (z + -zetaExplicitFormulaOnePoleInnerLeftEdge g R)))
        hleft
    _ = zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R := by
      rfl

/-- The four-cell boundary sum in named, unsplit full-edge form. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_namedGroupedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
      (zetaExplicitFormulaOnePoleOuterBottomEdge g F T -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) +
          zetaExplicitFormulaOnePoleRightBottomSegment g F T R -
            zetaExplicitFormulaOnePoleLeftBottomSegment g F T R) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          zetaExplicitFormulaOnePoleOuterTopEdge g F T +
          zetaExplicitFormulaOnePoleRightTopSegment g F T R -
            zetaExplicitFormulaOnePoleLeftTopSegment g F T R) +
          (zetaExplicitFormulaOnePoleBottomLeftSegment g F R -
            zetaExplicitFormulaOnePoleTopLeftSegment g F R +
            zetaExplicitFormulaOnePoleInnerLeftEdge g R -
              zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
            (zetaExplicitFormulaOnePoleBottomRightSegment g F R -
              zetaExplicitFormulaOnePoleTopRightSegment g F R +
              zetaExplicitFormulaOnePoleRightMiddleSegment g F R -
                zetaExplicitFormulaOnePoleInnerRightEdge g R) := by
  exact zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_groupedEdges
    g F T R

/-- The four-cell boundary sum in named form after the two puncture-height
horizontal full edges have been split into left, inner, and right pieces. -/
theorem zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_namedSplitHorizontalEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) =
        (zetaExplicitFormulaOnePoleBottomLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerBottomEdge g R) +
            zetaExplicitFormulaOnePoleBottomRightSegment g F R)
    (htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaOnePoleTopLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerTopEdge g R) +
            zetaExplicitFormulaOnePoleTopRightSegment g F R) :
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
      zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary g F T R := by
  have hsplit :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
          (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) +
            (∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I))) +
              (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
          (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
            (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
              ((∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
                (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                    Complex.I •
                      (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))) :=
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_splitHorizontalEdges
      g F T R hbottom htop
  calc
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) -
          (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) +
            (∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I))) +
              (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I))) +
          (((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
            (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
              (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
              Complex.I •
                (∫ y : ℝ in R..T, g (F.c + y * Complex.I)) -
                Complex.I •
                  (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) +
            ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) -
              (∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
                Complex.I •
                  (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I)) -
                  Complex.I •
                    (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
              ((∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) -
                (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) +
                  Complex.I •
                    (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)) -
                    Complex.I •
                      (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))) :=
      hsplit
    _ =
      (zetaExplicitFormulaOnePoleOuterBottomEdge g F T -
          ((zetaExplicitFormulaOnePoleBottomLeftSegment g F R +
            zetaExplicitFormulaOnePoleInnerBottomEdge g R) +
              zetaExplicitFormulaOnePoleBottomRightSegment g F R) +
          zetaExplicitFormulaOnePoleRightBottomSegment g F T R -
            zetaExplicitFormulaOnePoleLeftBottomSegment g F T R) +
        (((zetaExplicitFormulaOnePoleTopLeftSegment g F R +
            zetaExplicitFormulaOnePoleInnerTopEdge g R) +
              zetaExplicitFormulaOnePoleTopRightSegment g F R) -
          zetaExplicitFormulaOnePoleOuterTopEdge g F T +
          zetaExplicitFormulaOnePoleRightTopSegment g F T R -
            zetaExplicitFormulaOnePoleLeftTopSegment g F T R) +
          (zetaExplicitFormulaOnePoleBottomLeftSegment g F R -
            zetaExplicitFormulaOnePoleTopLeftSegment g F R +
            zetaExplicitFormulaOnePoleInnerLeftEdge g R -
              zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
            (zetaExplicitFormulaOnePoleBottomRightSegment g F R -
              zetaExplicitFormulaOnePoleTopRightSegment g F R +
              zetaExplicitFormulaOnePoleRightMiddleSegment g F R -
                zetaExplicitFormulaOnePoleInnerRightEdge g R) := by
      rfl

/-- The named split four-cell boundary is the named vertical-split exposed
square-punctured boundary. -/
theorem zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary_eq_verticalSplitExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary g F T R =
      zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R :=
  zetaExplicitFormulaOnePole_fourCellSplitBoundary_eq_verticalSplitExposed_algebra
    (zetaExplicitFormulaOnePoleOuterBottomEdge g F T)
    (zetaExplicitFormulaOnePoleOuterTopEdge g F T)
    (zetaExplicitFormulaOnePoleInnerBottomEdge g R)
    (zetaExplicitFormulaOnePoleInnerTopEdge g R)
    (zetaExplicitFormulaOnePoleBottomLeftSegment g F R)
    (zetaExplicitFormulaOnePoleBottomRightSegment g F R)
    (zetaExplicitFormulaOnePoleTopLeftSegment g F R)
    (zetaExplicitFormulaOnePoleTopRightSegment g F R)
    (zetaExplicitFormulaOnePoleRightBottomSegment g F T R)
    (zetaExplicitFormulaOnePoleRightMiddleSegment g F R)
    (zetaExplicitFormulaOnePoleRightTopSegment g F T R)
    (zetaExplicitFormulaOnePoleInnerRightEdge g R)
    (zetaExplicitFormulaOnePoleLeftBottomSegment g F T R)
    (zetaExplicitFormulaOnePoleLeftMiddleSegment g F R)
    (zetaExplicitFormulaOnePoleLeftTopSegment g F T R)
    (zetaExplicitFormulaOnePoleInnerLeftEdge g R)

/-- The square-punctured boundary equals the four-cell boundary once the two
puncture-height horizontal edges and the two outer vertical edges have been
split into their cell segments. -/
theorem zetaExplicitFormulaOnePoleSquarePuncturedBoundary_eq_fourCellBoundary_of_edgeSplits
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) =
        (zetaExplicitFormulaOnePoleBottomLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerBottomEdge g R) +
            zetaExplicitFormulaOnePoleBottomRightSegment g F R)
    (htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaOnePoleTopLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerTopEdge g R) +
            zetaExplicitFormulaOnePoleTopRightSegment g F R)
    (hright :
      zetaExplicitFormulaOnePoleOuterRightEdge g F T =
        (zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
          zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleRightTopSegment g F T R)
    (hleft :
      zetaExplicitFormulaOnePoleOuterLeftEdge g F T =
        (zetaExplicitFormulaOnePoleLeftBottomSegment g F T R +
          zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleLeftTopSegment g F T R) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R := by
  have hsquare :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R :=
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq_namedExposedEdges
      g F T R
  have hvertical :
      zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R =
        zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R :=
    zetaExplicitFormulaOnePoleNamedSquareExposedBoundary_eq_verticalSplit
      g F T R hright hleft
  have hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R =
        zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary g F T R :=
    zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum_eq_namedSplitHorizontalEdges
      g F T R hbottom htop
  have halgebra :
      zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary g F T R =
        zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R :=
    zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary_eq_verticalSplitExposedBoundary
      g F T R
  calc
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        zetaExplicitFormulaOnePoleNamedSquareExposedBoundary g F T R := hsquare
    _ = zetaExplicitFormulaOnePoleNamedVerticalSplitExposedBoundary g F T R :=
      hvertical
    _ = zetaExplicitFormulaOnePoleNamedFourCellSplitBoundary g F T R :=
      halgebra.symm
    _ = zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum g F T R :=
      hfour.symm

/-- Canonical full-boundary assembly for the isolated `s = 1` correction
kernel.

This is finite contour accounting: the outer standard boundary minus the inner
square boundary is assembled from the four rectangular cell boundaries after
the canonical edge splits. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalSquarePuncturedBoundary_eq_fourCellBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) := by
  let R : ℝ := zetaExplicitFormulaOnePolePunctureRadius F T
  let g : ℂ → ℂ :=
    fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z
  have hR_pos : 0 < R :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F T hT
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR_pos
  have hnegR_ne : -R ≠ 0 := by
    intro hzero
    exact hR_ne (neg_eq_zero.mp hzero)
  have hright_re_ne : F.c ≠ 1 :=
    ne_of_gt F.c_gt_one
  have hleft_re_ne : 1 - F.c ≠ 1 := by
    intro hleft
    have hc_zero : F.c = 0 :=
      sub_eq_self.mp hleft
    exact (ne_of_gt F.c_pos) hc_zero
  have hbottom_left :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I))
        volume (1 - F.c) (1 - R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) (1 - F.c) (1 - R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x (-R) hnegR_ne)))
  have hbottom_inner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I))
        volume (1 - R) (1 + R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) (1 - R) (1 + R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x (-R) hnegR_ne)))
  have hbottom_right :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I))
        volume (1 + R) F.c := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) (1 + R) F.c
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x (-R) hnegR_ne)))
  have htop_left :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume (1 - F.c) (1 - R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R (1 - F.c) (1 - R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x R hR_ne)))
  have htop_inner :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume (1 - R) (1 + R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R (1 - R) (1 + R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x R hR_ne)))
  have htop_right :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume (1 + R) F.c := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R (1 + R) F.c
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hx.2
                    (zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
                      x R hR_ne)))
  have hright_bottom :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (-T) (-R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c (-T) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      F.c y hright_re_ne)))
  have hright_middle :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (-R) R := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      F.c y hright_re_ne)))
  have hright_top :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume R T := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c R T
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      F.c y hright_re_ne)))
  have hleft_bottom :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume (-T) (-R) := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) (-T) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      (1 - F.c) y hleft_re_ne)))
  have hleft_middle :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume (-R) R := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      (1 - F.c) y hleft_re_ne)))
  have hleft_top :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume R T := by
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) R T
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w - 1 ≠ 0)
                hy.2
                    (zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
                      (1 - F.c) y hleft_re_ne)))
  have hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) =
        (zetaExplicitFormulaOnePoleBottomLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerBottomEdge g R) +
            zetaExplicitFormulaOnePoleBottomRightSegment g F R :=
    zetaCompletedExplicitFormulaCorrectionOnePole_bottomPunctureHorizontal_full_eq_segments_canonicalRadius
      f F T hbottom_left hbottom_inner hbottom_right
  have htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaOnePoleTopLeftSegment g F R +
          zetaExplicitFormulaOnePoleInnerTopEdge g R) +
            zetaExplicitFormulaOnePoleTopRightSegment g F R :=
    zetaCompletedExplicitFormulaCorrectionOnePole_topPunctureHorizontal_full_eq_segments_canonicalRadius
      f F T htop_left htop_inner htop_right
  have hright :
      zetaExplicitFormulaOnePoleOuterRightEdge g F T =
        (zetaExplicitFormulaOnePoleRightBottomSegment g F T R +
          zetaExplicitFormulaOnePoleRightMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleRightTopSegment g F T R :=
    zetaCompletedExplicitFormulaCorrectionOnePole_rightOuterVertical_full_eq_segments_canonicalRadius
      f F T hright_bottom hright_middle hright_top
  have hleft :
      zetaExplicitFormulaOnePoleOuterLeftEdge g F T =
        (zetaExplicitFormulaOnePoleLeftBottomSegment g F T R +
          zetaExplicitFormulaOnePoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaOnePoleLeftTopSegment g F T R :=
    zetaCompletedExplicitFormulaCorrectionOnePole_leftOuterVertical_full_eq_segments_canonicalRadius
      f F T hleft_bottom hleft_middle hleft_top
  exact
    zetaExplicitFormulaOnePoleSquarePuncturedBoundary_eq_fourCellBoundary_of_edgeSplits
      g F T R hbottom htop hright hleft

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

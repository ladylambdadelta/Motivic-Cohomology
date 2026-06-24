import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedBoundaryAlgebra
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedConsumers

/-!
# Named edge integrals for the zero-pole square-punctured rectangle

This file gives stable names to the concrete edge integrals used in the
zero-centered square-punctured boundary decomposition.  It owns the first pure
bookkeeping step: rewriting the outer-minus-inner boundary as exposed named
edges.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Outer bottom edge of the zero-pole rectangle in standard orientation. -/
noncomputable def zetaExplicitFormulaZeroPoleOuterBottomEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)

/-- Outer top edge of the zero-pole rectangle, before the standard boundary sign. -/
noncomputable def zetaExplicitFormulaZeroPoleOuterTopEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)

/-- Outer right vertical edge of the zero-pole rectangle with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleOuterRightEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I))

/-- Outer left vertical edge of the zero-pole rectangle with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleOuterLeftEdge
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I))

/-- Inner square bottom edge around the pole `0`. -/
noncomputable def zetaExplicitFormulaZeroPoleInnerBottomEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (-R)..R, g (x + (-R) * Complex.I)

/-- Inner square top edge around the pole `0`, before the standard boundary sign. -/
noncomputable def zetaExplicitFormulaZeroPoleInnerTopEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (-R)..R, g (x + R * Complex.I)

/-- Inner square right vertical edge around the pole `0` with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleInnerRightEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g (R + y * Complex.I))

/-- Inner square left vertical edge around the pole `0` with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleInnerLeftEdge
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g ((-R) + y * Complex.I))

/-- Named exposed boundary normal form for the zero-pole square-punctured
rectangle. -/
noncomputable def zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
      -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
    (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
      -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
    ((zetaExplicitFormulaZeroPoleOuterRightEdge g F T +
        -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
      (zetaExplicitFormulaZeroPoleOuterLeftEdge g F T +
        -zetaExplicitFormulaZeroPoleInnerLeftEdge g R))

/-- The zero-pole outer standard boundary in named edge-integral form. -/
theorem zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral_eq_namedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T =
      zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
        zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          (zetaExplicitFormulaZeroPoleOuterRightEdge g F T -
            zetaExplicitFormulaZeroPoleOuterLeftEdge g F T) := by
  rfl

/-- The zero-pole inner square boundary in named edge-integral form. -/
theorem zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral_eq_namedEdges
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
      zetaExplicitFormulaZeroPoleInnerBottomEdge g R -
        zetaExplicitFormulaZeroPoleInnerTopEdge g R +
          (zetaExplicitFormulaZeroPoleInnerRightEdge g R -
            zetaExplicitFormulaZeroPoleInnerLeftEdge g R) := by
  rfl

/-- The zero-pole square-punctured boundary in named outer and inner edge form. -/
theorem zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral_eq_namedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
          zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            (zetaExplicitFormulaZeroPoleOuterRightEdge g F T -
              zetaExplicitFormulaZeroPoleOuterLeftEdge g F T)) -
        (zetaExplicitFormulaZeroPoleInnerBottomEdge g R -
          zetaExplicitFormulaZeroPoleInnerTopEdge g R +
            (zetaExplicitFormulaZeroPoleInnerRightEdge g R -
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R)) := by
  rfl

/-- The zero-pole square-punctured boundary in named exposed-edge form. -/
theorem zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral_eq_namedExposedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R := by
  let outerBottom : ℂ := zetaExplicitFormulaZeroPoleOuterBottomEdge g F T
  let outerTop : ℂ := zetaExplicitFormulaZeroPoleOuterTopEdge g F T
  let outerRight : ℂ := zetaExplicitFormulaZeroPoleOuterRightEdge g F T
  let outerLeft : ℂ := zetaExplicitFormulaZeroPoleOuterLeftEdge g F T
  let innerBottom : ℂ := zetaExplicitFormulaZeroPoleInnerBottomEdge g R
  let innerTop : ℂ := zetaExplicitFormulaZeroPoleInnerTopEdge g R
  let innerRight : ℂ := zetaExplicitFormulaZeroPoleInnerRightEdge g R
  let innerLeft : ℂ := zetaExplicitFormulaZeroPoleInnerLeftEdge g R
  have hboundary :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
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
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) := hboundary
    _ =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) := halgebra
    _ =
      zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R := by
      rfl

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

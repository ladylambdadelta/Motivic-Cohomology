import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedEdges

/-!
# Split edge normal forms for the zero-pole square-punctured rectangle

This file owns the named exposed segments and pure boundary normal forms used
to compare the zero-centered square-punctured boundary with its four-cell
subdivision.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- A zero-pole correction kernel restricted to a continuous real parametrized
segment is interval-integrable once the complex kernel is continuous on that
segment image. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_param_intervalIntegrable_of_continuousOn
    (f : ZetaAdmissibleFunction)
    (γ : ℝ → ℂ)
    {a b : ℝ}
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (hkernel :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        (γ '' Set.uIcc a b)) :
    IntervalIntegrable
      (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f (γ x))
      volume a b := by
  have hmaps :
      Set.MapsTo γ (Set.uIcc a b) (γ '' Set.uIcc a b) := by
    intro x hx
    exact Set.mem_image_of_mem γ hx
  have hcont :
      ContinuousOn
        (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f (γ x))
        (Set.uIcc a b) :=
    ContinuousOn.comp hkernel hγ hmaps
  exact hcont.intervalIntegrable

/-- Combined off-pole parametrized segment integrability for the zero-pole
correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_param_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (γ : ℝ → ℂ)
    {a b : ℝ}
    (hγ : ContinuousOn γ (Set.uIcc a b))
    (havoid : ∀ z : ℂ, z ∈ γ '' Set.uIcc a b → z ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f (γ x))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_param_intervalIntegrable_of_continuousOn
      f γ hγ
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_continuousOn_of_avoids_pole
        f hPhi (γ '' Set.uIcc a b) havoid)

/-- A horizontal affine point at nonzero height is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
    (x y : ℝ) (hy : y ≠ 0) :
    (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
  intro hpoint
  have him_eq :
      ((x : ℂ) + (y : ℂ) * Complex.I).im = (0 : ℂ).im :=
    congrArg Complex.im hpoint
  have hy_zero : y = 0 := by
    calc
      y = ((x : ℂ) + (y : ℂ) * Complex.I).im := by
        exact (zetaExplicitFormulaOnePole_horizontalAffine_im x y).symm
      _ = (0 : ℂ).im := him_eq
      _ = 0 := Complex.zero_im
  exact hy hy_zero

/-- A vertical affine point with nonzero real coordinate is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
    (x y : ℝ) (hx : x ≠ 0) :
    (x : ℂ) + (y : ℂ) * Complex.I ≠ 0 := by
  intro hpoint
  have hre_eq :
      ((x : ℂ) + (y : ℂ) * Complex.I).re = (0 : ℂ).re :=
    congrArg Complex.re hpoint
  have hx_zero : x = 0 := by
    calc
      x = ((x : ℂ) + (y : ℂ) * Complex.I).re := by
        exact (zetaExplicitFormulaOnePole_verticalAffine_re x y).symm
      _ = (0 : ℂ).re := hre_eq
      _ = 0 := Complex.zero_re
  exact hx hx_zero

/-- Horizontal rectangular zero-pole segment integrability from off-pole image
avoidance. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (y : ℝ)
    (a b : ℝ)
    (havoid :
      ∀ z : ℂ,
        z ∈ (fun x : ℝ => (x : ℂ) + y * Complex.I) '' Set.uIcc a b →
          z ≠ 0) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          ((x : ℂ) + y * Complex.I))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_param_intervalIntegrable_of_avoids_pole
      f hPhi (fun x : ℝ => (x : ℂ) + y * Complex.I)
      (zetaExplicitFormulaOnePole_horizontalAffine_continuousOn y a b)
      havoid

/-- Vertical rectangular zero-pole segment integrability from off-pole image
avoidance. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl f)
    (x : ℝ)
    (a b : ℝ)
    (havoid :
      ∀ z : ℂ,
        z ∈ (fun y : ℝ => (x : ℂ) + y * Complex.I) '' Set.uIcc a b →
          z ≠ 0) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          ((x : ℂ) + y * Complex.I))
      volume a b := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_param_intervalIntegrable_of_avoids_pole
      f hPhi (fun y : ℝ => (x : ℂ) + y * Complex.I)
      (zetaExplicitFormulaOnePole_verticalAffine_continuousOn x a b)
      havoid

/-- Bottom exposed left horizontal segment at the lower side of the zero
puncture. -/
noncomputable def zetaExplicitFormulaZeroPoleBottomLeftSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..(-R), g (x + (((-R : ℝ) : ℂ) * Complex.I))

/-- Bottom exposed right horizontal segment at the lower side of the zero
puncture. -/
noncomputable def zetaExplicitFormulaZeroPoleBottomRightSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in R..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))

/-- Top exposed left horizontal segment at the upper side of the zero puncture. -/
noncomputable def zetaExplicitFormulaZeroPoleTopLeftSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in (1 - F.c)..(-R), g (x + R * Complex.I)

/-- Top exposed right horizontal segment at the upper side of the zero puncture. -/
noncomputable def zetaExplicitFormulaZeroPoleTopRightSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  ∫ x : ℝ in R..F.c, g (x + R * Complex.I)

/-- Right outer vertical bottom segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleRightBottomSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I))

/-- Right outer vertical middle segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleRightMiddleSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))

/-- Right outer vertical top segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleRightTopSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in R..T, g (F.c + y * Complex.I))

/-- Left outer vertical bottom segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleLeftBottomSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))

/-- Left outer vertical middle segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleLeftMiddleSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))

/-- Left outer vertical top segment with tangent factor. -/
noncomputable def zetaExplicitFormulaZeroPoleLeftTopSegment
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  Complex.I • (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))

/-- Named four-cell boundary normal form after horizontal subdivision. -/
noncomputable def zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
      ((zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
        zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
          zetaExplicitFormulaZeroPoleBottomRightSegment g F R) +
      zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
        zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
    (((zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
        zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
          zetaExplicitFormulaZeroPoleTopRightSegment g F R) -
      zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
      zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
        zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
      (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
        zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
        zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
          zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
        (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
          zetaExplicitFormulaZeroPoleTopRightSegment g F R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
            zetaExplicitFormulaZeroPoleInnerRightEdge g R)

/-- Named exposed boundary normal form with the outer vertical sides already
written as the three vertical cell segments. -/
noncomputable def zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
      -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
    (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
      -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
    ((((zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
        zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R) +
        -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
      ((((zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
        zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
          zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
          -zetaExplicitFormulaZeroPoleInnerLeftEdge g R)))

/-- The named split zero-pole four-cell boundary is the named vertical-split
exposed square-punctured boundary. -/
theorem zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary_eq_verticalSplitExposedBoundary
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R =
      zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R :=
  zetaExplicitFormulaOnePole_fourCellSplitBoundary_eq_verticalSplitExposed_algebra
    (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T)
    (zetaExplicitFormulaZeroPoleOuterTopEdge g F T)
    (zetaExplicitFormulaZeroPoleInnerBottomEdge g R)
    (zetaExplicitFormulaZeroPoleInnerTopEdge g R)
    (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R)
    (zetaExplicitFormulaZeroPoleBottomRightSegment g F R)
    (zetaExplicitFormulaZeroPoleTopLeftSegment g F R)
    (zetaExplicitFormulaZeroPoleTopRightSegment g F R)
    (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R)
    (zetaExplicitFormulaZeroPoleRightMiddleSegment g F R)
    (zetaExplicitFormulaZeroPoleRightTopSegment g F T R)
    (zetaExplicitFormulaZeroPoleInnerRightEdge g R)
    (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R)
    (zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R)
    (zetaExplicitFormulaZeroPoleLeftTopSegment g F T R)
    (zetaExplicitFormulaZeroPoleInnerLeftEdge g R)

/-- Reassociate the standard rectangle boundary expression into the exposed
edge convention used by the zero-pole named cells. -/
theorem zetaExplicitFormulaZeroPole_rectangleFourEdges_reassociate
    (a b c d : ℂ) :
    (a - b) + (c - d) = ((a - b) + c) - d := by
  calc
    (a - b) + (c - d) = (a - b) + (c + -d) := by
      exact congrArg (fun z : ℂ => (a - b) + z) (sub_eq_add_neg c d)
    _ = ((a - b) + c) + -d := by
      exact (add_assoc (a - b) c (-d)).symm
    _ = ((a - b) + c) - d := by
      exact (sub_eq_add_neg ((a - b) + c) d).symm

/-- The bottom zero-pole puncture cell unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
          zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R := by
  have hleftCorner :
      (1 - (F.c : ℂ)) + (-(T : ℂ)) * Complex.I =
        (((1 - F.c : ℝ) : ℂ) + (((-T : ℝ) : ℂ) * Complex.I)) :=
    congrArg₂
      (fun a b : ℂ => a + b * Complex.I)
      (Complex.ofReal_sub (1 : ℝ) F.c).symm
      (Complex.ofReal_neg T).symm
  have hrightCorner :
      (F.c : ℂ) + (-(R : ℂ)) * Complex.I =
        (F.c + (((-R : ℝ) : ℂ) * Complex.I)) :=
    congrArg
      (fun b : ℂ => (F.c : ℂ) + b * Complex.I)
      (Complex.ofReal_neg R).symm
  have hcorner :
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I) =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (((-T : ℝ) : ℂ) * Complex.I)))
            (F.c + (((-R : ℝ) : ℂ) * Complex.I)) :=
    congrArg₂
      (fun z w : ℂ => zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z w)
      hleftCorner hrightCorner
  calc
    zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral g F T R =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I) := by
      rfl
    _ =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (((-T : ℝ) : ℂ) * Complex.I)))
            (F.c + (((-R : ℝ) : ℂ) * Complex.I)) := hcorner
    _ =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - F.c) F.c (-T) (-R) := by
      exact
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_affine_eq_standard
          g (1 - F.c) F.c (-T) (-R)
    _ =
      zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
          zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R := by
      unfold zetaExplicitFormulaZeroPoleOuterBottomEdge
      unfold zetaExplicitFormulaZeroPoleRightBottomSegment
      unfold zetaExplicitFormulaZeroPoleLeftBottomSegment
      exact
        Eq.trans
          (zetaExplicitFormulaOnePole_standardRectangleBoundaryCoordinateIntegral_eq_four_edges
            g (1 - F.c) F.c (-T) (-R))
          (zetaExplicitFormulaZeroPole_rectangleFourEdges_reassociate
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-T : ℝ) : ℂ) * Complex.I)))
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I)))
            (Complex.I • (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)))
            (Complex.I •
              (∫ y : ℝ in -T..(-R),
                g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))))

/-- The top zero-pole puncture cell unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
        zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R := by
  have hleftCorner :
      (1 - (F.c : ℂ)) + (R : ℂ) * Complex.I =
        (((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I) :=
    congrArg (fun a : ℂ => a + (R : ℂ) * Complex.I)
      (Complex.ofReal_sub (1 : ℝ) F.c).symm
  have hcorner :
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I) =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I)) (F.c + T * Complex.I) :=
    congrArg
      (fun z : ℂ =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z (F.c + T * Complex.I))
      hleftCorner
  calc
    zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I) := by
      rfl
    _ =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (R : ℂ) * Complex.I)) (F.c + T * Complex.I) :=
      hcorner
    _ =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - F.c) F.c R T := by
      exact
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_affine_eq_standard
          g (1 - F.c) F.c R T
    _ =
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
        zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R := by
      unfold zetaExplicitFormulaZeroPoleOuterTopEdge
      unfold zetaExplicitFormulaZeroPoleRightTopSegment
      unfold zetaExplicitFormulaZeroPoleLeftTopSegment
      exact
        Eq.trans
          (zetaExplicitFormulaOnePole_standardRectangleBoundaryCoordinateIntegral_eq_four_edges
            g (1 - F.c) F.c R T)
          (zetaExplicitFormulaZeroPole_rectangleFourEdges_reassociate
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I))
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I))
            (Complex.I • (∫ y : ℝ in R..T, g (F.c + y * Complex.I)))
            (Complex.I •
              (∫ y : ℝ in R..T,
                g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))))

/-- The left zero-pole puncture cell unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
        zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
            zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R := by
  have hleftCorner :
      (1 - (F.c : ℂ)) + (-(R : ℂ)) * Complex.I =
        (((1 - F.c : ℝ) : ℂ) + (((-R : ℝ) : ℂ) * Complex.I)) :=
    congrArg₂
      (fun a b : ℂ => a + b * Complex.I)
      (Complex.ofReal_sub (1 : ℝ) F.c).symm
      (Complex.ofReal_neg R).symm
  have hrightCorner :
      (-(R : ℂ)) + (R : ℂ) * Complex.I =
        (((-R : ℝ) : ℂ) + (R : ℂ) * Complex.I) :=
    congrArg (fun a : ℂ => a + (R : ℂ) * Complex.I)
      (Complex.ofReal_neg R).symm
  have hcorner :
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + (-R) * Complex.I) ((-R) + R * Complex.I) =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (((-R : ℝ) : ℂ) * Complex.I)))
            (((-R : ℝ) : ℂ) + (R : ℂ) * Complex.I) :=
    congrArg₂
      (fun z w : ℂ => zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z w)
      hleftCorner hrightCorner
  calc
    zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((1 - F.c) + (-R) * Complex.I) ((-R) + R * Complex.I) := by
      rfl
    _ =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((((1 - F.c : ℝ) : ℂ) + (((-R : ℝ) : ℂ) * Complex.I)))
            (((-R : ℝ) : ℂ) + (R : ℂ) * Complex.I) := hcorner
    _ =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - F.c) (-R) (-R) R := by
      exact
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_affine_eq_standard
          g (1 - F.c) (-R) (-R) R
    _ =
      zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
        zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
            zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R := by
      unfold zetaExplicitFormulaZeroPoleBottomLeftSegment
      unfold zetaExplicitFormulaZeroPoleTopLeftSegment
      unfold zetaExplicitFormulaZeroPoleInnerLeftEdge
      unfold zetaExplicitFormulaZeroPoleLeftMiddleSegment
      exact
        Eq.trans
          (zetaExplicitFormulaOnePole_standardRectangleBoundaryCoordinateIntegral_eq_four_edges
            g (1 - F.c) (-R) (-R) R)
          (zetaExplicitFormulaZeroPole_rectangleFourEdges_reassociate
            (∫ x : ℝ in (1 - F.c)..(-R), g (x + (((-R : ℝ) : ℂ) * Complex.I)))
            (∫ x : ℝ in (1 - F.c)..(-R), g (x + R * Complex.I))
            (Complex.I •
              (∫ y : ℝ in -R..R,
                g (((-R : ℝ) : ℂ) + y * Complex.I)))
            (Complex.I •
              (∫ y : ℝ in -R..R,
                g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))))

/-- The right zero-pole puncture cell unfolds to its four coordinate sides. -/
theorem zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
        zetaExplicitFormulaZeroPoleTopRightSegment g F R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
            zetaExplicitFormulaZeroPoleInnerRightEdge g R := by
  have hleftCorner :
      (R : ℂ) + (-(R : ℂ)) * Complex.I =
        (R + (((-R : ℝ) : ℂ) * Complex.I)) :=
    congrArg (fun b : ℂ => (R : ℂ) + b * Complex.I)
      (Complex.ofReal_neg R).symm
  have hcorner :
      zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g (R + (-R) * Complex.I) (F.c + R * Complex.I) =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((R + (((-R : ℝ) : ℂ) * Complex.I))) (F.c + R * Complex.I) :=
    congrArg
      (fun z : ℂ =>
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral g z (F.c + R * Complex.I))
      hleftCorner
  calc
    zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g (R + (-R) * Complex.I) (F.c + R * Complex.I) := by
      rfl
    _ =
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
          g ((R + (((-R : ℝ) : ℂ) * Complex.I))) (F.c + R * Complex.I) :=
      hcorner
    _ =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g R F.c (-R) R := by
      exact
        zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral_affine_eq_standard
          g R F.c (-R) R
    _ =
      zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
        zetaExplicitFormulaZeroPoleTopRightSegment g F R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
            zetaExplicitFormulaZeroPoleInnerRightEdge g R := by
      unfold zetaExplicitFormulaZeroPoleBottomRightSegment
      unfold zetaExplicitFormulaZeroPoleTopRightSegment
      unfold zetaExplicitFormulaZeroPoleRightMiddleSegment
      unfold zetaExplicitFormulaZeroPoleInnerRightEdge
      exact
        Eq.trans
          (zetaExplicitFormulaOnePole_standardRectangleBoundaryCoordinateIntegral_eq_four_edges
            g R F.c (-R) R)
          (zetaExplicitFormulaZeroPole_rectangleFourEdges_reassociate
            (∫ x : ℝ in R..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I)))
            (∫ x : ℝ in R..F.c, g (x + R * Complex.I))
            (Complex.I • (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)))
            (Complex.I •
              (∫ y : ℝ in -R..R,
                g (R + y * Complex.I))))

/-- The zero-pole four-cell boundary sum in named, unsplit full-edge form. -/
theorem zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_namedGroupedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
      (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
          zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
          (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
            zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
            zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
              zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
            (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
              zetaExplicitFormulaZeroPoleTopRightSegment g F R +
              zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
                zetaExplicitFormulaZeroPoleInnerRightEdge g R) := by
  let B : ℂ := zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral g F T R
  let U : ℂ := zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R
  let L : ℂ := zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R
  let Q : ℂ := zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R
  have hB :
      B =
        zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
          (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R :=
    zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral_eq g F T R
  have hU :
      U =
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R :=
    zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral_eq g F T R
  have hL :
      L =
        zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
          zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
            zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
              zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R :=
    zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral_eq g F T R
  have hQ :
      Q =
        zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
          zetaExplicitFormulaZeroPoleTopRightSegment g F R +
            zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
              zetaExplicitFormulaZeroPoleInnerRightEdge g R :=
    zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral_eq g F T R
  calc
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
        B + U + L + Q := by
      rfl
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) + U + L + Q := by
      exact congrArg (fun z : ℂ => z + U + L + Q) hB
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) + L + Q := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
              zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
                zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) + z + L + Q)
        hU
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
            (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
              zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) + Q := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
              zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
                zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
            ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
              zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
              zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
                zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) + z + Q)
        hL
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
            (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
              zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
              (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
                zetaExplicitFormulaZeroPoleTopRightSegment g F R +
                zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
                  zetaExplicitFormulaZeroPoleInnerRightEdge g R) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
              (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
              zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
                zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
            ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
              zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
              zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
                zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
              (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
                zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
                zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                  zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) + z)
        hQ

/-- The bottom zero-puncture horizontal edge over the full rectangle is the sum
of its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaZeroPole_bottomPunctureHorizontal_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I))) volume (1 - F.c) (-R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I))) volume (-R) R)
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I))) volume R F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) =
      ((∫ x : ℝ in (1 - F.c)..(-R), g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
        (∫ x : ℝ in (-R)..R, g (x + (((-R : ℝ) : ℂ) * Complex.I)))) +
          (∫ x : ℝ in R..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) :=
  (zetaExplicitFormulaSinglePole_intervalIntegral_split_three
    (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I)))
    (1 - F.c) (-R) R F.c
    hleft hinner hright).symm

/-- The top zero-puncture horizontal edge over the full rectangle is the sum
of its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaZeroPole_topPunctureHorizontal_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 - F.c) (-R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (-R) R)
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume R F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
      ((∫ x : ℝ in (1 - F.c)..(-R), g (x + R * Complex.I)) +
        (∫ x : ℝ in (-R)..R, g (x + R * Complex.I))) +
          (∫ x : ℝ in R..F.c, g (x + R * Complex.I)) :=
  (zetaExplicitFormulaSinglePole_intervalIntegral_split_three
    (fun x : ℝ => g (x + R * Complex.I))
    (1 - F.c) (-R) R F.c
    hleft hinner hright).symm

/-- The right outer vertical edge is the sum of its bottom, middle, and top
segments in the zero-pole four-cell subdivision. -/
theorem zetaExplicitFormulaZeroPole_rightOuterVertical_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I)) volume R T) :
    zetaExplicitFormulaZeroPoleOuterRightEdge g F T =
      (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
        zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R := by
  calc
    zetaExplicitFormulaZeroPoleOuterRightEdge g F T =
        Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I)) := by
      rfl
    _ =
        Complex.I •
          (((∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) +
            (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))) +
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I))) := by
      exact
        (zetaExplicitFormulaSinglePole_verticalIntegral_split_three
          (fun y : ℝ => g (F.c + y * Complex.I))
          (-T) (-R) R T hbottom hmiddle htop).symm
    _ =
        (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R := by
      unfold zetaExplicitFormulaZeroPoleRightBottomSegment
      unfold zetaExplicitFormulaZeroPoleRightMiddleSegment
      unfold zetaExplicitFormulaZeroPoleRightTopSegment
      exact Eq.trans
        (smul_add Complex.I
          ((∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) +
            (∫ y : ℝ in -R..R, g (F.c + y * Complex.I)))
          (∫ y : ℝ in R..T, g (F.c + y * Complex.I)))
        (congrArg
          (fun z : ℂ =>
            z + Complex.I •
              (∫ y : ℝ in R..T, g (F.c + y * Complex.I)))
          (smul_add Complex.I
            (∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I))
            (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))))

/-- The left outer vertical edge is the sum of its bottom, middle, and top
segments in the zero-pole four-cell subdivision. -/
theorem zetaExplicitFormulaZeroPole_leftOuterVertical_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) volume R T) :
    zetaExplicitFormulaZeroPoleOuterLeftEdge g F T =
      (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
        zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
          zetaExplicitFormulaZeroPoleLeftTopSegment g F T R := by
  calc
    zetaExplicitFormulaZeroPoleOuterLeftEdge g F T =
        Complex.I • (∫ y : ℝ in -T..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) := by
      unfold zetaExplicitFormulaZeroPoleOuterLeftEdge
      exact Eq.refl _
    _ =
        Complex.I •
          (((∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) +
            (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
              (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) := by
      exact
        (zetaExplicitFormulaSinglePole_verticalIntegral_split_three
          (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
          (-T) (-R) R T hbottom hmiddle htop).symm
    _ =
        (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R := by
      unfold zetaExplicitFormulaZeroPoleLeftBottomSegment
      unfold zetaExplicitFormulaZeroPoleLeftMiddleSegment
      unfold zetaExplicitFormulaZeroPoleLeftTopSegment
      exact Eq.trans
        (smul_add Complex.I
          ((∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) +
            (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)))
          (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)))
        (congrArg
          (fun z : ℂ =>
            z + Complex.I •
              (∫ y : ℝ in R..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)))
          (smul_add Complex.I
            (∫ y : ℝ in -T..(-R), g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
            (∫ y : ℝ in -R..R, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))))

/-- The zero-pole four-cell boundary sum in named form after the two
puncture-height horizontal full edges have been split into left, inner, and
right pieces. -/
theorem zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_namedSplitHorizontalEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) =
        (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
            zetaExplicitFormulaZeroPoleBottomRightSegment g F R)
    (htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            zetaExplicitFormulaZeroPoleTopRightSegment g F R) :
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
      zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R := by
  have hgrouped :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
            (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
              zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
              (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
                zetaExplicitFormulaZeroPoleTopRightSegment g F R +
                zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
                  zetaExplicitFormulaZeroPoleInnerRightEdge g R) :=
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_namedGroupedEdges
      g F T R
  calc
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          ((∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
            (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
              zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
              (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
                zetaExplicitFormulaZeroPoleTopRightSegment g F R +
                zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
                  zetaExplicitFormulaZeroPoleInnerRightEdge g R) := hgrouped
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
            ((zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
                zetaExplicitFormulaZeroPoleBottomRightSegment g F R) +
            zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R) +
          (((zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
                zetaExplicitFormulaZeroPoleTopRightSegment g F R) -
            zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
            (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
              zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
              zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
                zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
              (zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
                zetaExplicitFormulaZeroPoleTopRightSegment g F R +
                zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
                  zetaExplicitFormulaZeroPoleInnerRightEdge g R) := by
      let B₀ : ℂ :=
        zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
          (∫ x : ℝ in (1 - F.c)..F.c,
            g (x + (((-R : ℝ) : ℂ) * Complex.I))) +
          zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R
      let B₁ : ℂ :=
        zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
          ((zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
            zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
              zetaExplicitFormulaZeroPoleBottomRightSegment g F R) +
          zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R
      let U₀ : ℂ :=
        (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) -
          zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R
      let U₁ : ℂ :=
        ((zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            zetaExplicitFormulaZeroPoleTopRightSegment g F R) -
          zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
          zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R
      let L₀ : ℂ :=
        zetaExplicitFormulaZeroPoleBottomLeftSegment g F R -
          zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerLeftEdge g R -
            zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R
      let Q₀ : ℂ :=
        zetaExplicitFormulaZeroPoleBottomRightSegment g F R -
          zetaExplicitFormulaZeroPoleTopRightSegment g F R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R -
            zetaExplicitFormulaZeroPoleInnerRightEdge g R
      have hB : B₀ = B₁ :=
        congrArg
          (fun z : ℂ =>
            zetaExplicitFormulaZeroPoleOuterBottomEdge g F T -
              z +
              zetaExplicitFormulaZeroPoleRightBottomSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R)
          hbottom
      have hU : U₀ = U₁ :=
        congrArg
          (fun z : ℂ =>
            z -
              zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
              zetaExplicitFormulaZeroPoleRightTopSegment g F T R -
              zetaExplicitFormulaZeroPoleLeftTopSegment g F T R)
          htop
      have hBU : B₀ + U₀ = B₁ + U₁ :=
        congrArg₂ (fun a b : ℂ => a + b) hB hU
      exact congrArg (fun z : ℂ => z + L₀ + Q₀) hBU
    _ = zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R := by
      rfl

/-- Replacing the right and left outer vertical edges in the named zero-pole
exposed boundary by their three-segment forms gives the vertical-split normal
form. -/
theorem zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary_eq_verticalSplit
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hright :
      zetaExplicitFormulaZeroPoleOuterRightEdge g F T =
        (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R)
    (hleft :
      zetaExplicitFormulaZeroPoleOuterLeftEdge g F T =
        (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) :
    zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R =
      zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R := by
  calc
    zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
          (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
          ((zetaExplicitFormulaZeroPoleOuterRightEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
            (zetaExplicitFormulaZeroPoleOuterLeftEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerLeftEdge g R)) := by
      rfl
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
          (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
          ((((zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
              zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
                zetaExplicitFormulaZeroPoleRightTopSegment g F T R) +
              -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
            (zetaExplicitFormulaZeroPoleOuterLeftEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerLeftEdge g R)) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
            (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            ((z + -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
              (zetaExplicitFormulaZeroPoleOuterLeftEdge g F T +
                -zetaExplicitFormulaZeroPoleInnerLeftEdge g R)))
        hright
    _ =
        (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
          (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
            -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
          ((((zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
              zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
                zetaExplicitFormulaZeroPoleRightTopSegment g F T R) +
              -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
            ((((zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
              zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
                zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) +
                -zetaExplicitFormulaZeroPoleInnerLeftEdge g R))) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaExplicitFormulaZeroPoleOuterBottomEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerBottomEdge g R) -
            (zetaExplicitFormulaZeroPoleOuterTopEdge g F T +
              -zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            ((((zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
                zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
                  zetaExplicitFormulaZeroPoleRightTopSegment g F T R) +
                -zetaExplicitFormulaZeroPoleInnerRightEdge g R) -
              (z + -zetaExplicitFormulaZeroPoleInnerLeftEdge g R)))
        hleft
    _ = zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R := by
      rfl

/-- The zero-pole square-punctured boundary equals the four-cell boundary once
the two puncture-height horizontal edges and the two outer vertical edges have
been split into their cell segments. -/
theorem zetaExplicitFormulaZeroPoleSquarePuncturedBoundary_eq_fourCellBoundary_of_edgeSplits
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) =
        (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
            zetaExplicitFormulaZeroPoleBottomRightSegment g F R)
    (htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            zetaExplicitFormulaZeroPoleTopRightSegment g F R)
    (hright :
      zetaExplicitFormulaZeroPoleOuterRightEdge g F T =
        (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R)
    (hleft :
      zetaExplicitFormulaZeroPoleOuterLeftEdge g F T =
        (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R := by
  have hsquare :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R :=
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral_eq_namedExposedEdges
      g F T R
  have hvertical :
      zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R =
        zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R :=
    zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary_eq_verticalSplit
      g F T R hright hleft
  have hfour :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R =
        zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R :=
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_namedSplitHorizontalEdges
      g F T R hbottom htop
  have halgebra :
      zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R =
        zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R :=
    zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary_eq_verticalSplitExposedBoundary
      g F T R
  calc
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        zetaExplicitFormulaZeroPoleNamedSquareExposedBoundary g F T R := hsquare
    _ = zetaExplicitFormulaZeroPoleNamedVerticalSplitExposedBoundary g F T R :=
      hvertical
    _ = zetaExplicitFormulaZeroPoleNamedFourCellSplitBoundary g F T R :=
      halgebra.symm
    _ = zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum g F T R :=
      hfour.symm

/-- Canonical zero-pole square-punctured boundary bookkeeping: the punctured
outer rectangle boundary is the four-cell boundary sum around the isolated
`s = 0` square. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_fourCellBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  let g : ℂ → ℂ :=
    fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z
  have hR_pos : 0 < R :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have hR_ne : R ≠ 0 :=
    ne_of_gt hR_pos
  have hnegR_ne : -R ≠ 0 := by
    intro hzero
    exact hR_ne (neg_eq_zero.mp hzero)
  have hright_re_ne : F.c ≠ 0 :=
    ne_of_gt F.c_pos
  have hleft_re_ne : 1 - F.c ≠ 0 :=
    ne_of_lt F.one_sub_c_neg
  have hbottom_left :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I)))
        volume (1 - F.c) (-R) := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) (1 - F.c) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x (-R) hnegR_ne)))
  have hbottom_inner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I)))
        volume (-R) R := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x (-R) hnegR_ne)))
  have hbottom_right :
      IntervalIntegrable
        (fun x : ℝ => g (x + (((-R : ℝ) : ℂ) * Complex.I)))
        volume R F.c := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control (-R) R F.c
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x (-R) hnegR_ne)))
  have htop_left :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume (1 - F.c) (-R) := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R (1 - F.c) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x R hR_ne)))
  have htop_inner :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume (-R) R := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x R hR_ne)))
  have htop_right :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I))
        volume R F.c := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_horizontal_intervalIntegrable_of_avoids_pole
        f h.phi_control R R F.c
        (fun z hz =>
          Exists.elim hz
            (fun x hx =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hx.2
                (zetaExplicitFormulaZeroPole_horizontalAffine_ne_zero_of_height_ne_zero
                  x R hR_ne)))
  have hright_bottom :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (-T) (-R) := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c (-T) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  F.c y hright_re_ne)))
  have hright_middle :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (-R) R := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  F.c y hright_re_ne)))
  have hright_top :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume R T := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control F.c R T
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  F.c y hright_re_ne)))
  have hleft_bottom :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (-T) (-R) := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) (-T) (-R)
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  (1 - F.c) y hleft_re_ne)))
  have hleft_middle :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (-R) R := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) (-R) R
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  (1 - F.c) y hleft_re_ne)))
  have hleft_top :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume R T := by
    unfold g
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel_vertical_intervalIntegrable_of_avoids_pole
        f h.phi_control (1 - F.c) R T
        (fun z hz =>
          Exists.elim hz
            (fun y hy =>
              Eq.subst
                (motive := fun w : ℂ => w ≠ 0)
                hy.2
                (zetaExplicitFormulaZeroPole_verticalAffine_ne_zero_of_re_ne_zero
                  (1 - F.c) y hleft_re_ne)))
  have hbottom :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + (((-R : ℝ) : ℂ) * Complex.I))) =
        (zetaExplicitFormulaZeroPoleBottomLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerBottomEdge g R) +
            zetaExplicitFormulaZeroPoleBottomRightSegment g F R :=
    zetaExplicitFormulaZeroPole_bottomPunctureHorizontal_full_eq_segments
      g F R hbottom_left hbottom_inner hbottom_right
  have htop :
      (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
        (zetaExplicitFormulaZeroPoleTopLeftSegment g F R +
          zetaExplicitFormulaZeroPoleInnerTopEdge g R) +
            zetaExplicitFormulaZeroPoleTopRightSegment g F R :=
    zetaExplicitFormulaZeroPole_topPunctureHorizontal_full_eq_segments
      g F R htop_left htop_inner htop_right
  have hright :
      zetaExplicitFormulaZeroPoleOuterRightEdge g F T =
        (zetaExplicitFormulaZeroPoleRightBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleRightMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleRightTopSegment g F T R :=
    zetaExplicitFormulaZeroPole_rightOuterVertical_full_eq_segments
      g F T R hright_bottom hright_middle hright_top
  have hleft :
      zetaExplicitFormulaZeroPoleOuterLeftEdge g F T =
        (zetaExplicitFormulaZeroPoleLeftBottomSegment g F T R +
          zetaExplicitFormulaZeroPoleLeftMiddleSegment g F R) +
            zetaExplicitFormulaZeroPoleLeftTopSegment g F T R :=
    zetaExplicitFormulaZeroPole_leftOuterVertical_full_eq_segments
      g F T R hleft_bottom hleft_middle hleft_top
  exact
    zetaExplicitFormulaZeroPoleSquarePuncturedBoundary_eq_fourCellBoundary_of_edgeSplits
      g F T R hbottom htop hright hleft

/-- Canonical zero-pole square-punctured Cauchy cancellation for the generic
zero-centered contour object. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  have hboundary :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_fourCellBoundary
      f F h T hT
  have hfour :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalFourCellBoundary_eq_zero_of_pos_height
      f F h T hT
  exact Eq.trans hboundary hfour

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

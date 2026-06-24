import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.OnePoleFourCellCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedBoundaryAlgebra

/-!
# Edge split lemmas for the one-pole square-punctured boundary

This file specializes the interval-splitting lemmas from the single-pole contour
owner to the four edges that occur when the outer rectangle is subdivided by the
inner square around `s = 1`.

The declarations here are deliberately small: each one states one edge
decomposition with the exact orientation used by the four-cell boundary sum.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The bottom puncture-height horizontal edge over the full rectangle is the
sum of its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_bottomPunctureHorizontal_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 - F.c) (1 - R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 - R) (1 + R))
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + (-R) * Complex.I)) volume (1 + R) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c, g (x + (-R) * Complex.I)) =
      ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (-R) * Complex.I)) +
        (∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I))) +
          (∫ x : ℝ in (1 + R)..F.c, g (x + (-R) * Complex.I)) :=
  (zetaExplicitFormulaOnePole_bottomPunctureHorizontal_threeSegments
    g F R hleft hinner hright).symm

/-- The top puncture-height horizontal edge over the full rectangle is the sum
of its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_topPunctureHorizontal_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (R : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 - F.c) (1 - R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 - R) (1 + R))
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + R * Complex.I)) volume (1 + R) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c, g (x + R * Complex.I)) =
      ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + R * Complex.I)) +
        (∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I))) +
          (∫ x : ℝ in (1 + R)..F.c, g (x + R * Complex.I)) :=
  (zetaExplicitFormulaOnePole_topPunctureHorizontal_threeSegments
    g F R hleft hinner hright).symm

/-- The right outer vertical edge is the sum of its bottom, middle, and top
segments in the one-pole four-cell subdivision. -/
theorem zetaExplicitFormulaOnePole_rightOuterVertical_full_eq_segments
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
    Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in -T..(-R), g (F.c + y * Complex.I)) +
          (∫ y : ℝ in -R..R, g (F.c + y * Complex.I))) +
            (∫ y : ℝ in R..T, g (F.c + y * Complex.I))) :=
  (zetaExplicitFormulaOnePole_rightOuterVertical_eq_threeSegments
    g F T R hbottom hmiddle htop).symm

/-- The left outer vertical edge is the sum of its bottom, middle, and top
segments in the one-pole four-cell subdivision. -/
theorem zetaExplicitFormulaOnePole_leftOuterVertical_full_eq_segments
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I)) volume R T) :
    Complex.I • (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in -T..(-R), g ((1 - F.c) + y * Complex.I)) +
          (∫ y : ℝ in -R..R, g ((1 - F.c) + y * Complex.I))) +
            (∫ y : ℝ in R..T, g ((1 - F.c) + y * Complex.I))) :=
  (zetaExplicitFormulaOnePole_leftOuterVertical_eq_threeSegments
    g F T R hbottom hmiddle htop).symm

/-- The bottom puncture-height horizontal edge at the canonical one-pole
puncture radius splits into its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_bottomPunctureHorizontal_full_eq_segments_canonicalRadius
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            g (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) :=
  zetaExplicitFormulaOnePole_bottomPunctureHorizontal_full_eq_segments
    g F (zetaExplicitFormulaOnePolePunctureRadius F T)
    hleft hinner hright

/-- The top puncture-height horizontal edge at the canonical one-pole puncture
radius splits into its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_topPunctureHorizontal_full_eq_segments_canonicalRadius
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            g (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) :=
  zetaExplicitFormulaOnePole_topPunctureHorizontal_full_eq_segments
    g F (zetaExplicitFormulaOnePolePunctureRadius F T)
    hleft hinner hright

/-- The right outer vertical edge at the canonical one-pole puncture radius
splits into its bottom, middle, and top pieces. -/
theorem zetaExplicitFormulaOnePole_rightOuterVertical_full_eq_segments_canonicalRadius
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g (F.c + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            g (F.c + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            g (F.c + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              g (F.c + y * Complex.I))) :=
  zetaExplicitFormulaOnePole_rightOuterVertical_full_eq_segments
    g F T (zetaExplicitFormulaOnePolePunctureRadius F T)
    hbottom hmiddle htop

/-- The left outer vertical edge at the canonical one-pole puncture radius
splits into its bottom, middle, and top pieces. -/
theorem zetaExplicitFormulaOnePole_leftOuterVertical_full_eq_segments_canonicalRadius
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g ((1 - F.c) + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I • (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            g ((1 - F.c) + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            g ((1 - F.c) + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              g ((1 - F.c) + y * Complex.I))) :=
  zetaExplicitFormulaOnePole_leftOuterVertical_full_eq_segments
    g F T (zetaExplicitFormulaOnePolePunctureRadius F T)
    hbottom hmiddle htop

/-- The bottom puncture-height horizontal edge for the isolated `s = 1`
correction kernel splits into its left, inner-square, and right pieces at the
canonical one-pole puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_bottomPunctureHorizontal_full_eq_segments_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (x + (-(zetaExplicitFormulaOnePolePunctureRadius F T)) * Complex.I)) :=
  zetaExplicitFormulaOnePole_bottomPunctureHorizontal_full_eq_segments_canonicalRadius
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    F T hleft hinner hright

/-- The top puncture-height horizontal edge for the isolated `s = 1`
correction kernel splits into its left, inner-square, and right pieces at the
canonical one-pole puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_topPunctureHorizontal_full_eq_segments_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (x + (zetaExplicitFormulaOnePolePunctureRadius F T) * Complex.I)) :=
  zetaExplicitFormulaOnePole_topPunctureHorizontal_full_eq_segments_canonicalRadius
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    F T hleft hinner hright

/-- The right outer vertical edge for the isolated `s = 1` correction kernel
splits into its bottom, middle, and top pieces at the canonical one-pole
puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_rightOuterVertical_full_eq_segments_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (F.c + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (F.c + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (F.c + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I •
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (F.c + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (F.c + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (F.c + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                (F.c + y * Complex.I))) :=
  zetaExplicitFormulaOnePole_rightOuterVertical_full_eq_segments_canonicalRadius
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    F T hbottom hmiddle htop

/-- The left outer vertical edge for the isolated `s = 1` correction kernel
splits into its bottom, middle, and top pieces at the canonical one-pole
puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_leftOuterVertical_full_eq_segments_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hbottom :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            ((1 - F.c) + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            ((1 - F.c) + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            ((1 - F.c) + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I •
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            ((1 - F.c) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              ((1 - F.c) + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              ((1 - F.c) + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                ((1 - F.c) + y * Complex.I))) :=
  zetaExplicitFormulaOnePole_leftOuterVertical_full_eq_segments_canonicalRadius
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    F T hbottom hmiddle htop

/-- The horizontal affine coordinate `x + y I` has imaginary part `y`. -/
theorem zetaExplicitFormulaOnePole_horizontalAffine_im
    (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by
  calc
    ((x : ℂ) + (y : ℂ) * Complex.I).im =
        (x : ℂ).im + ((y : ℂ) * Complex.I).im := by
      exact Complex.add_im (x : ℂ) ((y : ℂ) * Complex.I)
    _ = 0 + ((y : ℂ) * Complex.I).im := by
      exact congrArg
        (fun r : ℝ => r + ((y : ℂ) * Complex.I).im)
        (Complex.ofReal_im x)
    _ = 0 + (y : ℂ).re := by
      exact congrArg (fun r : ℝ => 0 + r) (Complex.mul_I_im (y : ℂ))
    _ = 0 + y := by
      exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re y)
    _ = y := by
      exact zero_add y

/-- A horizontal affine point at nonzero height is not the pole `1`. -/
theorem zetaExplicitFormulaOnePole_horizontalAffine_ne_one_of_height_ne_zero
    (x y : ℝ) (hy : y ≠ 0) :
    (x : ℂ) + (y : ℂ) * Complex.I ≠ 1 := by
  intro hpoint
  have him_eq :
      ((x : ℂ) + (y : ℂ) * Complex.I).im = (1 : ℂ).im :=
    congrArg Complex.im hpoint
  have hy_zero : y = 0 := by
    calc
      y = ((x : ℂ) + (y : ℂ) * Complex.I).im := by
        exact (zetaExplicitFormulaOnePole_horizontalAffine_im x y).symm
      _ = (1 : ℂ).im := him_eq
      _ = 0 := Complex.ofReal_im (1 : ℝ)
  exact hy hy_zero

/-- A horizontal affine point at nonzero height avoids the denominator
`z - 1`. -/
theorem zetaExplicitFormulaOnePole_horizontalAffine_sub_one_ne_zero_of_height_ne_zero
    (x y : ℝ) (hy : y ≠ 0) :
    ((x : ℂ) + (y : ℂ) * Complex.I) - 1 ≠ 0 :=
  sub_ne_zero.mpr
    (zetaExplicitFormulaOnePole_horizontalAffine_ne_one_of_height_ne_zero
      x y hy)

/-- The vertical affine coordinate `x + y I` has real part `x`. -/
theorem zetaExplicitFormulaOnePole_verticalAffine_re
    (x y : ℝ) :
    ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by
  calc
    ((x : ℂ) + (y : ℂ) * Complex.I).re =
        (x : ℂ).re + ((y : ℂ) * Complex.I).re := by
      exact Complex.add_re (x : ℂ) ((y : ℂ) * Complex.I)
    _ = x + ((y : ℂ) * Complex.I).re := by
      exact congrArg
        (fun r : ℝ => r + ((y : ℂ) * Complex.I).re)
        (Complex.ofReal_re x)
    _ = x + (-(y : ℂ).im) := by
      exact congrArg (fun r : ℝ => x + r) (Complex.mul_I_re (y : ℂ))
    _ = x + (-0) := by
      exact congrArg (fun r : ℝ => x + (-r)) (Complex.ofReal_im y)
    _ = x + 0 := by
      exact congrArg (fun r : ℝ => x + r) (neg_zero)
    _ = x := by
      exact add_zero x

/-- A vertical affine point with real part different from `1` is not the pole
`1`. -/
theorem zetaExplicitFormulaOnePole_verticalAffine_ne_one_of_re_ne_one
    (x y : ℝ) (hx : x ≠ 1) :
    (x : ℂ) + (y : ℂ) * Complex.I ≠ 1 := by
  intro hpoint
  have hre_eq :
      ((x : ℂ) + (y : ℂ) * Complex.I).re = (1 : ℂ).re :=
    congrArg Complex.re hpoint
  have hx_one : x = 1 := by
    calc
      x = ((x : ℂ) + (y : ℂ) * Complex.I).re := by
        exact (zetaExplicitFormulaOnePole_verticalAffine_re x y).symm
      _ = (1 : ℂ).re := hre_eq
      _ = 1 := Complex.ofReal_re (1 : ℝ)
  exact hx hx_one

/-- A vertical affine point whose real coordinate is not `1` avoids the
denominator `z - 1`. -/
theorem zetaExplicitFormulaOnePole_verticalAffine_sub_one_ne_zero_of_re_ne_one
    (x y : ℝ) (hx : x ≠ 1) :
    ((x : ℂ) + (y : ℂ) * Complex.I) - 1 ≠ 0 :=
  sub_ne_zero.mpr
    (zetaExplicitFormulaOnePole_verticalAffine_ne_one_of_re_ne_one
      x y hx)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

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
        (fun x : ℝ => g (x + (↑(-R) : ℂ) * Complex.I)) volume (1 - F.c) (1 - R))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ => g (x + (↑(-R) : ℂ) * Complex.I)) volume (1 - R) (1 + R))
    (hright :
      IntervalIntegrable
        (fun x : ℝ => g (x + (↑(-R) : ℂ) * Complex.I)) volume (1 + R) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c, g (x + (↑(-R) : ℂ) * Complex.I)) =
      ((∫ x : ℝ in (1 - F.c)..(1 - R), g (x + (↑(-R) : ℂ) * Complex.I)) +
        (∫ x : ℝ in (1 - R)..(1 + R), g (x + (↑(-R) : ℂ) * Complex.I))) +
          (∫ x : ℝ in (1 + R)..F.c, g (x + (↑(-R) : ℂ) * Complex.I)) :=
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
        (fun y : ℝ => g ((↑(1 - F.c) : ℂ) + y * Complex.I)) volume (-T) (-R))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g ((↑(1 - F.c) : ℂ) + y * Complex.I)) volume (-R) R)
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g ((↑(1 - F.c) : ℂ) + y * Complex.I)) volume R T) :
    Complex.I • (∫ y : ℝ in -T..T, g ((↑(1 - F.c) : ℂ) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in -T..(-R), g ((↑(1 - F.c) : ℂ) + y * Complex.I)) +
          (∫ y : ℝ in -R..R, g ((↑(1 - F.c) : ℂ) + y * Complex.I))) +
            (∫ y : ℝ in R..T, g ((↑(1 - F.c) : ℂ) + y * Complex.I))) :=
  (zetaExplicitFormulaOnePole_leftOuterVertical_eq_threeSegments
    g F T R hbottom hmiddle htop).symm

/-- The bottom puncture-height horizontal edge at the canonical one-pole
puncture radius splits into its left, inner-square, and right pieces. -/
theorem zetaExplicitFormulaOnePole_bottomPunctureHorizontal_full_eq_segments_canonicalRadius
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hleft :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            g (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) :=
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
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ => g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I • (∫ y : ℝ in -T..T, g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            g (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              g (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) :=
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
            (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume (1 - F.c) (1 - zetaExplicitFormulaOnePolePunctureRadius F T))
    (hinner :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)
          (1 + zetaExplicitFormulaOnePolePunctureRadius F T))
    (hright :
      IntervalIntegrable
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))
        volume (1 + zetaExplicitFormulaOnePolePunctureRadius F T) F.c) :
    (∫ x : ℝ in (1 - F.c)..F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) =
      ((∫ x : ℝ in
          (1 - F.c)..(1 - zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) +
        (∫ x : ℝ in
          (1 - zetaExplicitFormulaOnePolePunctureRadius F T)..
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T),
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I))) +
          (∫ x : ℝ in
            (1 + zetaExplicitFormulaOnePolePunctureRadius F T)..F.c,
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (x + ((-(zetaExplicitFormulaOnePolePunctureRadius F T) : ℝ) : ℂ) * Complex.I)) :=
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
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (-T) (-(zetaExplicitFormulaOnePolePunctureRadius F T)))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume
          (-(zetaExplicitFormulaOnePolePunctureRadius F T))
          (zetaExplicitFormulaOnePolePunctureRadius F T))
    (htop :
      IntervalIntegrable
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
        volume (zetaExplicitFormulaOnePolePunctureRadius F T) T) :
    Complex.I •
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) =
      Complex.I •
        (((∫ y : ℝ in
            -T..(-(zetaExplicitFormulaOnePolePunctureRadius F T)),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) +
          (∫ y : ℝ in
            (-(zetaExplicitFormulaOnePolePunctureRadius F T))..
              (zetaExplicitFormulaOnePolePunctureRadius F T),
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) +
            (∫ y : ℝ in
              (zetaExplicitFormulaOnePolePunctureRadius F T)..T,
              zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
                (((1 - F.c : ℝ) : ℂ) + y * Complex.I))) :=
  zetaExplicitFormulaOnePole_leftOuterVertical_full_eq_segments_canonicalRadius
    (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
    F T hbottom hmiddle htop

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

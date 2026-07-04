import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleContourPrimitives

/-!
# Zero-pole four-cell contour primitives

This file owns the zero-centered analogue of the one-pole finite four-cell
contour geometry.  The Cauchy engine itself lives in the generic single-pole
contour owner; this file only supplies the `s = 0` subdivision objects and the
coordinate lemmas needed to feed that engine.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Standard boundary of the zero-centered inner square with half-width `R`. -/
noncomputable def zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral
    (g : ℂ → ℂ) (R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
    g (-R) R (-R) R

/-- The outer rectangle boundary for the zero-pole contour family, in the
standard rectangle convention. -/
noncomputable def zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
    g (1 - F.c) F.c (-T) T

/-- The bottom cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `0`. -/
noncomputable def zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + (-T) * Complex.I) (F.c + (-R) * Complex.I)

/-- The top cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `0`. -/
noncomputable def zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + R * Complex.I) (F.c + T * Complex.I)

/-- The left cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `0`. -/
noncomputable def zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g ((1 - F.c) + (-R) * Complex.I) ((-R) + R * Complex.I)

/-- The right cell in the four-rectangle decomposition of the rectangle
punctured by the inner square around `0`. -/
noncomputable def zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaSinglePoleSubdivisionCellBoundaryIntegral
    g (R + (-R) * Complex.I) (F.c + R * Complex.I)

/-- The finite four-cell boundary sum for the rectangle with the zero-pole
inner square removed. -/
noncomputable def zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral g F T R +
    zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
      zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
        zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R

/-- The finite square-punctured rectangle boundary: outer standard boundary
minus the zero-centered inner square boundary. -/
noncomputable def zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) : ℂ :=
  zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T -
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R

/-- The named zero-pole inner square boundary unfolds to the standard rectangle
coordinate convention. -/
theorem zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral_eq
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
        g (-R) R (-R) R :=
  rfl

/-- The named zero-pole outer boundary unfolds to the standard rectangle
coordinate convention. -/
theorem zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T =
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
        g (1 - F.c) F.c (-T) T :=
  rfl

/-- The named finite zero-pole square-punctured rectangle boundary unfolds to
outer-minus-inner. -/
theorem zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral_eq
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T -
        zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R :=
  rfl

/-- A complex point with negative imaginary coordinate is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_ne_zero_of_im_lt_zero
    {z : ℂ} (hz : z.im < 0) :
    z ≠ 0 := by
  intro hzero
  have him_eq : z.im = (0 : ℂ).im :=
    congrArg Complex.im hzero
  have him_zero : z.im = 0 := by
    calc
      z.im = (0 : ℂ).im := him_eq
      _ = 0 := Complex.zero_im
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun y : ℝ => y < 0) him_zero hz)

/-- A complex point with positive imaginary coordinate is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_ne_zero_of_zero_lt_im
    {z : ℂ} (hz : 0 < z.im) :
    z ≠ 0 := by
  intro hzero
  have him_eq : z.im = (0 : ℂ).im :=
    congrArg Complex.im hzero
  have him_zero : z.im = 0 := by
    calc
      z.im = (0 : ℂ).im := him_eq
      _ = 0 := Complex.zero_im
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun y : ℝ => 0 < y) him_zero hz)

/-- A complex point with negative real coordinate is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_ne_zero_of_re_lt_zero
    {z : ℂ} (hz : z.re < 0) :
    z ≠ 0 := by
  intro hzero
  have hre_eq : z.re = (0 : ℂ).re :=
    congrArg Complex.re hzero
  have hre_zero : z.re = 0 := by
    calc
      z.re = (0 : ℂ).re := hre_eq
      _ = 0 := Complex.zero_re
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun x : ℝ => x < 0) hre_zero hz)

/-- A complex point with positive real coordinate is not the zero pole. -/
theorem zetaExplicitFormulaZeroPole_ne_zero_of_zero_lt_re
    {z : ℂ} (hz : 0 < z.re) :
    z ≠ 0 := by
  intro hzero
  have hre_eq : z.re = (0 : ℂ).re :=
    congrArg Complex.re hzero
  have hre_zero : z.re = 0 := by
    calc
      z.re = (0 : ℂ).re := hre_eq
      _ = 0 := Complex.zero_re
  exact (lt_irrefl (0 : ℝ)) (Eq.subst (motive := fun x : ℝ => 0 < x) hre_zero hz)

/-- The lower canonical zero-pole four-cell lies strictly below the real axis,
hence avoids the isolated pole `0`. -/
theorem zetaExplicitFormulaZeroPole_canonicalBottomCell_avoids_zero_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          ([[ ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).re,
               (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                  Complex.I).re ]] ×ℂ
            [[ ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im,
               (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                  Complex.I).im ]]) →
        z ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have hbottom_left :
      ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im < 0 := by
    calc
      ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im = -T :=
        zetaExplicitFormulaOnePole_horizontalAffine_im (1 - F.c) (-T)
      _ < 0 := neg_lt_zero.mpr hT
  have hbottom_right :
      (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
          Complex.I).im < 0 := by
    calc
      (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
          Complex.I).im =
          -(zetaExplicitFormulaZeroPolePunctureRadius F T) :=
        zetaExplicitFormulaOnePole_horizontalAffine_im
          F.c (-(zetaExplicitFormulaZeroPolePunctureRadius F T))
      _ < 0 := neg_lt_zero.mpr hR_pos
  have him_mem :
      z.im ∈
        [[ ((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im,
           (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
              Complex.I).im ]] :=
    (Complex.mem_reProdIm.mp hz).2
  have him_sup_lt :
      (((1 - F.c : ℝ) + (-T : ℝ) * Complex.I).im ⊔
        (F.c + (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
          Complex.I).im) < 0 :=
    sup_lt_iff.mpr (And.intro hbottom_left hbottom_right)
  have him_lt_zero : z.im < 0 :=
    lt_of_le_of_lt him_mem.2 him_sup_lt
  exact zetaExplicitFormulaZeroPole_ne_zero_of_im_lt_zero him_lt_zero

/-- The upper canonical zero-pole four-cell lies strictly above the real axis,
hence avoids the isolated pole `0`. -/
theorem zetaExplicitFormulaZeroPole_canonicalTopCell_avoids_zero_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          ([[ ((1 - F.c : ℝ) +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).re,
               (F.c + T * Complex.I).re ]] ×ℂ
            [[ ((1 - F.c : ℝ) +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).im,
               (F.c + T * Complex.I).im ]]) →
        z ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have htop_left :
      ((1 - F.c : ℝ) +
          (zetaExplicitFormulaZeroPolePunctureRadius F T) * Complex.I).im > 0 := by
    calc
      ((1 - F.c : ℝ) +
          (zetaExplicitFormulaZeroPolePunctureRadius F T) * Complex.I).im =
          zetaExplicitFormulaZeroPolePunctureRadius F T :=
        zetaExplicitFormulaOnePole_horizontalAffine_im
          (1 - F.c) (zetaExplicitFormulaZeroPolePunctureRadius F T)
      _ > 0 := hR_pos
  have htop_right :
      (F.c + T * Complex.I).im > 0 := by
    calc
      (F.c + T * Complex.I).im = T :=
        zetaExplicitFormulaOnePole_horizontalAffine_im F.c T
      _ > 0 := hT
  have him_mem :
      z.im ∈
        [[ ((1 - F.c : ℝ) +
              (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                Complex.I).im,
           (F.c + T * Complex.I).im ]] :=
    (Complex.mem_reProdIm.mp hz).2
  have him_inf_pos :
      0 <
        (((1 - F.c : ℝ) +
              (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                Complex.I).im ⊓
          (F.c + T * Complex.I).im) :=
    lt_inf_iff.mpr (And.intro htop_left htop_right)
  have him_pos : 0 < z.im :=
    lt_of_lt_of_le him_inf_pos him_mem.1
  exact zetaExplicitFormulaZeroPole_ne_zero_of_zero_lt_im him_pos

/-- The left canonical zero-pole four-cell lies strictly to the left of the
pole's real coordinate. -/
theorem zetaExplicitFormulaZeroPole_canonicalLeftCell_avoids_zero_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          ([[ ((1 - F.c : ℝ) +
                  (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                    Complex.I).re,
               ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).re ]] ×ℂ
            [[ ((1 - F.c : ℝ) +
                  (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                    Complex.I).im,
               ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).im ]]) →
        z ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have hleft_lower :
      ((1 - F.c : ℝ) +
          (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
            Complex.I).re < 0 := by
    calc
      ((1 - F.c : ℝ) +
          (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
            Complex.I).re = 1 - F.c :=
        zetaExplicitFormulaOnePole_verticalAffine_re
          (1 - F.c) (-(zetaExplicitFormulaZeroPolePunctureRadius F T))
      _ < 0 := F.one_sub_c_neg
  have hleft_upper :
      ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
          (zetaExplicitFormulaZeroPolePunctureRadius F T) *
            Complex.I).re < 0 := by
    calc
      ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
          (zetaExplicitFormulaZeroPolePunctureRadius F T) *
            Complex.I).re =
          -zetaExplicitFormulaZeroPolePunctureRadius F T :=
        zetaExplicitFormulaOnePole_verticalAffine_re
          (-zetaExplicitFormulaZeroPolePunctureRadius F T)
          (zetaExplicitFormulaZeroPolePunctureRadius F T)
      _ < 0 := neg_lt_zero.mpr hR_pos
  have hre_mem :
      z.re ∈
        [[ ((1 - F.c : ℝ) +
              (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                Complex.I).re,
           ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
              (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                Complex.I).re ]] :=
    (Complex.mem_reProdIm.mp hz).1
  have hre_sup_lt :
      (((1 - F.c : ℝ) +
          (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
            Complex.I).re ⊔
        ((-zetaExplicitFormulaZeroPolePunctureRadius F T) +
          (zetaExplicitFormulaZeroPolePunctureRadius F T) *
            Complex.I).re) < 0 :=
    sup_lt_iff.mpr (And.intro hleft_lower hleft_upper)
  have hre_lt_zero : z.re < 0 :=
    lt_of_le_of_lt hre_mem.2 hre_sup_lt
  exact zetaExplicitFormulaZeroPole_ne_zero_of_re_lt_zero hre_lt_zero

/-- The right canonical zero-pole four-cell lies strictly to the right of the
pole's real coordinate. -/
theorem zetaExplicitFormulaZeroPole_canonicalRightCell_avoids_zero_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    ∀ z : ℂ,
      z ∈
          ([[ (zetaExplicitFormulaZeroPolePunctureRadius F T +
                  (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                    Complex.I).re,
               (F.c +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).re ]] ×ℂ
            [[ (zetaExplicitFormulaZeroPolePunctureRadius F T +
                  (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                    Complex.I).im,
               (F.c +
                  (zetaExplicitFormulaZeroPolePunctureRadius F T) *
                    Complex.I).im ]]) →
        z ≠ 0 := by
  intro z hz
  have hR_pos :
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T :=
    zetaExplicitFormulaZeroPolePunctureRadius_pos F hT
  have hright_lower :
      0 <
        (zetaExplicitFormulaZeroPolePunctureRadius F T +
          (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
            Complex.I).re := by
    calc
      0 < zetaExplicitFormulaZeroPolePunctureRadius F T := hR_pos
      _ =
          (zetaExplicitFormulaZeroPolePunctureRadius F T +
            (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
              Complex.I).re := by
        exact
          (zetaExplicitFormulaOnePole_verticalAffine_re
            (zetaExplicitFormulaZeroPolePunctureRadius F T)
            (-(zetaExplicitFormulaZeroPolePunctureRadius F T))).symm
  have hright_upper :
      0 <
        (F.c + (zetaExplicitFormulaZeroPolePunctureRadius F T) *
          Complex.I).re := by
    calc
      0 < F.c := F.c_pos
      _ =
          (F.c + (zetaExplicitFormulaZeroPolePunctureRadius F T) *
            Complex.I).re := by
        exact
          (zetaExplicitFormulaOnePole_verticalAffine_re
            F.c (zetaExplicitFormulaZeroPolePunctureRadius F T)).symm
  have hre_mem :
      z.re ∈
        [[ (zetaExplicitFormulaZeroPolePunctureRadius F T +
              (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
                Complex.I).re,
           (F.c + (zetaExplicitFormulaZeroPolePunctureRadius F T) *
              Complex.I).re ]] :=
    (Complex.mem_reProdIm.mp hz).1
  have hre_inf_gt :
      0 <
        ((zetaExplicitFormulaZeroPolePunctureRadius F T +
            (-zetaExplicitFormulaZeroPolePunctureRadius F T : ℝ) *
              Complex.I).re ⊓
          (F.c + (zetaExplicitFormulaZeroPolePunctureRadius F T) *
            Complex.I).re) :=
    lt_inf_iff.mpr (And.intro hright_lower hright_upper)
  have hzero_lt_re : 0 < z.re :=
    lt_of_lt_of_le hre_inf_gt hre_mem.1
  exact zetaExplicitFormulaZeroPole_ne_zero_of_zero_lt_re hzero_lt_re

/-- The zero-pole four-cell boundary sum vanishes once each of its four cell
boundaries vanishes. -/
theorem zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cells
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hbottom :
      zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral
        g F T R = 0)
    (htop :
      zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
        g F T R = 0)
    (hleft :
      zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
        g F T R = 0)
    (hright :
      zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
        g F T R = 0) :
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
      g F T R = 0 := by
  calc
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        g F T R =
        zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral g F T R +
          zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      rfl
    _ = 0 +
          zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact congrArg
        (fun z : ℂ =>
          z +
            zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
                zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
        hbottom
    _ =
          zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact
        Eq.trans
          (congrArg
            (fun z : ℂ =>
              z + zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
            (add_assoc
              (0 : ℂ)
              (zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R)
              (zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R)))
          (congrArg
            (fun z : ℂ =>
              z + zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
            (zero_add
              (zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral g F T R +
                zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R)))
    _ = 0 +
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact congrArg
        (fun z : ℂ =>
          z +
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
        htop
    _ =
            zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact
        Eq.trans
          (add_assoc
            (0 : ℂ)
            (zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R)
            (zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R))
          (zero_add
            (zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral g F T R +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R))
    _ = 0 +
              zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact congrArg
        (fun z : ℂ =>
          z + zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
        hleft
    _ = zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R := by
      exact zero_add
        (zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral g F T R)
    _ = 0 := hright

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

import Boundary.LFunctions.ZetaExplicitFormulaRectangleAPI
import Boundary.LFunctions.ZetaExplicitFormulaContourPaths
import Boundary.LFunctions.ZetaExplicitFormulaContourPathLemmas
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl
import Mathlib.Topology.Basic

/-!
# Boundary explicit-formula geometry

This file owns the contour-path, boundary-side, and contour-integral vocabulary
for the explicit-formula argument. The rectangle type itself lives in the
standalone rectangle API file; the analytic estimates and package wrappers live
elsewhere.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real number `1 / 2` is positive. -/
theorem real_half_pos_for_contourGeometry : (0 : ℝ) < 1 / 2 :=
  one_div_pos.mpr zero_lt_two

/-- Data describing the completed explicit-formula contour problem. -/
structure ExplicitFormulaContourData where
  rectangle : ExplicitFormulaRectangle
  c_gt_half : (1 / 2 : ℝ) < rectangle.c
  T_pos : 0 < rectangle.T

/-- A contour family indexed by the height parameter `T`. -/
structure ExplicitFormulaContourFamily where
  c : ℝ
  c_gt_half : (1 / 2 : ℝ) < c

/-- The contour rectangle at height `T` in a contour family. -/
def ExplicitFormulaContourFamily.rectangle (F : ExplicitFormulaContourFamily) (T : ℝ) :
    ExplicitFormulaRectangle :=
  ⟨F.c, T⟩

/-- A contour-family real edge strictly to the right of `1 / 2` is positive. -/
theorem ExplicitFormulaContourFamily.c_pos
    (F : ExplicitFormulaContourFamily) :
    0 < F.c :=
  lt_trans real_half_pos_for_contourGeometry F.c_gt_half

/-- The rectangle attached to a contour family has real edge `F.c`. -/
theorem ExplicitFormulaContourFamily.rectangle_c
    (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (F.rectangle T).c = F.c :=
  Eq.refl _

/-- Positivity transports across the right-path real-coordinate identity. -/
theorem rightPath_re_pos_of_family_re
    (F : ExplicitFormulaContourFamily) (t : ℝ)
    (hcr : (zetaCompletedExplicitFormulaRightPath (F.rectangle t) t).re = F.c) :
    0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle t) t).re :=
  hcr.symm ▸ F.c_pos

/-- The contour family exposes the right-edge positivity at every height. -/
theorem ExplicitFormulaContourFamily.rightPath_re
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    (zetaCompletedExplicitFormulaRightPath (F.rectangle t) t).re = F.c := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaRightPath_re (F.rectangle t) t)
      (F.rectangle_c t)

/-- The contour family exposes the right-edge positivity at every height. -/
theorem ExplicitFormulaContourFamily.rightPath_re_pos
    (F : ExplicitFormulaContourFamily) (t : ℝ) :
    0 < (zetaCompletedExplicitFormulaRightPath (F.rectangle t) t).re := by
  exact rightPath_re_pos_of_family_re F t (F.rightPath_re t)

/-- The contour family exposes the top strip bound at every height. -/
theorem ExplicitFormulaContourFamily.topPath_strip
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    F.c ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).re ∧
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x).re ≤ 1 - F.c := by
  exact zetaCompletedExplicitFormulaTopPath_strip (F.rectangle T) x hx1 hx2

/-- The contour family exposes the bottom strip bound at every height. -/
theorem ExplicitFormulaContourFamily.bottomPath_strip
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    F.c ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).re ∧
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x).re ≤ 1 - F.c := by
  exact zetaCompletedExplicitFormulaBottomPath_strip (F.rectangle T) x hx1 hx2

/-- Data describing a zero of the completed zeta function with multiplicity. -/
structure ExplicitFormulaZeroData where
  zero : ℂ
  multiplicity : ℕ

/-- The residue contribution of a single zero. -/
def explicitFormulaZeroResidue
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) : ℂ :=
  - (ρ.multiplicity : ℂ) * zetaCompletedExplicitFormulaPhi f (ρ.zero - 1 / 2)

/-- The residue contribution unfolds definitionally. -/
theorem explicitFormulaZeroResidue_def
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) :
    explicitFormulaZeroResidue f ρ =
      - (ρ.multiplicity : ℂ) * zetaCompletedExplicitFormulaPhi f (ρ.zero - 1 / 2) :=
  rfl

/-- The contour-side residue sum over a finite family of zeros. -/
def explicitFormulaResidueSum (f : ZetaAdmissibleFunction) :
    List ExplicitFormulaZeroData → ℂ
  | [] => 0
  | ρ :: S => explicitFormulaResidueSum f S + explicitFormulaZeroResidue f ρ

/-- The residue sum of the empty list is zero. -/
theorem explicitFormulaResidueSum_nil (f : ZetaAdmissibleFunction) :
    explicitFormulaResidueSum f [] = 0 :=
  rfl

/-- The residue sum unfolds over `cons`. -/
theorem explicitFormulaResidueSum_cons
    (f : ZetaAdmissibleFunction) (ρ : ExplicitFormulaZeroData) (S : List ExplicitFormulaZeroData) :
    explicitFormulaResidueSum f (ρ :: S) =
      (explicitFormulaResidueSum f S) + explicitFormulaZeroResidue f ρ := by
  show explicitFormulaResidueSum f S + explicitFormulaZeroResidue f ρ =
    explicitFormulaResidueSum f S + explicitFormulaZeroResidue f ρ
  exact Eq.refl _

/-- The boundary sum on the explicit-formula side, as a named object. -/
def zetaCompletedExplicitFormulaBoundaryPieces
    (f : ZetaAdmissibleFunction) :
    ℂ × ℂ × ℂ :=
  (zetaCompletedExplicitFormulaPrimeContribution f,
    zetaCompletedExplicitFormulaArchimedeanContribution f,
    zetaCompletedExplicitFormulaCorrectionContribution f)

/-- The combined boundary sum assembled from the three explicit pieces. -/
def zetaCompletedExplicitFormulaBoundarySumAnalytic
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The combined boundary sum is the analytic boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f :=
  rfl

/-- The right-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaRightLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ t in Set.Icc (-r.T) r.T,
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightPath r t) *
      zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightPath r t - 1 / 2)

/-- User-facing name for the right vertical integral. -/
abbrev zetaVerticalIntegralRight
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r

/-- The left-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaLeftLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ t in Set.Icc (-r.T) r.T,
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftPath r t) *
      zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaLeftPath r t - 1 / 2)

/-- User-facing name for the left vertical integral. -/
abbrev zetaVerticalIntegralLeft
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaLeftLineIntegral f r

/-- The top-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaTopLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ x in Set.uIcc r.c (1 - r.c),
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaTopPath r x) *
      zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaTopPath r x - 1 / 2)

/-- User-facing name for the top horizontal integral. -/
abbrev zetaHorizontalIntegralTop
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f r

/-- The bottom-side line integral of the contour integrand. -/
noncomputable def zetaCompletedExplicitFormulaBottomLineIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  ∫ x in Set.uIcc r.c (1 - r.c),
    completedZetaNegLogDeriv (zetaCompletedExplicitFormulaBottomPath r x) *
      zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaBottomPath r x - 1 / 2)

/-- User-facing name for the bottom horizontal integral. -/
abbrev zetaHorizontalIntegralBottom
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral f r

/-- The contour integral around the rectangle. -/
noncomputable def zetaCompletedExplicitFormulaContourIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r +
    zetaCompletedExplicitFormulaTopLineIntegral f r -
    zetaCompletedExplicitFormulaBottomLineIntegral f r

/-- User-facing name for the rectangle boundary integral. -/
abbrev zetaRectangleBoundaryIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : ℂ :=
  zetaCompletedExplicitFormulaContourIntegral f r

/-- The horizontal-side decay target for the contour argument. -/
def explicitFormulaHorizontalDecayTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  Tendsto
    (fun _T : ℝ => zetaCompletedExplicitFormulaTopLineIntegral f r -
      zetaCompletedExplicitFormulaBottomLineIntegral f r)
    atTop
    (𝓝 0)

/-- The horizontal-side decay target indexed by a contour family. -/
def explicitFormulaHorizontalDecayTargetFamily
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
    atTop
    (𝓝 0)

/-- The vertical-side decomposition target for the contour argument. -/
def explicitFormulaVerticalDecompositionTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedExplicitFormulaRightLineIntegral f r -
    zetaCompletedExplicitFormulaLeftLineIntegral f r =
    zetaCompletedExplicitFormulaBoundarySumAnalytic f

/-- The residue-theorem target for the explicit formula. -/
def explicitFormulaResidueTheoremTarget
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  zetaCompletedExplicitFormulaContourIntegral f r =
    explicitFormulaResidueSum f []

/-- The main residue-formula proposition in the analytic note's normalization. -/
def completedZeta_rectangleResidueFormula
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r =
    - explicitFormulaResidueSum f []

/-- The equivalent zero-sum proposition solving for the residue sum. -/
def zetaZeroSumInRectangle_eq_neg_boundaryIntegral
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  explicitFormulaResidueSum f [] =
    - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r

/-- The horizontal-vanishing proposition in note form, indexed by the contour family. -/
def zetaHorizontalIntegrals_vanish
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
    atTop
    (𝓝 0)

/-- The residue theorem target for the explicit formula. -/
def explicitFormulaResidueTheoremStatement
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle)
    (S : List ExplicitFormulaZeroData) : Prop :=
  zetaCompletedExplicitFormulaContourIntegral f r =
    explicitFormulaResidueSum f S

/-- The horizontal decay target for the explicit formula. -/
def explicitFormulaHorizontalDecayStatement
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) : Prop :=
  Tendsto
    (fun _T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r)
    atTop
    (𝓝 0)

/-- The family-indexed horizontal decay statement. -/
def explicitFormulaHorizontalDecayStatementFamily
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) : Prop :=
  Tendsto
    (fun T : ℝ =>
      zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
    atTop
    (𝓝 0)

/-- The right vertical integral is the right line integral. -/
theorem zetaVerticalIntegralRight_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralRight f r = zetaCompletedExplicitFormulaRightLineIntegral f r :=
  rfl

/-- The left vertical integral is the left line integral. -/
theorem zetaVerticalIntegralLeft_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralLeft f r = zetaCompletedExplicitFormulaLeftLineIntegral f r :=
  rfl

/-- The top horizontal integral is the top line integral. -/
theorem zetaHorizontalIntegralTop_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralTop f r = zetaCompletedExplicitFormulaTopLineIntegral f r :=
  rfl

/-- The bottom horizontal integral is the bottom line integral. -/
theorem zetaHorizontalIntegralBottom_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralBottom f r = zetaCompletedExplicitFormulaBottomLineIntegral f r :=
  rfl

/-- The rectangle boundary integral is the contour integral. -/
theorem zetaRectangleBoundaryIntegral_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaRectangleBoundaryIntegral f r = zetaCompletedExplicitFormulaContourIntegral f r :=
  rfl

/-- The contour integral is the signed sum of the four side integrals. -/
theorem zetaCompletedExplicitFormulaContourIntegral_eq
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral f r =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r +
        zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r :=
  rfl

/-- The rectangle boundary integral is the signed sum of the four side integrals. -/
theorem zetaRectangleBoundaryIntegral_eq_fourSides
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaRectangleBoundaryIntegral f r =
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r +
        zetaCompletedExplicitFormulaTopLineIntegral f r -
        zetaCompletedExplicitFormulaBottomLineIntegral f r :=
  rfl

/-- The right vertical integral is the right side line integral. -/
theorem zetaVerticalIntegralRight_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralRight f r = zetaCompletedExplicitFormulaRightLineIntegral f r :=
  rfl

/-- The left vertical integral is the left side line integral. -/
theorem zetaVerticalIntegralLeft_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaVerticalIntegralLeft f r = zetaCompletedExplicitFormulaLeftLineIntegral f r :=
  rfl

/-- The vertical decomposition target unfolds to the boundary-side identity. -/
theorem explicitFormulaVerticalDecompositionTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaVerticalDecompositionTarget f r ↔
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  show
    (zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f) ↔
      zetaCompletedExplicitFormulaRightLineIntegral f r -
        zetaCompletedExplicitFormulaLeftLineIntegral f r =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f
  exact Iff.rfl

/-- The residue theorem target unfolds to the contour-integral identity. -/
theorem explicitFormulaResidueTheoremTarget_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    explicitFormulaResidueTheoremTarget f r ↔
      zetaCompletedExplicitFormulaContourIntegral f r =
        explicitFormulaResidueSum f [] := by
  show
    (zetaCompletedExplicitFormulaContourIntegral f r =
      explicitFormulaResidueSum f []) ↔
      zetaCompletedExplicitFormulaContourIntegral f r =
        explicitFormulaResidueSum f []
  exact Iff.rfl

/-- The zero-sum proposition is the same statement solved for the sum. -/
theorem zetaZeroSumInRectangle_eq_neg_boundaryIntegral_iff
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaZeroSumInRectangle_eq_neg_boundaryIntegral f r ↔
      explicitFormulaResidueSum f [] =
        - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r := by
  show
    (explicitFormulaResidueSum f [] =
      - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r) ↔
      explicitFormulaResidueSum f [] =
        - (1 / (2 * Real.pi * Complex.I)) * zetaRectangleBoundaryIntegral f r
  exact Iff.rfl

/-- The family-indexed horizontal decay statement is the same limit. -/
theorem explicitFormulaHorizontalDecayStatementFamily_iff
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) :
    explicitFormulaHorizontalDecayStatementFamily f F ↔
      Tendsto
        (fun T : ℝ =>
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
        atTop
        (𝓝 0) := by
  show
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 0) ↔
    Tendsto
      (fun T : ℝ =>
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      atTop
      (𝓝 0)
  exact Iff.rfl

/-- The top horizontal integral is the top side line integral. -/
theorem zetaHorizontalIntegralTop_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralTop f r = zetaCompletedExplicitFormulaTopLineIntegral f r :=
  rfl

/-- The bottom horizontal integral is the bottom side line integral. -/
theorem zetaHorizontalIntegralBottom_eq_contour
    (f : ZetaAdmissibleFunction) (r : ExplicitFormulaRectangle) :
    zetaHorizontalIntegralBottom f r = zetaCompletedExplicitFormulaBottomLineIntegral f r :=
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

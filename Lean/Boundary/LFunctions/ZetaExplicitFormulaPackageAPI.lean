import Mathlib.MeasureTheory.Integral.IntegrableOn
import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
import Boundary.LFunctions.ZetaExplicitFormulaFinalTarget
import Boundary.LFunctions.ZetaExplicitFormulaPuncturedPlane
import Boundary.LFunctions.ZetaPacketComparison

/-!
# Boundary explicit-formula package API

This file owns the package/wrapper layer for the explicit-formula contour
argument. The analytic core stays in `ZetaExplicitFormulaComplexAnalysis`; this
file only republishes those owner results through package records and
convenience theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The analytic package exposes the transform control. -/
def ExplicitFormulaAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The analytic package exposes the log-derivative control. -/
def ExplicitFormulaAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The analytic package exposes fixed-degree zero-excised polynomial growth for the
completed negative log derivative. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact h.logderiv_control.zeroExcisedPolynomialGrowth a b E

/-- The analytic package exposes zero-excised polynomial strip growth for the completed
negative log derivative. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_zeroExcisedStripBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.logderiv_control.zeroExcisedStripBound a b E N

/-- The package-level completed negative log derivative has zero-excised polynomial
strip growth. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_zeroExcisedStripBound_exists
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.completedZetaNegLogDeriv_zeroExcisedStripBound a b E N

/-- The package-level completed negative log derivative has zero-excised polynomial
strip growth. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_zeroExcisedStripBound_sigma
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.completedZetaNegLogDeriv_zeroExcisedStripBound_exists a b E N

/-- The analytic package exposes the zeta-side logarithmic derivative with its Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_eq_zetaSide_add_invGammaCorrection
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    completedZetaNegLogDeriv s =
      zetaSideNegLogDeriv s +
        deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
  exact
    sub_eq_iff_eq_add.mp
      (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction hs0 hs1 hΛ hΓ).symm

/-- The analytic package exposes the zeta-side factorized contour integrand with Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_eq_factorized
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f hs0 hs1 hΛ hΓ

/-- The analytic package exposes the negative-log-derivative form of the contour integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_eq_neg_logDeriv
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (- logDeriv completedRiemannZeta s) * zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_eq_neg_logDeriv f s

/-- The analytic package exposes the contour data. -/
def ExplicitFormulaAnalyticPackage.contourData
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ExplicitFormulaContourData := by
  exact h.contour_data

/-- The family-level package exposes the transform control. -/
def ExplicitFormulaFamilyAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The family-level package exposes the log-derivative control. -/
def ExplicitFormulaFamilyAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The family-level package exposes fixed-degree zero-excised polynomial growth for the
completed negative log derivative. -/
theorem ExplicitFormulaFamilyAnalyticPackage.completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact h.logderiv_control.zeroExcisedPolynomialGrowth a b E

/-- The analytic package induces the family package for every contour family. -/
def ExplicitFormulaAnalyticPackage.toFamilyPackage
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) :
    ExplicitFormulaFamilyAnalyticPackage f F := by
  exact { phi_control := h.phi_control, logderiv_control := h.logderiv_control }

/-- The analytic package exposes the residue-theorem target once the residue identity itself is
available. -/
theorem ExplicitFormulaAnalyticPackage.residueTheoremTarget
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (hres :
      zetaCompletedExplicitFormulaContourIntegral f h.contour_data.rectangle =
        explicitFormulaResidueSum f []) :
    explicitFormulaResidueTheoremTarget f h.contour_data.rectangle :=
  hres

/-- The contour-data owner object exposes the edge continuity statements for the contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_continuousAt_rightPath
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_rightPath
    (r := h.contour_data.rectangle) t hZ hΦ

/-- The contour-data owner object exposes the left-edge continuity statement for the contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_continuousAt_leftPath
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (t : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_leftPath
    (r := h.contour_data.rectangle) t hZ hΦ

/-- The contour-data owner object exposes the top-edge continuity statement for the contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_continuousAt_topPath
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_topPath
    (r := h.contour_data.rectangle) x hZ hΦ

/-- The contour-data owner object exposes the bottom-edge continuity statement for the contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_continuousAt_bottomPath
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) (x : ℝ)
    (hZ : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x))
    (hΦ : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_continuousAt_bottomPath
    (r := h.contour_data.rectangle) x hZ hΦ

/-- The contour-data owner object packages the contour-integrand continuity on all four edges. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_continuousAt_edges
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (t : ℝ)
    (hZr : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t))
    (hΦr : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - (1 / 2 : ℂ)))
    (hZl : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t))
    (hΦl : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - (1 / 2 : ℂ)))
    (x : ℝ)
    (hZt : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
    (hΦt : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x - (1 / 2 : ℂ)))
    (hZb : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x))
    (hΦb : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x - (1 / 2 : ℂ))) :
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t) ∧
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t) ∧
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x) ∧
    ContinuousAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x) := by
  constructor
  · exact h.contourIntegrand_continuousAt_rightPath t hZr hΦr
  · constructor
    · exact h.contourIntegrand_continuousAt_leftPath t hZl hΦl
    · constructor
      · exact h.contourIntegrand_continuousAt_topPath x hZt hΦt
      · exact h.contourIntegrand_continuousAt_bottomPath x hZb hΦb

/-- The contour-data owner object packages the contour integrand differentiability on all four
edges. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_differentiableAt_edges
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (t : ℝ)
    (hZr : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t))
    (hΦr : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - (1 / 2 : ℂ)))
    (hZl : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t))
    (hΦl : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - (1 / 2 : ℂ)))
    (x : ℝ)
    (hZt : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x))
    (hΦt : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x - (1 / 2 : ℂ)))
    (hZb : DifferentiableAt ℂ completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x))
    (hΦb : DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x - (1 / 2 : ℂ))) :
    DifferentiableAt ℂ (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t) ∧
    DifferentiableAt ℂ (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t) ∧
    DifferentiableAt ℂ (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x) ∧
    DifferentiableAt ℂ (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x) := by
  constructor
  · exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_rightPath
      (r := h.contour_data.rectangle) t hZr hΦr
  · constructor
    · exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_leftPath
        (r := h.contour_data.rectangle) t hZl hΦl
    · constructor
      · exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_topPath
          (r := h.contour_data.rectangle) x hZt hΦt
      · exact zetaCompletedExplicitFormulaContourIntegrand_differentiableAt_bottomPath
          (r := h.contour_data.rectangle) x hZb hΦb

/-- The analytic package exposes the rectangle theorem input for the contour integrand. -/
theorem ExplicitFormulaAnalyticPackage.rectangleBoundaryIdentity
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
      (Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re ×ℂ
        Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo
        (min (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re)
        (max (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re) ×ℂ
        Set.Ioo
          (min (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
            (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im)
          (max (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
            (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im) \ s →
        HasFDerivAt (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z) (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re ×ℂ
        Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im) volume) :
    (((∫ x in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im * Complex.I)) -
        ∫ x in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im * Complex.I)) +
      Complex.I • ∫ y in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re + y * Complex.I)) -
      Complex.I • ∫ y in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
        zetaCompletedExplicitFormulaContourIntegrand f
          ((h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re + y * Complex.I)
      =
      ∫ x in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
        ∫ y in (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I := by
  exact zetaCompletedExplicitFormulaRectangleBoundaryIdentity
    (f := f) h.contour_data.rectangle f' s hs Hc Hd Hi

/-- The contour-data owner object packages the rectangle theorem input for the factorized contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.rectangleBoundaryIdentity_factorized
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (f' : ℂ → (ℂ →L[ℝ] ℂ))
    (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn (fun z : ℂ =>
      (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
        zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
      (Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re ×ℂ
        Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im))
    (Hd : ∀ x, x ∈ Set.Ioo
        (min (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re)
        (max (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re) ×ℂ
        Set.Ioo
          (min (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
            (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im)
          (max (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
            (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im) \ s →
        HasFDerivAt
          (fun z : ℂ =>
            (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹) z) *
              zetaCompletedExplicitFormulaPhi f (z - 1 / 2))
          (f' x) x)
    (Hi : IntegrableOn
      (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re ×ℂ
        Set.uIcc (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im) volume) :
    (((∫ x in
          (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im *
              Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) *
                Complex.I).im * Complex.I - 1 / 2)) -
        ∫ x in
          (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
          (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
            (x + (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im *
              Complex.I)) *
            zetaCompletedExplicitFormulaPhi f
              (x + (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) *
                Complex.I).im * Complex.I - 1 / 2)) +
      Complex.I • ∫ y in
        (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re +
            y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re +
              y * Complex.I - 1 / 2)) -
      Complex.I • ∫ y in
        (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
        (- logDeriv (fun w : ℂ => completedRiemannZeta w * (Gammaℝ w)⁻¹)
          ((h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re +
            y * Complex.I)) *
          zetaCompletedExplicitFormulaPhi f
            ((h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re +
              y * Complex.I - 1 / 2)
      =
      ∫ x in
        (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).re..
        (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).re,
        ∫ y in
          (h.contour_data.rectangle.c + (-h.contour_data.rectangle.T) * Complex.I).im..
          (h.contour_data.rectangle.c + (h.contour_data.rectangle.T) * Complex.I).im,
          Complex.I • ⇑(f' (x + y * Complex.I)) 1 -
            ⇑(f' (x + y * Complex.I)) Complex.I := by
  exact zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
    f h.contour_data.rectangle f' s hs Hc Hd Hi

/-- The analytic package yields the family horizontal decay target after choosing a family. -/
theorem ExplicitFormulaAnalyticPackage.horizontalDecayTargetFamily
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    explicitFormulaHorizontalDecayTargetFamily f F := by
  exact ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
    (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package proves the actual horizontal-vanishing statement for any family. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_horizontalIntegralsVanish
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    explicitFormulaHorizontalDecayStatementFamily f F := by
  exact ExplicitFormulaFamilyAnalyticPackage.horizontalDecay
    (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package proves the family-indexed horizontal decay statement. -/
theorem ExplicitFormulaAnalyticPackage.horizontalDecayStatementFamily
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    explicitFormulaHorizontalDecayStatementFamily f F := by
  exact (ExplicitFormulaAnalyticPackage.completedZeta_horizontalIntegralsVanish
    (f := f) h F N)

/-- The analytic package proves the explicit horizontal envelope decay for a contour family. -/
theorem ExplicitFormulaAnalyticPackage.horizontalDifferenceEnvelopeDecay
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        horizontalUnorderedFamilyDifferenceEnvelopeSplit
          (h.toFamilyPackage F).phi_control
          (h.toFamilyPackage F).logderiv_control
          F N (N + N.succ) T)
      atTop (𝓝 (0 : ℝ)) := by
  exact ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope
    (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package exposes the residue-theorem target in unfolded contour notation. -/
theorem ExplicitFormulaAnalyticPackage.residueTheoremTarget_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaResidueTheoremTarget f h.contour_data.rectangle ↔
      zetaCompletedExplicitFormulaContourIntegral f h.contour_data.rectangle =
        explicitFormulaResidueSum f [] := by
  rfl

/-- The analytic package exposes the full-integrand residue regularity theorem. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_rectangleResidueFormula_regular_off_countable
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ∀ {z : ℂ},
      z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
        (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ) →
      ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
        DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  fun {z} hz =>
    Boundary.LFunctions.ZetaAdmissibleFunction.completedZeta_rectangleResidueFormula_regular_off_countable
      h hz

/-- The analytic package exposes countability of the full-integrand singular set. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_rectangleResidueFormula_singularSet_countable
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} :
      Set ℂ).Countable :=
  Boundary.LFunctions.ZetaAdmissibleFunction.completedZeta_rectangleResidueFormula_singularSet_countable h

/-- The primed package wrapper records the zeta-side logarithmic derivative with Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_eq_zetaSide_add_invGammaCorrection'
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    completedZetaNegLogDeriv s =
      zetaSideNegLogDeriv s +
        deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
  exact
    sub_eq_iff_eq_add.mp
      (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction hs0 hs1 hΛ hΓ).symm

/-- The analytic package packages the zeta-side factorized contour integrand with Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormulaContourIntegrand_eq_factorized'
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f hs0 hs1 hΛ hΓ

/-- The family-level package yields the top-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ ≤ C := by
  exact
    zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- The family-level package yields the top-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ ≤ C := by
  exact h.topEdgeContourBound N T x hx1 hx2

/-- The package-level top edge contour bound. -/
theorem ExplicitFormulaAnalyticPackage.topEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C := by
  exact
    zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N

/-- The family-level package yields the bottom-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖ ≤ C := by
  exact
    zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- The family-level package yields the bottom-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖ ≤ C := by
  exact h.bottomEdgeContourBound N T x hx1 hx2

/-- The package-level bottom edge contour bound. -/
theorem ExplicitFormulaAnalyticPackage.bottomEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C := by
  exact
    zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
      h.phi_control h.logderiv_control h.contour_data.rectangle x hx1 hx2 N

/-- The analytic package yields the pointwise top/bottom contour bounds on the horizontal
edges. -/
theorem ExplicitFormulaAnalyticPackage.horizontalEdgeContourBoundTop
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.topEdgeContourBound_witness N x hx1 hx2

/-- The analytic package yields the pointwise contour bound on the bottom horizontal edge. -/
theorem ExplicitFormulaAnalyticPackage.horizontalEdgeContourBoundBottom
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.bottomEdgeContourBound_witness N x hx1 hx2

/-- The analytic package bundles the horizontal contour bounds as a named pair. -/
theorem ExplicitFormulaAnalyticPackage.horizontalEdgeContourBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C := by
  rcases h.topEdgeContourBound_witness N x hx1 hx2 with ⟨Ctop, htop⟩
  rcases h.bottomEdgeContourBound_witness N x hx1 hx2 with ⟨Cbot, hbot⟩
  refine ⟨max Ctop Cbot, ?_⟩
  constructor
  · exact le_trans htop (le_max_left _ _)
  · exact le_trans hbot (le_max_right _ _)

/-- The analytic package yields the top-edge contour bound directly. -/
theorem ExplicitFormulaAnalyticPackage.topEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.horizontalEdgeContourBoundTop N x hx1 hx2

/-- The analytic package yields the bottom-edge contour bound directly. -/
theorem ExplicitFormulaAnalyticPackage.bottomEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.horizontalEdgeContourBoundBottom N x hx1 hx2

/-- The package-level right vertical edge contour bound. -/
theorem ExplicitFormulaAnalyticPackage.rightEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C := by
  exact
    ⟨‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖,
      le_rfl⟩

/-- The package-level left vertical edge contour bound. -/
theorem ExplicitFormulaAnalyticPackage.leftEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C := by
  exact
    ⟨‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖,
      le_rfl⟩

/-- The analytic package yields the pointwise contour bound on the right vertical edge. -/
theorem ExplicitFormulaAnalyticPackage.rightEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C := by
  exact h.rightEdgeContourBound_witness N t ht1 ht2

/-- The analytic package yields the pointwise contour bound on the left vertical edge. -/
theorem ExplicitFormulaAnalyticPackage.leftEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C := by
  exact h.leftEdgeContourBound_witness N t ht1 ht2

/-- The analytic package bundles the vertical contour bounds as a named pair. -/
theorem ExplicitFormulaAnalyticPackage.verticalEdgeContourBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C := by
  rcases h.rightEdgeContourBound_witness N t ht1 ht2 with ⟨Cr, hCr⟩
  rcases h.leftEdgeContourBound_witness N t ht1 ht2 with ⟨Cl, hCl⟩
  exact
    ⟨max Cr Cl,
      And.intro
        (le_trans hCr (le_max_left Cr Cl))
        (le_trans hCl (le_max_right Cr Cl))⟩

/-- The package-level four-edge contour bound. -/
theorem ExplicitFormulaAnalyticPackage.contourEdgeBounds_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x t : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C := by
  rcases h.topEdgeContourBound_witness N x hx1 hx2 with ⟨Ctop, htop⟩
  rcases h.bottomEdgeContourBound_witness N x hx1 hx2 with ⟨Cbottom, hbottom⟩
  rcases h.rightEdgeContourBound_witness N t ht1 ht2 with ⟨Cright, hright⟩
  rcases h.leftEdgeContourBound_witness N t ht1 ht2 with ⟨Cleft, hleft⟩
  let Ch := max Ctop Cbottom
  let Cv := max Cright Cleft
  let C0 := max Ch Cv
  let C := C0 + 1
  have htop_nonneg : 0 ≤ Ctop :=
    le_trans (norm_nonneg _) htop
  have hC0_nonneg : 0 ≤ C0 :=
    le_trans htop_nonneg
      (le_trans (le_max_left Ctop Cbottom) (le_max_left Ch Cv))
  have hC_pos : 0 < C :=
    lt_of_le_of_lt hC0_nonneg (lt_add_of_pos_right C0 zero_lt_one)
  have hC0_le_C : C0 ≤ C :=
    le_add_of_nonneg_right zero_le_one
  have htop_le : Ctop ≤ C :=
    le_trans (le_trans (le_max_left Ctop Cbottom) (le_max_left Ch Cv)) hC0_le_C
  have hbottom_le : Cbottom ≤ C :=
    le_trans (le_trans (le_max_right Ctop Cbottom) (le_max_left Ch Cv)) hC0_le_C
  have hright_le : Cright ≤ C :=
    le_trans (le_trans (le_max_left Cright Cleft) (le_max_right Ch Cv)) hC0_le_C
  have hleft_le : Cleft ≤ C :=
    le_trans (le_trans (le_max_right Cright Cleft) (le_max_right Ch Cv)) hC0_le_C
  exact
    ⟨C,
      And.intro hC_pos
        (And.intro
          (le_trans htop htop_le)
          (And.intro
            (le_trans hbottom hbottom_le)
            (And.intro
              (le_trans hright hright_le)
              (le_trans hleft hleft_le))))⟩

/-- The analytic package bundles the four pointwise contour edge bounds. -/
theorem ExplicitFormulaAnalyticPackage.contourEdgeBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x t : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C := by
  rcases h.contourEdgeBounds_witness N x t hx1 hx2 ht1 ht2 with
    ⟨C, _hCpos, htop, hbottom, hright, hleft⟩
  exact ⟨C, htop, hbottom, hright, hleft⟩

/-- The contour-data owner object packages the contour-integrand strip bounds on all four edges. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_stripBounds
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (x : ℝ) (hx1 : h.contour_data.rectangle.c ≤ x) (hx2 : x ≤ 1 - h.contour_data.rectangle.c)
    (N : ℕ) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle x)‖ ≤ C := by
  rcases h.topEdgeContourBound_witness N x hx1 hx2 with ⟨Ctop, htop⟩
  rcases h.bottomEdgeContourBound_witness N x hx1 hx2 with ⟨Cbottom, hbottom⟩
  let wr := ‖zetaCompletedExplicitFormulaContourIntegrand f
    (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle x)‖
  let wl := ‖zetaCompletedExplicitFormulaContourIntegrand f
    (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle x)‖
  let Ch := max Ctop Cbottom
  let Cv := max wr wl
  let C := max Ch Cv
  have htop_le : Ctop ≤ C :=
    le_trans (le_max_left Ctop Cbottom) (le_max_left Ch Cv)
  have hbottom_le : Cbottom ≤ C :=
    le_trans (le_max_right Ctop Cbottom) (le_max_left Ch Cv)
  have hright_le : wr ≤ C :=
    le_trans (le_max_left wr wl) (le_max_right Ch Cv)
  have hleft_le : wl ≤ C :=
    le_trans (le_max_right wr wl) (le_max_right Ch Cv)
  exact
    ⟨C,
      And.intro
        (le_trans htop htop_le)
        (And.intro
          (le_trans hbottom hbottom_le)
          (And.intro
            hright_le
            hleft_le))⟩

/-- The analytic package exposes the contour-shift target once the residue and decay inputs are
instantiated. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget'
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f :=
  explicitFormulaContourShiftTarget_iff f h.contour_data.rectangle

/-- The analytic package packages the contour-shift target once the final equality is available. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (htarget :
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle :=
  htarget

/-- The analytic package exposes the contour-shift target in unfolded notation. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

/-- The analytic package packages the vertical decomposition target once the vertical equality is
available. -/
theorem ExplicitFormulaAnalyticPackage.verticalDecompositionTarget
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (hvertical :
      zetaCompletedExplicitFormulaRightLineIntegral f h.contour_data.rectangle -
        zetaCompletedExplicitFormulaLeftLineIntegral f h.contour_data.rectangle =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f) :
    explicitFormulaVerticalDecompositionTarget f h.contour_data.rectangle :=
  hvertical

/-- The analytic package exposes the vertical decomposition target in unfolded notation. -/
theorem ExplicitFormulaAnalyticPackage.verticalDecompositionTarget_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaVerticalDecompositionTarget f h.contour_data.rectangle ↔
      zetaCompletedExplicitFormulaRightLineIntegral f h.contour_data.rectangle -
        zetaCompletedExplicitFormulaLeftLineIntegral f h.contour_data.rectangle =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
import Boundary.LFunctions.ZetaExplicitFormulaFinalTarget

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

namespace ZetaAdmissibleFunction

/-- The analytic package exposes the transform control. -/
theorem ExplicitFormulaAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The analytic package exposes the log-derivative control. -/
theorem ExplicitFormulaAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The analytic package exposes the strip bound for the completed negative log derivative. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_stripBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact h.logderiv_control.stripBound a b N

/-- A constructive witness for the completed negative log derivative strip bound. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_stripBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (N : ℕ) :
    {C : ℝ //
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))} := by
  rcases h.logderiv_control.stripBound a b N with ⟨C, hC⟩
  exact ⟨C, hC⟩

/-- A constructive witness for the package-level log-derivative strip bound. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_stripBound_sigma
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (a b : ℝ) (N : ℕ) :
    {C : ℝ //
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))} := by
  exact h.completedZetaNegLogDeriv_stripBound_witness a b N

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
theorem ExplicitFormulaAnalyticPackage.contourData
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ExplicitFormulaContourData := by
  exact h.contour_data

/-- The analytic package exposes the residue-theorem target once the rectangle theorem is
instantiated. -/
theorem ExplicitFormulaAnalyticPackage.residueTheoremTarget
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
    explicitFormulaResidueTheoremTarget f h.contour_data.rectangle := by
  exact zetaCompletedExplicitFormulaRectangleBoundaryIdentity
    (f := f) h.contour_data.rectangle f' s hs Hc Hd Hi

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
  rcases h.horizontalEdgeContourBounds N x hx1 hx2 with ⟨Ch, hCh⟩
  rcases h.verticalEdgeContourBounds N x
    (by simpa using (h.contour_data.T_pos)) (by simpa using (neg_le_neg_iff).2 (le_of_lt h.contour_data.T_pos)) with
      ⟨Cv, hCv⟩
  exact ⟨⟨Ch, hCh⟩, ⟨Cv, hCv⟩⟩

/-- The contour-data owner object packages the rectangle theorem input for the factorized
contour integrand. -/
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
    zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
      (f := f) h.contour_data.rectangle f' s hs Hc Hd Hi := by
  exact zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
    (f := f) h.contour_data.rectangle f' s hs Hc Hd Hi

/-- The contour-data owner object exposes the factorized rectangle theorem in unfolded notation. -/
theorem ExplicitFormulaAnalyticPackage.rectangleBoundaryIdentity_factorized_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized f
      h.contour_data.rectangle ↔
      ∀ (f' : ℂ → (ℂ →L[ℝ] ℂ)) (s : Set ℂ) (hs : s.Countable)
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
      zetaCompletedExplicitFormulaRectangleBoundaryIdentity_factorized
        (f := f) h.contour_data.rectangle f' s hs Hc Hd Hi := by
  rfl

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

/-- The analytic package yields the family horizontal decay target after choosing a family. -/
theorem ExplicitFormulaAnalyticPackage.horizontalDecayTargetFamily
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    explicitFormulaHorizontalDecayTargetFamily f F := by
  exact
    ExplicitFormulaFamilyAnalyticPackage.horizontalDecayTargetFamily
      (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package proves the actual horizontal-vanishing statement for any family. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_horizontalIntegralsVanish
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    completedZeta_horizontalIntegralsVanish f F := by
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
    ∃ C : ℝ,
      Tendsto (fun T : ℝ => C * (1 + ‖T‖) ^ (-(N : ℤ)) * (1 + ‖T‖) ^ (-(N : ℤ)))
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
  fun {z} hz => completedZeta_rectangleResidueFormula_regular_off_countable h hz

/-- The analytic package exposes countability of the full-integrand singular set. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_rectangleResidueFormula_singularSet_countable
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} :
      Set ℂ).Countable :=
  completedZeta_rectangleResidueFormula_singularSet_countable h

/-- The analytic package exposes the residue-theorem target as the residue formula. -/
theorem ExplicitFormulaAnalyticPackage.residueTheoremTarget_iff_completedZetaRectangleResidueFormula
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaResidueTheoremTarget f h.contour_data.rectangle ↔
      completedZeta_rectangleResidueFormula f h.contour_data.rectangle := by
  constructor
  · intro hres
    rw [explicitFormulaResidueTheoremTarget, completedZeta_rectangleResidueFormula,
      explicitFormulaResidueSum_nil, zetaRectangleBoundaryIntegral, ← hres]
  · intro hres
    rw [explicitFormulaResidueTheoremTarget, completedZeta_rectangleResidueFormula,
      explicitFormulaResidueSum_nil, zetaRectangleBoundaryIntegral] at hres
    exact hres

/-- The analytic package exposes the vanishing of the analytic boundary sum. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormulaBoundarySumAnalytic_zero
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f = 0 := by
  exact zetaCompletedExplicitFormulaBoundarySumAnalytic_zero f

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

/-- The family-level package exposes the transform control. -/
theorem ExplicitFormulaFamilyAnalyticPackage.phiControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ZetaPhiAnalyticControl f := by
  exact h.phi_control

/-- The family-level package exposes the log-derivative control. -/
theorem ExplicitFormulaFamilyAnalyticPackage.logDerivControl
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    CompletedZetaNegLogDerivControl f := by
  exact h.logderiv_control

/-- The analytic package induces the family package for every contour family. -/
theorem ExplicitFormulaAnalyticPackage.toFamilyPackage
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) :
    ExplicitFormulaFamilyAnalyticPackage f F := by
  exact { phi_control := h.phi_control, logderiv_control := h.logderiv_control }

/-- The family-level package yields the top-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ ≤ C := by
  rcases h.logderiv_control.stripBound F.c (1 - F.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N
    with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖T‖) ^ (-(N : ℤ)) * CPhi * (1 + ‖T‖) ^ (-(N : ℤ)), ?_⟩
  exact zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
    h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- A constructive witness for the family-level top edge contour bound constant. -/
theorem ExplicitFormulaFamilyAnalyticPackage.topEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    {C : ℝ //
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound F.c (1 - F.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N
    with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖T‖) ^ (-(N : ℤ)) * CPhi * (1 + ‖T‖) ^ (-(N : ℤ)), ?_⟩
  exact zetaCompletedExplicitFormulaTopPath_contourIntegrand_strip_bound
    h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- A constructive witness for the package-level top edge contour bound constant. -/
theorem ExplicitFormulaAnalyticPackage.topEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    {C : ℝ // ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2)
      (1 / 2 - h.contour_data.rectangle.c) N with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      CPhi * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)), ?_⟩
  exact h.topEdgeContourBound N x hx1 hx2

/-- The family-level package yields the bottom-edge contour bound at height `T`. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖ ≤ C := by
  rcases h.logderiv_control.stripBound F.c (1 - F.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N
    with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖T‖) ^ (-(N : ℤ)) * CPhi * (1 + ‖T‖) ^ (-(N : ℤ)), ?_⟩
  exact zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
    h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- A constructive witness for the family-level bottom edge contour bound constant. -/
theorem ExplicitFormulaFamilyAnalyticPackage.bottomEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (N : ℕ) (T x : ℝ)
    (hx1 : F.c ≤ x) (hx2 : x ≤ 1 - F.c) :
    {C : ℝ //
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound F.c (1 - F.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay (F.c - 1 / 2) (1 / 2 - F.c) N
    with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖T‖) ^ (-(N : ℤ)) * CPhi * (1 + ‖T‖) ^ (-(N : ℤ)), ?_⟩
  exact zetaCompletedExplicitFormulaBottomPath_contourIntegrand_strip_bound
    h.phi_control h.logderiv_control (F.rectangle T) x hx1 hx2 N

/-- A constructive witness for the package-level bottom edge contour bound constant. -/
theorem ExplicitFormulaAnalyticPackage.bottomEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    {C : ℝ // ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2)
      (1 / 2 - h.contour_data.rectangle.c) N with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      CPhi * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)), ?_⟩
  exact h.bottomEdgeContourBound N x hx1 hx2

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
  rcases h.rightEdgeContourBound_witness N t ht1 ht2 with ⟨Cr, hr⟩
  rcases h.leftEdgeContourBound_witness N t ht1 ht2 with ⟨Cl, hl⟩
  refine ⟨max Cr Cl, ?_⟩
  constructor
  · exact le_trans hr (le_max_left _ _)
  · exact le_trans hl (le_max_right _ _)

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

/-- A constructive witness for the package-level right vertical edge contour bound constant. -/
theorem ExplicitFormulaAnalyticPackage.rightEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    {C : ℝ //
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2)
      (1 / 2 - h.contour_data.rectangle.c) N with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      CPhi * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)), ?_⟩
  have hstrip :
      h.contour_data.rectangle.c ≤
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).re ∧
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).re ≤
        1 - h.contour_data.rectangle.c := by
    constructor
    · rw [zetaCompletedExplicitFormulaRightPath_re]
    · rw [zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
  have hshiftstrip :
      h.contour_data.rectangle.c - 1 / 2 ≤
        (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ≤
        1 / 2 - h.contour_data.rectangle.c := by
    constructor
    · rw [sub_re, zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
    · rw [sub_re, zetaCompletedExplicitFormulaRightPath_re]
      linarith [h.contour_data.c_gt_half]
  have htopim :
      ‖(zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).im‖ = ‖t‖ := by
    rw [zetaCompletedExplicitFormulaRightPath_im]
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2 : ℂ).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaRightPath_im]
  exact by
    calc
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖
          ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ *
              ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t - 1 / 2)‖ := by
              exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
      _ ≤ (CLog * (1 + ‖(zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t).im‖) ^ (-(N : ℤ))) *
            (CPhi * (1 + ‖((zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t) - 1 / 2).im‖) ^ (-(N : ℤ))) := by
            gcongr
            · exact hLogC.2 _ hstrip.1 hstrip.2
            · exact hPhi.2 _ hshiftstrip.1 hshiftstrip.2
      _ = (CLog * (1 + ‖t‖) ^ (-(N : ℤ))) *
            (CPhi * (1 + ‖t‖) ^ (-(N : ℤ))) := by
            simp [CLog, CPhi, htopim, hshiftim, mul_comm, mul_left_comm, mul_assoc]

/-- A constructive witness for the package-level left vertical edge contour bound constant. -/
theorem ExplicitFormulaAnalyticPackage.leftEdgeContourBound_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (t : ℝ)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    {C : ℝ //
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2)
      (1 / 2 - h.contour_data.rectangle.c) N with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      CPhi * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)), ?_⟩
  have hstrip :
      h.contour_data.rectangle.c ≤
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).re ∧
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).re ≤
        1 - h.contour_data.rectangle.c := by
    constructor
    · rw [zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
    · rw [zetaCompletedExplicitFormulaLeftPath_re]
  have hshiftstrip :
      h.contour_data.rectangle.c - 1 / 2 ≤
        (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ∧
      (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).re ≤
        1 / 2 - h.contour_data.rectangle.c := by
    constructor
    · rw [sub_re, zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
    · rw [sub_re, zetaCompletedExplicitFormulaLeftPath_re]
      linarith [h.contour_data.c_gt_half]
  have hleftim :
      ‖(zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).im‖ = ‖t‖ := by
    rw [zetaCompletedExplicitFormulaLeftPath_im]
    simp
  have hshiftim :
      ‖(zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2 : ℂ).im‖ = ‖t‖ := by
    simp [zetaCompletedExplicitFormulaLeftPath_im]
  exact by
    calc
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖
          ≤ ‖completedZetaNegLogDeriv (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ *
              ‖zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t - 1 / 2)‖ := by
              exact norm_zetaCompletedExplicitFormulaContourIntegrand_le f _
      _ ≤ (CLog * (1 + ‖(zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t).im‖) ^ (-(N : ℤ))) *
            (CPhi * (1 + ‖((zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t) - 1 / 2).im‖) ^ (-(N : ℤ))) := by
            gcongr
            · exact hLogC.2 _ hstrip.1 hstrip.2
            · exact hPhi.2 _ hshiftstrip.1 hshiftstrip.2
      _ = (CLog * (1 + ‖t‖) ^ (-(N : ℤ))) *
            (CPhi * (1 + ‖t‖) ^ (-(N : ℤ))) := by
            simp [CLog, CPhi, hleftim, hshiftim, mul_comm, mul_left_comm, mul_assoc]

/-- A constructive witness for the package-level four-edge contour bound constant. -/
theorem ExplicitFormulaAnalyticPackage.contourEdgeBounds_witness
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x t : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c)
    (ht1 : t ≤ h.contour_data.rectangle.T)
    (ht2 : -h.contour_data.rectangle.T ≤ t) :
    {C : ℝ //
      0 < C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C ∧
      ‖zetaCompletedExplicitFormulaContourIntegrand f
          (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C} := by
  rcases h.logderiv_control.stripBound h.contour_data.rectangle.c
      (1 - h.contour_data.rectangle.c) N with ⟨CLog, hCLog, hLog⟩
  rcases h.phi_control.verticalStripRapidDecay
      (h.contour_data.rectangle.c - 1 / 2)
      (1 / 2 - h.contour_data.rectangle.c) N with ⟨CPhi, hCPhi, hPhi⟩
  refine ⟨CLog * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)) *
      CPhi * (1 + ‖h.contour_data.rectangle.T‖) ^ (-(N : ℤ)), ?_⟩
  constructor
  · positivity
  · exact ⟨(h.topEdgeContourBound N x hx1 hx2).2,
      (h.bottomEdgeContourBound N x hx1 hx2).2,
      (h.rightEdgeContourBound N t ht1 ht2).2,
      (h.leftEdgeContourBound N t ht1 ht2).2⟩

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
  rcases h.contourEdgeBounds_witness N x t hx1 hx2 ht1 ht2 with ⟨C, hC⟩
  exact ⟨C, hC⟩

/-- The analytic package yields the top-edge contour bound directly. -/
theorem ExplicitFormulaAnalyticPackage.topEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.topEdgeContourBound_witness N x hx1 hx2

/-- The analytic package yields the bottom-edge contour bound directly. -/
theorem ExplicitFormulaAnalyticPackage.bottomEdgeContourBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) (x : ℝ)
    (hx1 : h.contour_data.rectangle.c ≤ x)
    (hx2 : x ≤ 1 - h.contour_data.rectangle.c) :
    ∃ C : ℝ,
      ‖zetaCompletedExplicitFormulaContourIntegrand f
        (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C := by
  exact h.bottomEdgeContourBound_witness N x hx1 hx2

/-- The analytic package yields a single uniform edge bound constant for all four sides. -/
theorem ExplicitFormulaAnalyticPackage.uniformContourEdgeBound
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x t : ℝ,
        (h.contour_data.rectangle.c ≤ x → x ≤ 1 - h.contour_data.rectangle.c →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaTopPath h.contour_data.rectangle x)‖ ≤ C) ∧
        (h.contour_data.rectangle.c ≤ x → x ≤ 1 - h.contour_data.rectangle.c →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaBottomPath h.contour_data.rectangle x)‖ ≤ C) ∧
        (t ≤ h.contour_data.rectangle.T → -h.contour_data.rectangle.T ≤ t →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaRightPath h.contour_data.rectangle t)‖ ≤ C) ∧
        (t ≤ h.contour_data.rectangle.T → -h.contour_data.rectangle.T ≤ t →
          ‖zetaCompletedExplicitFormulaContourIntegrand f
            (zetaCompletedExplicitFormulaLeftPath h.contour_data.rectangle t)‖ ≤ C) := by
  rcases h.contourEdgeBounds_witness N h.contour_data.rectangle.c h.contour_data.rectangle.T
      (by linarith [h.contour_data.T_pos]) (by linarith [h.contour_data.T_pos])
      (by linarith [h.contour_data.T_pos]) (by linarith [h.contour_data.T_pos]) with
    ⟨C, hC⟩
  refine ⟨C, hC.1, ?_⟩
  intro x t
  constructor
  · intro hx1 hx2
    exact le_trans (h.topEdgeContourBound_witness N x hx1 hx2).2 hC.2.1
  constructor
  · intro hx1 hx2
    exact le_trans (h.bottomEdgeContourBound_witness N x hx1 hx2).2 hC.2.2.1
  constructor
  · intro ht1 ht2
    exact le_trans (h.rightEdgeContourBound_witness N t ht1 ht2).2 hC.2.2.2.1
  · intro ht1 ht2
    exact le_trans (h.leftEdgeContourBound_witness N t ht1 ht2).2 hC.2.2.2.2

/-- The analytic package yields the family horizontal decay target after choosing a family. -/
theorem ExplicitFormulaAnalyticPackage.horizontalDecayTargetFamily
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    explicitFormulaHorizontalDecayTargetFamily f F := by
  exact
    ExplicitFormulaFamilyAnalyticPackage.horizontalDecayTargetFamily
      (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package proves the actual horizontal-vanishing statement for any family. -/
theorem ExplicitFormulaAnalyticPackage.completedZeta_horizontalIntegralsVanish
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (F : ExplicitFormulaContourFamily) (N : ℕ) :
    completedZeta_horizontalIntegralsVanish f F := by
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
    ∃ C : ℝ,
      Tendsto (fun T : ℝ => C * (1 + ‖T‖) ^ (-(N : ℤ)) * (1 + ‖T‖) ^ (-(N : ℤ)))
        atTop (𝓝 (0 : ℝ)) := by
  exact ExplicitFormulaFamilyAnalyticPackage.horizontalDecayEnvelope
    (f := f) (F := F) (h := h.toFamilyPackage F) N

/-- The analytic package exposes contour-shift invariance under reflected autocorrelation. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    explicitFormulaContourShiftTarget
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r ↔
      explicitFormulaContourShiftTarget
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact zetaCompletedExplicitFormulaContourShiftTarget_autocorrelation_reflect f r

/-- The analytic package exposes the reflected-autocorrelation sign rule for the contour
integrand. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegrand_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (s : ℂ) :
    zetaCompletedExplicitFormulaContourIntegrand
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) (1 - s) =
      - zetaCompletedExplicitFormulaContourIntegrand
        (ZetaAdmissibleFunction.autocorrelation f) s := by
  exact zetaCompletedExplicitFormulaContourIntegrand_autocorrelation_reflect f s

/-- The analytic package exposes the reflected-autocorrelation sign rule for the right vertical
line integral. -/
theorem ExplicitFormulaAnalyticPackage.rightLineIntegral_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaRightLineIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaRightLineIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact zetaCompletedExplicitFormulaRightLineIntegral_autocorrelation_reflect f r

/-- The analytic package exposes the reflected-autocorrelation sign rule for the left vertical
line integral. -/
theorem ExplicitFormulaAnalyticPackage.leftLineIntegral_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaLeftLineIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaLeftLineIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact zetaCompletedExplicitFormulaLeftLineIntegral_autocorrelation_reflect f r

/-- The analytic package exposes the reflected-autocorrelation sign rule for the top horizontal
line integral. -/
theorem ExplicitFormulaAnalyticPackage.topLineIntegral_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaTopLineIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact zetaCompletedExplicitFormulaTopLineIntegral_autocorrelation_reflect f r

/-- The analytic package exposes the reflected-autocorrelation sign rule for the contour
integral itself. -/
theorem ExplicitFormulaAnalyticPackage.contourBoundary_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact zetaCompletedExplicitFormulaContourBoundary_autocorrelation_reflect f r

/-- The analytic package exposes the reflected-autocorrelation sign rule for the full contour
boundary integral in the final contour-shift normalization. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftBoundary_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact h.contourBoundary_autocorrelation_reflect r

/-- The analytic package exposes the reflected-autocorrelation boundary-defect compatibility. -/
theorem ExplicitFormulaAnalyticPackage.zeroKreinGram_autocorrelation_reflect_boundaryDefect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect f

/-- The analytic package exposes the reflected-probe zero-side Krein form compatibility. -/
theorem ExplicitFormulaAnalyticPackage.zeroKreinGram_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect' f

/-- The analytic package exposes the reflected-probe zero-side boundary-defect compatibility. -/
theorem ExplicitFormulaAnalyticPackage.zeroKreinGram_autocorrelation_reflect_boundaryDefect'
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect f

/-- The analytic package exposes the reflected autocorrelation boundary-defect Gram comparison. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedBoundaryDefectGram_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zetaCompletedBoundaryDefectGram_autocorrelation_reflect
    (f := f)

/-- The analytic package exposes the reflected autocorrelation zero-side packet norm comparison. -/
theorem ExplicitFormulaAnalyticPackage.zeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq_classFree f

/-- The analytic package exposes the reflected autocorrelation packet norm comparison. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedPacketNormSq_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedPacketNormSq
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zetaCompletedPacketNormSq_autocorrelation_reflect
    (f := f)

/-- The analytic package exposes the reflected autocorrelation packet-norm identity in Weil form. -/
theorem ExplicitFormulaAnalyticPackage.zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaWeilFormCompleted_autocorrelation_reflect_eq_packetNormSq (f := f)

/-- The analytic package exposes the reflected autocorrelation packet-norm identity in zero-side form. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedPacketNormSq (ZetaAdmissibleFunction.autocorrelation f) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaCompletedZeroKreinGram_autocorrelation_reflect_eq_completedPacketNormSq (f := f)

/-- The analytic package exposes the reflected autocorrelation nonnegativity statement. -/
theorem ExplicitFormulaAnalyticPackage.zetaWeilFormCompleted_autocorrelation_reflect_nonnegative
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaWeilFormCompleted_autocorrelation_reflect_nonnegative (f := f)

/-- The analytic package exposes the reflected autocorrelation nonnegativity statement, class-free. -/
theorem ExplicitFormulaAnalyticPackage.zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_classFree
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    0 ≤ zetaWeilFormCompleted
      (ZetaAdmissibleFunction.autocorrelation
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction
    .zetaWeilFormCompleted_autocorrelation_reflect_nonnegative_classFree (f := f)

/-- The analytic package exposes the zeta-side logarithmic derivative with its Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.completedZetaNegLogDeriv_eq_zetaSide_add_invGammaCorrection
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedZetaNegLogDeriv s =
      zetaSideNegLogDeriv s +
        deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
  exact
    sub_eq_iff_eq_add.mp
      (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction hs0 hs1 hΛ hΓ).symm

/-- The analytic package exposes the zeta-side factorized contour integrand with Gamma correction. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedExplicitFormulaContourIntegrand_eq_factorized
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaCompletedExplicitFormulaContourIntegrand f s =
      (zetaSideNegLogDeriv s +
          deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹) *
        zetaCompletedExplicitFormulaPhi f (s - 1 / 2) := by
  exact zetaCompletedExplicitFormulaContourIntegrand_eq_factorized f hs0 hs1 hΛ hΓ

/-- The analytic package exposes the reflected-autocorrelation sign rule for the contour
integral itself. -/
theorem ExplicitFormulaAnalyticPackage.contourIntegral_autocorrelation_reflect
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    (r : ExplicitFormulaRectangle) :
    zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) r =
      - zetaCompletedExplicitFormulaContourIntegral
        (ZetaAdmissibleFunction.autocorrelation f) r := by
  exact h.contourBoundary_autocorrelation_reflect r

/-- The analytic package exposes the contour-shift target once the residue and decay inputs are
instantiated. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget'
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle := by
  exact explicitFormulaContourShiftTarget_iff (f := f) (r := h.contour_data.rectangle)

/-- The analytic package exposes the contour-shift target in unfolded notation. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

/-- The analytic package exposes the zero-valued contour-shift target in the current
normalization. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget_iff_zero
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaContourShiftTarget f h.contour_data.rectangle ↔
      zetaCompletedZeroKreinGram f = 0 := by
  exact explicitFormulaContourShiftTarget_iff_zero f h.contour_data.rectangle

/-- The analytic package proves the zero-valued contour-shift target in the current normalization. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget_zero
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram f = 0 := by
  exact (h.contourShiftTarget_iff_zero).1 h.contourShiftTarget'

/-- The analytic package exposes the zero-side Krein/boundary-defect comparison. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedZeroKreinGram_eq_boundaryDefectGram
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram f = zetaCompletedBoundaryDefectGram f := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zetaCompletedZeroKreinGram_eq_boundaryDefectGram
    (f := f)

/-- The analytic package exposes the zero-side Krein/packet norm comparison. -/
theorem ExplicitFormulaAnalyticPackage.zetaCompletedZeroKreinGram_eq_completedPacketNormSq
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    zetaCompletedZeroKreinGram f = zetaCompletedPacketNormSq f := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zetaCompletedZeroKreinGram_eq_completedPacketNormSq
    (f := f)

/-- The analytic package exposes the final contour-shift target once the residue and decay
theorems are instantiated. -/
theorem ExplicitFormulaAnalyticPackage.contourShiftTarget
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
    explicitFormulaContourShiftTarget f h.contour_data.rectangle := by
  exact explicitFormulaContourShiftTarget f h.contour_data.rectangle

/-- The analytic package exposes the vertical decomposition target. -/
theorem ExplicitFormulaAnalyticPackage.verticalDecompositionTarget
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaVerticalDecompositionTarget f h.contour_data.rectangle := by
  exact explicitFormulaVerticalDecompositionTarget_iff (f := f) (r := h.contour_data.rectangle)

/-- The analytic package exposes the vertical decomposition target in unfolded notation. -/
theorem ExplicitFormulaAnalyticPackage.verticalDecompositionTarget_iff
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaVerticalDecompositionTarget f h.contour_data.rectangle ↔
      zetaCompletedExplicitFormulaRightLineIntegral f h.contour_data.rectangle -
        zetaCompletedExplicitFormulaLeftLineIntegral f h.contour_data.rectangle =
      zetaCompletedExplicitFormulaBoundarySumAnalytic f := by
  rfl

/-- The analytic package exposes the zero-valued vertical decomposition target in current
normalization. -/
theorem ExplicitFormulaAnalyticPackage.verticalDecompositionTarget_iff_zero
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f) :
    explicitFormulaVerticalDecompositionTarget f h.contour_data.rectangle ↔
      zetaCompletedExplicitFormulaRightLineIntegral f h.contour_data.rectangle -
        zetaCompletedExplicitFormulaLeftLineIntegral f h.contour_data.rectangle = 0 := by
  exact explicitFormulaVerticalDecompositionTarget_iff_zero f h.contour_data.rectangle

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaExplicitFormulaContourPaths
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary admissible transform regularity

This file owns the analytic control package for the explicit-formula transform
`Φ_f`. The point is to make the regularity hypotheses explicit at the owner
level so the contour theorem can consume them without ad hoc side conditions.

The file only records the package structure and the bridge lemmas that unpack
it. The actual analytic construction of the package belongs upstream in the
transform theory.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Analytic control data for the explicit-formula transform `Φ_f`. -/
structure ZetaPhiAnalyticControl (f : ZetaAdmissibleFunction) where
  /-- `Φ_f` is entire. -/
  entire_phi : AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ
  /-- `Φ_f` is differentiable at every point. -/
  differentiableAt_phi : ∀ z : ℂ,
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z
  /-- `Φ_f` has vertical-strip rapid decay. -/
  vertical_strip_rapid_decay :
    ∀ (a b : ℝ) (N : ℕ),
      {C : ℝ //
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi f z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))}

/-- The analytic control package exposes pointwise differentiability. -/
theorem ZetaPhiAnalyticControl.differentiableAt
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z := by
  exact h.differentiableAt_phi z

/-- The analytic control package exposes the entireity statement. -/
theorem ZetaPhiAnalyticControl.entire
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) :
    AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ := by
  exact h.entire_phi

/-- The analytic control package exposes the vertical-strip decay bound. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecay
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact ⟨(h.vertical_strip_rapid_decay a b N).1, (h.vertical_strip_rapid_decay a b N).2⟩

/-- A constructive selector for the `Φ_f` vertical-strip constant. -/
def ZetaPhiAnalyticControl.verticalStripRapidDecayConstant
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  (h.vertical_strip_rapid_decay a b N).1

/-- The constructive `Φ_f` vertical-strip constant is positive. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_pos
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    0 < h.verticalStripRapidDecayConstant a b N :=
  (h.vertical_strip_rapid_decay a b N).2.1

/-- The constructive `Φ_f` vertical-strip constant satisfies its strip bound. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_bound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖zetaCompletedExplicitFormulaPhi f z‖
        ≤ h.verticalStripRapidDecayConstant a b N * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  (h.vertical_strip_rapid_decay a b N).2.2

/-- `Φ_f` is differentiable along the right contour edge whenever the control package is present. -/
theorem ZetaPhiAnalyticControl.differentiableAt_rightPath
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (r : ExplicitFormulaRectangle) (t : ℝ) :
    DifferentiableAt ℂ
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (zetaCompletedExplicitFormulaRightPath r t) := by
  exact h.differentiableAt_phi _

/-- The vertical-strip bound of `Φ_f` applies to the right contour edge once the rectangle is
inside the chosen strip. -/
theorem ZetaPhiAnalyticControl.rightPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (t : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaRightPath r t).re)
    (hb : (zetaCompletedExplicitFormulaRightPath r t).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightPath r t)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaRightPath r t).im‖) ^ (-(N : ℤ)) := by
  rcases h.verticalStripRapidDecay a b N with ⟨C, hC, hbound⟩
  exact ⟨C, hC, hbound (zetaCompletedExplicitFormulaRightPath r t) ha hb⟩

/-- The vertical-strip bound of `Φ_f` applies to the top contour edge once the rectangle is inside
the chosen strip. -/
theorem ZetaPhiAnalyticControl.topPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaTopPath r x).re)
    (hb : (zetaCompletedExplicitFormulaTopPath r x).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaTopPath r x)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaTopPath r x).im‖) ^ (-(N : ℤ)) := by
  rcases h.verticalStripRapidDecay a b N with ⟨C, hC, hbound⟩
  exact ⟨C, hC, hbound (zetaCompletedExplicitFormulaTopPath r x) ha hb⟩

/-- The vertical-strip bound of `Φ_f` applies to the bottom contour edge once the rectangle is
inside the chosen strip. -/
theorem ZetaPhiAnalyticControl.bottomPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaBottomPath r x).re)
    (hb : (zetaCompletedExplicitFormulaBottomPath r x).re ≤ b) :
    ∃ C : ℝ,
      0 < C ∧
      ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaBottomPath r x)‖
        ≤ C * (1 + ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖) ^ (-(N : ℤ)) := by
  rcases h.verticalStripRapidDecay a b N with ⟨C, hC, hbound⟩
  exact ⟨C, hC, hbound (zetaCompletedExplicitFormulaBottomPath r x) ha hb⟩

/-- The transform package is the owner-level input for contour estimates. -/
def ZetaPhiAnalyticControlPackage (f : ZetaAdmissibleFunction) : Type :=
  ZetaPhiAnalyticControl f

/-- The transform package is exactly the analytic control data. -/
def ZetaPhiAnalyticControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    ZetaPhiAnalyticControlPackage f = ZetaPhiAnalyticControl f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

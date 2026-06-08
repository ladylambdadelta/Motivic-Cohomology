import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
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
structure ZetaPhiAnalyticControl (f : ZetaAdmissibleFunction) : Prop where
  /-- `Φ_f` is entire. -/
  entire_phi : AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ
  /-- `Φ_f` is differentiable at every point. -/
  differentiableAt_phi : ∀ z : ℂ,
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z
  /-- `Φ_f` has vertical-strip rapid decay. -/
  vertical_strip_rapid_decay :
    ∀ (a b : ℝ) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi f z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))

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
  exact h.vertical_strip_rapid_decay a b N

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
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaRightPath r t)‖
      ≤ Classical.choose (h.verticalStripRapidDecay a b N) * (1 +
        ‖(zetaCompletedExplicitFormulaRightPath r t).im‖) ^ (-(N : ℤ)) := by
  let C : ℝ := Classical.choose (h.verticalStripRapidDecay a b N)
  have hC : 0 < C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    exact Classical.choose_spec (h.verticalStripRapidDecay a b N)
  have hbound := hC.2 (zetaCompletedExplicitFormulaRightPath r t) ha hb
  exact hbound

/-- The vertical-strip bound of `Φ_f` applies to the top contour edge once the rectangle is inside
the chosen strip. -/
theorem ZetaPhiAnalyticControl.topPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaTopPath r x).re)
    (hb : (zetaCompletedExplicitFormulaTopPath r x).re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaTopPath r x)‖
      ≤ Classical.choose (h.verticalStripRapidDecay a b N) * (1 +
        ‖(zetaCompletedExplicitFormulaTopPath r x).im‖) ^ (-(N : ℤ)) := by
  let C : ℝ := Classical.choose (h.verticalStripRapidDecay a b N)
  have hC : 0 < C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    exact Classical.choose_spec (h.verticalStripRapidDecay a b N)
  have hbound := hC.2 (zetaCompletedExplicitFormulaTopPath r x) ha hb
  exact hbound

/-- The vertical-strip bound of `Φ_f` applies to the bottom contour edge once the rectangle is
inside the chosen strip. -/
theorem ZetaPhiAnalyticControl.bottomPath_verticalStripBound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (r : ExplicitFormulaRectangle) (x : ℝ)
    (ha : a ≤ (zetaCompletedExplicitFormulaBottomPath r x).re)
    (hb : (zetaCompletedExplicitFormulaBottomPath r x).re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f (zetaCompletedExplicitFormulaBottomPath r x)‖
      ≤ Classical.choose (h.verticalStripRapidDecay a b N) * (1 +
        ‖(zetaCompletedExplicitFormulaBottomPath r x).im‖) ^ (-(N : ℤ)) := by
  let C : ℝ := Classical.choose (h.verticalStripRapidDecay a b N)
  have hC : 0 < C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
    exact Classical.choose_spec (h.verticalStripRapidDecay a b N)
  have hbound := hC.2 (zetaCompletedExplicitFormulaBottomPath r x) ha hb
  exact hbound

/-- The transform package is the owner-level input for contour estimates. -/
def ZetaPhiAnalyticControlPackage (f : ZetaAdmissibleFunction) : Prop :=
  ZetaPhiAnalyticControl f

/-- The transform package is exactly the analytic control data. -/
theorem ZetaPhiAnalyticControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    ZetaPhiAnalyticControlPackage f = ZetaPhiAnalyticControl f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

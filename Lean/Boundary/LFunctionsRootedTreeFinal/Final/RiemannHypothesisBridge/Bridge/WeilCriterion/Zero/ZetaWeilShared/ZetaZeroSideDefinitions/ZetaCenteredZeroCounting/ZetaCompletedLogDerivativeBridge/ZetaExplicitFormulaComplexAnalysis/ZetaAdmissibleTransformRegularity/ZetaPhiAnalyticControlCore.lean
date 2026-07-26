import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base

/-!
# Completed transform analytic-control core

This file owns the selector-free analytic-control record for the completed
explicit-formula transform `Phi_f`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Analytic control data for the explicit-formula transform `Phi_f`. -/
structure ZetaPhiAnalyticControl (f : ZetaAdmissibleFunction) where
  /-- `Phi_f` is entire. -/
  entire_phi : AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ
  /-- `Phi_f` is differentiable at every point. -/
  differentiableAt_phi : ∀ z : ℂ,
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z
  /-- `Phi_f` has vertical-strip rapid decay. -/
  vertical_strip_rapid_decay :
    ∀ (a b : ℝ) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi f z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))
  /-- A concrete rapid-decay constant for `Phi_f` on each vertical strip. -/
  vertical_strip_rapid_decay_constant : ℝ → ℝ → ℕ → ℝ
  /-- The concrete vertical-strip rapid-decay constant is positive. -/
  vertical_strip_rapid_decay_constant_pos :
    ∀ (a b : ℝ) (N : ℕ),
      0 < vertical_strip_rapid_decay_constant a b N
  /-- The concrete vertical-strip rapid-decay constant bounds `Phi_f` on the strip. -/
  vertical_strip_rapid_decay_constant_bound :
    ∀ (a b : ℝ) (N : ℕ) (z : ℂ),
      a ≤ z.re →
      z.re ≤ b →
      ‖zetaCompletedExplicitFormulaPhi f z‖
        ≤ vertical_strip_rapid_decay_constant a b N *
          (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- The analytic control package exposes pointwise differentiability. -/
theorem ZetaPhiAnalyticControl.differentiableAt
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z :=
  h.differentiableAt_phi z

/-- The analytic control package exposes the entireity statement. -/
theorem ZetaPhiAnalyticControl.entire
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f) :
    AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ :=
  h.entire_phi

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
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  ⟨h.vertical_strip_rapid_decay_constant a b N,
    h.vertical_strip_rapid_decay_constant_pos a b N,
    h.vertical_strip_rapid_decay_constant_bound a b N⟩

/-- The recorded concrete constant gives the existential vertical-strip decay
projection. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecay_from_constant
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  h.verticalStripRapidDecay a b N

/-- The recorded rapid-decay constant for `Phi_f` on a vertical strip. -/
def ZetaPhiAnalyticControl.verticalStripRapidDecayConstant
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  h.vertical_strip_rapid_decay_constant a b N

/-- The recorded vertical-strip rapid-decay constant is positive. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_pos
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) :
    0 < h.verticalStripRapidDecayConstant a b N :=
  h.vertical_strip_rapid_decay_constant_pos a b N

/-- The recorded vertical-strip rapid-decay constant bounds `Phi_f` on the strip. -/
theorem ZetaPhiAnalyticControl.verticalStripRapidDecayConstant_bound
    {f : ZetaAdmissibleFunction} (h : ZetaPhiAnalyticControl f)
    (a b : ℝ) (N : ℕ) (z : ℂ)
    (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖zetaCompletedExplicitFormulaPhi f z‖
      ≤ h.verticalStripRapidDecayConstant a b N *
        (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  h.vertical_strip_rapid_decay_constant_bound a b N z ha hb

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

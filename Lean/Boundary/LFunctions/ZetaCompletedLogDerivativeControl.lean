import Boundary.LFunctions.ZetaCompletedLogDerivativeCore

/-!
# Boundary completed-log-derivative control

This file owns the strip-control package for the completed zeta negative
logarithmic derivative. The actual analytic bound is part of the upstream
completion theory; this file only records the owner-level interface the
contour estimate will consume.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Strip control data for the completed zeta negative logarithmic derivative. -/
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) : Prop where
  /-- A uniform strip bound on the completed negative log derivative. -/
  strip_bound :
    ∀ (a b : ℝ) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))

/-- The strip-control package exposes the pointwise bound. -/
theorem CompletedZetaNegLogDerivControl.stripBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact h.strip_bound a b N

/-- The completed negative log-derivative control is the owner-level strip package. -/
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Prop :=
  CompletedZetaNegLogDerivControl f

/-- The package is exactly the strip-control data. -/
theorem CompletedZetaNegLogDerivControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivControlPackage f = CompletedZetaNegLogDerivControl f := by
  rfl

/-- A critical-line specialization of the strip bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
  rcases h.stripBound (1 / 2 : ℝ) (1 / 2 : ℝ) N with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t
  have hre_left :
      (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + t * Complex.I).re := by
    simp
  have hre_right :
      ((1 / 2 : ℂ) + t * Complex.I).re ≤ (1 / 2 : ℝ) := by
    simp
  have hnorm : ‖((1 / 2 : ℂ) + t * Complex.I).im‖ = ‖t‖ := by
    simp
  simpa [hnorm] using hbound ((1 / 2 : ℂ) + t * Complex.I) hre_left hre_right

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

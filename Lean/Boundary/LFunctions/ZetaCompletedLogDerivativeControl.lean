import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

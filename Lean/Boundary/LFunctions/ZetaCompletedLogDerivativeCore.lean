import Boundary.LFunctions.ZetaCompletedNormalization
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Boundary completed-log-derivative core

This file owns the completed zeta negative logarithmic derivative and its
basic normalization theorem. It is separated from the contour package so the
strip-control file can depend on the logarithmic derivative without importing
the full contour bridge back.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed zeta negative logarithmic derivative. -/
def completedZetaNegLogDeriv (s : ℂ) : ℂ :=
  - deriv completedRiemannZeta s / completedRiemannZeta s

/-- The completed negative logarithmic derivative is the negative `logDeriv`. -/
theorem completedZetaNegLogDeriv_eq_neg_logDeriv (s : ℂ) :
    completedZetaNegLogDeriv s = - logDeriv completedRiemannZeta s := by
  unfold completedZetaNegLogDeriv
  rw [logDeriv_apply]
  rw [neg_div]

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

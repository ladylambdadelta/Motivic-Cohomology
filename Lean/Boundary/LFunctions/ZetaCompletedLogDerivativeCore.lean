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
  calc
    (-deriv completedRiemannZeta s) / completedRiemannZeta s =
        -(deriv completedRiemannZeta s / completedRiemannZeta s) := by
      exact neg_div (completedRiemannZeta s) (deriv completedRiemannZeta s)
    _ = - logDeriv completedRiemannZeta s := by
      exact Eq.symm <| congrArg Neg.neg (logDeriv_apply (f := completedRiemannZeta) (x := s))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

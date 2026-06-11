import Boundary.LFunctions.ZetaAdmissibleFunction
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
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) where
  /-- A uniform strip bound on the completed negative log derivative. -/
  strip_bound :
    ∀ (a b : ℝ) (N : ℕ),
      {C : ℝ //
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ))}

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
  exact ⟨(h.strip_bound a b N).1, (h.strip_bound a b N).2⟩

/-- A constructive selector for the completed-zeta strip-bound constant. -/
def CompletedZetaNegLogDerivControl.stripBoundConstant
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (N : ℕ) : ℝ :=
  (h.strip_bound a b N).1

/-- The constructive completed-zeta strip-bound constant is positive. -/
theorem CompletedZetaNegLogDerivControl.stripBoundConstant_pos
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (N : ℕ) :
    0 < h.stripBoundConstant a b N :=
  (h.strip_bound a b N).2.1

/-- The constructive completed-zeta strip-bound constant satisfies its strip bound. -/
theorem CompletedZetaNegLogDerivControl.stripBoundConstant_bound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (N : ℕ) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖completedZetaNegLogDeriv z‖
        ≤ h.stripBoundConstant a b N * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
  (h.strip_bound a b N).2.2

/-- The completed negative log-derivative control is the owner-level strip package. -/
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Type :=
  CompletedZetaNegLogDerivControl f

/-- The package is exactly the strip-control data. -/
def CompletedZetaNegLogDerivControlPackage_eq
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
  have hre : ((1 / 2 : ℂ) + t * Complex.I).re = (1 / 2 : ℝ) := by
    norm_num [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have him : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
    norm_num [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hre_le : (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + t * Complex.I).re := by
    exact le_of_eq hre.symm
  have hre_ge : ((1 / 2 : ℂ) + t * Complex.I).re ≤ (1 / 2 : ℝ) := by
    exact le_of_eq hre
  have hbound' :=
    hbound ((1 / 2 : ℂ) + t * Complex.I) hre_le hre_ge
  have hRHS :
      C * (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ (-(N : ℤ)) =
        C * (1 + ‖t‖) ^ (-(N : ℤ)) := by
    exact congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ (-(N : ℤ))) him
  exact hbound'.trans (le_of_eq hRHS)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

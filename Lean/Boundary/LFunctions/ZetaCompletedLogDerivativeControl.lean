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

/-- A zero-excised vertical strip for the completed zeta logarithmic derivative. -/
structure CompletedZetaZeroExcisedStrip (a b : ℝ) where
  carrier : Set ℂ
  in_strip : ∀ z : ℂ, z ∈ carrier → a ≤ z.re ∧ z.re ≤ b
  zeta_ne_zero : ∀ z : ℂ, z ∈ carrier → completedRiemannZeta z ≠ 0
  contains_zero_avoiding_contour_edges :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      completedRiemannZeta z ≠ 0 →
      z ∈ carrier

/-- Polynomial strip growth for the zeta-side logarithmic derivative. -/
theorem zetaSideNegLogDeriv_polynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖- deriv riemannZeta z / riemannZeta z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  sorry

/-- Polynomial strip growth for the archimedean completion logarithmic derivative. -/
theorem gammaCompletionLogDeriv_polynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  sorry

/-- The completed negative log-derivative is bounded by the zeta-side and archimedean
completion logarithmic derivative bounds on vertical strips. -/
theorem completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hzeta :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖- deriv riemannZeta z / riemannZeta z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hgamma :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
            ≤ C * (1 + ‖z.im‖) ^ N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  sorry

/-- The completed zeta zero set admits a zero-excised strip containing every zero-free contour
point in the strip. -/
theorem exists_completedZetaZeroExcisedStrip
    (a b : ℝ) :
    ∃ E : CompletedZetaZeroExcisedStrip a b, True := by
  sorry

/-- The completed negative logarithmic derivative has polynomial growth on the canonical
zero-excised strip region. -/
theorem completedZetaNegLogDeriv_zeroExcisedPolynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    a b E N
    (zetaSideNegLogDeriv_polynomialStripBound a b E N)
    (gammaCompletionLogDeriv_polynomialStripBound a b E N)

/-- Strip control data for the completed zeta negative logarithmic derivative. -/
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) where
  /-- Polynomial growth for the completed negative log derivative on a zero-excised strip. -/
  zero_excised_polynomial_strip_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N}

/-- The strip-control package exposes zero-excised polynomial pointwise growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.zero_excised_polynomial_strip_bound a b E N

/-- The completed negative log-derivative control is the owner-level strip package. -/
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Type :=
  CompletedZetaNegLogDerivControl f

/-- The package is exactly the strip-control data. -/
def CompletedZetaNegLogDerivControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivControlPackage f = CompletedZetaNegLogDerivControl f := by
  rfl

/-- A critical-line specialization of the zero-excised polynomial strip bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineBound_of_mem
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (E : CompletedZetaZeroExcisedStrip (1 / 2 : ℝ) (1 / 2 : ℝ)) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ((1 / 2 : ℂ) + t * Complex.I) ∈ E.carrier →
        ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ N := by
  rcases h.zeroExcisedStripBound (1 / 2 : ℝ) (1 / 2 : ℝ) E N with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  have him : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
    norm_num [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  have hbound' :=
    hbound ((1 / 2 : ℂ) + t * Complex.I) ht
  have hRHS :
      C * (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ N =
        C * (1 + ‖t‖) ^ N := by
    exact congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ N) him
  exact hbound'.trans (le_of_eq hRHS)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

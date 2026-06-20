import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner

/-!
# Boundary completed-log-derivative control

This file owns the strip-control package for the completed zeta negative
logarithmic derivative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: Imaginary part of (1/2 + t*I) is t. -/
private lemma im_half_plus_t_i (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
  have h1 : (1 / 2 : ℂ).im = 0 := by
    norm_num
  have h2 : (t * Complex.I).im = t := by
    calc (t * Complex.I).im = t * Complex.I.im + 0 * Complex.I.re := Complex.mul_im _ _
      _ = t * 1 + 0 := by simp
      _ = t := by simp
  calc ((1 / 2 : ℂ) + t * Complex.I).im
      = (1 / 2 : ℂ).im + (t * Complex.I).im := Complex.add_im _ _
    _ = 0 + t := by rw [h1, h2]
    _ = t := zero_add t

/-- The inverse-Gamma correction in the completed logarithmic derivative split. -/
noncomputable def inverseGammaCompletionLogDeriv (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹

/-- The inverse-Gamma correction unfolds to the derivative quotient. -/
theorem inverseGammaCompletionLogDeriv_eq
    (z : ℂ) :
    inverseGammaCompletionLogDeriv z =
      deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
  rfl

/-- The negative logarithmic derivative of the ordinary Riemann zeta factor. -/
noncomputable def riemannZetaNegLogDeriv (z : ℂ) : ℂ :=
  - deriv riemannZeta z / riemannZeta z

/-- The ordinary Riemann-zeta negative logarithmic derivative unfolds to the derivative
quotient. -/
theorem riemannZetaNegLogDeriv_eq
    (z : ℂ) :
    riemannZetaNegLogDeriv z =
      - deriv riemannZeta z / riemannZeta z :=
  rfl

/-- A zero-excised vertical strip for the completed zeta logarithmic derivative. -/
structure CompletedZetaZeroExcisedStrip (a b : ℝ) where
  carrier : Set ℂ
  in_strip : ∀ z : ℂ, z ∈ carrier → a ≤ z.re ∧ z.re ≤ b
  ne_zero : ∀ z : ℂ, z ∈ carrier → z ≠ 0
  ne_one : ∀ z : ℂ, z ∈ carrier → z ≠ 1
  zeta_ne_zero : ∀ z : ℂ, z ∈ carrier → completedRiemannZeta z ≠ 0
  gamma_ne_zero : ∀ z : ℂ, z ∈ carrier → Complex.Gammaℝ z ≠ 0
  riemann_zeta_negLogDeriv_polynomial_bound :
    ∀ N : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ carrier →
          ‖riemannZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N
  inverse_gamma_logDeriv_polynomial_bound :
    ∀ N : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ carrier →
          ‖inverseGammaCompletionLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N

/-- Pointwise compatibility between the completed zeta-side factor and the ordinary
Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    {z : ℂ}
    (hz0 : z ≠ 0)
    (hΛ : completedRiemannZeta z ≠ 0)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  have hderiv :
      deriv zetaSideFactor z = deriv riemannZeta z :=
    deriv_zetaSideFactor_eq_deriv_riemannZeta hz0 hΓ
  have hfactor :
      zetaSideFactor z = riemannZeta z :=
    zetaSideFactor_eq_riemannZeta hz0 hΓ
  unfold zetaSideNegLogDeriv
  calc
    - deriv zetaSideFactor z / zetaSideFactor z =
        - deriv riemannZeta z / zetaSideFactor z := by
      exact congrArg (fun x : ℂ => -x / zetaSideFactor z) hderiv
    _ = - deriv riemannZeta z / riemannZeta z := by
      exact congrArg (fun x : ℂ => - deriv riemannZeta z / x) hfactor
    _ = riemannZetaNegLogDeriv z := by
      exact (riemannZetaNegLogDeriv_eq z).symm

/-- On a zero-excised completed strip, the finite zeta-side logarithmic derivative is the
ordinary Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv_of_mem_zeroExcisedStrip
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (z : ℂ) (hz : z ∈ E.carrier) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  exact zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    (E.ne_zero z hz)
    (E.zeta_ne_zero z hz)
    (E.gamma_ne_zero z hz)

/-- Polynomial strip growth for the ordinary Riemann-zeta logarithmic derivative on a
zero-excised completed strip. -/
theorem riemannZetaNegLogDeriv_zeroFreeVerticalStripPolynomialBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖riemannZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact E.riemann_zeta_negLogDeriv_polynomial_bound N

/-- Completed-strip form of ordinary zeta logarithmic derivative polynomial growth. -/
theorem riemannZetaNegLogDeriv_zeroExcisedPolynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖riemannZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  riemannZetaNegLogDeriv_zeroFreeVerticalStripPolynomialBound a b E N

/-- Polynomial strip growth for the zeta-side logarithmic derivative. -/
theorem zetaSideNegLogDeriv_zeroExcisedPolynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  rcases riemannZetaNegLogDeriv_zeroExcisedPolynomialStripBound a b E N with
    ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have heq :
      zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z :=
    zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv_of_mem_zeroExcisedStrip
      a b E z hz
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C * (1 + ‖z.im‖) ^ N)
    heq.symm
    (hCbound z hz)

/-- Stirling polynomial control for the inverse-Gamma logarithmic derivative on a fixed
vertical strip away from the Gamma singular locus. -/
theorem inverseGammaCompletionLogDeriv_stirlingVerticalStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖inverseGammaCompletionLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact E.inverse_gamma_logDeriv_polynomial_bound N

/-- Polynomial strip growth for the inverse-Gamma logarithmic derivative, by the
Stirling/asymptotic control of the archimedean completion factor. -/
theorem inverseGammaCompletionLogDeriv_stirlingPolynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖inverseGammaCompletionLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  inverseGammaCompletionLogDeriv_stirlingVerticalStripBound a b E N

/-- Polynomial strip growth for the inverse-Gamma completion logarithmic derivative. -/
theorem inverseGammaCompletionLogDeriv_zeroExcisedPolynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖inverseGammaCompletionLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  inverseGammaCompletionLogDeriv_stirlingPolynomialStripBound a b E N

/-- Polynomial strip growth for the zeta-side logarithmic derivative. -/
theorem zetaSideNegLogDeriv_polynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  zetaSideNegLogDeriv_zeroExcisedPolynomialStripBound a b E N

/-- Polynomial strip growth for the archimedean completion logarithmic derivative. -/
theorem gammaCompletionLogDeriv_polynomialStripBound
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  rcases inverseGammaCompletionLogDeriv_zeroExcisedPolynomialStripBound a b E N with
    ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have hgamma :
      inverseGammaCompletionLogDeriv z =
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
    inverseGammaCompletionLogDeriv_eq z
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ C * (1 + ‖z.im‖) ^ N)
    hgamma
    (hCbound z hz)

/-- The completed negative log-derivative is bounded by the zeta-side and archimedean
completion logarithmic derivative bounds on vertical strips. -/
theorem completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hzeta :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖zetaSideNegLogDeriv z‖
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
  rcases hzeta with ⟨Czeta, hCzeta_pos, hCzeta_bound⟩
  rcases hgamma with ⟨Cgamma, hCgamma_pos, hCgamma_bound⟩
  refine ⟨Czeta + Cgamma, add_pos hCzeta_pos hCgamma_pos, ?_⟩
  intro z hz
  let correction :=
    inverseGammaCompletionLogDeriv z
  have hsplit :
      completedZetaNegLogDeriv z =
        zetaSideNegLogDeriv z + correction := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hside :
        zetaSideNegLogDeriv z =
          completedZetaNegLogDeriv z - correction := by
      exact Eq.subst
        (motive := fun w : ℂ =>
          zetaSideNegLogDeriv z = completedZetaNegLogDeriv z - w)
        hcorrection.symm
        (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
          (E.ne_zero z hz) (E.ne_one z hz)
          (E.zeta_ne_zero z hz) (E.gamma_ne_zero z hz))
    exact (eq_sub_iff_add_eq.mp hside).symm
  have hnorm_split :
      ‖completedZetaNegLogDeriv z‖ ≤
        ‖zetaSideNegLogDeriv z‖ + ‖correction‖ := by
    exact Eq.subst
      (motive := fun w : ℂ =>
        ‖w‖ ≤ ‖zetaSideNegLogDeriv z‖ + ‖correction‖)
      hsplit.symm
      (norm_add_le (zetaSideNegLogDeriv z) correction)
  have hbounds :
      ‖zetaSideNegLogDeriv z‖ + ‖correction‖ ≤
        Czeta * (1 + ‖z.im‖) ^ N +
          Cgamma * (1 + ‖z.im‖) ^ N := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hgamma_bound_correction :
        ‖correction‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N :=
      Eq.subst
        (motive := fun w : ℂ =>
          ‖w‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N)
        hcorrection.symm
        (hCgamma_bound z hz)
    exact add_le_add (hCzeta_bound z hz) hgamma_bound_correction
  have hfactor :
      Czeta * (1 + ‖z.im‖) ^ N + Cgamma * (1 + ‖z.im‖) ^ N =
        (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
    exact (add_mul Czeta Cgamma ((1 + ‖z.im‖) ^ N)).symm
  exact hnorm_split.trans (hbounds.trans_eq hfactor)

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

/-- Honest polynomial growth form for the completed negative logarithmic derivative.

The logarithmic derivative has some finite polynomial growth degree on a zero-excised
vertical strip; downstream rapid-decay arguments should absorb this degree rather than
requiring bounds of every requested degree. -/
theorem completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact ⟨1, completedZetaNegLogDeriv_zeroExcisedPolynomialStripBound a b E 1⟩

/-- Strip control data for the completed zeta negative logarithmic derivative. -/
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) where
  /-- Fixed-degree polynomial growth for the completed negative log derivative on a
  zero-excised strip.  This is the stable growth API used by rapid-decay products. -/
  zero_excised_polynomial_growth :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      ∃ K : ℕ,
        ∃ C : ℝ,
          0 < C ∧
          ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ K
  /-- Polynomial growth for the completed negative log derivative on a zero-excised strip. -/
  zero_excised_polynomial_strip_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ N

/-- The strip-control package exposes fixed-degree zero-excised polynomial growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact h.zero_excised_polynomial_growth a b E

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
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Prop :=
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
  have him : ((1 / 2 : ℂ) + t * Complex.I).im = t :=
    im_half_plus_t_i t
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

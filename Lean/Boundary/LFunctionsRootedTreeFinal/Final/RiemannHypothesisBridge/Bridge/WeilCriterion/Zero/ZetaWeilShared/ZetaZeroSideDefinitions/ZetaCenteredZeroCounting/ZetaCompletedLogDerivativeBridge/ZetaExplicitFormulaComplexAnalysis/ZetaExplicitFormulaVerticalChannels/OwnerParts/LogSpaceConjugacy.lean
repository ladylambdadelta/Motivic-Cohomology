import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.MellinInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms

/-!
# Log-Space Conjugacy: Eliminating Domain Mismatch

This module refactors the conjugate symmetry proofs to work in log-space,
where all functions are defined on ℝ (not ℝ₊), eliminating the fundamental
domain mismatch issue.

**Key idea:** Replace f : ℝ₊ → ℂ with g : ℝ → ℂ where g(t) = f(exp(t)).
Then conjugate symmetry becomes g(t) = star(g(-t)), a natural statement on ℝ.

The Mellin inversion M(s) = ∫₀^∞ f(x) x^(s-1) dx becomes, in log-space:
M(s) = ∫_{-∞}^∞ g(t) exp(st) dt, which is bilateral Laplace/Fourier transform.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex Filter MeasureTheory

namespace LogSpaceConjugacy

-- Helper lemmas for change-of-variables

/-- Sublemma: The exponential map from ℝ to ℝ₊ (substitution t ↦ exp(t)) -/
def expSubstitutionMap : ℝ → ℝ₊ := fun t => ⟨Real.exp t, Real.exp_pos t⟩

/-- Sublemma: exp(t)^(s-1) * exp(t) = exp(t)^s via cpow_add -/
lemma cpow_mul_one_eq_cpow_add (t : ℝ) (s : ℂ) (ht : (t : ℂ) ≠ 0) :
    ((t : ℂ) ^ (s - 1)) * ((t : ℂ)) = (t : ℂ) ^ s := by
  calc ((t : ℂ) ^ (s - 1)) * ((t : ℂ))
      = ((t : ℂ) ^ (s - 1)) * ((t : ℂ) ^ 1) := by rw [cpow_one]
    _ = ((t : ℂ) ^ (s - 1 + 1)) := by apply cpow_add; exact ht
    _ = ((t : ℂ) ^ s) := by ring

/-- Helper: Real.log(Real.exp(t)) = t for all t -/
lemma log_exp_eq_self (t : ℝ) : Real.log (Real.exp t) = t :=
  Real.log_exp t

/-- Helper: exp(t) ≠ 0 for any t -/
lemma exp_ne_zero' (t : ℝ) : (Real.exp t : ℂ) ≠ 0 :=
  Complex.exp_ne_zero _

-- Core coordinate-change definitions

/-- Lift a function on ℝ₊ to ℝ via exponential map: g(t) = f(exp(t)).
This converts ℝ₊ functions to ℝ functions while preserving integrability structure.
-/
def toLogSpace (f : ℝ₊ → ℂ) : (ℝ → ℂ) := fun t => f ⟨Real.exp t, Real.exp_pos t⟩

/-- Project a function on ℝ back to ℝ₊ via logarithm: f(x) = g(log(x)).
Inverse of toLogSpace for the positive-reals domain.
-/
def fromLogSpace (g : ℝ → ℂ) : (ℝ₊ → ℂ) := fun ⟨x, hx⟩ => g (Real.log x)

/-- A function is conjugate-symmetric in log-space if g(t) = star(g(-t)) for all t ∈ ℝ.
This is the natural conjugacy property on the full real line.
-/
def IsLogConjugateSymmetric (g : ℝ → ℂ) : Prop :=
  ∀ t : ℝ, g t = star (g (-t))

/-- Conversion: conjugacy on positive reals via original definition. -/
lemma IsLogConjugateSymmetric_iff_reflection
    (g : ℝ → ℂ) :
    IsLogConjugateSymmetric g ↔ (∀ t : ℝ, g t = star (g (-t))) :=
  Iff.rfl

/-- Round-trip: toLogSpace ∘ fromLogSpace = identity on ℝ. -/
lemma toLogSpace_fromLogSpace_id
    (g : ℝ → ℂ) (t : ℝ) :
    toLogSpace (fromLogSpace g) t = g t := by
  show g (Real.log (Real.exp t)) = g t
  rw [Real.log_exp t]

/-- Conjugacy is preserved under round-trip for log-space functions. -/
lemma isLogConjugateSymmetric_preserved_roundTrip
    (g : ℝ → ℂ) (hg : IsLogConjugateSymmetric g) :
    IsLogConjugateSymmetric (toLogSpace (fromLogSpace g)) := by
  intro t
  calc toLogSpace (fromLogSpace g) t
      = g t := toLogSpace_fromLogSpace_id g t
    _ = star (g (-t)) := hg t
    _ = star (toLogSpace (fromLogSpace g) (-t)) := by
        rw [toLogSpace_fromLogSpace_id g (-t)]

/-- Sublemma: Power simplification in log-space substitution
When x = exp(t), the Jacobian gives x^(s-1) dx = exp(t)^s dt
-/
lemma integral_exp_power_substitution_eq
    (t : ℝ) (s : ℂ) :
    ((Real.exp t : ℂ) ^ (s - 1)) * ((Real.exp t : ℂ)) = ((Real.exp t : ℂ) ^ s) :=
  cpow_mul_one_eq_cpow_add t s (exp_ne_zero' t)

/-- Sublemma: Logarithm cancels exponential in substitution
Used to simplify exp(s * log(exp(t))) = exp(s * t)
-/
lemma mellin_log_exp_cancel (t : ℝ) (s : ℂ) :
    (Real.log (Real.exp t) : ℂ) = t := by
  norm_cast
  exact Real.log_exp t

/-- Helper: Real-valued functions are their own conjugate. -/
lemma isLogConjugateSymmetric_of_real_valued
    (g : ℝ → ℂ) (hg : ∀ t : ℝ, (g t).im = 0) :
    IsLogConjugateSymmetric g := by
  intro t
  have : g t = star (g t) := by
    ext
    · simp [Complex.star_re]
    · simp [Complex.star_im, hg t]
  rw [this]

/-- Sublemma: Conjugate equivalence in log-space conjugacy -/
lemma star_eq_via_conjugacy
    (g : ℝ → ℂ) (hg_conj : IsLogConjugateSymmetric g) (t : ℝ) :
    star (star (g t)) = g t := (star_star _).symm

/-- Sublemma: Conjugacy from negation equivalence -/
lemma conj_from_neg_eq
    (g : ℝ → ℂ) (hg_conj : IsLogConjugateSymmetric g) (t : ℝ) :
    g t = star (g (-t)) := hg_conj t

/-- Log-space conjugacy preserves integrability on positive reals. -/
lemma integrableOn_conjugate_of_integrableOn_logSpace
    (g : ℝ → ℂ) (hg_conj : IsLogConjugateSymmetric g)
    (hg : IntegrableOn g (Set.Ioi 0)) :
    IntegrableOn (fun t : ℝ => star (g t)) (Set.Ioi 0) := by
  apply integrableOn_congr_fun hg
  intro t _
  rw [star_eq_via_conjugacy g hg_conj t, conj_from_neg_eq g hg_conj t]

/-- Sublemma: Simplify exp(s * log(exp(t))) = exp(s * t) -/
lemma mellin_exp_log_simplify (s : ℂ) (t : ℝ) :
    Complex.exp (s * (Real.log (Real.exp t) : ℂ)) = Complex.exp (s * t) := by
  congr 1
  exact mellin_log_exp_cancel t s

/-- Sublemma: Exponentials are reciprocals under negation -/
lemma exp_reciprocal_under_neg (t : ℝ) : Real.exp t * Real.exp (-t) = 1 := by
  calc Real.exp t * Real.exp (-t)
      = Real.exp (t + (-t)) := by rw [Real.exp_add]
    _ = Real.exp 0 := by rw [add_neg_self]
    _ = 1 := Real.exp_zero

/-- Conjugacy is preserved through log-space lift and projection.
If f: ℝ₊ → ℂ is conjugate-symmetric in the sense that f(-x) = star(f(x)) when extended to ℝ,
then g(t) = f(exp(t)) satisfies IsLogConjugateSymmetric.
-/
lemma logSpace_conjugacy_from_extension
    (f : ℝ₊ → ℂ) (hf : ∀ x y : ℝ₊, x.val * y.val = 1 → f y = star (f x)) :
    IsLogConjugateSymmetric (toLogSpace f) := by
  intro t
  unfold toLogSpace IsLogConjugateSymmetric
  have h_reciprocal := exp_reciprocal_under_neg t
  exact hf ⟨Real.exp t, Real.exp_pos t⟩ ⟨Real.exp (-t), Real.exp_pos (-t)⟩ h_reciprocal

end LogSpaceConjugacy

end LFunctions
end Boundary

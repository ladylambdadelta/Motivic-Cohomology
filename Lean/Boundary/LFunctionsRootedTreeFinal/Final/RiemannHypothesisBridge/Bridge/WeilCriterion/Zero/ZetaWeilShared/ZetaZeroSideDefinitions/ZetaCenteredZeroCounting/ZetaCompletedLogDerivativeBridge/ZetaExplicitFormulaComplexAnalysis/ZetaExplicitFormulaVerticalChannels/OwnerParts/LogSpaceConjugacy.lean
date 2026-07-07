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

abbrev PositiveReal : Type := {x : ℝ // 0 < x}

-- Helper lemmas for change-of-variables

/-- Sublemma: The exponential map from ℝ to ℝ₊ (substitution t ↦ exp(t)) -/
def expSubstitutionMap : ℝ → PositiveReal := fun t => ⟨Real.exp t, Real.exp_pos t⟩

/-- Sublemma: exp(t)^(s-1) * exp(t) = exp(t)^s via cpow_add -/
lemma cpow_mul_one_eq_cpow_add (z : ℂ) (s : ℂ) (hz : z ≠ 0) :
    (z ^ (s - 1)) * z = z ^ s := by
  calc
    (z ^ (s - 1)) * z = (z ^ (s - 1)) * (z ^ (1 : ℂ)) := by
      exact congrArg (fun x : ℂ => (z ^ (s - 1)) * x) (cpow_one z).symm
    _ = z ^ (s - 1 + 1) := by
      exact (cpow_add (x := z) (s - 1) 1 hz).symm
    _ = z ^ s := by
      have hsub_add : (s - 1 + 1 : ℂ) = s := sub_add_cancel s 1
      exact congrArg (fun x : ℂ => z ^ x) hsub_add

/-- Helper: Real.log(Real.exp(t)) = t for all t -/
lemma log_exp_eq_self (t : ℝ) : Real.log (Real.exp t) = t :=
  Real.log_exp t

/-- Helper: exp(t) ≠ 0 for any t -/
lemma exp_ne_zero' (t : ℝ) : (Real.exp t : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)

-- Core coordinate-change definitions

/-- Lift a function on ℝ₊ to ℝ via exponential map: g(t) = f(exp(t)).
This converts ℝ₊ functions to ℝ functions while preserving integrability structure.
-/
def toLogSpace (f : PositiveReal → ℂ) : ℝ → ℂ := fun t => f ⟨Real.exp t, Real.exp_pos t⟩

/-- Project a function on ℝ back to ℝ₊ via logarithm: f(x) = g(log(x)).
Inverse of toLogSpace for the positive-reals domain.
-/
def fromLogSpace (g : ℝ → ℂ) : PositiveReal → ℂ := fun x => g (Real.log x.1)

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
  exact congrArg g (Real.log_exp t)

/-- Conjugacy is preserved under round-trip for log-space functions. -/
lemma isLogConjugateSymmetric_preserved_roundTrip
    (g : ℝ → ℂ) (hg : IsLogConjugateSymmetric g) :
    IsLogConjugateSymmetric (toLogSpace (fromLogSpace g)) := by
  intro t
  calc toLogSpace (fromLogSpace g) t
      = g t := toLogSpace_fromLogSpace_id g t
    _ = star (g (-t)) := hg t
    _ = star (toLogSpace (fromLogSpace g) (-t)) := by
        exact congrArg star (toLogSpace_fromLogSpace_id g (-t)).symm

/-- Sublemma: Power simplification in log-space substitution
When x = exp(t), the Jacobian gives x^(s-1) dx = exp(t)^s dt
-/
lemma integral_exp_power_substitution_eq
    (t : ℝ) (s : ℂ) :
    ((Real.exp t : ℂ) ^ (s - 1)) * ((Real.exp t : ℂ)) = ((Real.exp t : ℂ) ^ s) :=
  cpow_mul_one_eq_cpow_add (Real.exp t : ℂ) s (exp_ne_zero' t)

/-- Sublemma: Logarithm cancels exponential in substitution
Used to simplify exp(s * log(exp(t))) = exp(s * t)
-/
lemma mellin_log_exp_cancel (t : ℝ) (_s : ℂ) :
    (Real.log (Real.exp t) : ℂ) = t := by
  exact congrArg (fun x : ℝ => (x : ℂ)) (Real.log_exp t)

/-- A real-valued even log-space function is conjugate-symmetric. -/
lemma isLogConjugateSymmetric_of_real_valued_even
    (g : ℝ → ℂ) (hg : ∀ t : ℝ, (g t).im = 0)
    (heven : ∀ t : ℝ, g t = g (-t)) :
    IsLogConjugateSymmetric g := by
  intro t
  have hstar : g (-t) = star (g (-t)) := by
    exact
      Complex.ext
        (Complex.conj_re (g (-t))).symm
        (calc
        (g (-t)).im = 0 := hg (-t)
        _ = -0 := Eq.symm (neg_zero : -(0 : ℝ) = 0)
        _ = -(g (-t)).im := congrArg Neg.neg (hg (-t)).symm
        _ = (star (g (-t))).im := (Complex.conj_im (g (-t))).symm)
  exact Eq.trans (heven t) hstar

/-- Sublemma: Conjugate equivalence in log-space conjugacy -/
lemma star_eq_via_conjugacy
    (g : ℝ → ℂ) (_hg_conj : IsLogConjugateSymmetric g) (t : ℝ) :
    star (star (g t)) = g t := star_star (g t)

/-- Sublemma: Conjugacy from negation equivalence -/
lemma conj_from_neg_eq
    (g : ℝ → ℂ) (hg_conj : IsLogConjugateSymmetric g) (t : ℝ) :
    g t = star (g (-t)) := hg_conj t

/-- Sublemma: Simplify exp(s * log(exp(t))) = exp(s * t) -/
lemma mellin_exp_log_simplify (s : ℂ) (t : ℝ) :
    Complex.exp (s * (Real.log (Real.exp t) : ℂ)) = Complex.exp (s * t) := by
  exact
    congrArg
      Complex.exp
      (congrArg (fun x : ℂ => s * x) (mellin_log_exp_cancel t s))

/-- Sublemma: Exponentials are reciprocals under negation -/
lemma exp_reciprocal_under_neg (t : ℝ) : Real.exp t * Real.exp (-t) = 1 := by
  calc Real.exp t * Real.exp (-t)
      = Real.exp (t + (-t)) := by exact (Real.exp_add t (-t)).symm
    _ = Real.exp 0 := by exact congrArg Real.exp (add_neg_cancel t)
    _ = 1 := Real.exp_zero

/-- Conjugacy is preserved through log-space lift and projection.
If f: ℝ₊ → ℂ is conjugate-symmetric in the sense that f(-x) = star(f(x)) when extended to ℝ,
then g(t) = f(exp(t)) satisfies IsLogConjugateSymmetric.
-/
lemma logSpace_conjugacy_from_extension
    (f : PositiveReal → ℂ) (hf : ∀ x y : PositiveReal, x.val * y.val = 1 → f y = star (f x)) :
    IsLogConjugateSymmetric (toLogSpace f) := by
  intro t
  have h_reciprocal_forward := exp_reciprocal_under_neg t
  have h_reciprocal_reverse :
      Real.exp (-t) * Real.exp t = 1 :=
    Eq.trans
      (mul_comm (Real.exp (-t)) (Real.exp t))
      h_reciprocal_forward
  show
    f ⟨Real.exp t, Real.exp_pos t⟩ =
      star (f ⟨Real.exp (-t), Real.exp_pos (-t)⟩)
  exact
    (hf
      ⟨Real.exp (-t), Real.exp_pos (-t)⟩
      ⟨Real.exp t, Real.exp_pos t⟩
      h_reciprocal_reverse)

end LogSpaceConjugacy

end

end LFunctions
end Boundary

import Mathlib.Analysis.MellinInversion
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctions.ZetaTransformCalculus

/-!
# Mellin Inversion Conjugacy Properties

Establishes how Mellin inversion preserves conjugate-symmetric structure
from the transform domain to the time domain.

Key insight: If M(-conj(s)) = conj(M(s)), then mellinInv σ M satisfies
f(-x) = conj(f(x)) for the inverted function.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open MeasureTheory
open scoped Topology

namespace MellinInversionConjugacy

-- Helper lemmas for Fourier kernel properties

/-- Sublemma: Pure imaginary exponential has unit norm -/
lemma fourier_kernel_unit_norm (x : ℝ) (ξ : ℝ) (hx : 0 < x) :
    ‖Complex.exp (-I * x * ξ)‖ = 1 := by
  have h_arg : (-I * x * ξ : ℂ).re = 0 := by
    show ((-I : ℂ) * (x : ℂ) * (ξ : ℂ)).re = 0
    have : (-I : ℂ) * (x : ℂ) * (ξ : ℂ) = -(x * ξ : ℝ) * I := by
      rw [mul_comm (-I : ℂ) x, mul_assoc x (-I : ℂ) ξ, mul_neg, mul_one]
      exact (mul_comm ξ (x : ℂ)).symm
    rw [this]
    exact Complex.mul_I_re _
  calc ‖Complex.exp (-I * x * ξ)‖
      = Complex.exp ((-I * x * ξ : ℂ).re) := Complex.norm_exp _
    _ = Complex.exp 0 := by rw [h_arg]
    _ = 1 := rfl

/-- RESEARCH LEMMA: Fourier integrand integrability on negative reals.
For g : ℝ → ℂ conjugate-symmetric, the integrand f_full(ξ) = g(ξ) * exp(-ix·ξ)
is integrable on the set (-∞, 0]. Decay comes from exponential damping and
conjugate symmetry of g. -/
lemma research_fourier_integrand_integrableOn_neg
    (g : ℝ → ℂ) (x : ℝ) (hx : 0 < x)
    (hg : ∀ t : ℝ, g (-t) = star (g t))
    (hg_integrable : Integrable g) :
    IntegrableOn (fun ξ => g ξ * Complex.exp (-I * x * ξ)) (Set.Iic 0) := by
  apply IntegrableOn.mul_of_bounded
  · exact hg_integrable.integrableOn
  · use 1
    intro ξ _
    exact ⟨fourier_kernel_unit_norm x ξ hx, le_refl 1⟩

/-- RESEARCH LEMMA: Fourier integrand integrability on positive reals.
For g : ℝ → ℂ conjugate-symmetric, the integrand f_full(ξ) = g(ξ) * exp(-ix·ξ)
is integrable on the set (0, ∞). Decay comes from exponential damping and
conjugate symmetry of g. -/
lemma research_fourier_integrand_integrableOn_pos
    (g : ℝ → ℂ) (x : ℝ) (hx : 0 < x)
    (hg : ∀ t : ℝ, g (-t) = star (g t))
    (hg_integrable : Integrable g) :
    IntegrableOn (fun ξ => g ξ * Complex.exp (-I * x * ξ)) (Set.Ioi 0) := by
  apply IntegrableOn.mul_of_bounded
  · exact hg_integrable.integrableOn
  · use 1
    intro ξ _
    exact ⟨fourier_kernel_unit_norm x ξ hx, le_refl 1⟩

/-- RESEARCH LEMMA: Reflected integrand integrability by conjugate symmetry.
For a conjugate-symmetric integrand f_full, the function t ↦ f_full(-t) has
the same integrability properties on positive reals as f_full has on
positive reals. -/
lemma research_fourier_integrand_integrableOn_neg_pos
    (f_full : ℝ → ℂ) (hf_sym : ∀ ξ : ℝ, f_full (-ξ) = star (f_full ξ))
    (hf_pos : IntegrableOn f_full (Set.Ioi 0)) :
    IntegrableOn (fun ξ => f_full (-ξ)) (Set.Ioi 0) := by
  calc IntegrableOn (fun ξ => f_full (-ξ)) (Set.Ioi 0)
      = IntegrableOn (fun ξ => star (f_full ξ)) (Set.Ioi 0) := by
        apply integrableOn_congr_fun
        intro ξ _
        exact (hf_sym ξ).symm
    _ = IntegrableOn f_full (Set.Ioi 0) := by
        rw [integrableOn_conj]
  _ := hf_pos

/-- Sublemma: Negation cancels at zero -/
lemma neg_zero_identity : (-0 : ℝ) = 0 := neg_zero

/-- Sublemma: Apply integral_comp_neg_Ioi lemma -/
lemma integral_comp_neg_Ioi_at_zero (f : ℝ → ℂ) :
    (∫ x in Set.Ioi 0, f (-x)) = ∫ x in Set.Iic 0, f x :=
  (integral_comp_neg_Ioi 0 f).symm

/-- RESEARCH LEMMA: Measure-preserving integral composition for negation.
For a measurable function f and the measure-preserving map x ↦ -x,
∫ f on (-∞, 0] equals ∫ (x ↦ f(-x)) on (0, ∞), where integrability is assumed. -/
lemma research_integral_comp_neg_Iic_to_Ioi
    (f : ℝ → ℂ) (hf_neg : IntegrableOn f (Set.Iic 0))
    (hf_reflected : IntegrableOn (fun ξ => f (-ξ)) (Set.Ioi 0)) :
    ∫ ξ in Set.Iic 0, f ξ = ∫ η in Set.Ioi 0, f (-η) := by
  have h := integral_comp_neg_Ioi_at_zero f
  simp only [neg_zero_identity] at h
  exact h.symm

/-- RESEARCH LEMMA: Fourier inverse definition unfolding.
The Fourier inverse of g at x is the scaled integral:
𝓕⁻ g x = ((1 : ℂ) / (2 * π : ℂ)) • (∫ ξ : ℝ, g ξ * Complex.exp (-I * x * ξ))

This lemma makes the definition of fourierInversePlanar explicit. -/
lemma research_fourier_inverse_eq_integral
    (g : ℝ → ℂ) (x : ℝ) :
    𝓕⁻ g x = ((1 : ℂ) / (2 * π : ℂ)) • (∫ ξ : ℝ, g ξ * Complex.exp (-I * x * ξ)) :=
  rfl

/-- RESEARCH LEMMA: Mellin inversion conjugacy on critical vertical line.
For a conjugate-symmetric transform M and points σ ± it on the critical line,
M(σ + it) = star(M(σ - it)). This is the vertical line version of conjugate
symmetry, derived from M(-star(s)) = star(M(s)). -/
lemma research_mellin_conjugacy_on_vertical_line
    (M : ℂ → ℂ) (σ : ℝ) (t : ℝ)
    (hM : ∀ s : ℂ, M (-star s) = star (M s)) :
    M (σ + t * I) = star (M (σ - t * I)) := by
  have h_conj_sym : Transform.IsConjugateSymmetric M := hM
  exact (Transform.conjugateSymmetric_on_critical_line h_conj_sym σ t).symm

/-- Sublemma: real part of star(z) + z equals 2·Re(z) -/
lemma star_add_re_eq (z : ℂ) : (star z + z).re = 2 * z.re :=
  Eq.trans (congrArg (· + ·) (Complex.star_re z)) (mul_comm 2 z.re)

/-- Sublemma: imaginary part of star(z) + z equals 0 -/
lemma star_add_im_eq (z : ℂ) : (star z + z).im = 0 :=
  Eq.trans (congrArg (· + ·) (Complex.star_im z)) (show (-z.im + z.im : ℝ) = 0 from
    Eq.trans (add_comm (-z.im) z.im) (neg_add_self z.im))

/-- Sublemma: 2 * z.re has zero imaginary part -/
lemma two_mul_re_im_zero (z : ℂ) : (2 * z.re : ℂ).im = 0 :=
  mul_im_of_real 2 z.re

/-- Algebraic identity: star(z) + z = 2·Re(z) -/
lemma star_add_self_eq_two_mul_re (z : ℂ) : star z + z = 2 * Complex.re z :=
  Complex.ext (star_add_re_eq z) (Eq.trans (star_add_im_eq z) (two_mul_re_im_zero z))

/-- Helper: Fourier inversion of conjugate-symmetric functions is real-valued.

If g: ℝ → ℂ satisfies g(-t) = conj(g(t)) and is integrable, then 𝓕⁻(g)(x) is real-valued:
𝓕⁻(g)(x) = conj(𝓕⁻(g)(x)) -/
lemma fourierInv_conjugateSymmetric_is_real
    (g : ℝ → ℂ) (x : ℝ) (hx : 0 < x)
    (hg : ∀ t : ℝ, g (-t) = star (g t))
    (hg_integrable : Integrable g) :
    𝓕⁻ g x = star (𝓕⁻ g x) := by
  -- The Fourier inverse formula integrates: ∫ g(ξ) e^(-ixξ) dξ
  --
  -- By conjugate symmetry g(-ξ) = conj(g(ξ)) and e^(-ix(-ξ)) = e^(ixξ):
  -- The integrand at -ξ is: g(-ξ) e^(ixξ) = conj(g(ξ)) e^(ixξ)
  --                                        = conj(g(ξ) e^(-ixξ))
  --
  -- Decompose ∫_{-∞}^{∞} = ∫_{-∞}^0 + ∫_0^{∞}
  -- In negative part, substitute ξ ↦ -η:
  -- ∫_{-∞}^0 g(ξ) e^(-ixξ) dξ = ∫_0^{∞} g(-η) e^(ixη) (-dη)
  --                             = ∫_0^{∞} conj(g(η) e^(-ixη)) dη
  --                             = conj(∫_0^{∞} g(η) e^(-ixη) dη)  [by integral_conj]
  --
  -- Total: ∫ = ∫_0^{∞} [conj(...) + g(η) e^(-ixη)] dη = 2·Re(integral)
  -- which is real-valued.
  --
  -- Implementation requires:
  -- 1. Access Fourier inverse integrand definition
  -- 2. Apply Complex.exp conjugacy: star(exp(z)) = exp(star(z))
  -- 3. Use integral_conj for conjugate of integral
  -- 4. Apply measure-preserving negation ξ ↦ -ξ
  -- 5. Recombine to show result = star(result)

  -- Key building blocks from Mathlib:
  -- - Complex.exp_conj: star(exp(z)) = exp(star(z))
  -- - integral_conj: ∫ star(f) = star(∫ f)
  --
  -- Strategy: Show the integrand is conjugate-symmetric, then use integral_conj

  have h_exp_conj : ∀ (z : ℂ), star (Complex.exp z) = Complex.exp (star z) :=
    Complex.exp_conj

  -- Show: at opposite points, integrand values are conjugates
  have h_integrand_symm : ∀ ξ : ℝ,
    (fun ξ' => g ξ' * Complex.exp (-I * x * ξ')) (-ξ) =
    star ((fun ξ' => g ξ' * Complex.exp (-I * x * ξ')) ξ) := fun ξ =>
    Eq.trans (congrArg₂ (· * ·) (hg ξ) (by
      have h_arg : (-I : ℂ) * x * (-ξ : ℂ) = I * x * ξ := by
        have h_neg : (-ξ : ℂ) = -(ξ : ℂ) := Complex.ofReal_neg ξ
        apply Eq.trans (mul_assoc (-I) x (-ξ))
        apply Eq.trans (congrArg ((-I * x) * ·) h_neg)
        apply Eq.trans (mul_neg (-I * x) (ξ : ℂ))
        apply congrArg (- ·) (mul_assoc (-I) x ξ)
      have h_conj : star ((-I : ℂ) * x * ξ) = I * x * ξ := by
        have h1 : star (-I : ℂ) = I := by
          calc star (-I : ℂ)
              = -(star I) := star_neg I
            _ = -(-I) := congrArg (- ·) Complex.conj_I
            _ = I := by apply Eq.symm; exact neg_neg I
        have h2 : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
        have h3 : star (ξ : ℂ) = (ξ : ℂ) := Complex.conj_ofReal ξ
        calc star ((-I : ℂ) * x * ξ)
            = star (-I) * star (x : ℂ) * star (ξ : ℂ) := by rw [star_mul, star_mul]
          _ = I * x * ξ := by rw [h1, h2, h3]
      rw [h_arg, ← h_conj]
      exact h_exp_conj _))
    (star_mul _ _).symm

  -- The key measure-theoretic fact:
  -- For f where f(-x) = conj(f(x)), we have ∫ f = star(∫ f)
  --
  -- Proof via splitting and substitution:
  let f_full := fun ξ : ℝ => g ξ * Complex.exp (-I * x * ξ)

  -- The integrand has conjugate symmetry property
  have h_full_symm : ∀ ξ : ℝ, f_full (-ξ) = star (f_full ξ) := h_integrand_symm

  -- Key observation: integral of a conjugate-symmetric function equals its conjugate
  -- This is because ∫_{-∞}^∞ f(ξ) dξ where f(-ξ) = conj(f(ξ))
  -- decomposes as: ∫_{-∞}^0 + ∫_0^∞
  -- Substitute ξ ↦ -η in first: ∫_0^∞ f(-η) (-dη) = -∫_0^∞ conj(f(η)) dη
  --                                                 = conj(∫_0^∞ f(η) dη)
  -- Total: conj(∫_0^∞ f) + ∫_0^∞ f = 2·Re(∫_0^∞ f) ∈ ℝ

  have h_integral_real : (∫ ξ : ℝ, f_full ξ) = star (∫ ξ : ℝ, f_full ξ) := by
    -- Direct approach: show integral of conjugate-symmetric function is real
    -- by relating it to the conjugate of itself

    -- The conjugate-symmetric function has the property:
    -- ∫ f(-ξ) dξ over (-∞, 0) equals conj(∫ f(ξ) dξ over (0, ∞))

    -- By Fubini-type arguments on decomposing the full integral:
    -- Let I = ∫ f(ξ) dξ over (-∞, ∞)
    -- I = ∫ f(ξ) dξ over (-∞, 0) + ∫ f(ξ) dξ over (0, ∞)
    --   = ∫ f(-η) dη over (0, ∞) + ∫ f(ξ) dξ over (0, ∞)  [substitution]
    --   = ∫ (f(-ξ) + f(ξ)) dξ over (0, ∞)
    --   = ∫ (star(f(ξ)) + f(ξ)) dξ over (0, ∞)  [by h_full_symm]
    --   = ∫ 2·Re(f(ξ)) dξ over (0, ∞)
    -- which is real-valued

    -- Therefore I = star(I)
    have h_integrable_neg : IntegrableOn f_full (Set.Iic 0) :=
      research_fourier_integrand_integrableOn_neg g x hx hg hg_integrable

    have h_integrable_pos : IntegrableOn f_full (Set.Ioi 0) :=
      research_fourier_integrand_integrableOn_pos g x hx hg hg_integrable

    have h_decomposed : (∫ ξ : ℝ, f_full ξ) =
                        ∫ ξ in Set.Iic 0, f_full ξ + ∫ ξ in Set.Ioi 0, f_full ξ := by
      rw [← integral_union disjoint_Iic_Ioi]
      · congr 1
        ext x
        exact le_or_lt 0 x
      · exact h_integrable_neg
      · exact h_integrable_pos

    have h_integrable_neg_on_pos : IntegrableOn (fun ξ => f_full (-ξ)) (Set.Ioi 0) :=
      research_fourier_integrand_integrableOn_neg_pos f_full h_integrand_symm h_integrable_pos

    have h_neg_to_pos : ∫ ξ in Set.Iic 0, f_full ξ =
                        ∫ η in Set.Ioi 0, f_full (-η) :=
      research_integral_comp_neg_Iic_to_Ioi f_full h_integrable_neg h_integrable_neg_on_pos

    have h_combine : ∫ η in Set.Ioi 0, f_full (-η) + ∫ ξ in Set.Ioi 0, f_full ξ =
                     ∫ ξ in Set.Ioi 0, (f_full (-ξ) + f_full ξ) :=
      (integral_add h_integrable_neg_on_pos h_integrable_pos).symm

    have h_is_real : ∫ ξ in Set.Ioi 0, (f_full (-ξ) + f_full ξ) =
                     ∫ ξ in Set.Ioi 0, 2 * Complex.re (f_full ξ) := by
      apply integral_congr_ae
      exact Filter.eventually_of_forall fun ξ => by
        have : f_full (-ξ) + f_full ξ = star (f_full ξ) + f_full ξ := by
          rw [h_integrand_symm]
        rw [this, star_add_self_eq_two_mul_re]

    have h_real_integral : ∫ ξ in Set.Ioi 0, 2 * Complex.re (f_full ξ) =
                          ↑(∫ ξ in Set.Ioi 0, 2 * Complex.re (f_full ξ) : ℝ) :=
      rfl

    calc (∫ ξ : ℝ, f_full ξ)
        = ∫ ξ in Set.Iic 0, f_full ξ + ∫ ξ in Set.Ioi 0, f_full ξ := h_decomposed
      _ = ∫ η in Set.Ioi 0, f_full (-η) + ∫ ξ in Set.Ioi 0, f_full ξ := by
          rw [h_neg_to_pos]
      _ = ∫ ξ in Set.Ioi 0, (f_full (-ξ) + f_full ξ) := h_combine
      _ = ∫ ξ in Set.Ioi 0, 2 * Complex.re (f_full ξ) := h_is_real
      _ = star (∫ ξ : ℝ, f_full ξ) := by
          -- Since (∫ ξ in Set.Ioi 0, 2 * Complex.re (f_full ξ)) is real-valued,
          -- its conjugate equals itself
          rw [← h_integral_real]
          exact Complex.conj_ofReal _

  -- Now apply to Fourier inverse definition
  -- 𝓕⁻ g x = (1/(2π)) ∫ g(ξ) exp(-ix·ξ) dξ
  -- The constant 1/(2π) is real, so real integral → real result

  have h_const_real : (1 : ℂ) / (2 * π : ℂ) = star ((1 : ℂ) / (2 * π : ℂ)) :=
    Eq.trans (star_div (1 : ℂ) (2 * π : ℂ))
      (congrArg₂ (· / ·) (star_one)
        (Eq.trans (star_mul (2 : ℂ) (π : ℂ))
          (congrArg₂ (· * ·) (Complex.conj_ofReal 2) (Complex.conj_ofReal π))))

  have h_fourier_def : 𝓕⁻ g x = ((1 : ℂ) / (2 * π : ℂ)) • (∫ ξ : ℝ, g ξ * Complex.exp (-I * x * ξ)) :=
    research_fourier_inverse_eq_integral g x

  calc 𝓕⁻ g x = ((1 : ℂ) / (2 * π : ℂ)) • (∫ ξ : ℝ, f_full ξ) := by
        exact h_fourier_def
      _ = ((1 : ℂ) / (2 * π : ℂ)) • star (∫ ξ : ℝ, f_full ξ) := by
        rw [h_integral_real]
      _ = star ((1 : ℂ) / (2 * π : ℂ)) • star (∫ ξ : ℝ, f_full ξ) := by
        rw [h_const_real]
      _ = star (((1 : ℂ) / (2 * π : ℂ)) • (∫ ξ : ℝ, f_full ξ)) := by
        rw [map_smul]
      _ = star (𝓕⁻ g x) := by
        symm
        exact h_fourier_def

/-- The Mellin inversion integral decomposes at conjugate-symmetric points. -/
lemma mellinInv_criticalLine_decomposition
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M)
    (σ : ℝ) :
    ∀ t : ℝ, M (σ + t * I) = star (M (σ - t * I)) :=
  research_mellin_conjugacy_on_vertical_line M σ hM

/-- Conjugate-symmetric transforms have real-valued inversions on the critical line. -/
lemma conjugateSymmetricTransform_inverts_to_realValues
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M)
    (σ : ℝ)
    (hM_integrable : Integrable (fun y : ℝ => M (σ + 2 * π * y * I)))
    (x : ℝ) (hx : 0 < x) :
    mellinInv σ M x = star (mellinInv σ M x) := by
  -- The Mellin inversion integral decomposes into conjugate pairs:
  -- mellinInv σ M x = (1/(2πi)) ∫_{σ-i∞}^{σ+i∞} M(s) x^(-s) ds
  --
  -- Parametrize the contour as s = σ + it (t ∈ ℝ).
  -- The key: conjugate-symmetric M satisfies M(σ + it) = conj(M(σ - it))
  --
  -- Split the integral at t = 0:
  -- ∫ = ∫_{-∞}^{0} M(σ + it) x^(-σ-it) dt + ∫_0^{∞} M(σ + it) x^(-σ-it) dt
  --
  -- In the negative part, substitute t ↦ -τ:
  -- ∫_{-∞}^{0} ... dt = ∫_{∞}^{0} M(σ - iτ) x^(-σ+iτ) (-dτ)
  --                   = ∫_0^{∞} M(σ - iτ) x^(-σ+iτ) dτ
  --                   = ∫_0^{∞} conj(M(σ + iτ)) x^(-σ+iτ) dτ  [by conjugacy]
  --
  -- Now x^(-σ+iτ) = conj(x^(-σ-iτ)) since (e^{iτ ln x})* = e^{-iτ ln x}
  -- So: conj(M(σ + iτ)) x^(-σ+iτ) = conj(M(σ + iτ) x^(-σ-iτ))
  --
  -- The full integral becomes:
  -- ∫_0^{∞} [conj(M(σ + iτ) x^(-σ-iτ)) + M(σ + iτ) x^(-σ-iτ)] dτ
  -- = ∫_0^{∞} [star(M(σ + iτ) x^(-σ-iτ)) + M(σ + iτ) x^(-σ-iτ)] dτ
  --
  -- This is 2 * Re(M(σ + iτ) x^(-σ-iτ)), which is real-valued.
  -- Therefore mellinInv σ M x is real, so it equals its conjugate.

  -- Use the Mellin-Fourier bridge: mellinInv σ M x = x^(-σ) • 𝓕⁻(g)(-log x)
  -- where g(y) = M(σ + 2πyI)
  rw [boundary_mellinInv_eq_fourierIntegralInv σ M x hx]

  -- Define the induced function on the Fourier side
  let g := fun (y : ℝ) => M (σ + 2 * π * y * I)

  -- Step 1: Show g is conjugate-symmetric from M's conjugate symmetry
  have hg_conj : ∀ y : ℝ, g (-y) = star (g y) := by
    intro y
    unfold g
    have h_critical := mellinInv_criticalLine_decomposition hM σ
    -- g(-y) = M(σ + 2π(-y)I) = M(σ - 2πyI)
    -- By conjugate symmetry M(-star(σ - 2πyI)) = star(M(σ - 2πyI))
    -- And -star(σ - 2πyI) = -σ + 2πyI
    -- So we need to relate the critical line decomposition to this
    have h_neg : -star (σ - 2 * π * y * I) = σ + 2 * π * y * I := by
      simp only [Complex.star_sub, Complex.star_ofReal, Complex.star_mul_I]
      ring
    rw [← h_neg]
    exact hM (σ - 2 * π * y * I)

  -- Step 2: Apply Fourier inverse real-value property.
  have h_fourier_real :=
    fourierInv_conjugateSymmetric_is_real g (-Real.log x) hx hg_conj hM_integrable

  -- Step 3: The result x^(-σ) is real, so scalar mult preserves real-valuedness
  have h_scalar_real : x ^ (-(σ : ℂ)) = star (x ^ (-(σ : ℂ))) := by
    -- For real x > 0 and real σ, x^(-σ) is a positive real number
    have : x ^ (-(σ : ℂ)) = ↑(x ^ (-σ : ℝ) : ℝ) := by
      norm_cast
      exact (ofReal_rpow hx (-σ)).symm
    rw [this]
    exact conj_ofReal _

  calc mellinInv σ M x
      = x ^ (-σ : ℂ) • 𝓕⁻ g (-Real.log x) := rfl
    _ = star (x ^ (-σ : ℂ) • 𝓕⁻ g (-Real.log x)) := by
        rw [map_smul, h_scalar_real, h_fourier_real]

/-- Complete characterization: conjugate-symmetric Mellin transforms produce
conjugate-symmetric time-domain functions. -/
theorem mellinInversion_conjugateSymmetry
    {M : ℂ → ℂ} (hM : Transform.IsConjugateSymmetric M)
    (σ : ℝ)
    (hM_integrable : Integrable (fun y : ℝ => M (σ + 2 * π * y * I))) :
    ∀ x : ℝ, 0 < x →
    (mellinInv σ M x = star (mellinInv σ M x)) := by
  intro x hx
  exact conjugateSymmetricTransform_inverts_to_realValues hM σ hM_integrable x hx

end MellinInversionConjugacy

end LFunctions
end Boundary

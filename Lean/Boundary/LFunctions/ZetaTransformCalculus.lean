import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.AutocorrelationCore

/-!
# Boundary zeta transform calculus

This file exposes the classical Mellin/Fourier and zeta-normalization lemmas
that the explicit-formula route needs as upstream transform calculus.

The statements here are not the RH theorem itself. They are the precise
transform and normalization lemmas that later owner files will consume.
-/

namespace Boundary

open scoped FourierTransform
open Real Complex Set MeasureTheory
open AddCircle

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Mellin

/-- The zeta Laplace transform attached to a test function. -/
noncomputable def zetaLaplaceTransform
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) : ℂ :=
  ∫ t : ℝ, φ t * Complex.exp (z * t)

/-- The zeta Laplace transform is definitionally stable under pointwise equality. -/
theorem zetaLaplaceTransform_congr
    {φ ψ : LFunctions.ZetaTestFunction}
    (h : ∀ t : ℝ, φ t = ψ t) :
    zetaLaplaceTransform φ = zetaLaplaceTransform ψ := by
  funext z
  unfold zetaLaplaceTransform
  refine integral_congr_ae ?_
  filter_upwards with t
  exact congrArg (fun x => x * Complex.exp (z * t)) (h t)

/-- The zeta Laplace transform of an autocorrelation unfolds pointwise. -/
theorem zetaLaplaceTransform_autocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform (LFunctions.ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  unfold zetaLaplaceTransform
  rw [LFunctions.ZetaAdmissibleFunction.autocorrelation_eq]

/-- The zeta Laplace transform of an admissible function is continuous in the spectral variable. -/
theorem zetaLaplaceTransform_continuous
    (φ : LFunctions.ZetaAdmissibleFunction) :
    Continuous (fun z => zetaLaplaceTransform φ.toZetaTestFunction' z) := by
  rw [continuous_iff_continuousOn_univ]
  have hcs : HasCompactSupport φ.toZetaTestFunction' := by
    simpa using φ.toZetaTestFunction.hasCompactSupport
  let K : Set ℝ := tsupport φ.toZetaTestFunction'
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport, tsupport] using hcs
  refine continuousOn_integral_of_compact_support hK ?_ ?_
  · have hcont : Continuous fun p : ℂ × ℝ => φ p.2 * Complex.exp (p.1 * p.2) := by
      fun_prop
    exact hcont.continuousOn
  · intro p t hp ht
    have hφ : φ.toZetaTestFunction' t = 0 := by
      exact image_eq_zero_of_nmem_tsupport ht
    rw [hφ, zero_mul]

/-- The zeta Laplace transform is compatible with reflection of the test function. -/
theorem zetaLaplaceTransform_reflect
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    zetaLaplaceTransform (LFunctions.ZetaTestFunction.reflect φ) z =
      zetaLaplaceTransform φ (-z) := by
  unfold zetaLaplaceTransform
  rw [LFunctions.ZetaTestFunction.reflect_apply, ← intervalIntegral.integral_comp_neg]
  congr with t
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- The zeta Laplace transform of the reflected dagger probe is the reflected Laplace transform. -/
theorem zetaLaplaceTransform_dagger_reflect
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform (LFunctions.ZetaAdmissibleFunction.zetaAdmissibleDagger φ) z =
      zetaLaplaceTransform φ.toZetaTestFunction' (-z) := by
  have h := zetaLaplaceTransform_reflect (LFunctions.ZetaAdmissibleFunction.zetaAdmissibleDagger φ) z
  rw [LFunctions.ZetaAdmissibleFunction.zetaAdmissibleDagger_dagger] at h
  simpa using h

/-- The weighted zeta Laplace transform attached to an admissible test function. -/
noncomputable def zetaLaplaceTransformWeighted
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) * φ t * Complex.exp (z * t)

/-- The weighted zeta Laplace transform of an admissible function is continuous in the spectral variable. -/
theorem zetaLaplaceTransformWeighted_continuous
    (φ : LFunctions.ZetaAdmissibleFunction) :
    Continuous (fun z => zetaLaplaceTransformWeighted φ.toZetaTestFunction' z) := by
  rw [continuous_iff_continuousOn_univ]
  have hcs : HasCompactSupport φ.toZetaTestFunction' := by
    simpa using φ.toZetaTestFunction.hasCompactSupport
  let K : Set ℝ := tsupport φ.toZetaTestFunction'
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport, tsupport] using hcs
  refine continuousOn_integral_of_compact_support hK ?_ ?_
  · have hcont : Continuous fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2) := by
      fun_prop
    exact hcont.continuousOn
  · intro p t hp ht
    have hφ : φ.toZetaTestFunction' t = 0 := by
      exact image_eq_zero_of_nmem_tsupport ht
    rw [hφ, mul_zero, zero_mul]

/-- The weighted Laplace kernel of an admissible function has compact support in the real variable. -/
theorem hasCompactSupport_weightedLaplaceKernel
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    HasCompactSupport (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t)) := by
  refine HasCompactSupport.of_support_subset_isCompact ?_ ?_
  · simpa [HasCompactSupport] using φ.toZetaTestFunction.hasCompactSupport
  intro t ht
  have h1 :
      t ∈ Function.support (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t)) := by
    exact Function.support_mul_subset_right (f := fun t : ℝ => (t : ℂ))
      (g := fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t)) ht
  have h2 :
      t ∈ Function.support φ.toZetaTestFunction' := by
    exact Function.support_mul_subset_right (f := fun t : ℝ => φ.toZetaTestFunction' t)
      (g := fun t : ℝ => Complex.exp (z * t)) h1
  simpa [HasCompactSupport, tsupport] using h2

/-- The weighted zeta Laplace transform of an autocorrelation unfolds pointwise. -/
theorem zetaLaplaceTransformWeighted_autocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransformWeighted (LFunctions.ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (t : ℂ) * (f t * star (f t)) * Complex.exp (z * t) := by
  unfold zetaLaplaceTransformWeighted
  rw [LFunctions.ZetaAdmissibleFunction.autocorrelation_eq]

/-- The weighted Laplace derivative kernel is uniformly bounded on a fixed closed ball. -/
theorem weightedLaplaceKernel_uniform_bound_on_closedBall
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z 1 →
      ∀ t : ℝ, t ∈ tsupport φ.toZetaTestFunction' →
        ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ C := by
  have hcomp : IsCompact ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ.toZetaTestFunction')) := by
    exact (isCompact_closedBall z 1).prod (by
      simpa using φ.toZetaTestFunction.hasCompactSupport)
  have hcont :
      Continuous fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ.toZetaTestFunction' p.2 * Complex.exp (p.1 * p.2)‖ := by
    fun_prop
  obtain ⟨C, hC⟩ := hcomp.bddAbove_image hcont.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro w hw t ht
  have hmem : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ∈
      (fun p : ℂ × ℝ => ‖(p.2 : ℂ) * φ.toZetaTestFunction' p.2 * Complex.exp (p.1 * p.2)‖) ''
        ((Metric.closedBall z 1 : Set ℂ) ×ˢ (tsupport φ.toZetaTestFunction')) := by
    exact ⟨(w, t), by exact ⟨hw, ht⟩, rfl⟩
  have hle := hC hmem
  have hle' : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 := by
    exact le_trans hle (le_max_left _ _)
  have : ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ max C 0 + 1 := by
    linarith
  exact this

/-- The Laplace kernel has the expected pointwise derivative. -/
theorem hasDerivAt_laplaceKernel
    (φ : LFunctions.ZetaTestFunction) (t : ℝ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => φ t * Complex.exp (w * t))
      ((t : ℂ) * φ t * Complex.exp (z * t))
      z := by
  have hmul : HasDerivAt (fun w : ℂ => w * (t : ℂ)) (t : ℂ) z := by
    simpa [mul_comm] using (hasDerivAt_id' z).mul_const (t : ℂ)
  have hexp : HasDerivAt (fun w : ℂ => Complex.exp (w * t))
      (Complex.exp (z * t) * (t : ℂ)) z :=
    (Complex.hasDerivAt_exp (z * t)).comp z hmul
  have hconst : HasDerivAt (fun w : ℂ => φ t) 0 z := hasDerivAt_const z (φ t)
  have hmul' :
      HasDerivAt (fun w : ℂ => φ t * Complex.exp (w * t))
        (φ t * (Complex.exp (z * t) * (t : ℂ))) z :=
    by
      have htmp := hconst.mul hexp
      simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using htmp
  simpa [mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm, add_assoc] using hmul'

/-- The zeta Laplace transform is differentiable at every spectral parameter. -/
theorem zetaLaplaceTransform_differentiableAt
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    DifferentiableAt ℂ (fun w => zetaLaplaceTransform φ.toZetaTestFunction' w) z := by
  let K : Set ℝ := tsupport φ.toZetaTestFunction'
  rcases weightedLaplaceKernel_uniform_bound_on_closedBall (φ := φ) z with ⟨C, hCpos, hC⟩
  let bound : ℝ → ℝ := Set.indicator K (fun _ => C)
  have hK : IsCompact K := by
    simpa [K, HasCompactSupport, tsupport] using φ.toZetaTestFunction.hasCompactSupport
  have hK_meas : MeasurableSet K := hK.measurableSet
  have hF_meas :
      ∀ᶠ w in nhds z, AEStronglyMeasurable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (w * t))
        (volume : Measure ℝ) := by
    refine Filter.Eventually.of_forall fun w => ?_
    have hcont : Continuous (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (w * t)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hF_int : Integrable (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t)) (volume : Measure ℝ) := by
    have hcont : Continuous (fun t : ℝ => φ.toZetaTestFunction' t * Complex.exp (z * t)) := by
      fun_prop
    exact hcont.integrable_of_hasCompactSupport
      (by simpa [HasCompactSupport] using φ.toZetaTestFunction.hasCompactSupport)
  have hF'_meas :
      AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t))
        (volume : Measure ℝ) := by
    have hcont : Continuous (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
      ‖(t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)‖ ≤ bound t := by
    filter_upwards with t
    by_cases ht : t ∈ K
    · intro w hw
      have hw' : w ∈ Metric.closedBall z 1 := Metric.mem_closedBall.2 (le_of_lt hw)
      have hle := hC w hw' t ht
      simpa [bound, ht] using hle
    · intro w hw
      have hφ : φ.toZetaTestFunction' t = 0 := by
        exact image_eq_zero_of_nmem_tsupport ht
      simp [bound, ht, hφ]
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), ∀ w ∈ Metric.ball z 1,
      HasDerivAt (fun x : ℂ => φ.toZetaTestFunction' t * Complex.exp (x * t))
        ((t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (w * t)) w := by
    filter_upwards with t w hw
    simpa [mul_assoc, mul_left_comm, mul_comm] using hasDerivAt_laplaceKernel (φ := φ.toZetaTestFunction') t w
  have hbound_int : Integrable bound := by
    unfold bound
    exact (integrable_const C).indicator hK_meas
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε_pos := by norm_num) hF_meas hF_int
      hF'_meas h_bound hbound_int h_diff
  unfold zetaLaplaceTransform
  exact h.2.differentiableAt

/-- Boundary name for mathlib's Mellin/Fourier bridge. -/
theorem boundary_mellin_eq_fourierIntegral (f : ℝ → E) {s : ℂ} :
    mellin f s =
      𝓕 (fun (u : ℝ) ↦ (Real.exp (-s.re * u) • f (Real.exp (-u)))) (s.im / (2 * π)) := by
  exact mellin_eq_fourierIntegral (f := f) (s := s)

/-- Boundary name for the inverse Mellin/Fourier bridge. -/
theorem boundary_mellinInv_eq_fourierIntegralInv (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 < x) :
    mellinInv σ f x =
      (x : ℂ) ^ (-σ : ℂ) • 𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x) := by
  exact mellinInv_eq_fourierIntegralInv (σ := σ) (f := f) (x := x) hx

/-- Boundary name for Mellin inversion. -/
theorem boundary_mellin_inversion (σ : ℝ) (f : ℝ → E) {x : ℝ} (hx : 0 < x)
    [CompleteSpace E] (hf : MellinConvergent f σ) (hFf : Complex.VerticalIntegrable (mellin f) σ)
    (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  exact mellin_inversion (σ := σ) (f := f) (x := x) hx hf hFf hfx

end Mellin

section FourierInterval

theorem boundary_fourierCoeffOn_of_hasDerivAt {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ∀ x, x ∈ Set.uIcc a b → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hf'

/-- Boundary name for the interval version of the Fourier derivative identity. -/
theorem boundary_fourierCoeffOn_of_hasDerivAt_Ioo {a b : ℝ} (hab : a < b) {f f' : ℝ → ℂ}
    {n : ℤ} (hn : n ≠ 0)
    (hf : ContinuousOn f (Set.uIcc a b))
    (hff' : ∀ x, x ∈ Set.Ioo (min a b) (max a b) → HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    fourierCoeffOn hab f n =
      1 / (-2 * π * I * n) *
        (fourier (-n) (a : AddCircle (b - a)) * (f b - f a) -
          (b - a) * fourierCoeffOn hab f' n) := by
  exact fourierCoeffOn_of_hasDerivAt_Ioo (a := a) (b := b)
    (f := f) (f' := f') hab hn hf hff' hf'

end FourierInterval

section Zeta

/-- Boundary name for the completed zeta decomposition. -/
theorem boundary_completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

/-- Boundary name for the symmetry of the completed zeta function. -/
theorem boundary_completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact completedRiemannZeta_one_sub s

/-- Boundary name for zeta's functional equation identity in mathlib. -/
theorem boundary_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  exact riemannZeta_one_sub (s := s) hs hs'

/-- Boundary name for the Dirichlet-series expansion of zeta. -/
theorem boundary_riemannZeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  exact zeta_eq_tsum_one_div_nat_cpow (s := s) hs

end Zeta

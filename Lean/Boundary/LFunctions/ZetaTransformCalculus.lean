import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.AutocorrelationCore
import Boundary.LFunctions.ZetaTransformCalculusZeta

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

/-- The zeta Laplace transform is additive. -/
theorem zetaLaplaceTransform_add
    (φ ψ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hψ : Integrable (fun t : ℝ => ψ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (φ + ψ) z =
      zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
  unfold zetaLaplaceTransform
  have hfun :
      (fun t : ℝ => (φ + ψ) t * Complex.exp (z * t)) =
        fun t : ℝ => φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
    funext t
    exact add_mul (φ t) (ψ t) (Complex.exp (z * t))
  calc
    zetaLaplaceTransform (φ + ψ) z
        = ∫ t : ℝ, φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
            unfold zetaLaplaceTransform
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) hfun)
    _ = zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
          exact integral_add hφ hψ

/-- The zeta Laplace transform is homogeneous under scalar multiplication. -/
theorem zetaLaplaceTransform_smul
    (a : ℂ) (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (_hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (a • φ) z = a * zetaLaplaceTransform φ z := by
  have hfun :
      (fun t : ℝ => (a • φ) t * Complex.exp (z * t)) =
        fun t : ℝ => a * (φ t * Complex.exp (z * t)) := by
    funext t
    change (a * φ t) * Complex.exp (z * t) = a * (φ t * Complex.exp (z * t))
    exact mul_assoc a (φ t) (Complex.exp (z * t))
  calc
    zetaLaplaceTransform (a • φ) z
        = ∫ t : ℝ, (a • φ) t * Complex.exp (z * t) := by rfl
    _ = ∫ t : ℝ, a * (φ t * Complex.exp (z * t)) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) hfun)
    _ = a * zetaLaplaceTransform φ z := by
          exact integral_mul_left a (fun t : ℝ => φ t * Complex.exp (z * t))

/-- The zeta Laplace transform commutes with finite sums. -/
theorem zetaLaplaceTransform_sum_apply
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (t : ℝ) :
    (∑ a in s, f a).toFun t = ∑ a in s, f a t := by
  induction s using Finset.induction_on with
  | empty =>
      exact rfl
  | @insert a s ha ih =>
      calc
        (∑ a in insert a s, f a).toFun t
            = (f a + ∑ b in s, f b).toFun t := by
                exact congrArg (fun g : LFunctions.ZetaTestFunction => g t)
                  (Finset.sum_insert ha)
        _ = f a t + (∑ b in s, f b).toFun t := by
              rfl
        _ = f a t + ∑ b in s, f b t := by
              exact congrArg (fun x : ℂ => f a t + x) ih
        _ = ∑ a in insert a s, f a t := by
              show f a t + ∑ b in s, f b t = ∑ a in insert a s, f a t
              exact (Finset.sum_insert ha (f := fun a => f a t)).symm

/-- The zeta Laplace transform commutes with finite sums. -/
theorem zetaLaplaceTransform_sum_integrand
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (z : ℂ) :
    (fun t : ℝ => (∑ a in s, f a).toFun t * Complex.exp (z * t)) =
      fun t : ℝ => ∑ a in s, f a t * Complex.exp (z * t) := by
  funext t
  calc
    (∑ a in s, f a).toFun t * Complex.exp (z * t)
        = (∑ a in s, f a t) * Complex.exp (z * t) := by
            exact congrArg (fun x => x * Complex.exp (z * t))
              (zetaLaplaceTransform_sum_apply (s := s) (f := f) t)
    _ = ∑ a in s, f a t * Complex.exp (z * t) := by
          exact Finset.sum_mul (s := s) (f := fun a => f a t) (a := Complex.exp (z * t))

/-- The zeta Laplace transform of the empty sum is zero. -/
theorem zetaLaplaceTransform_sum_empty_integrand
    {α : Type*} (f : α → LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t)) =
      fun _ : ℝ => (0 : ℂ) := by
  funext t
  have hsum : (∑ a in (∅ : Finset α), f a) = (0 : LFunctions.ZetaTestFunction) := by
    exact Finset.sum_empty (f := f)
  calc
    (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t)
        = (0 : ℂ) * Complex.exp (z * t) := by
            exact congrArg (fun x : ℂ => x * Complex.exp (z * t))
              (congrArg (fun g : LFunctions.ZetaTestFunction => g t) hsum)
    _ = 0 := by
          exact zero_mul _

/-- The zeta Laplace transform of the empty sum is zero. -/
theorem zetaLaplaceTransform_sum_empty
    {α : Type*} (f : α → LFunctions.ZetaTestFunction) (z : ℂ) :
    zetaLaplaceTransform (∑ a in (∅ : Finset α), f a) z = 0 := by
  change ∫ t : ℝ, (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t) = 0
  calc
    ∫ t : ℝ, (∑ a in (∅ : Finset α), f a).toFun t * Complex.exp (z * t)
        = ∫ t : ℝ, (0 : ℂ) := by
            exact integral_congr_ae (Filter.Eventually.of_forall
              (fun t => by exact zero_mul _))
    _ = 0 := by
          exact (integral_zero (α := ℝ) (G := ℂ) (μ := (volume : Measure ℝ)))

/-- The zeta Laplace transform of the insert step is the sum of transforms. -/
theorem zetaLaplaceTransform_sum_insert_integrand
    {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (f : α → LFunctions.ZetaTestFunction)
    (z : ℂ) :
    (fun t : ℝ => (∑ b in insert a s, f b).toFun t * Complex.exp (z * t)) =
      fun t : ℝ => ∑ b in insert a s, f b t * Complex.exp (z * t) := by
  exact zetaLaplaceTransform_sum_integrand (s := insert a s) f z

/-- The zeta Laplace transform of a nonempty finite sum is the sum of transforms. -/
theorem zetaLaplaceTransform_sum_insert_integral
    {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (_ha : a ∉ s)
    (f : α → LFunctions.ZetaTestFunction) (z : ℂ)
    (h : ∀ b ∈ insert a s, Integrable (fun t : ℝ => f b t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    ∫ t : ℝ, ∑ b in insert a s, f b t * Complex.exp (z * t)
      = ∑ b in insert a s, zetaLaplaceTransform (f b) z := by
  exact MeasureTheory.integral_finset_sum
    (s := insert a s)
    (f := fun b t => f b t * Complex.exp (z * t))
    (fun b hb => h b hb)

/-- The zeta Laplace transform of a nonempty finite sum is the sum of transforms. -/
theorem zetaLaplaceTransform_sum_insert
    {α : Type*} [DecidableEq α] (a : α) (s : Finset α) (ha : a ∉ s)
    (f : α → LFunctions.ZetaTestFunction) (z : ℂ)
    (h : ∀ b ∈ insert a s, Integrable (fun t : ℝ => f b t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (∑ b in insert a s, f b) z =
      ∑ b in insert a s, zetaLaplaceTransform (f b) z := by
  calc
    zetaLaplaceTransform (∑ b in insert a s, f b) z
        = ∫ t : ℝ, (∑ b in insert a s, f b).toFun t * Complex.exp (z * t) := by
            rfl
    _ = ∫ t : ℝ, ∑ b in insert a s, f b t * Complex.exp (z * t) := by
          exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
            congrArg (fun g => g t) (zetaLaplaceTransform_sum_insert_integrand (a := a) (s := s) f z))
    _ = ∑ b in insert a s, zetaLaplaceTransform (f b) z := by
          exact zetaLaplaceTransform_sum_insert_integral a s ha f z h

/-- The zeta Laplace transform commutes with finite sums. -/
theorem zetaLaplaceTransform_sum
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → LFunctions.ZetaTestFunction) (z : ℂ)
    (h : ∀ a ∈ s, Integrable (fun t : ℝ => f a t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (∑ a in s, f a) z =
      ∑ a in s, zetaLaplaceTransform (f a) z := by
  induction s using Finset.induction_on with
  | empty =>
      exact zetaLaplaceTransform_sum_empty f z
  | @insert a s ha ih =>
      exact zetaLaplaceTransform_sum_insert a s ha f z h

/-- The zeta Laplace transform is definitionally stable under pointwise equality. -/
theorem zetaLaplaceTransform_congr
    {φ ψ : LFunctions.ZetaTestFunction}
    (h : ∀ t : ℝ, φ t = ψ t) :
    zetaLaplaceTransform φ = zetaLaplaceTransform ψ := by
  funext z
  unfold zetaLaplaceTransform
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun t =>
    congrArg (fun x => x * Complex.exp (z * t)) (h t)

/-- The pointwise Laplace integrand is continuous in the pair `(z, t)`. -/
theorem continuous_laplaceIntegrand
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (fun p : ℂ × ℝ => φ p.2 * Complex.exp (p.1 * p.2)) := by
  have hφ : Continuous (fun p : ℂ × ℝ => φ p.2) :=
    φ.continuous.comp continuous_snd
  have hmul : Continuous (fun p : ℂ × ℝ => p.1 * p.2) :=
    continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)
  have hexp : Continuous (fun p : ℂ × ℝ => Complex.exp (p.1 * p.2)) :=
    Complex.continuous_exp.comp hmul
  exact hφ.mul hexp

/-- The Laplace integrand, viewed as a curried function, is continuous on the full product. -/
theorem continuousOn_laplaceIntegrand_uncurried
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn (Function.uncurry fun z (t : ℝ) => φ t * Complex.exp (z * t))
      ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ)) := by
  change ContinuousOn (fun p : ℂ × ℝ => φ p.2 * Complex.exp (p.1 * p.2))
    ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ))
  exact (continuous_laplaceIntegrand φ).continuousOn

/-- The weighted pointwise Laplace integrand is continuous in the pair `(z, t)`. -/
theorem continuous_weightedLaplaceIntegrand
    (φ : LFunctions.ZetaTestFunction) :
    Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2)) := by
  have ht : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_snd
  have hφ : Continuous (fun p : ℂ × ℝ => φ p.2) :=
    φ.continuous.comp continuous_snd
  have hmul : Continuous (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2) :=
    ht.mul hφ
  have hmul' : Continuous (fun p : ℂ × ℝ => p.1 * p.2) :=
    continuous_fst.mul (Complex.continuous_ofReal.comp continuous_snd)
  have hexp : Continuous (fun p : ℂ × ℝ => Complex.exp (p.1 * p.2)) :=
    Complex.continuous_exp.comp hmul'
  exact hmul.mul hexp

/-- The weighted Laplace integrand, viewed as a curried function, is continuous on the full product. -/
theorem continuousOn_weightedLaplaceIntegrand_uncurried
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn (Function.uncurry fun z (t : ℝ) => (t : ℂ) * φ t * Complex.exp (z * t))
      ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ)) := by
  change ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ) * φ p.2 * Complex.exp (p.1 * p.2))
    ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ))
  exact (continuous_weightedLaplaceIntegrand φ).continuousOn

/-- The one-variable Laplace kernel is continuous. -/
theorem continuous_laplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    Continuous (fun t : ℝ => φ t * Complex.exp (z * t)) := by
  have hφ : Continuous (fun t : ℝ => φ t) :=
    φ.continuous
  have hmul : Continuous (fun t : ℝ => (z : ℂ) * t) := by
    exact continuous_const.mul Complex.continuous_ofReal
  have hexp : Continuous (fun t : ℝ => Complex.exp (z * t)) :=
    Complex.continuous_exp.comp hmul
  exact hφ.mul hexp

/-- The Laplace kernel inherits compact support from the underlying test function. -/
theorem hasCompactSupport_laplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun t : ℝ => φ t * Complex.exp (z * t)) := by
  exact hφ.mul_right

theorem integrable_laplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  exact (continuous_laplaceKernel φ z).integrable_of_hasCompactSupport
    (hasCompactSupport_laplaceKernel_of_hasCompactSupport φ z hφ)

/-- The Laplace kernel is strongly measurable whenever it is continuous. -/
theorem aestronglyMeasurable_laplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  exact (continuous_laplaceKernel φ z).aestronglyMeasurable

/-- The one-variable weighted Laplace kernel is continuous. -/
theorem continuous_weightedLaplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    Continuous (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) := by
  have ht : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal
  have hφ : Continuous (fun t : ℝ => φ t) :=
    φ.continuous
  have hmul : Continuous (fun t : ℝ => (t : ℂ) * φ t) :=
    ht.mul hφ
  have hmul' : Continuous (fun t : ℝ => (z : ℂ) * t) := by
    exact continuous_const.mul Complex.continuous_ofReal
  have hexp : Continuous (fun t : ℝ => Complex.exp (z * t)) :=
    Complex.continuous_exp.comp hmul'
  exact hmul.mul hexp

/-- A compact-support kernel stays compactly supported after multiplying by `t`. -/
theorem hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) := by
  have hcompact :
      HasCompactSupport (fun t : ℝ => (t : ℂ) * (φ t * Complex.exp (z * t))) := by
    exact HasCompactSupport.mul_left (f := fun t : ℝ => (t : ℂ))
      (hasCompactSupport_laplaceKernel_of_hasCompactSupport φ z hφ)
  have hEq :
      (fun t : ℝ => (t : ℂ) * (φ t * Complex.exp (z * t))) =
        fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t) := by
    funext t
    exact (mul_assoc (t : ℂ) (φ t) (Complex.exp (z * t))).symm
  exact hEq ▸ hcompact

/-- A Laplace kernel vanishes outside the support of the underlying test function. -/
theorem laplaceKernel_eq_zero_of_nmem_tsupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    φ t * Complex.exp (z * t) = 0 := by
  have hφ : φ t = 0 := image_eq_zero_of_nmem_tsupport ht
  calc
    φ t * Complex.exp (z * t) = 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => x * Complex.exp (z * t)) hφ
    _ = 0 := by
      exact zero_mul _

/-- A weighted Laplace kernel vanishes outside the support of the underlying test function. -/
theorem weightedLaplaceKernel_eq_zero_of_nmem_tsupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    (t : ℂ) * φ t * Complex.exp (z * t) = 0 := by
  have hφ : φ t = 0 := image_eq_zero_of_nmem_tsupport ht
  calc
    (t : ℂ) * φ t * Complex.exp (z * t) = (t : ℂ) * 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => (t : ℂ) * x * Complex.exp (z * t)) hφ
    _ = 0 * Complex.exp (z * t) := by
      exact congrArg (fun x => x * Complex.exp (z * t)) (mul_zero (t : ℂ))
    _ = 0 := by
      exact zero_mul _

/-- The indicator of a support set is equal to the constant on points inside the set. -/
theorem indicator_eq_of_mem {K : Set ℝ} {C : ℝ} {t : ℝ} (ht : t ∈ K) :
    K.indicator (fun _ => C) t = C := by
  exact Set.indicator_of_mem ht (fun _ : ℝ => C)

/-- The indicator of a support set is zero outside the set. -/
theorem indicator_eq_zero_of_not_mem {K : Set ℝ} {C : ℝ} {t : ℝ} (ht : t ∉ K) :
    K.indicator (fun _ => C) t = 0 := by
  exact Set.indicator_of_not_mem ht (fun _ : ℝ => C)

/-- Reflection turns the Laplace kernel at `z` into the unreflected kernel at `-z`. -/
theorem reflect_laplaceKernel_eq_comp_neg_pointwise
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) (t : ℝ) :
    (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t) =
      φ (-t) * Complex.exp (-z * (-t)) := by
  have hmul : z * t = (-z) * (-t) := by
    exact (neg_mul_neg z t).symm
  calc
    (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)
        = φ (-t) * Complex.exp (z * t) := by
            exact congrArg (fun x => x * Complex.exp (z * t))
              (LFunctions.ZetaTestFunction.reflect_apply φ t)
    _ = φ (-t) * Complex.exp (-z * (-t)) := by
          exact congrArg (fun x => φ (-t) * Complex.exp x) hmul

theorem reflect_laplaceKernel_eq_comp_neg
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)) =
      fun t : ℝ => φ (-t) * Complex.exp (-z * (-t)) := by
  funext t
  exact reflect_laplaceKernel_eq_comp_neg_pointwise φ z t

/-- The weighted Laplace kernel vanishes outside the support of the underlying test function. -/
theorem weightedLaplaceKernel_eq_zero_of_nmem_tsupport'
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    (fun x : ℝ => (x : ℂ) * φ x * Complex.exp (z * x)) t = 0 := by
  exact weightedLaplaceKernel_eq_zero_of_nmem_tsupport φ z ht

/-- The weighted Laplace kernel with compact support is integrable. -/
theorem integrable_weightedLaplaceKernel_of_hasCompactSupport
    (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : HasCompactSupport φ) :
    Integrable (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) (volume : Measure ℝ) := by
  have hcs :
      HasCompactSupport (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) := by
    exact hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport φ z hφ
  exact (continuous_weightedLaplaceKernel φ z).integrable_of_hasCompactSupport hcs

/-- The weighted Laplace kernel is strongly measurable whenever it is continuous. -/
theorem aestronglyMeasurable_weightedLaplaceKernel
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t))
      (volume : Measure ℝ) := by
  exact (continuous_weightedLaplaceKernel φ z).aestronglyMeasurable

/-- The zeta Laplace transform of an autocorrelation unfolds pointwise. -/
theorem zetaLaplaceTransform_autocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransform (LFunctions.ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  unfold zetaLaplaceTransform
  exact congrArg (fun g : ℝ → ℂ => ∫ t : ℝ, g t * Complex.exp (z * t))
    (LFunctions.ZetaAdmissibleFunction.autocorrelation_eq f)

/-- The zeta Laplace transform of an admissible function is continuous in the spectral variable. -/
theorem zetaLaplaceTransform_continuous
    (φ : LFunctions.ZetaAdmissibleFunction) :
    Continuous (fun z => zetaLaplaceTransform φ.toZetaTestFunction' z) := by
  have hcs : HasCompactSupport φ.toZetaTestFunction' := by
    exact φ.toZetaTestFunction.hasCompactSupport
  let K : Set ℝ := tsupport φ.toZetaTestFunction'
  have hK : IsCompact K := by
    exact hcs.isCompact
  have hcont :
      Continuous (fun p : ℂ × ℝ => φ.toZetaTestFunction' p.2 * Complex.exp (p.1 * p.2)) :=
    continuous_laplaceIntegrand φ.toZetaTestFunction'
  have hcontOn :=
    continuousOn_laplaceIntegrand_uncurried φ.toZetaTestFunction'
  have hzero :
      ∀ p : ℂ, ∀ t : ℝ, p ∈ (Set.univ : Set ℂ) → t ∉ K →
        φ.toZetaTestFunction' t * Complex.exp (p * t) = 0 := by
    intro p t _ ht
    exact laplaceKernel_eq_zero_of_nmem_tsupport φ.toZetaTestFunction' p ht
  have hcont' :
      ContinuousOn (fun z => ∫ t : ℝ, φ.toZetaTestFunction' t * Complex.exp (z * t))
        (Set.univ : Set ℂ) := by
    exact continuousOn_integral_of_compact_support
      (μ := (volume : Measure ℝ))
      (f := fun z t => φ.toZetaTestFunction' t * Complex.exp (z * t))
      (s := (Set.univ : Set ℂ))
      (k := K)
      hK
      hcontOn
      hzero
  exact continuous_iff_continuousOn_univ.mpr hcont'

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

end
end Boundary

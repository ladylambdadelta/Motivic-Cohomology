import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.AutocorrelationCore
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Boundary

open scoped MeasureTheory
open Real Complex Set MeasureTheory

noncomputable section

section Mellin

/-- The zeta Laplace transform attached to a test function. -/
noncomputable def zetaLaplaceTransform
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) : ℂ :=
  ∫ t : ℝ, φ t * Complex.exp (z * t)

/-- The pointwise integrand for additivity. -/
theorem zetaLaplaceTransform_add_integrand
    (φ ψ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (φ + ψ) t * Complex.exp (z * t)) =
      fun t : ℝ => φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
  funext t
  exact add_mul (φ t) (ψ t) (Complex.exp (z * t))

/-- The zeta Laplace transform is additive. -/
theorem zetaLaplaceTransform_add
    (φ ψ : LFunctions.ZetaTestFunction) (z : ℂ)
    (hφ : Integrable (fun t : ℝ => φ t * Complex.exp (z * t)) (volume : Measure ℝ))
    (hψ : Integrable (fun t : ℝ => ψ t * Complex.exp (z * t)) (volume : Measure ℝ)) :
    zetaLaplaceTransform (φ + ψ) z =
      zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
  unfold zetaLaplaceTransform
  calc
    zetaLaplaceTransform (φ + ψ) z
        = ∫ t : ℝ, φ t * Complex.exp (z * t) + ψ t * Complex.exp (z * t) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) (zetaLaplaceTransform_add_integrand φ ψ z))
    _ = zetaLaplaceTransform φ z + zetaLaplaceTransform ψ z := by
          exact integral_add hφ hψ

/-- The pointwise integrand for scalar multiplication. -/
theorem zetaLaplaceTransform_smul_integrand
    (a : ℂ) (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    (fun t : ℝ => (a • φ) t * Complex.exp (z * t)) =
      fun t : ℝ => a * (φ t * Complex.exp (z * t)) := by
  funext t
  change (a * φ t) * Complex.exp (z * t) = a * (φ t * Complex.exp (z * t))
  exact mul_assoc a (φ t) (Complex.exp (z * t))

/-- The zeta Laplace transform is homogeneous under scalar multiplication. -/
theorem zetaLaplaceTransform_smul
    (a : ℂ) (φ : LFunctions.ZetaTestFunction) (z : ℂ)
    :
    zetaLaplaceTransform (a • φ) z = a * zetaLaplaceTransform φ z := by
  unfold zetaLaplaceTransform
  calc
    ∫ t : ℝ, (a • φ) t * Complex.exp (z * t)
        = ∫ t : ℝ, a * (φ t * Complex.exp (z * t)) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              congrArg (fun g => g t) (zetaLaplaceTransform_smul_integrand a φ z))
    _ = a * zetaLaplaceTransform φ z := by
          exact integral_mul_left a (fun t : ℝ => φ t * Complex.exp (z * t))

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
  have h :
      HasCompactSupport
        ((fun t : ℝ => (t : ℂ)) * (fun t : ℝ => φ t * Complex.exp (z * t))) := by
    exact HasCompactSupport.mul_left
      (f := fun t : ℝ => (t : ℂ))
      (f' := fun t : ℝ => φ t * Complex.exp (z * t))
      (hf := hasCompactSupport_laplaceKernel_of_hasCompactSupport φ z hφ)
  simpa [mul_assoc] using h

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
  simpa using (Set.indicator_of_mem (s := K) (f := fun _ : ℝ => C) ht)

/-- The indicator of a support set is zero outside the set. -/
theorem indicator_eq_zero_of_not_mem {K : Set ℝ} {C : ℝ} {t : ℝ} (ht : t ∉ K) :
    K.indicator (fun _ => C) t = 0 := by
  simpa using (Set.indicator_of_not_mem (s := K) (f := fun _ : ℝ => C) ht)

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
  have hcs : HasCompactSupport (fun t : ℝ => (t : ℂ) * φ t * Complex.exp (z * t)) :=
    hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport φ z hφ
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

end Mellin

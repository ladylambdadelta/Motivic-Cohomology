import Boundary.LFunctions.ZetaTransformCalculusBase
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Boundary

open Real Complex Set MeasureTheory
open AddCircle

noncomputable section

section Mellin

/-- The zeta Laplace transform is compatible with reflection of the test function. -/
theorem reflect_laplaceKernel_pointwise
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) (t : ℝ) :
    (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t) =
      φ (-t) * Complex.exp (-z * (-t)) := by
  exact reflect_laplaceKernel_eq_comp_neg_pointwise φ z t

/-- The reflected Laplace kernel is the unreflected kernel at the negated variable. -/
theorem reflect_laplaceKernel_integral_comp
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    ∫ t : ℝ, φ (-t) * Complex.exp (-z * (-t))
      = ∫ t : ℝ, φ t * Complex.exp (-z * t) := by
  have hneg : MeasurePreserving (Homeomorph.neg ℝ).toMeasurableEquiv
      (volume : Measure ℝ) (volume : Measure ℝ) :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  simpa using hneg.integral_comp' (g := fun t : ℝ => φ t * Complex.exp (-z * t))

/-- The zeta Laplace transform is compatible with reflection of the test function. -/
theorem zetaLaplaceTransform_reflect_aux
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    ∫ t : ℝ, (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)
        = ∫ t : ℝ, φ t * Complex.exp (-z * t) := by
  calc
    ∫ t : ℝ, (LFunctions.ZetaTestFunction.reflect φ) t * Complex.exp (z * t)
        = ∫ t : ℝ, φ (-t) * Complex.exp (-z * (-t)) := by
            exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
              reflect_laplaceKernel_pointwise φ z t)
    _ = ∫ t : ℝ, φ t * Complex.exp (-z * t) := by
          exact reflect_laplaceKernel_integral_comp φ z

theorem zetaLaplaceTransform_reflect
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) :
    zetaLaplaceTransform (LFunctions.ZetaTestFunction.reflect φ) z =
      zetaLaplaceTransform φ (-z) := by
  unfold zetaLaplaceTransform
  exact zetaLaplaceTransform_reflect_aux (φ := φ) (z := z)

/-- The weighted zeta Laplace transform attached to an admissible test function. -/
noncomputable def zetaLaplaceTransformWeighted
    (φ : LFunctions.ZetaTestFunction) (z : ℂ) : ℂ :=
  ∫ t : ℝ, (t : ℂ) * φ t * Complex.exp (z * t)

/-- The weighted kernel is zero off the compact support. -/
theorem weightedLaplaceKernel_zero_off_support
    (φ : LFunctions.ZetaTestFunction) (p : ℂ) {t : ℝ}
    (ht : t ∉ tsupport φ) :
    (t : ℂ) * φ t * Complex.exp (p * t) = 0 := by
  exact weightedLaplaceKernel_eq_zero_of_nmem_tsupport φ p ht

/-- The weighted transform integrand is continuous on the product. -/
theorem continuousOn_weightedLaplaceTransformIntegrand_uncurried
    (φ : LFunctions.ZetaTestFunction) :
    ContinuousOn (Function.uncurry fun z (t : ℝ) => (t : ℂ) * φ t * Complex.exp (z * t))
      ((Set.univ : Set ℂ) ×ˢ (Set.univ : Set ℝ)) := by
  exact continuousOn_weightedLaplaceIntegrand_uncurried φ

/-- The weighted transform is continuous on compact support data. -/
theorem continuousOn_zetaLaplaceTransformWeighted_of_compact_support
    (φ : LFunctions.ZetaTestFunction) (hcs : HasCompactSupport φ) :
    ContinuousOn (fun z => zetaLaplaceTransformWeighted φ z) (Set.univ : Set ℂ) := by
  let K : Set ℝ := tsupport φ
  have hK : IsCompact K := by
    exact hcs.isCompact
  have hcontOn :=
    continuousOn_weightedLaplaceTransformIntegrand_uncurried φ
  have hzero :
      ∀ p : ℂ, ∀ t : ℝ, p ∈ (Set.univ : Set ℂ) → t ∉ K →
        (t : ℂ) * φ t * Complex.exp (p * t) = 0 := by
    intro p t _ ht
    exact weightedLaplaceKernel_zero_off_support φ p ht
  exact continuousOn_integral_of_compact_support
    (μ := (volume : Measure ℝ))
    (f := fun z t => (t : ℂ) * φ t * Complex.exp (z * t))
    (s := (Set.univ : Set ℂ))
    (k := K)
    hK
    hcontOn
    hzero

/-- The weighted zeta Laplace transform of an admissible function is continuous in the spectral variable. -/
theorem zetaLaplaceTransformWeighted_continuous
    (φ : LFunctions.ZetaAdmissibleFunction) :
    Continuous (fun z => zetaLaplaceTransformWeighted φ.toZetaTestFunction' z) := by
  have hcont' :=
    continuousOn_zetaLaplaceTransformWeighted_of_compact_support
      φ.toZetaTestFunction' φ.toZetaTestFunction.hasCompactSupport
  exact continuous_iff_continuousOn_univ.mpr hcont'

/-- The weighted Laplace kernel of an admissible function has compact support in the real variable. -/
theorem hasCompactSupport_weightedLaplaceKernel
    (φ : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    HasCompactSupport (fun t : ℝ => (t : ℂ) * φ.toZetaTestFunction' t * Complex.exp (z * t)) := by
  exact hasCompactSupport_weightedLaplaceKernel_of_hasCompactSupport
    φ.toZetaTestFunction' z φ.toZetaTestFunction.hasCompactSupport

/-- The weighted zeta Laplace transform of an autocorrelation unfolds pointwise. -/
theorem zetaLaplaceTransformWeighted_autocorrelation
    (f : LFunctions.ZetaAdmissibleFunction) (z : ℂ) :
    zetaLaplaceTransformWeighted
        (LFunctions.ZetaAdmissibleFunction.autocorrelation f).toZetaTestFunction' z =
      ∫ t : ℝ, (t : ℂ) * (f t * star (f t)) * Complex.exp (z * t) := by
  unfold zetaLaplaceTransformWeighted
  exact congrArg (fun g : ℝ → ℂ => ∫ t : ℝ, (t : ℂ) * g t * Complex.exp (z * t))
    (LFunctions.ZetaAdmissibleFunction.autocorrelation_eq f)

end Mellin

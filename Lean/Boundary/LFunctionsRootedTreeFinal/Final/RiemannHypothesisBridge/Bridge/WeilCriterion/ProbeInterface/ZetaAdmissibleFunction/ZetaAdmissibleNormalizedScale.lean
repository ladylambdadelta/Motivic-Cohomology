import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.ZetaAdmissibleComplexModulation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Normalized dilation of admissible probes

The normalized dilation `a⁻¹ f(a⁻¹ t)` is the physical-space operation whose Laplace
transform is evaluated at the scaled spectral coordinate `a z`.
-/

namespace Boundary
namespace LFunctions
noncomputable section

open MeasureTheory

namespace ZetaAdmissibleFunction

/-- Dilation normalized to preserve the Laplace-transform amplitude for positive scales. -/
def normalizedScale
    (a : ℝ)
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  (a⁻¹ : ℂ) • scale a⁻¹ f

/-- Pointwise form of normalized dilation at a nonzero scale. -/
theorem normalizedScale_apply
    (a : ℝ)
    (ha : a ≠ 0)
    (f : ZetaAdmissibleFunction)
    (t : ℝ) :
    normalizedScale a f t =
      (a⁻¹ : ℂ) * f (a⁻¹ * t) := by
  have hscale :
      scale a⁻¹ f t = f (a⁻¹ * t) := by
    exact scale_nonzero_apply a⁻¹ (inv_ne_zero ha) f t
  calc
    normalizedScale a f t = (a⁻¹ : ℂ) * scale a⁻¹ f t := by
      exact smul_apply (a⁻¹ : ℂ) (scale a⁻¹ f) t
    _ = (a⁻¹ : ℂ) * f (a⁻¹ * t) := by
      exact congrArg (fun value : ℂ => (a⁻¹ : ℂ) * value) hscale

/-- Positive normalized dilation evaluates the Laplace transform at the corresponding
scaled spectral coordinate. -/
theorem zetaLaplaceTransform_normalizedScale
    (a : ℝ)
    (ha : 0 < a)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaLaplaceTransform (normalizedScale a f).toZetaTestFunction' z =
      zetaLaplaceTransform f.toZetaTestFunction' ((a : ℂ) * z) := by
  have ha_ne_zero : a ≠ 0 := ne_of_gt ha
  have ha_complex_ne_zero : (a : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr ha_ne_zero
  let g : ℝ → ℂ :=
    fun y : ℝ => f.toZetaTestFunction' y *
      Complex.exp (((a : ℂ) * z) * (y : ℂ))
  have hscaled_integrand :
      ∀ x : ℝ,
        (normalizedScale a f).toZetaTestFunction' x * Complex.exp (z * (x : ℂ)) =
          (a⁻¹ : ℂ) * g (a⁻¹ * x) := by
    intro x
    have hscale :
        normalizedScale a f x =
          (a⁻¹ : ℂ) * f (a⁻¹ * x) :=
      normalizedScale_apply a ha_ne_zero f x
    have hcast_inv_mul :
        ((a⁻¹ * x : ℝ) : ℂ) = (a⁻¹ : ℂ) * (x : ℂ) := by
      simpa only [Complex.ofReal_inv] using Complex.ofReal_mul a⁻¹ x
    have hcoefficient :
        (a : ℂ) * (a⁻¹ : ℂ) = 1 := by
      exact mul_inv_cancel₀ ha_complex_ne_zero
    have hexponent_argument :
        ((a : ℂ) * z) * ((a⁻¹ * x : ℝ) : ℂ) = z * (x : ℂ) := by
      calc
        ((a : ℂ) * z) * ((a⁻¹ * x : ℝ) : ℂ) =
            ((a : ℂ) * z) * ((a⁻¹ : ℂ) * (x : ℂ)) := by
              exact congrArg (fun value : ℂ => ((a : ℂ) * z) * value) hcast_inv_mul
        _ = (((a : ℂ) * z) * (a⁻¹ : ℂ)) * (x : ℂ) := by
              exact (mul_assoc ((a : ℂ) * z) (a⁻¹ : ℂ) (x : ℂ)).symm
        _ = ((z * (a : ℂ)) * (a⁻¹ : ℂ)) * (x : ℂ) := by
              exact congrArg
                (fun value : ℂ => (value * (a⁻¹ : ℂ)) * (x : ℂ))
                (mul_comm (a : ℂ) z)
        _ = (z * ((a : ℂ) * (a⁻¹ : ℂ))) * (x : ℂ) := by
              exact congrArg (fun value : ℂ => value * (x : ℂ))
                (mul_assoc z (a : ℂ) (a⁻¹ : ℂ))
        _ = (z * 1) * (x : ℂ) := by
              exact congrArg (fun value : ℂ => (z * value) * (x : ℂ)) hcoefficient
        _ = z * (x : ℂ) := by
              exact congrArg (fun value : ℂ => value * (x : ℂ)) (mul_one z)
    have hexponent :
        Complex.exp (((a : ℂ) * z) * ((a⁻¹ * x : ℝ) : ℂ)) =
          Complex.exp (z * (x : ℂ)) := by
      exact congrArg Complex.exp hexponent_argument
    calc
      (normalizedScale a f).toZetaTestFunction' x * Complex.exp (z * (x : ℂ)) =
          ((a⁻¹ : ℂ) * f (a⁻¹ * x)) * Complex.exp (z * (x : ℂ)) := by
            exact congrArg (fun value : ℂ => value * Complex.exp (z * (x : ℂ))) hscale
      _ = (a⁻¹ : ℂ) *
            (f (a⁻¹ * x) * Complex.exp (z * (x : ℂ))) := by
            exact mul_assoc (a⁻¹ : ℂ) (f (a⁻¹ * x))
              (Complex.exp (z * (x : ℂ)))
      _ = (a⁻¹ : ℂ) *
            (f (a⁻¹ * x) *
              Complex.exp (((a : ℂ) * z) * ((a⁻¹ * x : ℝ) : ℂ))) := by
            exact congrArg
              (fun value : ℂ => (a⁻¹ : ℂ) * (f (a⁻¹ * x) * value))
              hexponent.symm
      _ = (a⁻¹ : ℂ) * g (a⁻¹ * x) := by
            exact rfl
  have hintegrand :
      (fun x : ℝ =>
        (normalizedScale a f).toZetaTestFunction' x * Complex.exp (z * (x : ℂ))) =
        fun x : ℝ => (a⁻¹ : ℂ) * g (a⁻¹ * x) := by
    exact funext hscaled_integrand
  have hchange :
      (∫ x : ℝ, g (a⁻¹ * x)) = a • ∫ y : ℝ, g y := by
    have hraw := Measure.integral_comp_inv_mul_left g a
    have habs : |a| = a := abs_of_pos ha
    exact Eq.trans hraw (congrArg (fun c : ℝ => c • ∫ y : ℝ, g y) habs)
  have hnormalization :
      (a⁻¹ : ℂ) * (a • ∫ y : ℝ, g y) = ∫ y : ℝ, g y := by
    have hsmul : a • ∫ y : ℝ, g y = (a : ℂ) * ∫ y : ℝ, g y := by
      exact rfl
    calc
      (a⁻¹ : ℂ) * (a • ∫ y : ℝ, g y) =
          (a⁻¹ : ℂ) * ((a : ℂ) * ∫ y : ℝ, g y) := by
            exact congrArg (fun value : ℂ => (a⁻¹ : ℂ) * value) hsmul
      _ = ((a⁻¹ : ℂ) * (a : ℂ)) * ∫ y : ℝ, g y := by
            exact (mul_assoc (a⁻¹ : ℂ) (a : ℂ) (∫ y : ℝ, g y)).symm
      _ = 1 * ∫ y : ℝ, g y := by
            exact congrArg (fun value : ℂ => value * ∫ y : ℝ, g y)
              (inv_mul_cancel₀ ha_complex_ne_zero)
      _ = ∫ y : ℝ, g y := one_mul (∫ y : ℝ, g y)
  unfold zetaLaplaceTransform
  calc
    ∫ x : ℝ,
        (normalizedScale a f).toZetaTestFunction' x * Complex.exp (z * (x : ℂ)) =
        ∫ x : ℝ, (a⁻¹ : ℂ) * g (a⁻¹ * x) := by
          exact congrArg (fun h : ℝ → ℂ => ∫ x : ℝ, h x) hintegrand
    _ = (a⁻¹ : ℂ) * ∫ x : ℝ, g (a⁻¹ * x) := by
          exact MeasureTheory.integral_mul_left (a⁻¹ : ℂ) (fun x : ℝ => g (a⁻¹ * x))
    _ = (a⁻¹ : ℂ) * (a • ∫ y : ℝ, g y) := by
          exact congrArg (fun value : ℂ => (a⁻¹ : ℂ) * value) hchange
    _ = ∫ y : ℝ, g y := hnormalization
    _ = ∫ y : ℝ,
          f.toZetaTestFunction' y *
            Complex.exp (((a : ℂ) * z) * (y : ℂ)) := by
          exact rfl

/-- Positive normalized dilation evaluates the admissible spectral transform at the
scaled spectral coordinate. -/
theorem zetaSpectralEval_normalizedScale
    (a : ℝ)
    (ha : 0 < a)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaSpectralEval (normalizedScale a f) z =
      zetaSpectralEval f ((a : ℂ) * z) := by
  calc
    zetaSpectralEval (normalizedScale a f) z =
        zetaLaplaceTransform (normalizedScale a f).toZetaTestFunction' z := by
          exact zetaSpectralEval_eq_laplace (normalizedScale a f) z
    _ = zetaLaplaceTransform f.toZetaTestFunction' ((a : ℂ) * z) := by
          exact zetaLaplaceTransform_normalizedScale a ha f z
    _ = zetaSpectralEval f ((a : ℂ) * z) := by
          exact (zetaSpectralEval_eq_laplace f ((a : ℂ) * z)).symm

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

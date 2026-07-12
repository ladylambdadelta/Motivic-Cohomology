import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.SchwartzCompactSupport
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Finite Poisson reconstruction

This file owns the exact passage from a finitely supported family of integer
samples to the Fourier-mode family of a Schwartz extension.  Construction and
estimation of the extension are separate owner layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped FourierTransform

/-- Exact Poisson reconstruction when the integer samples of a Schwartz
function vanish away from a prescribed finite set. -/
theorem Complex.finite_integerSample_poisson_reconstruction
    (f : SchwartzMap ℝ ℂ)
    (samples : Finset ℤ)
    (hsupport :
      ∀ n : ℤ,
        n ∉ samples → f (n : ℝ) = 0) :
    (∑ n ∈ samples, f (n : ℝ)) =
      ∑' m : ℤ, SchwartzMap.fourierTransformCLM ℝ f (m : ℝ) := by
  have hPoisson :=
    SchwartzMap.tsum_eq_tsum_fourierIntegral f 0
  have hLeft :
      (∑' n : ℤ, f ((0 : ℝ) + (n : ℝ))) =
        ∑ n ∈ samples, f (n : ℝ) := by
    calc
      (∑' n : ℤ, f ((0 : ℝ) + (n : ℝ))) =
          ∑' n : ℤ, f (n : ℝ) :=
        tsum_congr
          (fun n : ℤ =>
            congrArg f (zero_add (n : ℝ)))
      _ = ∑ n ∈ samples, f (n : ℝ) :=
        tsum_eq_sum hsupport
  have hRight :
      (∑' m : ℤ,
          SchwartzMap.fourierTransformCLM ℝ f (m : ℝ) *
            fourier m (0 : UnitAddCircle)) =
        ∑' m : ℤ, SchwartzMap.fourierTransformCLM ℝ f (m : ℝ) := by
    exact
      tsum_congr
        (fun m : ℤ =>
          (congrArg
            (fun value : ℂ =>
              SchwartzMap.fourierTransformCLM ℝ f (m : ℝ) * value)
            (fourier_eval_zero m)).trans
            (mul_one (SchwartzMap.fourierTransformCLM ℝ f (m : ℝ))))
  exact hLeft.symm.trans (hPoisson.trans hRight)

end

end LFunctions
end Boundary

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ConjugateSymmetricTransforms
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaTransformCalculus.Owner

/-!
# Contour Integral Decomposition for Conjugate Symmetry

Analyzes the measure-theoretic properties of contour integrals that preserve
conjugate symmetry. This is the foundation for extending conjugate-symmetric
properties from the spectral transform to the zeta function's explicit formula.

Key structural insight: The contour integral
  ∫ Φ_f(s) · K(s) ds
over vertical contours decomposes symmetrically when K(-conj(s)) = conj(K(s)).
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ContourIntegralDecomposition

/-- A contour integral kernel that is conjugate-symmetric. -/
def IsContourKernelConjugateSymmetric (K : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, K (-star s) = star (K s)

/-- Vertical contours decompose across the reflection `s ↦ -star s`. -/
lemma verticalContourDecomposition
    (K : ℂ → ℂ) (σ : ℝ) (hK : IsContourKernelConjugateSymmetric K)
    (φ : ℂ → ℂ) (hφ : Transform.IsConjugateSymmetric φ) :
    ∀ t : ℝ,
      K (-star ((σ : ℂ) + t * I)) * φ (-star ((σ : ℂ) + t * I)) =
      star (K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := by
  intro t
  have h_K :
      K (-star ((σ : ℂ) + t * I)) =
        star (K ((σ : ℂ) + t * I)) :=
    hK ((σ : ℂ) + t * I)
  have h_φ :
      φ (-star ((σ : ℂ) + t * I)) =
        star (φ ((σ : ℂ) + t * I)) :=
    hφ ((σ : ℂ) + t * I)
  calc
    K (-star ((σ : ℂ) + t * I)) * φ (-star ((σ : ℂ) + t * I))
        = star (K ((σ : ℂ) + t * I)) *
            star (φ ((σ : ℂ) + t * I)) := by
          exact congrArg₂ (fun x y : ℂ => x * y) h_K h_φ
    _ = star (K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := by
          exact
            (star_mul'
              (K ((σ : ℂ) + t * I))
              (φ ((σ : ℂ) + t * I))).symm

/-- Contour integrals of conjugate-symmetric kernels and transforms produce
conjugate-symmetric contributions. -/
theorem contourIntegral_conjugateSymmetry
    (K : ℂ → ℂ) (σ : ℝ) (hK : IsContourKernelConjugateSymmetric K)
    (φ : ℂ → ℂ) (hφ : Transform.IsConjugateSymmetric φ) :
    -- For any T > 0, the reflected vertical contour integral is the conjugate
    -- of the original vertical contour integral.
    ∀ T : ℝ, T > 0 →
      (∫ t : ℝ in Set.Icc (-T) T,
        K (-star ((σ : ℂ) + t * I)) * φ (-star ((σ : ℂ) + t * I)) : ℂ) =
      star (∫ t : ℝ in Set.Icc (-T) T,
        K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := by
  intro T hT
  have h_decomp := verticalContourDecomposition K σ hK φ hφ

  have h_integral : ∀ t : ℝ,
      K (-star ((σ : ℂ) + t * I)) * φ (-star ((σ : ℂ) + t * I)) =
      star (K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := h_decomp

  calc (∫ t : ℝ in Set.Icc (-T) T,
    K (-star ((σ : ℂ) + t * I)) * φ (-star ((σ : ℂ) + t * I)) : ℂ)
      = ∫ t : ℝ in Set.Icc (-T) T,
          star (K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := by
          exact integral_congr_ae (Filter.Eventually.of_forall h_integral)
    _ = star (∫ t : ℝ in Set.Icc (-T) T,
        K ((σ : ℂ) + t * I) * φ ((σ : ℂ) + t * I)) := by
          exact integral_conj

end ContourIntegralDecomposition

end

end LFunctions
end Boundary

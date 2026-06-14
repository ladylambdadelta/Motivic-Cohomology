import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketDecomposition.ZetaPacketKernel.ZetaPacketTransform.ZetaPacketCoefficients.Owner

/-!
# Boundary zeta packet transform

This file turns the packet labels and coefficients into an explicit coefficient
transform. The transform is intentionally concrete: a label-indexed function
with the reflection and duality laws that later Gram and kernel layers will use.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A packet transform is a label-indexed real coefficient function. -/
structure ZetaPacketTransform where
  coeff : ZetaPacketLabel → ℝ

namespace ZetaPacketTransform

instance : CoeFun ZetaPacketTransform (fun _ => ZetaPacketLabel → ℝ) :=
  ⟨ZetaPacketTransform.coeff⟩

@[ext]
theorem ext {f g : ZetaPacketTransform} (h : ∀ ℓ, f ℓ = g ℓ) : f = g := by
  cases f
  cases g
  congr
  funext ℓ
  exact h ℓ

/-- The canonical packet transform attached to the zeta coefficients. -/
def canonical : ZetaPacketTransform where
  coeff := zetaPacketCoeff

theorem canonical_apply (ℓ : ZetaPacketLabel) :
    canonical ℓ = zetaPacketCoeff ℓ := rfl

/-- Reflection on packet transforms by swapping prime indices. -/
def reflect (f : ZetaPacketTransform) : ZetaPacketTransform where
  coeff := fun ℓ => f (ZetaPacketLabel.swapPrimeIndices ℓ)

/-- Duality on packet transforms. -/
def dual (f : ZetaPacketTransform) : ZetaPacketTransform where
  coeff := fun ℓ => f (ZetaPacketLabel.dual ℓ)

theorem reflect_apply (f : ZetaPacketTransform) (ℓ : ZetaPacketLabel) :
    reflect f ℓ = f (ZetaPacketLabel.swapPrimeIndices ℓ) := rfl

theorem dual_apply (f : ZetaPacketTransform) (ℓ : ZetaPacketLabel) :
    dual f ℓ = f (ZetaPacketLabel.dual ℓ) := rfl

theorem reflect_reflect (f : ZetaPacketTransform) : reflect (reflect f) = f := by
  ext ℓ
  cases ℓ <;> rfl

theorem dual_dual (f : ZetaPacketTransform) : dual (dual f) = f := by
  ext ℓ
  cases ℓ <;> rfl

theorem dual_reflect (f : ZetaPacketTransform) :
    dual (reflect f) = reflect (dual f) := by
  ext ℓ
  cases ℓ <;> rfl

theorem canonical_dual :
    dual canonical = canonical := by
  ext ℓ
  cases ℓ <;> rfl

/-- The canonical packet transform is fixed by the dual involution. -/
theorem canonical_dual_reflect :
    dual (reflect canonical) = reflect canonical := by
  ext ℓ
  cases ℓ <;> rfl

end ZetaPacketTransform

end
end LFunctions
end Boundary

import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Localization.LocalizationLocalization

universe u

namespace Boundary

noncomputable section

namespace _root_.Algebra

/-- Relative-dimension-zero standard smoothness over a field is preserved by
localization at a prime of the target algebra. -/
theorem standardSmoothOfRelativeDimensionZero_localizationAtPrime
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A]
    (p : Ideal A) [p.IsPrime] :
    Algebra.IsStandardSmoothOfRelativeDimension 0 k (Localization.AtPrime p) := by
  let M : Submonoid k := (⊥ : Ideal k).primeCompl
  haveI : IsLocalization M k := by
    refine IsLocalization.at_units M ?_
    intro x hx
    rw [Submonoid.mem_bot] at hx
    exact isUnit_iff_ne_zero.mpr hx
  have hMmap : Submonoid.map (algebraMap k A) M ≤ p.primeCompl := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Submonoid.mem_bot] at hx
    have hxA : (algebraMap k A x) ≠ 0 := by
      exact (map_ne_zero_iff (algebraMap k A) (NoZeroSMulDivisors.algebraMap_injective k A)).2 hx
    exact by
      rw [Ideal.mem_primeCompl]
      exact hxA
  haveI : IsLocalization (Submonoid.map (algebraMap k A) M) (Localization.AtPrime p) :=
    IsLocalization.of_le (M := M.map (algebraMap k A)) (N := p.primeCompl) hMmap
      (fun r hr => by
        exact IsLocalization.map_units (Localization.AtPrime p) ⟨r, hr⟩)
  simpa [RingHom.IsStandardSmoothOfRelativeDimension] using
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves (n := 0)
      (algebraMap k A) M k (Localization.AtPrime p)
      (by
        simpa [RingHom.IsStandardSmoothOfRelativeDimension] using
          (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension 0 k A)))

end _root_.Algebra

end Boundary

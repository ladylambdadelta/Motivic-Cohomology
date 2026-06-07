import Boundary.PolynomialSmoothness.StandardSmoothConstructions
import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.Field

universe u

namespace Boundary

variable {k : Type u} [Field k]

namespace _root_.Algebra

/-- The affine scheme associated to a formally étale `k`-algebra is reduced. -/
theorem spec_isReduced_of_formallyEtale
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.FormallyEtale k A] [Algebra.EssFiniteType k A] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  rw [AlgebraicGeometry.affine_isReduced_iff]
  exact Algebra.FormallyUnramified.isReduced_of_field (K := k) (A := A)

/-- The affine scheme associated to a formally unramified essentially
finite-type `k`-algebra is reduced. -/
theorem spec_isReduced_of_formallyUnramified
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.FormallyUnramified k A] [Algebra.EssFiniteType k A] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  rw [AlgebraicGeometry.affine_isReduced_iff]
  exact Algebra.FormallyUnramified.isReduced_of_field (K := k) (A := A)

/-- The affine scheme associated to an étale `k`-algebra is reduced. -/
theorem spec_isReduced_of_etale
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.Etale k A] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  rw [AlgebraicGeometry.affine_isReduced_iff]
  exact Algebra.FormallyUnramified.isReduced_of_field (K := k) (A := A)

/-- Over a field, standard smooth algebras of relative dimension `0` are
formally unramified, hence reduced. -/
theorem isReduced_of_standardSmoothOfRelativeDimensionZero
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A] :
    _root_.IsReduced A := by
  letI : Algebra.FormallyUnramified k A :=
    Boundary.standardSmoothOfRelativeDimensionZero_formallyUnramified (R := k) (S := A)
  letI : Algebra.EssFiniteType k A := by
    letI : Algebra.IsStandardSmooth k A :=
      Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 0) (R := k) (S := A)
    letI : Algebra.FinitePresentation k A :=
      Boundary.standardSmooth_finitePresentation (R := k) (A := A)
    infer_instance
  exact Algebra.FormallyUnramified.isReduced_of_field (K := k) (A := A)

/-- Affine-scheme form of
`isReduced_of_standardSmoothOfRelativeDimensionZero`. -/
theorem spec_isReduced_of_standardSmoothOfRelativeDimensionZero
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (CommRingCat.of A)) := by
  rw [AlgebraicGeometry.affine_isReduced_iff]
  exact isReduced_of_standardSmoothOfRelativeDimensionZero (k := k) (A := A)

end _root_.Algebra

/-- Ring-hom form of relative-dimension-zero standard smoothness implying
formal unramifiedness. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_formallyUnramified
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ) :
    @Algebra.FormallyUnramified R _ A _ φ.toAlgebra := by
  letI : Algebra R A := φ.toAlgebra
  change @Algebra.FormallyUnramified R _ A _ (inferInstance : Algebra R A)
  have hss : @Algebra.IsStandardSmoothOfRelativeDimension 0 R A _ _ (inferInstance : Algebra R A) := by
    exact hφ.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R A := hss
  exact Boundary.standardSmoothOfRelativeDimensionZero_formallyUnramified (R := R) (S := A)

/-- Ring-hom form of relative-dimension-zero standard smoothness implying
formal smoothness. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_formallySmooth
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ) :
    @Algebra.FormallySmooth R _ A _ φ.toAlgebra := by
  letI : Algebra R A := φ.toAlgebra
  change @Algebra.FormallySmooth R _ A _ (inferInstance : Algebra R A)
  have hss : @Algebra.IsStandardSmoothOfRelativeDimension 0 R A _ _ (inferInstance : Algebra R A) := by
    exact hφ.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R A := hss
  exact Boundary.standardSmoothOfRelativeDimensionZero_formallySmooth (R := R) (S := A)

/-- Ring-hom form of relative-dimension-zero standard smoothness implying
formal étaleness. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_formallyEtale
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ) :
    @Algebra.FormallyEtale R _ A _ φ.toAlgebra := by
  letI : Algebra R A := φ.toAlgebra
  change @Algebra.FormallyEtale R _ A _ (inferInstance : Algebra R A)
  have hss : @Algebra.IsStandardSmoothOfRelativeDimension 0 R A _ _ (inferInstance : Algebra R A) := by
    exact hφ.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R A := hss
  haveI : Algebra.FormallyUnramified R A :=
    Boundary.standardSmoothOfRelativeDimensionZero_formallyUnramified (R := R) (S := A)
  haveI : Algebra.FormallySmooth R A :=
    Boundary.standardSmoothOfRelativeDimensionZero_formallySmooth (R := R) (S := A)
  exact Algebra.FormallyEtale.of_unramified_and_smooth

/-- Ring-hom form of relative-dimension-zero standard smoothness implying
étaleness. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_etale
    {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ) :
    @Algebra.Etale R _ A _ φ.toAlgebra := by
  letI : Algebra R A := φ.toAlgebra
  change @Algebra.Etale R _ A _ (inferInstance : Algebra R A)
  have hss : @Algebra.IsStandardSmoothOfRelativeDimension 0 R A _ _ (inferInstance : Algebra R A) := by
    exact hφ.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R A := hss
  haveI : Algebra.FormallyEtale R A :=
    ringHom_standardSmoothOfRelativeDimensionZero_formallyEtale (φ := φ) hφ
  haveI : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 0) (R := R) (S := A)
  haveI : Algebra.FinitePresentation R A :=
    Boundary.standardSmooth_finitePresentation (R := R) (A := A)
  exact ⟨inferInstance, inferInstance⟩

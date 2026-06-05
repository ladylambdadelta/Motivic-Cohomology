import Boundary.A1Invariance
import Boundary.ComponentGeometry
import Boundary.CorrespondenceSums
import Boundary.NisnevichDescent
import Boundary.PolynomialSmoothness
import Boundary.SmOver
import Geometry.Correspondences.Graph
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Localization.Bousfield
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Limits.Constructions.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Shapes.Images
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.RingTheory.RingHom.Locally
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
/-!
This file was split out of `Boundary.A1Geometry`; declarations remain in
namespace `Boundary` under their mathematical owner layer.
-/

universe u

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Polynomial
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Geometry

namespace Boundary

noncomputable section

variable {k : Type u} [Field k] [PerfectField k]
abbrev affineLineSchemeOver (k : Type u) [Field k] [PerfectField k] : Scheme.{u} :=
  Spec (CommRingCat.of (Polynomial k))

/-- The structural morphism `Spec(k[t]) ⟶ Spec(k)` induced by `Polynomial.C`. -/
abbrev affineLineStructMap (k : Type u) [Field k] [PerfectField k] :
    affineLineSchemeOver k ⟶ Spec (CommRingCat.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))

theorem affineLineSeparated (k : Type u) [Field k] [PerfectField k] :
    IsSeparated (affineLineStructMap k) := by
  infer_instance

theorem affineLineQuasiCompact (k : Type u) [Field k] [PerfectField k] :
    QuasiCompact (affineLineStructMap k) := by
  infer_instance

theorem affineLineLocallyOfFiniteType (k : Type u) [Field k] [PerfectField k] :
    LocallyOfFiniteType (affineLineStructMap k) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  change RingHom.FiniteType (Polynomial.C : k →+* Polynomial k)
  letI : Algebra k (Polynomial k) := (Polynomial.C).toAlgebra
  rw [RingHom.FiniteType]
  rw [polynomial_C_toAlgebra_eq]
  exact Algebra.FiniteType.polynomial k

theorem affineLineFiniteType (k : Type u) [Field k] [PerfectField k] :
    Geometry.IsOfFiniteType (affineLineStructMap k) := by
  exact ⟨affineLineQuasiCompact k, affineLineLocallyOfFiniteType k⟩

theorem polynomialAffineLine_isSmooth (k : Type u) [Field k] [PerfectField k] :
    IsSmooth (affineLineStructMap k) := by
  rw [HasRingHomProperty.Spec_iff (P := @IsSmooth)]
  exact RingHom.locally_of RingHom.isStandardSmooth_respectsIso
    (Polynomial.C : k →+* Polynomial k) (polynomial_C_isStandardSmooth k)

/-- The affine line as an object of `Sm/k`. -/
def A1_k :
    Geometry.SmSchemeOver k where
  scheme := affineLineSchemeOver k
  structMap := affineLineStructMap k
  smooth := polynomialAffineLine_isSmooth k
  separated := affineLineSeparated k
  finiteType := affineLineFiniteType k

/-- The smooth fiber product `X ×_k A1_k` over `Spec k`. -/
def productWithA1 (X : Geometry.SmSchemeOver k) : Geometry.SmSchemeOver k := by
  let A1 := A1_k (k := k)
  refine
    { scheme := overBaseProduct X A1
      structMap := overBaseProduct.fst X A1 ≫ X.structMap
      smooth := ?_
      separated := ?_
      finiteType := ?_ }
  · letI : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
      isSmooth_isStableUnderBaseChange
    letI : IsSmooth (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap A1.smooth
    letI : IsSmooth X.structMap := X.smooth
    infer_instance
  · letI : IsSeparated (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap A1.separated
    letI : IsSeparated X.structMap := X.separated
    infer_instance
  · letI : QuasiCompact A1.structMap := Geometry.SmSchemeOver.quasiCompact_structMap A1
    letI : LocallyOfFiniteType A1.structMap := Geometry.SmSchemeOver.locallyOfFiniteType_structMap A1
    letI : QuasiCompact X.structMap := Geometry.SmSchemeOver.quasiCompact_structMap X
    letI : LocallyOfFiniteType X.structMap := Geometry.SmSchemeOver.locallyOfFiniteType_structMap X
    letI : QuasiCompact (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap
        (Geometry.SmSchemeOver.quasiCompact_structMap A1)
    letI : LocallyOfFiniteType (overBaseProduct.fst X A1) :=
      MorphismProperty.pullback_fst X.structMap A1.structMap
        (Geometry.SmSchemeOver.locallyOfFiniteType_structMap A1)
    exact ⟨inferInstance, inferInstance⟩

/-- The projection `X ×_k A1_k ⟶ X` in `Sm/k`. -/
def projectionToBase (X : Geometry.SmSchemeOver k) : productWithA1 X ⟶ X where
  hom := overBaseProduct.fst X (A1_k (k := k))
  over := rfl

/-- The abstract `A1` geometry package from `A1Invariance` realized by the
actual affine-line object, product objects, and projections constructed here. -/
def canonicalA1GeometryData : A1GeometryDataQ (k := k) where
  affineLine := A1_k (k := k)
  productObj := productWithA1 (k := k)
  productIsoToOverBaseProduct := fun X => Iso.refl _
  projection := projectionToBase (k := k)
  projection_hom_eq_fst := fun X => rfl

end Boundary

import Boundary.PresheavesWithTransfers
import Boundary.MatAdditiveEnvelope
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Linear Presheaves and the Additive Envelope

This file rebuilds the additive-envelope comparison from the verified
`LinearPST` functor-category bridge.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

local instance moduleCat_hasFiniteBiproducts :
    HasFiniteBiproducts (ModuleCat.{u + 1} ℚ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

namespace LinearPST

abbrev additiveEnvelopeSource (category : SmCorQ (k := k)) :=
  CategoryTheory.Mat_ (correspondenceOpposite (category := category))

abbrev additiveEnvelopeFunctorCategory (category : SmCorQ (k := k)) :=
  letI := SmCorQCat category
  letI := SmCorQCat_op_preadditive category
  additiveEnvelopeSource (category := category) ⥤+ ModuleCat.{u + 1} ℚ

abbrev restrictAlongAdditiveEnvelopeEmbedding (category : SmCorQ (k := k))
    (F : additiveEnvelopeFunctorCategory (category := category)) :
    LinearPST_as_linear_functor_category (category := category) := by
  letI := SmCorQCat category
  letI := SmCorQCat_op_preadditive category
  let RF : correspondenceOpposite (category := category) ⥤ ModuleCat.{u + 1} ℚ :=
    CategoryTheory.Mat_.embedding (correspondenceOpposite (category := category)) ⋙ F.1
  exact AdditiveFunctor.of RF

def additiveEnvelopeLiftMap (category : SmCorQ (k := k)) :
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    {F G : correspondenceOpposite (category := category) ⥤ ModuleCat.{u + 1} ℚ} →
      [F.Additive] → [G.Additive] → (F ⟶ G) →
        ((CategoryTheory.Mat_.lift F :
          additiveEnvelopeSource (category := category) ⥤ ModuleCat.{u + 1} ℚ) ⟶
        (CategoryTheory.Mat_.lift G :
          additiveEnvelopeSource (category := category) ⥤ ModuleCat.{u + 1} ℚ)) := by
  letI := SmCorQCat category
  letI := SmCorQCat_op_preadditive category
  intro F G hF hG α
  letI : F.Additive := hF
  letI : G.Additive := hG
  exact CategoryTheory.Mat_.liftMap α

def toAdditiveEnvelopeFunctor (category : SmCorQ (k := k)) :
    LinearPST_as_linear_functor_category (category := category) ⥤
      additiveEnvelopeFunctorCategory (category := category) where
  obj F := by
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    letI : F.1.Additive := F.2
    exact AdditiveFunctor.of (CategoryTheory.Mat_.lift F.1)
  map {F G} α := by
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    letI : F.1.Additive := F.2
    letI : G.1.Additive := G.2
    exact additiveEnvelopeLiftMap (category := category) (F := F.1) (G := G.1) α
  map_id := by
    intro F
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    change additiveEnvelopeLiftMap (category := category) (F := F.1) (G := F.1) (𝟙 F) =
      𝟙 (AdditiveFunctor.of (CategoryTheory.Mat_.lift F.1))
    change CategoryTheory.Mat_.liftMap (𝟙 F.1) = 𝟙 (CategoryTheory.Mat_.lift F.1)
    exact CategoryTheory.Mat_.liftMap_id F.1
  map_comp := by
    intro F G H α β
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    change additiveEnvelopeLiftMap (category := category) (F := F.1) (G := H.1) (α ≫ β) =
      additiveEnvelopeLiftMap (category := category) (F := F.1) (G := G.1) α ≫
        additiveEnvelopeLiftMap (category := category) (F := G.1) (G := H.1) β
    change CategoryTheory.Mat_.liftMap (α ≫ β) =
      CategoryTheory.Mat_.liftMap α ≫ CategoryTheory.Mat_.liftMap β
    exact CategoryTheory.Mat_.liftMap_comp α β

def fromAdditiveEnvelopeFunctor (category : SmCorQ (k := k)) :
    additiveEnvelopeFunctorCategory (category := category) ⥤
      LinearPST_as_linear_functor_category (category := category) where
  obj F := by
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    exact restrictAlongAdditiveEnvelopeEmbedding (category := category) F
  map {F G} α := by
    letI := SmCorQCat category
    letI := SmCorQCat_op_preadditive category
    exact whiskerLeft (CategoryTheory.Mat_.embedding (correspondenceOpposite (category := category))) α
  map_id := by intro F; rfl
  map_comp := by intro F G H α β; rfl

/-- Comparison-packaging form of `Mat_.liftUnique`: any additive functor on the
additive envelope whose restriction along the embedded correspondence category
agrees with `F` is canonically isomorphic to the lifted functor. -/
noncomputable def additiveEnvelopeLiftUniqueIso
    (category : SmCorQ (k := k))
    (F : LinearPST_as_linear_functor_category (category := category))
    (G : additiveEnvelopeFunctorCategory (category := category))
    (η : (fromAdditiveEnvelopeFunctor (category := category)).obj G ≅ F) :
    G ≅ (toAdditiveEnvelopeFunctor (category := category)).obj F := by
  letI := SmCorQCat category
  letI := SmCorQCat_op_preadditive category
  cases F with
  | mk F hF =>
    cases G with
    | mk G hG =>
      change AdditiveFunctor.of G ≅ AdditiveFunctor.of (CategoryTheory.Mat_.lift F)
      have η' : CategoryTheory.Mat_.embedding (correspondenceOpposite (category := category)) ⋙ G ≅ F :=
        { hom := η.hom
          inv := η.inv
          hom_inv_id := η.hom_inv_id
          inv_hom_id := η.inv_hom_id }
      let e := CategoryTheory.Mat_.liftUnique F G η'
      exact
        { hom := e.hom
          inv := e.inv
          hom_inv_id := e.hom_inv_id
          inv_hom_id := e.inv_hom_id }

/-- Two additive functors out of the additive envelope are canonically
isomorphic as soon as their restrictions to the embedded correspondence
category are isomorphic. -/
noncomputable def additiveEnvelopeFunctorIsoOfRestrictionIso
    (category : SmCorQ (k := k))
    (G H : additiveEnvelopeFunctorCategory (category := category))
    (η : (fromAdditiveEnvelopeFunctor (category := category)).obj G ≅
      (fromAdditiveEnvelopeFunctor (category := category)).obj H) :
    G ≅ H := by
  calc
    G ≅ (toAdditiveEnvelopeFunctor (category := category)).obj
        ((fromAdditiveEnvelopeFunctor (category := category)).obj G) :=
      additiveEnvelopeLiftUniqueIso (category := category)
        ((fromAdditiveEnvelopeFunctor (category := category)).obj G) G (Iso.refl _)
    _ ≅ (toAdditiveEnvelopeFunctor (category := category)).obj
        ((fromAdditiveEnvelopeFunctor (category := category)).obj H) :=
      (toAdditiveEnvelopeFunctor (category := category)).mapIso η
    _ ≅ H :=
      (additiveEnvelopeLiftUniqueIso (category := category)
        ((fromAdditiveEnvelopeFunctor (category := category)).obj H) H (Iso.refl _)).symm

/-- Extensionality for additive-envelope functors: an isomorphism after
restriction to the generators extends canonically to an isomorphism upstairs. -/
noncomputable def additiveEnvelope_ext
    (category : SmCorQ (k := k))
    {G H : additiveEnvelopeFunctorCategory (category := category)}
    (η : (fromAdditiveEnvelopeFunctor (category := category)).obj G ≅
      (fromAdditiveEnvelopeFunctor (category := category)).obj H) :
    G ≅ H :=
  additiveEnvelopeFunctorIsoOfRestrictionIso (category := category) G H η

end LinearPST

end

end Boundary

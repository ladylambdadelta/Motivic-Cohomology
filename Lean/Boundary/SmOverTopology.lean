import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Underlying topological spaces of `Sm/k`

This file records the honest topological-space functor currently available for
`Sm/k`: the underlying Zariski topological space of the ambient scheme.

This is not analytification and should not be used as a Betti realization
input. It is the owner-level ordinary topology attached to the existing
`SmSchemeOver` and `SmOverHom` constructions.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

namespace SmOverHom

variable {k : Type u} [Field k] [PerfectField k]

/-- The underlying continuous map of a morphism in `Sm/k`. -/
abbrev baseMap {X Y : Geometry.SmSchemeOver k} (f : SmOverHom X Y) :
    X.scheme.toTopCat ⟶ Y.scheme.toTopCat :=
  Scheme.forgetToTop.map f.hom

@[simp] theorem baseMap_id (X : Geometry.SmSchemeOver k) :
    baseMap (SmOverHom.id X) = 𝟙 X.scheme.toTopCat :=
  rfl

@[simp] theorem baseMap_comp
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) :
    baseMap (SmOverHom.comp f g) = baseMap f ≫ baseMap g :=
  rfl

end SmOverHom

variable {k : Type u} [Field k] [PerfectField k]

/-- The forgetful functor from `Sm/k` to its underlying Zariski topological
spaces. -/
def smOverToTopCat : Geometry.SmSchemeOver k ⥤ TopCat where
  obj X := X.scheme.toTopCat
  map f := SmOverHom.baseMap f
  map_id X := SmOverHom.baseMap_id X
  map_comp f g := SmOverHom.baseMap_comp f g

@[simp] theorem smOverToTopCat_obj
    (X : Geometry.SmSchemeOver k) :
    smOverToTopCat.obj X = X.scheme.toTopCat :=
  rfl

@[simp] theorem smOverToTopCat_map
    {X Y : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) :
    smOverToTopCat.map f = Scheme.forgetToTop.map f.hom :=
  rfl

@[simp] theorem smOverToTopCat_map_id
    (X : Geometry.SmSchemeOver k) :
    smOverToTopCat.map (𝟙 X) = 𝟙 (smOverToTopCat.obj X) :=
  smOverToTopCat.map_id X

@[simp] theorem smOverToTopCat_map_comp
    {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) :
    smOverToTopCat.map (f ≫ g) =
      smOverToTopCat.map f ≫ smOverToTopCat.map g :=
  smOverToTopCat.map_comp f g

end Boundary

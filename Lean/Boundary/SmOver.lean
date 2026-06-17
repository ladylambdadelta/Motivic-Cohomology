import Geometry.Schemes.Basic

/-!
# The Ordinary Category `Sm/k`

This file equips `Geometry.SmSchemeOver k` with its ordinary category structure:
morphisms of schemes over `Spec k`.

Finite correspondences will later be defined on the same objects but with a
separate morphism type.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Boundary

/-- A morphism in `Sm/k`: a scheme morphism compatible with the structure maps to `Spec k`. -/
structure SmOverHom {k : Type u} [Field k] [PerfectField k]
    (X Y : Geometry.SmSchemeOver k) where
  hom : X.scheme ⟶ Y.scheme
  over : hom ≫ Y.structMap = X.structMap

namespace SmOverHom

variable {k : Type u} [Field k] [PerfectField k]

@[ext] theorem ext {X Y : Geometry.SmSchemeOver k} (f g : SmOverHom X Y)
    (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The identity map of a smooth `k`-scheme is compatible with the structure
map to `Spec k`. -/
theorem id_over (X : Geometry.SmSchemeOver k) :
    (𝟙 X.scheme) ≫ X.structMap = X.structMap :=
  Category.id_comp X.structMap

/-- Composition of maps over `Spec k` is again a map over `Spec k`. -/
theorem comp_over {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) :
    (f.hom ≫ g.hom) ≫ Z.structMap = X.structMap :=
  calc
    (f.hom ≫ g.hom) ≫ Z.structMap = f.hom ≫ (g.hom ≫ Z.structMap) := by
      exact Category.assoc f.hom g.hom Z.structMap
    _ = f.hom ≫ Y.structMap := by
      exact congrArg (fun h : Y.scheme ⟶ Spec (CommRingCat.of k) => f.hom ≫ h) g.over
    _ = X.structMap := f.over

/-- Identity morphism in `Sm/k`. -/
def id (X : Geometry.SmSchemeOver k) : SmOverHom X X where
  hom := 𝟙 X.scheme
  over := id_over X

/-- Composition in `Sm/k`. -/
def comp {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) : SmOverHom X Z where
  hom := f.hom ≫ g.hom
  over := comp_over f g

end SmOverHom

variable {k : Type u} [Field k] [PerfectField k]

instance : Category (Geometry.SmSchemeOver k) where
  Hom X Y := SmOverHom X Y
  id := SmOverHom.id
  comp f g := SmOverHom.comp f g
  id_comp := by
    intro X Y f
    apply SmOverHom.ext
    rfl
  comp_id := by
    intro X Y f
    apply SmOverHom.ext
    rfl
  assoc := by
    intro W X Y Z f g h
    apply SmOverHom.ext
    rfl

@[simp] theorem smOverHom_id_hom (X : Geometry.SmSchemeOver k) :
    (𝟙 X : SmOverHom X X).hom = 𝟙 X.scheme :=
  rfl

@[simp] theorem smOverHom_comp_hom {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) :
    (SmOverHom.comp f g).hom = f.hom ≫ g.hom :=
  rfl

end Boundary

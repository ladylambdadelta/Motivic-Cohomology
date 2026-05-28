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

/-- Identity morphism in `Sm/k`. -/
def id (X : Geometry.SmSchemeOver k) : SmOverHom X X where
  hom := 𝟙 X.scheme
  over := by simp

/-- Composition in `Sm/k`. -/
def comp {X Y Z : Geometry.SmSchemeOver k}
    (f : SmOverHom X Y) (g : SmOverHom Y Z) : SmOverHom X Z where
  hom := f.hom ≫ g.hom
  over := by
    calc
      (f.hom ≫ g.hom) ≫ Z.structMap = f.hom ≫ (g.hom ≫ Z.structMap) := by simp [Category.assoc]
      _ = f.hom ≫ Y.structMap := by rw [g.over]
      _ = X.structMap := f.over

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

end Boundary

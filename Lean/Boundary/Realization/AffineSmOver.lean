import Boundary.SmOver
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

universe u

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

namespace Boundary
namespace Realization

variable {k : Type u} [Field k] [PerfectField k]

/-- The full subcategory of affine smooth schemes over `k`. -/
abbrev AffineSmOver (k : Type u) [Field k] [PerfectField k] :=
  FullSubcategory fun X : Geometry.SmSchemeOver k => IsAffine X.scheme

/-- The inclusion of affine smooth schemes into `Sm/k`. -/
abbrev affineSmOverInclusion :
    AffineSmOver k ⥤ Geometry.SmSchemeOver k :=
  fullSubcategoryInclusion _

instance (X : AffineSmOver k) : IsAffine X.obj.scheme :=
  X.property

/-- The canonical affine open underlying the whole affine smooth scheme. -/
abbrev affineSmOverTop (X : AffineSmOver k) : X.obj.scheme.affineOpens :=
  ⟨⊤, AlgebraicGeometry.isAffineOpen_top X.obj.scheme⟩

@[simp]
theorem affineSmOverTop_val (X : AffineSmOver k) :
    ((affineSmOverTop X : X.obj.scheme.affineOpens) : X.obj.scheme.Opens) = ⊤ :=
  rfl

@[simp]
theorem affineSmOverTop_preimage
    {X Y : AffineSmOver k} (f : X ⟶ Y) :
    f.hom ⁻¹ᵁ ((affineSmOverTop Y : Y.obj.scheme.affineOpens) : Y.obj.scheme.Opens) =
      ((affineSmOverTop X : X.obj.scheme.affineOpens) : X.obj.scheme.Opens) := by
  ext x
  simp [affineSmOverTop]

theorem affineSmOverTop_le_preimage
    {X Y : AffineSmOver k} (f : X ⟶ Y) :
    ((affineSmOverTop X : X.obj.scheme.affineOpens) : X.obj.scheme.Opens) ≤
      f.hom ⁻¹ᵁ ((affineSmOverTop Y : Y.obj.scheme.affineOpens) : Y.obj.scheme.Opens) := by
  simpa [affineSmOverTop] using
    (le_rfl : (⊤ : X.obj.scheme.Opens) ≤ f.hom ⁻¹ᵁ (⊤ : Y.obj.scheme.Opens))

/-- On an affine smooth scheme, the top affine open is terminal in the affine-open category. -/
def affineSmOverTopIsTerminal (X : AffineSmOver k) :
    IsTerminal (affineSmOverTop X : X.obj.scheme.affineOpens) where
  lift U := homOfLE (show U.1 ≤ (affineSmOverTop X : X.obj.scheme.affineOpens).1 from le_top)
  uniq U m _ := by
    apply Subsingleton.elim

/-- Global sections over affine opens are computed by evaluation at the top affine open
for an affine smooth scheme. -/
noncomputable abbrev limitAffineOpensPresheafIsoTop
    {C : Type*} [Category C]
    (X : AffineSmOver k) (F : X.obj.scheme.affineOpensᵒᵖ ⥤ C) [HasLimit F] :
    limit F ≅ F.obj (Opposite.op (affineSmOverTop X)) := by
  letI : HasTerminal X.obj.scheme.affineOpens :=
    (affineSmOverTopIsTerminal X).hasTerminal
  haveI : HasInitial X.obj.scheme.affineOpensᵒᵖ := by infer_instance
  let e : ⊥_ (X.obj.scheme.affineOpens)ᵒᵖ ≅ Opposite.op (affineSmOverTop X) :=
    initialIsoIsInitial (initialOpOfTerminal (affineSmOverTopIsTerminal X))
  exact (limitOfInitial (F := F)).trans (F.mapIso e)

end Realization
end Boundary

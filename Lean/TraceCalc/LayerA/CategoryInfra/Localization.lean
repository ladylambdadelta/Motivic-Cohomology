import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso

universe u v

open CategoryTheory

namespace TraceCalc
namespace CategoryInfra

/-- Abstract interface for a localization step `Q : C ⥤ D` with marked weak equivalences in `C`. -/
structure LocalizationInterface where
  C : Type u
  D : Type u
  [catC : Category.{v} C]
  [catD : Category.{v} D]
  W : ∀ {X Y : C}, (X ⟶ Y) → Prop
  QObj : C → D
  QMap : ∀ {X Y : C}, (X ⟶ Y) → (QObj X ⟶ QObj Y)

attribute [instance] LocalizationInterface.catC LocalizationInterface.catD

namespace LocalizationInterface

def map_id (target : LocalizationInterface.{u, v}) : Prop :=
  ∀ X : target.C, target.QMap (𝟙 X) = 𝟙 (target.QObj X)

def map_comp (target : LocalizationInterface.{u, v}) : Prop :=
  ∀ {X Y Z : target.C} (f : X ⟶ Y) (g : Y ⟶ Z),
    target.QMap (f ≫ g) = target.QMap f ≫ target.QMap g

def transportQObj
    (target : LocalizationInterface.{u, v})
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (sourceCategoryAlignment : target.C = C)
    (targetCategoryAlignment : target.D = D) :
    C → D := by
  cases sourceCategoryAlignment
  cases targetCategoryAlignment
  letI : Category.{v} target.C := target.catC
  letI : Category.{v} target.D := target.catD
  exact target.QObj

end LocalizationInterface

structure LocalizationInterfaceLaws (target : LocalizationInterface.{u, v}) where
  map_id : target.map_id
  map_comp : target.map_comp

structure LocalizationInterfaceData (target : LocalizationInterface.{u, v}) where
  laws : LocalizationInterfaceLaws target
  invertsW : ∀ {X Y : target.C} (f : X ⟶ Y), target.W f → (target.QObj X ≅ target.QObj Y)

/-- Proof-relevant data for the infinity-side localization universal property.
This sits on top of the structural `LocalizationInterface`; functoriality and
weak-equivalence inversion live separately in `LocalizationInterfaceData`, while
code that needs an actual universal-property witness can ask for this structure
explicitly. -/
structure LocalizationUniversalPropertyData (L : LocalizationInterface) where
  liftObj :
    ∀ {E : Type u},
      (FObj : L.C → E) →
        (respectsW : ∀ {X Y : L.C} (f : X ⟶ Y), L.W f → FObj X = FObj Y) → L.D → E
  lift_commutes :
    ∀ {E : Type u}
      (FObj : L.C → E)
      (respectsW : ∀ {X Y : L.C} (f : X ⟶ Y), L.W f → FObj X = FObj Y)
      (X : L.C),
        liftObj FObj respectsW (L.QObj X) = FObj X

/-- Separate theorem target for the pi0 Verdier-localization shadow.

This is intentionally not bundled into `LocalizationUniversalPropertyData`:
passing from an infinity-level universal property to its triangulated / pi0
shadow is a distinct truncation bridge theorem, not data already carried by the
infinity witness itself. -/
structure LocalizationPiZeroShadowTheorem (L : LocalizationInterface) where
  shadowRel : L.D → L.D → Prop
  shadow_refl : ∀ X : L.D, shadowRel X X
  shadow_symm : ∀ {X Y : L.D}, shadowRel X Y → shadowRel Y X
  shadow_trans : ∀ {X Y Z : L.D}, shadowRel X Y → shadowRel Y Z → shadowRel X Z
  weakEquivalenceMapsToShadow :
    ∀ {X Y : L.C} (f : X ⟶ Y), L.W f → shadowRel (L.QObj X) (L.QObj Y)

end CategoryInfra
end TraceCalc
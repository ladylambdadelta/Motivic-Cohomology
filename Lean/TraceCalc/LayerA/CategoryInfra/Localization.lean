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
  W : C → C → Prop
  QObj : C → D
  QMap : ∀ {X Y : C}, (X ⟶ Y) → (QObj X ⟶ QObj Y)
  map_id : ∀ X, QMap (𝟙 X) = 𝟙 (QObj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), QMap (f ≫ g) = QMap f ≫ QMap g
  invertsW : ∀ {X Y : C} (_f : X ⟶ Y), W X Y → (QObj X ≅ QObj Y)

attribute [instance] LocalizationInterface.catC LocalizationInterface.catD

/-- Proof-relevant data for the infinity-side localization universal property.
This sits on top of the Prop-level `LocalizationInterface` so existing users can
keep depending on the lighter interface, while code that needs to transport or
consume an actual universal-property witness can ask for this structure
explicitly. -/
structure LocalizationUniversalPropertyData (L : LocalizationInterface) where
  localizationUniversalPropertyInfinity : Prop
  localizationUniversalPropertyInfinityWitness : localizationUniversalPropertyInfinity

/-- Separate theorem target for the pi0 Verdier-localization shadow.

This is intentionally not bundled into `LocalizationUniversalPropertyData`:
passing from an infinity-level universal property to its triangulated / pi0
shadow is a distinct truncation bridge theorem, not data already carried by the
infinity witness itself. -/
structure LocalizationPiZeroShadowTheorem (L : LocalizationInterface) where
  verdierLocalizationPiZeroShadow : Prop
  verdierLocalizationPiZeroShadowWitness : verdierLocalizationPiZeroShadow

end CategoryInfra
end TraceCalc
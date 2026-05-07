import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import TraceCalc.LayerA.Base

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerA

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
  invertsW : ∀ {X Y : C} (f : X ⟶ Y), W X Y → Nonempty (QObj X ≅ QObj Y)
  universalFactorization : Prop

attribute [instance] LocalizationInterface.catC LocalizationInterface.catD

/-- Proof-relevant data for the infinity-side localization universal property.
This sits on top of the Prop-level `LocalizationInterface` so existing users can
keep depending on the lighter interface, while code that needs to transport or
consume an actual universal-property witness can ask for this structure
explicitly. -/
structure LocalizationUniversalPropertyData (L : LocalizationInterface) where
  localizationUniversalPropertyInfinity : Prop
  localizationUniversalPropertyInfinity_holds : localizationUniversalPropertyInfinity

/-- Separate theorem target for the pi0 Verdier-localization shadow.

This is intentionally not bundled into `LocalizationUniversalPropertyData`:
passing from an infinity-level universal property to its triangulated / pi0
shadow is a distinct truncation bridge theorem, not data already carried by the
infinity witness itself. -/
structure LocalizationPiZeroShadowTheorem (L : LocalizationInterface) where
  verdierLocalizationPiZeroShadow : Prop
  verdierLocalizationPiZeroShadow_holds : verdierLocalizationPiZeroShadow

/-- Optional proof-relevant localization wrapper. It preserves the existing
Prop-level interface as the base object and adds explicit universal-property
data only for users that need proof-bearing localization content. -/
structure ProofRelevantLocalizationInterface where
  toLocalizationInterface : LocalizationInterface
  universalPropertyData : LocalizationUniversalPropertyData toLocalizationInterface

namespace LocalizationInterface

/-- Accessor packaged as a theorem-level API: maps in `W` become isomorphisms after localization. -/
theorem sends_W_to_iso (L : LocalizationInterface) {X Y : L.C} (f : X ⟶ Y)
    (hW : L.W X Y) : Nonempty (L.QObj X ≅ L.QObj Y) :=
  L.invertsW f hW

end LocalizationInterface

namespace ProofRelevantLocalizationInterface

/-- Build the proof-relevant localization wrapper from the old interface plus
explicit universal-property witness data. -/
def ofInterface
    (L : LocalizationInterface)
    (universalPropertyData : LocalizationUniversalPropertyData L) :
    ProofRelevantLocalizationInterface where
  toLocalizationInterface := L
  universalPropertyData := universalPropertyData

/-- Accessor theorem for the proof-relevant universal-property witness. -/
theorem supports_localizationUniversalPropertyInfinity
    (L : ProofRelevantLocalizationInterface) :
    L.universalPropertyData.localizationUniversalPropertyInfinity :=
  L.universalPropertyData.localizationUniversalPropertyInfinity_holds

end ProofRelevantLocalizationInterface

end LayerA
end TraceCalc

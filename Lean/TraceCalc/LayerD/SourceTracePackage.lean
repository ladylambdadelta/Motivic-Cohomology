import TraceCalc.LayerA.Base
import TraceCalc.LayerA.CategoryInfra.Localization

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerD

/-- Concrete localization-compatibility data exported by a source trace package.
It records how the package's weak-equivalence relation and object-level
localization map agree with the bundled `LocalizationInterface`, together with
the interface functoriality laws. -/
structure LocalizationCompatibilityData
    {Envelope : Type u}
    {Localized : Type u}
    [Category.{v} Envelope]
    [Category.{v} Localized]
    (weakEquivalence : Envelope → Envelope → Prop)
    (localizeObj : Envelope → Localized)
    (localizationInterface : CategoryInfra.LocalizationInterface) where
  weakEquivalenceAlignment : HEq localizationInterface.W weakEquivalence
  localizeObjAlignment : HEq localizationInterface.QObj localizeObj
  localizationMapId :
    ∀ X : localizationInterface.C,
      localizationInterface.QMap (𝟙 X) = 𝟙 (localizationInterface.QObj X)
  localizationMapComp :
    ∀ {X Y Z : localizationInterface.C}
      (f : X ⟶ Y) (g : Y ⟶ Z),
      localizationInterface.QMap (f ≫ g) =
        localizationInterface.QMap f ≫ localizationInterface.QMap g

/-- Consumer-side interface for the source trace package that Layer B will eventually
export into Layer D.

This deliberately avoids importing Layer B. It records only the abstract seam that the
Layer D universal-property and comparison contracts consume: raw syntax, the free stable
envelope, a motivically localized target, and the named shape axioms of that localization.
-/
structure SourceTracePackage where
  Syntax : Type u
  Envelope : Type u
  Localized : Type u
  [catEnvelope : Category.{v} Envelope]
  [catLocalized : Category.{v} Localized]
  includeSyntax : Syntax → Envelope
  stableEnvelope : LayerA.StableLike Envelope
  stableLocalized : LayerA.StableLike Localized
  weakEquivalence : Envelope → Envelope → Prop
  localizeObj : Envelope → Localized
  localizationInterface : CategoryInfra.LocalizationInterface
  localization_matches :
    localizationInterface.C = Envelope ∧
    localizationInterface.D = Localized
  localizationCompatibility :
    LocalizationCompatibilityData
      weakEquivalence localizeObj localizationInterface
  envelopeUniversalProperty : Prop
  hasNisnevichShape : Prop
  hasA1InvarianceShape : Prop
  hasTateInvertibilityShape : Prop

attribute [instance] SourceTracePackage.catEnvelope SourceTracePackage.catLocalized

namespace SourceTracePackage

/-- Additional theorem-sized source-side fields that Layer B will eventually have to export
alongside the consumer package before Layer D can treat the source-construction milestone as
covered. This is intentionally a cautious seam: the package provides the ambient source-side
objects and localization data, while the witness records the named theorem targets still needed
for the source-construction slice of the roadmap. -/
structure SourceConstructionWitness (S : SourceTracePackage.{u, v}) where
  symmetricMonoidalPiZero : Prop
  symmetricMonoidalPiZero_holds : symmetricMonoidalPiZero
  symmetricMonoidalInfinity : Prop
  symmetricMonoidalInfinity_holds : symmetricMonoidalInfinity
  triangulatedStablePiZero : Prop
  triangulatedStablePiZero_holds : triangulatedStablePiZero
  triangulatedStableInfinity : Prop
  triangulatedStableInfinity_holds : triangulatedStableInfinity
  a1InvariancePiZero : Prop
  a1InvariancePiZero_holds : a1InvariancePiZero
  a1InvarianceInfinity : Prop
  a1InvarianceInfinity_holds : a1InvarianceInfinity
  nisnevichDescentPiZero : Prop
  nisnevichDescentPiZero_holds : nisnevichDescentPiZero
  nisnevichDescentInfinity : Prop
  nisnevichDescentInfinity_holds : nisnevichDescentInfinity
  localizationPiZero : Prop
  localizationPiZero_holds : localizationPiZero
  localizationInfinity : Prop
  localizationInfinity_holds : localizationInfinity
  tateStabilizationPiZero : Prop
  tateStabilizationPiZero_holds : tateStabilizationPiZero
  tateStabilizationInfinity : Prop
  tateStabilizationInfinity_holds : tateStabilizationInfinity

def SourceConstructionWitness.readinessData
    {S : SourceTracePackage.{u, v}} (W : SourceConstructionWitness S) : Prop :=
  W.symmetricMonoidalPiZero ∧
    W.symmetricMonoidalInfinity ∧
    W.triangulatedStablePiZero ∧
    W.triangulatedStableInfinity ∧
    W.a1InvariancePiZero ∧
    W.a1InvarianceInfinity ∧
    W.nisnevichDescentPiZero ∧
    W.nisnevichDescentInfinity ∧
    W.localizationPiZero ∧
    W.localizationInfinity ∧
    W.tateStabilizationPiZero ∧
    W.tateStabilizationInfinity

theorem SourceConstructionWitness.readinessData_of_fields
    {S : SourceTracePackage.{u, v}} (W : SourceConstructionWitness S) :
    W.readinessData := by
  exact ⟨W.symmetricMonoidalPiZero_holds, W.symmetricMonoidalInfinity_holds,
    W.triangulatedStablePiZero_holds, W.triangulatedStableInfinity_holds,
    W.a1InvariancePiZero_holds, W.a1InvarianceInfinity_holds,
    W.nisnevichDescentPiZero_holds, W.nisnevichDescentInfinity_holds,
    W.localizationPiZero_holds, W.localizationInfinity_holds,
    W.tateStabilizationPiZero_holds, W.tateStabilizationInfinity_holds⟩

/-- The source-side geometric shape axioms exported to Layer D as a single bundled `Prop`. -/
def geometricShapeAxioms (S : SourceTracePackage.{u, v}) : Prop :=
  S.hasNisnevichShape ∧ S.hasA1InvarianceShape ∧ S.hasTateInvertibilityShape

/-- Minimal seam theorem: the package exposes a localization interface with the advertised
source and target categories; compatibility with the exported weak equivalence relation and
object function is tracked explicitly as separate propositions, not by definitional equality. -/
theorem localization_interface_exports (S : SourceTracePackage.{u, v}) :
    S.localizationInterface.C = S.Envelope ∧
    S.localizationInterface.D = S.Localized :=
  S.localization_matches

/-- The type of concrete localization-compatibility data exported alongside the
localization interface. -/
abbrev LocalizationCompatibilityType (S : SourceTracePackage.{u, v}) :=
  LocalizationCompatibilityData
    S.weakEquivalence S.localizeObj S.localizationInterface

/-- The compatibility statements exported alongside the localization interface are
recorded as concrete law-bearing data. -/
def localizationCompatibilityData (S : SourceTracePackage.{u, v}) :
    S.LocalizationCompatibilityType :=
  S.localizationCompatibility

theorem localizationCompatibilityData_weakEquivalenceAlignment
    (S : SourceTracePackage.{u, v}) :
    HEq S.localizationInterface.W S.weakEquivalence :=
  S.localizationCompatibility.weakEquivalenceAlignment

theorem localizationCompatibilityData_localizeObjAlignment
    (S : SourceTracePackage.{u, v}) :
    HEq S.localizationInterface.QObj S.localizeObj :=
  S.localizationCompatibility.localizeObjAlignment

theorem localizationCompatibilityData_map_id
    (S : SourceTracePackage.{u, v}) :
    ∀ X : S.localizationInterface.C,
      S.localizationInterface.QMap (𝟙 X) =
        𝟙 (S.localizationInterface.QObj X) :=
  S.localizationCompatibility.localizationMapId

theorem localizationCompatibilityData_map_comp
    (S : SourceTracePackage.{u, v}) :
    ∀ {X Y Z : S.localizationInterface.C}
      (f : X ⟶ Y) (g : Y ⟶ Z),
      S.localizationInterface.QMap (f ≫ g) =
        S.localizationInterface.QMap f ≫ S.localizationInterface.QMap g :=
  S.localizationCompatibility.localizationMapComp

/-- Consumer-facing readiness proposition for the future Layer B -> Layer D merge seam. -/
def readyForUniversalProperty (S : SourceTracePackage.{u, v}) : Prop :=
  S.envelopeUniversalProperty ∧ S.geometricShapeAxioms

theorem readyForUniversalProperty_components (S : SourceTracePackage.{u, v}) :
    S.readyForUniversalProperty →
      S.envelopeUniversalProperty ∧ S.geometricShapeAxioms := by
  intro h
  exact h

end SourceTracePackage

end LayerD
end TraceCalc
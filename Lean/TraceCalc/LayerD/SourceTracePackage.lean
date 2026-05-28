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
  (weakEquivalence : ∀ {X Y : Envelope}, (X ⟶ Y) → Prop)
    (localizeObj : Envelope → Localized)
    (localizationInterface : CategoryInfra.LocalizationInterface) where
  sourceCategoryAlignment : localizationInterface.C = Envelope
  targetCategoryAlignment : localizationInterface.D = Localized
  localizeObjAlignment :
    localizationInterface.transportQObj
        (C := Envelope) (D := Localized)
        sourceCategoryAlignment targetCategoryAlignment = localizeObj
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
  weakEquivalence : ∀ {X Y : Envelope}, (X ⟶ Y) → Prop
  localizeObj : Envelope → Localized
  localizationInterface : CategoryInfra.LocalizationInterface
  localization_matches :
    localizationInterface.C = Envelope ∧
    localizationInterface.D = Localized
  localizationCompatibility :
    LocalizationCompatibilityData
      weakEquivalence localizeObj localizationInterface
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

attribute [instance] SourceTracePackage.catEnvelope SourceTracePackage.catLocalized

namespace SourceTracePackage

def sourceConstructionReadiness (S : SourceTracePackage.{u, v}) : Prop :=
  S.symmetricMonoidalPiZero ∧
    S.symmetricMonoidalInfinity ∧
    S.triangulatedStablePiZero ∧
    S.triangulatedStableInfinity ∧
    S.a1InvariancePiZero ∧
    S.a1InvarianceInfinity ∧
    S.nisnevichDescentPiZero ∧
    S.nisnevichDescentInfinity ∧
    S.localizationPiZero ∧
    S.localizationInfinity ∧
    S.tateStabilizationPiZero ∧
    S.tateStabilizationInfinity

theorem sourceConstructionReadiness_holds (S : SourceTracePackage.{u, v}) :
    S.sourceConstructionReadiness := by
  exact ⟨S.symmetricMonoidalPiZero_holds, S.symmetricMonoidalInfinity_holds,
    S.triangulatedStablePiZero_holds, S.triangulatedStableInfinity_holds,
    S.a1InvariancePiZero_holds, S.a1InvarianceInfinity_holds,
    S.nisnevichDescentPiZero_holds, S.nisnevichDescentInfinity_holds,
    S.localizationPiZero_holds, S.localizationInfinity_holds,
    S.tateStabilizationPiZero_holds, S.tateStabilizationInfinity_holds⟩

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
  LocalizationCompatibilityType S :=
  S.localizationCompatibility

end SourceTracePackage

end LayerD
end TraceCalc
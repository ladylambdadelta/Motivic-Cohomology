import TraceCalc.LayerA.CategoryInfra.Localization

universe u v

open CategoryTheory

namespace TraceCalc
namespace LayerB

/-- Abstract interface for the free stable trace envelope attached to raw trace syntax. -/
structure FreeStableTraceEnvelope where
  Syntax : Type u
  Envelope : Type u
  [catEnvelope : Category.{v} Envelope]
  includeSyntax : Syntax → Envelope
  universalProperty : Prop

attribute [instance] FreeStableTraceEnvelope.catEnvelope

/-- Abstract interface for motivic localization of the free stable trace envelope. -/
structure MotivicLocalization where
  F : FreeStableTraceEnvelope
  Loc : Type u
  [catLoc : Category.{v} Loc]
  localizeObj : F.Envelope → Loc
  motivicWeakEq : ∀ {X Y : F.Envelope}, (X ⟶ Y) → Prop
  localization : CategoryInfra.LocalizationInterface
  localization_matches : localization.C = F.Envelope ∧ localization.D = Loc
  localizationLaws : CategoryInfra.LocalizationInterfaceLaws localization
  localizeObj_alignment :
    localization.transportQObj
        (C := F.Envelope) (D := Loc)
        localization_matches.1 localization_matches.2 = localizeObj
  hasNisnevichShape : Prop
  hasA1InvarianceShape : Prop
  hasTateInvertibilityShape : Prop

attribute [instance] MotivicLocalization.catLoc

namespace MotivicLocalization

/-- Source-category alignment exported by the localization package. -/
theorem sourceCategoryAlignment (M : MotivicLocalization) :
    M.localization.C = M.F.Envelope :=
  M.localization_matches.1

/-- Target-category alignment exported by the localization package. -/
theorem targetCategoryAlignment (M : MotivicLocalization) :
    M.localization.D = M.Loc :=
  M.localization_matches.2

end MotivicLocalization

end LayerB
end TraceCalc

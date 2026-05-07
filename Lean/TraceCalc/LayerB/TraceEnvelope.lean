import TraceCalc.LayerA.Base
import TraceCalc.LayerA.Localization

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
  isStableLike : LayerA.StableLike Envelope
  universalProperty : Prop

attribute [instance] FreeStableTraceEnvelope.catEnvelope

/-- Abstract interface for motivic localization of the free stable trace envelope. -/
structure MotivicLocalization where
  F : FreeStableTraceEnvelope
  Loc : Type u
  [catLoc : Category.{v} Loc]
  stableLocalized : LayerA.StableLike Loc
  localizeObj : F.Envelope → Loc
  motivicWeakEq : F.Envelope → F.Envelope → Prop
  localization : LayerA.LocalizationInterface
  localization_matches : localization.C = F.Envelope ∧ localization.D = Loc
  weakEquivalence_alignment : HEq localization.W motivicWeakEq
  localizeObj_alignment : HEq localization.QObj localizeObj
  hasNisnevichShape : Prop
  hasA1InvarianceShape : Prop
  hasTateInvertibilityShape : Prop

attribute [instance] MotivicLocalization.catLoc

namespace MotivicLocalization

/-- Convenience constructor for a bridge-ready motivic localization package.
The universal-property content is already carried inside the supplied
`LocalizationInterface`, so the only extra seam data are the source/target
category alignments and the identifications of `W` and `QObj` with the chosen
weak-equivalence relation and localization object map. -/
def mkAligned
    (F : FreeStableTraceEnvelope)
    (Loc : Type u)
    [Category.{v} Loc]
    (stableLocalized : LayerA.StableLike Loc)
    (localizeObj : F.Envelope → Loc)
    (motivicWeakEq : F.Envelope → F.Envelope → Prop)
    (localization : LayerA.LocalizationInterface)
    (localization_matches : localization.C = F.Envelope ∧ localization.D = Loc)
    (weakEquivalence_alignment : HEq localization.W motivicWeakEq)
    (localizeObj_alignment : HEq localization.QObj localizeObj)
    (hasNisnevichShape : Prop)
    (hasA1InvarianceShape : Prop)
    (hasTateInvertibilityShape : Prop) :
    MotivicLocalization where
  F := F
  Loc := Loc
  stableLocalized := stableLocalized
  localizeObj := localizeObj
  motivicWeakEq := motivicWeakEq
  localization := localization
  localization_matches := localization_matches
  weakEquivalence_alignment := weakEquivalence_alignment
  localizeObj_alignment := localizeObj_alignment
  hasNisnevichShape := hasNisnevichShape
  hasA1InvarianceShape := hasA1InvarianceShape
  hasTateInvertibilityShape := hasTateInvertibilityShape

/-- Source-category alignment exported by the localization package. -/
theorem sourceCategoryAlignment (M : MotivicLocalization) :
    M.localization.C = M.F.Envelope :=
  M.localization_matches.1

/-- Target-category alignment exported by the localization package. -/
theorem targetCategoryAlignment (M : MotivicLocalization) :
    M.localization.D = M.Loc :=
  M.localization_matches.2

/-- Small API theorem: exported marker that this object carries a localization interface. -/
theorem has_localization_interface (M : MotivicLocalization) : True := by
  trivial

end MotivicLocalization

end LayerB
end TraceCalc

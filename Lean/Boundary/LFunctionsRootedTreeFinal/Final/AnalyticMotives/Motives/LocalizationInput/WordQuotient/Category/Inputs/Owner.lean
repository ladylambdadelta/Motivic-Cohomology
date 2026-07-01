import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Atoms.Owner

/-!
# Localization inputs as arrows in the localized word category

This file gives each localization input a named source object, target object,
forward arrow, inverse arrow, and isomorphism in the wrapped localized-word
category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The wrapped source object of a localization input. -/
def TraceLocalizationInput.localizedSourceObject
    (input : TraceLocalizationInput) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject input.sourceObject

/-- The wrapped target object of a localization input. -/
def TraceLocalizationInput.localizedTargetObject
    (input : TraceLocalizationInput) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject input.targetObject

/-- The forward arrow of a localization input in the localized word category. -/
def TraceLocalizationInput.localizedForwardArrow
    (input : TraceLocalizationInput) :
    TraceLocalizedWordHom
      input.localizedSourceObject
      input.localizedTargetObject :=
  (TraceLocalizationAtom.forward input).localizedArrow

/-- The inverse arrow of a localization input in the localized word category. -/
def TraceLocalizationInput.localizedInverseArrow
    (input : TraceLocalizationInput) :
    TraceLocalizedWordHom
      input.localizedTargetObject
      input.localizedSourceObject :=
  (TraceLocalizationAtom.inverse input).localizedArrow

/-- The localized isomorphism of a localization input using named localized objects. -/
def TraceLocalizationInput.localizedIso
    (input : TraceLocalizationInput) :
    CategoryTheory.Iso
      input.localizedSourceObject
      input.localizedTargetObject :=
  input.localizedWordIso

/-- The named localized source object is the wrapped trace source object. -/
theorem TraceLocalizationInput.localizedSourceObject_eq
    (input : TraceLocalizationInput) :
    input.localizedSourceObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The named localized target object is the wrapped trace target object. -/
theorem TraceLocalizationInput.localizedTargetObject_eq
    (input : TraceLocalizationInput) :
    input.localizedTargetObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The named forward arrow is the forward atom arrow. -/
theorem TraceLocalizationInput.localizedForwardArrow_eq_forwardAtom
    (input : TraceLocalizationInput) :
    input.localizedForwardArrow =
      (TraceLocalizationAtom.forward input).localizedArrow :=
  rfl

/-- The named inverse arrow is the inverse atom arrow. -/
theorem TraceLocalizationInput.localizedInverseArrow_eq_inverseAtom
    (input : TraceLocalizationInput) :
    input.localizedInverseArrow =
      (TraceLocalizationAtom.inverse input).localizedArrow :=
  rfl

/-- The hom of the named localized isomorphism is the named forward arrow. -/
theorem TraceLocalizationInput.localizedIso_hom
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedIso input).hom =
      input.localizedForwardArrow :=
  rfl

/-- The inverse of the named localized isomorphism is the named inverse arrow. -/
theorem TraceLocalizationInput.localizedIso_inv
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedIso input).inv =
      input.localizedInverseArrow :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

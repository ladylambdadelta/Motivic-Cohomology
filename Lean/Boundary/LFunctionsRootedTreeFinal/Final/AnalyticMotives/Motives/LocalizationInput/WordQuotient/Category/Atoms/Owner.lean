import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Owner

/-!
# Atom arrows in the formal localized word category

This file exposes each formal localization atom as a one-step arrow in the
wrapped localized-word category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The wrapped source object of a formal localization atom. -/
def TraceLocalizationAtom.localizedSourceObject
    (atom : TraceLocalizationAtom) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject atom.sourceObject

/-- The wrapped target object of a formal localization atom. -/
def TraceLocalizationAtom.localizedTargetObject
    (atom : TraceLocalizationAtom) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject atom.targetObject

/-- The one-atom arrow in the formal localized word category. -/
def TraceLocalizationAtom.localizedArrow
    (atom : TraceLocalizationAtom) :
    TraceLocalizedWordHom
      atom.localizedSourceObject
      atom.localizedTargetObject :=
  TraceLocalizationWordClass.ofWord
    (TraceLocalizationWord.ofAtom atom)

/-- The localized source object of a forward atom is the input source object. -/
theorem TraceLocalizationAtom.forward_localizedSourceObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedSourceObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The localized target object of a forward atom is the input target object. -/
theorem TraceLocalizationAtom.forward_localizedTargetObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedTargetObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The localized source object of an inverse atom is the input target object. -/
theorem TraceLocalizationAtom.inverse_localizedSourceObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedSourceObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The localized target object of an inverse atom is the input source object. -/
theorem TraceLocalizationAtom.inverse_localizedTargetObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedTargetObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The localized arrow of a forward atom is the forward input word class. -/
theorem TraceLocalizationAtom.forward_localizedArrow
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedArrow =
      TraceLocalizationWordClass.ofInputForward input :=
  rfl

/-- The localized arrow of an inverse atom is the inverse input word class. -/
theorem TraceLocalizationAtom.inverse_localizedArrow
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedArrow =
      TraceLocalizationWordClass.ofInputInverse input :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

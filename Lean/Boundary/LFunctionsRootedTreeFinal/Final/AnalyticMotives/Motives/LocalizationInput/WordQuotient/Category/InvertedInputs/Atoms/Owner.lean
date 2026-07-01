import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Atoms.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.InvertedInputs.Owner

/-!
# Atom arrows for inverted localization inputs

This file identifies the two arrows of a localized-input isomorphism with the
localized arrows of the corresponding forward and inverse atoms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source object of the forward atom is the source of the localized-input isomorphism. -/
theorem TraceLocalizationInput.forwardAtom_localizedSourceObject_eq_isoSource
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedSourceObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The target object of the forward atom is the target of the localized-input isomorphism. -/
theorem TraceLocalizationInput.forwardAtom_localizedTargetObject_eq_isoTarget
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).localizedTargetObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The source object of the inverse atom is the target of the localized-input isomorphism. -/
theorem TraceLocalizationInput.inverseAtom_localizedSourceObject_eq_isoTarget
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedSourceObject =
      TraceLocalizedWordObject.ofTraceObject input.targetObject :=
  rfl

/-- The target object of the inverse atom is the source of the localized-input isomorphism. -/
theorem TraceLocalizationInput.inverseAtom_localizedTargetObject_eq_isoSource
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).localizedTargetObject =
      TraceLocalizedWordObject.ofTraceObject input.sourceObject :=
  rfl

/-- The hom of a localized-input isomorphism is the localized forward-atom arrow. -/
theorem TraceLocalizationInput.localizedWordIso_hom_eq_forwardAtom_arrow
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).hom =
      (TraceLocalizationAtom.forward input).localizedArrow :=
  rfl

/-- The inverse of a localized-input isomorphism is the localized inverse-atom arrow. -/
theorem TraceLocalizationInput.localizedWordIso_inv_eq_inverseAtom_arrow
    (input : TraceLocalizationInput) :
    (TraceLocalizationInput.localizedWordIso input).inv =
      (TraceLocalizationAtom.inverse input).localizedArrow :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

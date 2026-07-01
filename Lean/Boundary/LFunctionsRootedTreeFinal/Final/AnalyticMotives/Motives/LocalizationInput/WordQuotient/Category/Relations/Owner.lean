import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Words.Owner

/-!
# Word-relation equalities in the formal localized word category

This file turns generated formal localization word relations into equalities of
localized categorical arrows.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A generated word relation gives equality of localized categorical arrows. -/
theorem TraceLocalizationWordRelation.localizedArrow_eq
    {source target : TraceCorQObject}
    {left right : TraceLocalizationWord source target}
    (relation : TraceLocalizationWordRelation left right) :
    left.localizedArrow =
      right.localizedArrow :=
  TraceLocalizationWordClass.sound relation

/-- Forward-inverse cancellation gives localized categorical identity. -/
theorem TraceLocalizationWordRelation.localizedArrow_forwardInverse
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.forwardThenInverse input).localizedArrow =
      (TraceLocalizationWord.identity input.sourceObject).localizedArrow :=
  TraceLocalizationWordRelation.localizedArrow_eq
    (TraceLocalizationWordRelation.forwardInverse input)

/-- Inverse-forward cancellation gives localized categorical identity. -/
theorem TraceLocalizationWordRelation.localizedArrow_inverseForward
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.inverseThenForward input).localizedArrow =
      (TraceLocalizationWord.identity input.targetObject).localizedArrow :=
  TraceLocalizationWordRelation.localizedArrow_eq
    (TraceLocalizationWordRelation.inverseForward input)

/-- A word relation remains an arrow equality after a fixed prefix word. -/
theorem TraceLocalizationWordRelation.localizedArrow_withPrefix
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord second third}
    (prefix : TraceLocalizationWord first second)
    (relation : TraceLocalizationWordRelation left right) :
    (TraceLocalizationWord.comp prefix left).localizedArrow =
      (TraceLocalizationWord.comp prefix right).localizedArrow :=
  TraceLocalizationWordRelation.localizedArrow_eq
    (TraceLocalizationWordRelation.withPrefix prefix relation)

/-- A word relation remains an arrow equality before a fixed suffix word. -/
theorem TraceLocalizationWordRelation.localizedArrow_withSuffix
    {first second third : TraceCorQObject}
    {left right : TraceLocalizationWord first second}
    (relation : TraceLocalizationWordRelation left right)
    (suffix : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left suffix).localizedArrow =
      (TraceLocalizationWord.comp right suffix).localizedArrow :=
  TraceLocalizationWordRelation.localizedArrow_eq
    (TraceLocalizationWordRelation.withSuffix relation suffix)

end AnalyticMotives
end LFunctions
end Boundary

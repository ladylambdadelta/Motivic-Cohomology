import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Owner

/-!
# Word arrows in the formal localized word category

This file exposes every formal localization word as an arrow in the wrapped
localized-word category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The wrapped source object of a formal localization word. -/
def TraceLocalizationWord.localizedSourceObject
    {source target : TraceCorQObject}
    (_word : TraceLocalizationWord source target) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject source

/-- The wrapped target object of a formal localization word. -/
def TraceLocalizationWord.localizedTargetObject
    {source target : TraceCorQObject}
    (_word : TraceLocalizationWord source target) :
    TraceLocalizedWordObject :=
  TraceLocalizedWordObject.ofTraceObject target

/-- The localized categorical arrow represented by a formal localization word. -/
def TraceLocalizationWord.localizedArrow
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    TraceLocalizedWordHom
      word.localizedSourceObject
      word.localizedTargetObject :=
  TraceLocalizationWordClass.ofWord word

/-- The localized arrow of an identity word is the localized identity. -/
theorem TraceLocalizationWord.localizedArrow_identity
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).localizedArrow =
      TraceLocalizationWordClass.identity object :=
  rfl

/-- The localized arrow of a one-atom word is the one-atom quotient class. -/
theorem TraceLocalizationWord.localizedArrow_ofAtom
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).localizedArrow =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofAtom atom) :=
  rfl

/-- The localized arrow of a forward input word is the forward input class. -/
theorem TraceLocalizationWord.localizedArrow_ofInputForward
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).localizedArrow =
      TraceLocalizationWordClass.ofInputForward input :=
  rfl

/-- The localized arrow of an inverse input word is the inverse input class. -/
theorem TraceLocalizationWord.localizedArrow_ofInputInverse
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).localizedArrow =
      TraceLocalizationWordClass.ofInputInverse input :=
  rfl

/-- The localized arrow of a concatenated word is category composition of localized arrows. -/
theorem TraceLocalizationWord.localizedArrow_comp
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).localizedArrow =
      TraceLocalizationWordClass.comp
        left.localizedArrow
        right.localizedArrow :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

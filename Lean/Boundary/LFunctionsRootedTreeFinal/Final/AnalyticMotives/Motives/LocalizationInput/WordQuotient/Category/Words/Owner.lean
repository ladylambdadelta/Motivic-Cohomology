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

/-- The wrapped source object has the word's source as underlying object. -/
theorem TraceLocalizationWord.localizedSourceObject_underlying
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedSourceObject.underlying =
      source :=
  rfl

/-- The wrapped target object has the word's target as underlying object. -/
theorem TraceLocalizationWord.localizedTargetObject_underlying
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedTargetObject.underlying =
      target :=
  rfl

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

/-- The localized arrow of an identity word is the categorical identity. -/
theorem TraceLocalizationWord.localizedArrow_identity_eq_categoryIdentity
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).localizedArrow =
      (𝟙 (TraceLocalizationWord.identity object).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationWord.identity object).localizedSourceObject
          (TraceLocalizationWord.identity object).localizedTargetObject) :=
  rfl

/-- The identity localized arrow has a zero-atom chosen representative. -/
theorem TraceLocalizationWord.localizedArrow_identity_representative_atomCount
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).atomCount =
      0 :=
  rfl

/-- The localized arrow of a one-atom word is the one-atom quotient class. -/
theorem TraceLocalizationWord.localizedArrow_ofAtom
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).localizedArrow =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.ofAtom atom) :=
  rfl

/-- A one-atom localized arrow has a one-atom chosen representative. -/
theorem TraceLocalizationWord.localizedArrow_ofAtom_representative_atomCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).atomCount =
      0 + 1 :=
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

/-- The localized arrow of a concatenated word is categorical composition. -/
theorem TraceLocalizationWord.localizedArrow_comp_eq_categoryComp
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).localizedArrow =
      left.localizedArrow ≫ right.localizedArrow :=
  rfl

/-- A left identity word gives a left categorical identity for localized word arrows. -/
theorem TraceLocalizationWord.localizedArrow_identity_comp
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWord.identity source).localizedArrow ≫
        word.localizedArrow =
      word.localizedArrow :=
  TraceLocalizationWordClass.comp_identity_left
    word.localizedArrow

/-- A right identity word gives a right categorical identity for localized word arrows. -/
theorem TraceLocalizationWord.localizedArrow_comp_identity
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.localizedArrow ≫
        (TraceLocalizationWord.identity target).localizedArrow =
      word.localizedArrow :=
  TraceLocalizationWordClass.comp_identity_right
    word.localizedArrow

/-- Localized word arrows are associative under categorical composition. -/
theorem TraceLocalizationWord.localizedArrow_comp_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (middle : TraceLocalizationWord second third)
    (right : TraceLocalizationWord third fourth) :
    (left.localizedArrow ≫ middle.localizedArrow) ≫
        right.localizedArrow =
      left.localizedArrow ≫
        (middle.localizedArrow ≫ right.localizedArrow) :=
  TraceLocalizationWordClass.comp_assoc
    left.localizedArrow
    middle.localizedArrow
    right.localizedArrow

/-- The chosen representative of a localized concatenated arrow has additive atom count. -/
theorem TraceLocalizationWord.localizedArrow_comp_representative_atomCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).atomCount =
      left.atomCount + right.atomCount :=
  TraceLocalizationWord.comp_atomCount left right

end AnalyticMotives
end LFunctions
end Boundary

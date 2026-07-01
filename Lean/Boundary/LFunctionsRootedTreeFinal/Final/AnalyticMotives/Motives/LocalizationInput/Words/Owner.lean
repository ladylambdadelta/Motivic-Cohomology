import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.FormalInverses.Owner

/-!
# Formal localization words

This file owns composable words in localization atoms.  These words are syntax
for later localized arrows, not morphisms in the ambient presheaf category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A composable word in formal localization atoms, indexed by source and target objects. -/
inductive TraceLocalizationWord : TraceCorQObject → TraceCorQObject → Type where
  | identity (object : TraceCorQObject) :
      TraceLocalizationWord object object
  | snoc
      {source middle target : TraceCorQObject}
      (word : TraceLocalizationWord source middle)
      (atom : TraceLocalizationAtom)
      (middle_eq : middle = atom.sourceObject)
      (target_eq : atom.targetObject = target) :
      TraceLocalizationWord source target

/-- The identity formal localization word on an object. -/
def TraceLocalizationWord.id
    (object : TraceCorQObject) :
    TraceLocalizationWord object object :=
  TraceLocalizationWord.identity object

/-- Append a formal localization atom to a composable word. -/
def TraceLocalizationWord.appendAtom
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    TraceLocalizationWord source target :=
  TraceLocalizationWord.snoc word atom middle_eq target_eq

/-- A one-atom formal localization word. -/
def TraceLocalizationWord.ofAtom
    (atom : TraceLocalizationAtom) :
    TraceLocalizationWord atom.sourceObject atom.targetObject :=
  TraceLocalizationWord.snoc
    (TraceLocalizationWord.identity atom.sourceObject)
    atom
    rfl
    rfl

/-- A one-forward-generator formal localization word. -/
def TraceLocalizationWord.ofInputForward
    (input : TraceLocalizationInput) :
    TraceLocalizationWord input.sourceObject input.targetObject :=
  TraceLocalizationWord.ofAtom
    (TraceLocalizationAtom.forward input)

/-- A one-formal-inverse-generator formal localization word. -/
def TraceLocalizationWord.ofInputInverse
    (input : TraceLocalizationInput) :
    TraceLocalizationWord input.targetObject input.sourceObject :=
  TraceLocalizationWord.ofAtom
    (TraceLocalizationAtom.inverse input)

/-- Concatenate two composable formal localization words. -/
def TraceLocalizationWord.comp
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second) :
    TraceLocalizationWord second third →
      TraceLocalizationWord first third
  | identity _ => left
  | snoc word atom middle_eq target_eq =>
      TraceLocalizationWord.snoc
        (TraceLocalizationWord.comp left word)
        atom
        middle_eq
        target_eq

/-- Concatenate two composable formal localization words. -/
def TraceLocalizationWord.append
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    TraceLocalizationWord first third :=
  TraceLocalizationWord.comp left right

/-- The identity word constructor is `id`. -/
theorem TraceLocalizationWord.id_eq_identity
    (object : TraceCorQObject) :
    TraceLocalizationWord.id object =
      TraceLocalizationWord.identity object :=
  rfl

/-- Appending an atom is the `snoc` constructor. -/
theorem TraceLocalizationWord.appendAtom_eq_snoc
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    TraceLocalizationWord.appendAtom word atom middle_eq target_eq =
      TraceLocalizationWord.snoc word atom middle_eq target_eq :=
  rfl

/-- A one-atom word is identity followed by that atom. -/
theorem TraceLocalizationWord.ofAtom_eq_snoc_identity
    (atom : TraceLocalizationAtom) :
    TraceLocalizationWord.ofAtom atom =
      TraceLocalizationWord.snoc
        (TraceLocalizationWord.identity atom.sourceObject)
        atom
        rfl
        rfl :=
  rfl

/-- A forward input word is the one-atom word of the forward atom. -/
theorem TraceLocalizationWord.ofInputForward_eq_ofAtom
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.ofInputForward input =
      TraceLocalizationWord.ofAtom (TraceLocalizationAtom.forward input) :=
  rfl

/-- An inverse input word is the one-atom word of the inverse atom. -/
theorem TraceLocalizationWord.ofInputInverse_eq_ofAtom
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.ofInputInverse input =
      TraceLocalizationWord.ofAtom (TraceLocalizationAtom.inverse input) :=
  rfl

/-- Appending a right identity word returns the original word definitionally. -/
theorem TraceLocalizationWord.comp_identity_right
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    TraceLocalizationWord.comp word
        (TraceLocalizationWord.identity target) =
      word :=
  rfl

/-- Appending a `snoc` word appends the same final atom after concatenating prefixes. -/
theorem TraceLocalizationWord.comp_snoc
    {first second middle target : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    TraceLocalizationWord.comp left
        (TraceLocalizationWord.snoc right atom middle_eq target_eq) =
      TraceLocalizationWord.snoc
        (TraceLocalizationWord.comp left right)
        atom
        middle_eq
        target_eq :=
  rfl

/-- A left identity word concatenated with a word returns that word. -/
theorem TraceLocalizationWord.comp_identity_left
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    TraceLocalizationWord.comp
        (TraceLocalizationWord.identity source)
        word =
      word :=
  match word with
  | identity object => rfl
  | snoc word atom middle_eq target_eq =>
      congrArg
        (fun prefix =>
          TraceLocalizationWord.snoc prefix atom middle_eq target_eq)
        (TraceLocalizationWord.comp_identity_left word)

/-- Formal localization word concatenation is associative. -/
theorem TraceLocalizationWord.comp_assoc
    {first second third fourth : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (middle : TraceLocalizationWord second third)
    (right : TraceLocalizationWord third fourth) :
    TraceLocalizationWord.comp
        (TraceLocalizationWord.comp left middle)
        right =
      TraceLocalizationWord.comp
        left
        (TraceLocalizationWord.comp middle right) :=
  match right with
  | identity object => rfl
  | snoc word atom middle_eq target_eq =>
      congrArg
        (fun prefix =>
          TraceLocalizationWord.snoc prefix atom middle_eq target_eq)
        (TraceLocalizationWord.comp_assoc left middle word)

end AnalyticMotives
end LFunctions
end Boundary

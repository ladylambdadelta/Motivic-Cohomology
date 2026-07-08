import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.FormalInverses.Owner

/-!
# Formal localization words

This file owns composable words in localization atoms.  These words are the
formal arrow syntax used by the localization calculus, not morphisms in the
ambient presheaf category.
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

/-- The number of formal localization atoms in a word. -/
def TraceLocalizationWord.atomCount
    {source target : TraceCorQObject} :
    TraceLocalizationWord source target → Nat
  | identity _ => 0
  | snoc word _ _ _ => word.atomCount + 1

/-- The identity word constructor is `id`. -/
theorem TraceLocalizationWord.id_eq_identity
    (object : TraceCorQObject) :
    TraceLocalizationWord.id object =
      TraceLocalizationWord.identity object :=
  rfl

/-- The identity word has no atoms. -/
theorem TraceLocalizationWord.id_atomCount
    (object : TraceCorQObject) :
    (TraceLocalizationWord.id object).atomCount =
      0 :=
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

/-- Appending one atom increases word atom count by one. -/
theorem TraceLocalizationWord.appendAtom_atomCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).atomCount =
      word.atomCount + 1 :=
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

/-- A one-atom localization word has atom count one. -/
theorem TraceLocalizationWord.ofAtom_atomCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).atomCount =
      0 + 1 :=
  rfl

/-- A forward input word is the one-atom word of the forward atom. -/
theorem TraceLocalizationWord.ofInputForward_eq_ofAtom
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.ofInputForward input =
      TraceLocalizationWord.ofAtom (TraceLocalizationAtom.forward input) :=
  rfl

/-- A one-forward-generator word has atom count one. -/
theorem TraceLocalizationWord.ofInputForward_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).atomCount =
      0 + 1 :=
  rfl

/-- An inverse input word is the one-atom word of the inverse atom. -/
theorem TraceLocalizationWord.ofInputInverse_eq_ofAtom
    (input : TraceLocalizationInput) :
    TraceLocalizationWord.ofInputInverse input =
      TraceLocalizationWord.ofAtom (TraceLocalizationAtom.inverse input) :=
  rfl

/-- A one-formal-inverse-generator word has atom count one. -/
theorem TraceLocalizationWord.ofInputInverse_atomCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).atomCount =
      0 + 1 :=
  rfl

/-- Appending a right identity word returns the original word definitionally. -/
theorem TraceLocalizationWord.comp_identity_right
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    TraceLocalizationWord.comp word
        (TraceLocalizationWord.identity target) =
      word :=
  rfl

/-- Concatenating a right identity word preserves atom count. -/
theorem TraceLocalizationWord.comp_identity_right_atomCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWord.comp word
        (TraceLocalizationWord.identity target)).atomCount =
      word.atomCount :=
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

/-- Concatenating against a snoc word adds the final atom after the concatenated prefix. -/
theorem TraceLocalizationWord.comp_snoc_atomCount
    {first second middle target : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.comp left
        (TraceLocalizationWord.snoc right atom middle_eq target_eq)).atomCount =
      (TraceLocalizationWord.comp left right).atomCount + 1 :=
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
  | identity _ => rfl
  | snoc word atom middle_eq target_eq =>
      congrArg
        (fun prefixWord =>
          TraceLocalizationWord.snoc prefixWord atom middle_eq target_eq)
        (TraceLocalizationWord.comp_identity_left word)

/-- A left identity word concatenated with a word preserves atom count. -/
theorem TraceLocalizationWord.comp_identity_left_atomCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWord.comp
        (TraceLocalizationWord.identity source)
        word).atomCount =
      word.atomCount :=
  match word with
  | identity _ => rfl
  | snoc word atom middle_eq target_eq =>
      congrArg
        (fun count => count + 1)
        (TraceLocalizationWord.comp_identity_left_atomCount word)

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
  | identity _ => rfl
  | snoc word atom middle_eq target_eq =>
      congrArg
        (fun prefixWord =>
          TraceLocalizationWord.snoc prefixWord atom middle_eq target_eq)
        (TraceLocalizationWord.comp_assoc left middle word)

/-- Word concatenation adds atom counts. -/
theorem TraceLocalizationWord.comp_atomCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).atomCount =
      left.atomCount + right.atomCount :=
  match right with
  | identity _ => rfl
  | snoc word atom middle_eq target_eq =>
      Eq.trans
        (congrArg
          (fun count => count + 1)
          (TraceLocalizationWord.comp_atomCount left word))
        (Eq.symm
          (Nat.add_assoc left.atomCount word.atomCount 1))

end AnalyticMotives
end LFunctions
end Boundary

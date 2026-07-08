import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Owner

/-!
# Endpoint analytic payload for localization words

This file records the imported finite-rectangle payload carried by the source
and target endpoints of a formal localization word.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported finite explicit-formula rectangles carried by the source endpoint of a word. -/
def TraceLocalizationWord.sourceImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  source.importedRectangles

/-- The imported finite explicit-formula rectangles carried by the target endpoint of a word. -/
def TraceLocalizationWord.targetImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  target.importedRectangles

/-- The endpoint imported finite explicit-formula rectangles carried by a word. -/
def TraceLocalizationWord.endpointImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  word.sourceImportedRectangles ++
    word.targetImportedRectangles

/-- The source endpoint imported-rectangle count of a word. -/
def TraceLocalizationWord.sourceImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  source.importedRectangleCount

/-- The target endpoint imported-rectangle count of a word. -/
def TraceLocalizationWord.targetImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  target.importedRectangleCount

/-- The total endpoint imported-rectangle count of a word. -/
def TraceLocalizationWord.endpointImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  word.sourceImportedRectangleCount +
    word.targetImportedRectangleCount

/-- The source endpoint count is the length of the source endpoint rectangle list. -/
theorem TraceLocalizationWord.sourceImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.sourceImportedRectangleCount =
      word.sourceImportedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    source

/-- The target endpoint count is the length of the target endpoint rectangle list. -/
theorem TraceLocalizationWord.targetImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.targetImportedRectangleCount =
      word.targetImportedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    target

/-- The endpoint count is the length of the endpoint rectangle list. -/
theorem TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    word.endpointImportedRectangleCount =
      word.endpointImportedRectangles.length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceLocalizationWord.sourceImportedRectangleCount_eq_length word)
      (TraceLocalizationWord.targetImportedRectangleCount_eq_length word))
    (Eq.symm
      (List.length_append
        word.sourceImportedRectangles
        word.targetImportedRectangles))

/-- The identity word source endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizationWord.identity_sourceImportedRectangles
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).sourceImportedRectangles =
      object.importedRectangles :=
  rfl

/-- The identity word target endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizationWord.identity_targetImportedRectangles
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).targetImportedRectangles =
      object.importedRectangles :=
  rfl

/-- The identity word source endpoint count is the object's imported count. -/
theorem TraceLocalizationWord.identity_sourceImportedRectangleCount
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).sourceImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- The identity word target endpoint count is the object's imported count. -/
theorem TraceLocalizationWord.identity_targetImportedRectangleCount
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).targetImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- A one-atom word source endpoint rectangles are the atom source rectangles. -/
theorem TraceLocalizationWord.ofAtom_sourceImportedRectangles
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).sourceImportedRectangles =
      atom.sourceObject.importedRectangles :=
  rfl

/-- A one-atom word target endpoint rectangles are the atom target rectangles. -/
theorem TraceLocalizationWord.ofAtom_targetImportedRectangles
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).targetImportedRectangles =
      atom.targetObject.importedRectangles :=
  rfl

/-- A one-atom word source endpoint count is the atom source imported count. -/
theorem TraceLocalizationWord.ofAtom_sourceImportedRectangleCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).sourceImportedRectangleCount =
      atom.sourceObject.importedRectangleCount :=
  rfl

/-- A one-atom word target endpoint count is the atom target imported count. -/
theorem TraceLocalizationWord.ofAtom_targetImportedRectangleCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).targetImportedRectangleCount =
      atom.targetObject.importedRectangleCount :=
  rfl

/-- Appending an atom preserves the source endpoint rectangles of a word. -/
theorem TraceLocalizationWord.appendAtom_sourceImportedRectangles
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).sourceImportedRectangles =
      word.sourceImportedRectangles :=
  rfl

/-- Appending an atom changes the target endpoint rectangles to the new target. -/
theorem TraceLocalizationWord.appendAtom_targetImportedRectangles
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).targetImportedRectangles =
      target.importedRectangles :=
  rfl

/-- Appending an atom preserves the source endpoint count of a word. -/
theorem TraceLocalizationWord.appendAtom_sourceImportedRectangleCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).sourceImportedRectangleCount =
      word.sourceImportedRectangleCount :=
  rfl

/-- Appending an atom changes the target endpoint count to the new target. -/
theorem TraceLocalizationWord.appendAtom_targetImportedRectangleCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).targetImportedRectangleCount =
      target.importedRectangleCount :=
  rfl

/-- Concatenation keeps the left word's source endpoint rectangles. -/
theorem TraceLocalizationWord.comp_sourceImportedRectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).sourceImportedRectangles =
      left.sourceImportedRectangles :=
  rfl

/-- Concatenation keeps the right word's target endpoint rectangles. -/
theorem TraceLocalizationWord.comp_targetImportedRectangles
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).targetImportedRectangles =
      right.targetImportedRectangles :=
  rfl

/-- Concatenation keeps the left word's source endpoint count. -/
theorem TraceLocalizationWord.comp_sourceImportedRectangleCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).sourceImportedRectangleCount =
      left.sourceImportedRectangleCount :=
  rfl

/-- Concatenation keeps the right word's target endpoint count. -/
theorem TraceLocalizationWord.comp_targetImportedRectangleCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).targetImportedRectangleCount =
      right.targetImportedRectangleCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

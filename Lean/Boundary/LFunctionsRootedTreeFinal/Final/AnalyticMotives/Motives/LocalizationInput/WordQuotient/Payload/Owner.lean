import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Owner

/-!
# Endpoint analytic payload for localization word classes

This file records the imported finite-rectangle endpoint payload determined by
the source and target objects of a formal localized word class.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The imported finite explicit-formula rectangles carried by the source endpoint of a word class. -/
def TraceLocalizationWordClass.sourceImportedRectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  source.importedRectangles

/-- The imported finite explicit-formula rectangles carried by the target endpoint of a word class. -/
def TraceLocalizationWordClass.targetImportedRectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  target.importedRectangles

/-- The endpoint imported finite explicit-formula rectangles carried by a word class. -/
def TraceLocalizationWordClass.endpointImportedRectangles
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  wordClass.sourceImportedRectangles ++
    wordClass.targetImportedRectangles

/-- The source endpoint imported-rectangle count of a word class. -/
def TraceLocalizationWordClass.sourceImportedRectangleCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  source.importedRectangleCount

/-- The target endpoint imported-rectangle count of a word class. -/
def TraceLocalizationWordClass.targetImportedRectangleCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  target.importedRectangleCount

/-- The total endpoint imported-rectangle count of a word class. -/
def TraceLocalizationWordClass.endpointImportedRectangleCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  wordClass.sourceImportedRectangleCount +
    wordClass.targetImportedRectangleCount

/-- The source endpoint count is the length of the source endpoint rectangle list. -/
theorem TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.sourceImportedRectangleCount =
      wordClass.sourceImportedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    source

/-- The target endpoint count is the length of the target endpoint rectangle list. -/
theorem TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.targetImportedRectangleCount =
      wordClass.targetImportedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    target

/-- The endpoint count is the length of the endpoint rectangle list. -/
theorem TraceLocalizationWordClass.endpointImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    wordClass.endpointImportedRectangleCount =
      wordClass.endpointImportedRectangles.length :=
  Eq.trans
    (congrArg₂
      Nat.add
      (TraceLocalizationWordClass.sourceImportedRectangleCount_eq_length
        wordClass)
      (TraceLocalizationWordClass.targetImportedRectangleCount_eq_length
        wordClass))
    (Eq.symm
      (List.length_append
        wordClass.sourceImportedRectangles
        wordClass.targetImportedRectangles))

/-- A represented word class has the same source endpoint rectangles as its representative. -/
theorem TraceLocalizationWordClass.ofWord_sourceImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).sourceImportedRectangles =
      word.sourceImportedRectangles :=
  rfl

/-- A represented word class has the same target endpoint rectangles as its representative. -/
theorem TraceLocalizationWordClass.ofWord_targetImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).targetImportedRectangles =
      word.targetImportedRectangles :=
  rfl

/-- A represented word class has the same endpoint rectangles as its representative. -/
theorem TraceLocalizationWordClass.ofWord_endpointImportedRectangles
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).endpointImportedRectangles =
      word.endpointImportedRectangles :=
  rfl

/-- A represented word class has the same source endpoint count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_sourceImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).sourceImportedRectangleCount =
      word.sourceImportedRectangleCount :=
  rfl

/-- A represented word class has the same target endpoint count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_targetImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).targetImportedRectangleCount =
      word.targetImportedRectangleCount :=
  rfl

/-- A represented word class has the same endpoint count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_endpointImportedRectangleCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).endpointImportedRectangleCount =
      word.endpointImportedRectangleCount :=
  rfl

/-- The identity word class source endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizationWordClass.identity_sourceImportedRectangles
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).sourceImportedRectangles =
      object.importedRectangles :=
  rfl

/-- The identity word class target endpoint rectangles are the object's imported rectangles. -/
theorem TraceLocalizationWordClass.identity_targetImportedRectangles
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).targetImportedRectangles =
      object.importedRectangles :=
  rfl

/-- The identity word class source endpoint count is the object's imported count. -/
theorem TraceLocalizationWordClass.identity_sourceImportedRectangleCount
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).sourceImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- The identity word class target endpoint count is the object's imported count. -/
theorem TraceLocalizationWordClass.identity_targetImportedRectangleCount
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).targetImportedRectangleCount =
      object.importedRectangleCount :=
  rfl

/-- A forward-input word class source endpoint rectangles are the input source rectangles. -/
theorem TraceLocalizationWordClass.ofInputForward_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).sourceImportedRectangles =
      input.sourceObject.importedRectangles :=
  rfl

/-- A forward-input word class target endpoint rectangles are the input target rectangles. -/
theorem TraceLocalizationWordClass.ofInputForward_targetImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).targetImportedRectangles =
      input.targetObject.importedRectangles :=
  rfl

/-- A forward-input word class source endpoint count is the input source count. -/
theorem TraceLocalizationWordClass.ofInputForward_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).sourceImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  rfl

/-- A forward-input word class target endpoint count is the input target count. -/
theorem TraceLocalizationWordClass.ofInputForward_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).targetImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  rfl

/-- An inverse-input word class source endpoint rectangles are the input target rectangles. -/
theorem TraceLocalizationWordClass.ofInputInverse_sourceImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).sourceImportedRectangles =
      input.targetObject.importedRectangles :=
  rfl

/-- An inverse-input word class target endpoint rectangles are the input source rectangles. -/
theorem TraceLocalizationWordClass.ofInputInverse_targetImportedRectangles
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).targetImportedRectangles =
      input.sourceObject.importedRectangles :=
  rfl

/-- An inverse-input word class source endpoint count is the input target count. -/
theorem TraceLocalizationWordClass.ofInputInverse_sourceImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).sourceImportedRectangleCount =
      input.targetObject.importedRectangleCount :=
  rfl

/-- An inverse-input word class target endpoint count is the input source count. -/
theorem TraceLocalizationWordClass.ofInputInverse_targetImportedRectangleCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).targetImportedRectangleCount =
      input.sourceObject.importedRectangleCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

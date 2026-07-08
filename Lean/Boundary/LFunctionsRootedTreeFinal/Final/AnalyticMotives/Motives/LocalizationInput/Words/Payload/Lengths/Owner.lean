import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.TraceCalculus.Owner

/-!
# Localization word payload length facts

This file owns imported-rectangle length invariants for the endpoint payload of
formal localization word constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.identity_endpointImportedRectangleCount_eq_length
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).endpointImportedRectangleCount =
      (TraceLocalizationWord.identity object).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.identity object)

/-- A one-atom word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.ofAtom_endpointImportedRectangleCount_eq_length
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).endpointImportedRectangleCount =
      (TraceLocalizationWord.ofAtom atom).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofAtom atom)

/-- A one-forward-input word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.ofInputForward_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputForward input).endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputForward input).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofInputForward input)

/-- A one-inverse-input word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.ofInputInverse_endpointImportedRectangleCount_eq_length
    (input : TraceLocalizationInput) :
    (TraceLocalizationWord.ofInputInverse input).endpointImportedRectangleCount =
      (TraceLocalizationWord.ofInputInverse input).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.ofInputInverse input)

/-- An atom-appended word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.appendAtom_endpointImportedRectangleCount_eq_length
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).endpointImportedRectangleCount =
      (TraceLocalizationWord.appendAtom
        word
        atom
        middle_eq
        target_eq).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq)

/-- A composite word endpoint count is the length of its endpoint rectangle list. -/
theorem TraceLocalizationWord.comp_endpointImportedRectangleCount_eq_length
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).endpointImportedRectangleCount =
      (TraceLocalizationWord.comp left right).endpointImportedRectangles.length :=
  TraceLocalizationWord.endpointImportedRectangleCount_eq_length
    (TraceLocalizationWord.comp left right)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Owner

/-!
# Formal inverse atoms for localization inputs

This file owns the first arrow syntax used by localization: a generator map,
or a formal inverse of a generator map.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A formal localization atom is either a generator map or its formal inverse. -/
inductive TraceLocalizationAtom where
  | forward (input : TraceLocalizationInput)
  | inverse (input : TraceLocalizationInput)
  deriving Repr

/-- The localization input underlying a formal localization atom. -/
def TraceLocalizationAtom.input :
    TraceLocalizationAtom → TraceLocalizationInput
  | forward input => input
  | inverse input => input

/-- The source object of a formal localization atom. -/
def TraceLocalizationAtom.sourceObject :
    TraceLocalizationAtom → TraceCorQObject
  | forward input => input.sourceObject
  | inverse input => input.targetObject

/-- The target object of a formal localization atom. -/
def TraceLocalizationAtom.targetObject :
    TraceLocalizationAtom → TraceCorQObject
  | forward input => input.targetObject
  | inverse input => input.sourceObject

/-- The source representable presheaf of a formal localization atom. -/
def TraceLocalizationAtom.sourcePresheaf
    (atom : TraceLocalizationAtom) :
    TraceCorQPresheaf :=
  TraceCorQPresheaf.representable atom.sourceObject

/-- The target representable presheaf of a formal localization atom. -/
def TraceLocalizationAtom.targetPresheaf
    (atom : TraceLocalizationAtom) :
    TraceCorQPresheaf :=
  TraceCorQPresheaf.representable atom.targetObject

/-- A formal atom's source object is the source object of its underlying input orientation. -/
theorem TraceLocalizationAtom.sourceObject_certificateLedger
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.certificateLedger =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.sourceObject.certificateLedger
      | TraceLocalizationAtom.inverse input =>
          input.targetObject.certificateLedger :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's target object is the target object of its underlying input orientation. -/
theorem TraceLocalizationAtom.targetObject_certificateLedger
    (atom : TraceLocalizationAtom) :
    atom.targetObject.certificateLedger =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.targetObject.certificateLedger
      | TraceLocalizationAtom.inverse input =>
          input.sourceObject.certificateLedger :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's source object rewrite-step payload follows its orientation. -/
theorem TraceLocalizationAtom.sourceObject_rewriteStepCount
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.rewriteStepCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.sourceObject.rewriteStepCount
      | TraceLocalizationAtom.inverse input =>
          input.targetObject.rewriteStepCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's source object imported rectangles follow its orientation. -/
theorem TraceLocalizationAtom.sourceObject_importedRectangles
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.importedRectangles =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.sourceObject.importedRectangles
      | TraceLocalizationAtom.inverse input =>
          input.targetObject.importedRectangles :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's source imported count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.sourceObject_importedRectangleCount_eq_length_importedRectangles
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.importedRectangleCount =
      atom.sourceObject.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    atom.sourceObject

/-- A formal atom's target object rewrite-step payload follows its orientation. -/
theorem TraceLocalizationAtom.targetObject_rewriteStepCount
    (atom : TraceLocalizationAtom) :
    atom.targetObject.rewriteStepCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.targetObject.rewriteStepCount
      | TraceLocalizationAtom.inverse input =>
          input.sourceObject.rewriteStepCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's target object imported rectangles follow its orientation. -/
theorem TraceLocalizationAtom.targetObject_importedRectangles
    (atom : TraceLocalizationAtom) :
    atom.targetObject.importedRectangles =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.targetObject.importedRectangles
      | TraceLocalizationAtom.inverse input =>
          input.sourceObject.importedRectangles :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's target imported count is the length of its rectangle list. -/
theorem TraceLocalizationAtom.targetObject_importedRectangleCount_eq_length_importedRectangles
    (atom : TraceLocalizationAtom) :
    atom.targetObject.importedRectangleCount =
      atom.targetObject.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    atom.targetObject

/-- The concrete presheaf map carried by a forward localization atom. -/
def TraceLocalizationAtom.forwardMap
    (input : TraceLocalizationInput) :
    TraceCorQPresheafHom
      (TraceLocalizationAtom.forward input).sourcePresheaf
      (TraceLocalizationAtom.forward input).targetPresheaf :=
  input.map

/-- The concrete trace hom carried by a forward localization atom. -/
def TraceLocalizationAtom.forwardTraceHom
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).sourceObject ⟶
      (TraceLocalizationAtom.forward input).targetObject :=
  input.traceHom

/-- A forward atom's map is the representable map of its trace hom. -/
theorem TraceLocalizationAtom.forwardMap_eq_representableMap
    (input : TraceLocalizationInput) :
    TraceLocalizationAtom.forwardMap input =
      TraceCorQPresheaf.representableMap
        (TraceLocalizationAtom.forwardTraceHom input) :=
  TraceLocalizationInput.map_eq_representableMap input

/-- A forward atom map has the input trace hom as Yoneda preimage. -/
theorem TraceLocalizationAtom.forwardMap_preimage
    (input : TraceLocalizationInput) :
    TraceCorQPresheaf.representablePreimage
        (TraceLocalizationAtom.forwardMap input) =
      TraceLocalizationAtom.forwardTraceHom input :=
  TraceLocalizationInput.map_preimage input

/-- The source object of a forward atom is the input source object. -/
theorem TraceLocalizationAtom.forward_sourceObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).sourceObject =
      input.sourceObject :=
  rfl

/-- The target object of a forward atom is the input target object. -/
theorem TraceLocalizationAtom.forward_targetObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).targetObject =
      input.targetObject :=
  rfl

/-- The source presheaf of a forward atom is the input source representable. -/
theorem TraceLocalizationAtom.forward_sourcePresheaf
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).sourcePresheaf =
      input.sourcePresheaf :=
  rfl

/-- The target presheaf of a forward atom is the input target representable. -/
theorem TraceLocalizationAtom.forward_targetPresheaf
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.forward input).targetPresheaf =
      input.targetPresheaf :=
  rfl

/-- The source object of an inverse atom is the input target object. -/
theorem TraceLocalizationAtom.inverse_sourceObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).sourceObject =
      input.targetObject :=
  rfl

/-- The target object of an inverse atom is the input source object. -/
theorem TraceLocalizationAtom.inverse_targetObject
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).targetObject =
      input.sourceObject :=
  rfl

/-- The source presheaf of an inverse atom is the input target representable. -/
theorem TraceLocalizationAtom.inverse_sourcePresheaf
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).sourcePresheaf =
      input.targetPresheaf :=
  rfl

/-- The target presheaf of an inverse atom is the input source representable. -/
theorem TraceLocalizationAtom.inverse_targetPresheaf
    (input : TraceLocalizationInput) :
    (TraceLocalizationAtom.inverse input).targetPresheaf =
      input.sourcePresheaf :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

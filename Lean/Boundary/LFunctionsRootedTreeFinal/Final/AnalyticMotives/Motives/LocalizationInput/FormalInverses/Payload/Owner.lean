import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.FormalInverses.Owner

/-!
# Payload orientation for formal localization atoms

This file records how endpoint analytic payload follows the orientation of a
formal localization atom.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A formal atom's source imported count follows its orientation. -/
theorem TraceLocalizationAtom.sourceObject_importedRectangleCount
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.importedRectangleCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.sourceObject.importedRectangleCount
      | TraceLocalizationAtom.inverse input =>
          input.targetObject.importedRectangleCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's target imported count follows its orientation. -/
theorem TraceLocalizationAtom.targetObject_importedRectangleCount
    (atom : TraceLocalizationAtom) :
    atom.targetObject.importedRectangleCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.targetObject.importedRectangleCount
      | TraceLocalizationAtom.inverse input =>
          input.sourceObject.importedRectangleCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's source bookkeeping payload follows its orientation. -/
theorem TraceLocalizationAtom.sourceObject_traceBookkeepingCount
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.traceBookkeepingCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.sourceObject.traceBookkeepingCount
      | TraceLocalizationAtom.inverse input =>
          input.targetObject.traceBookkeepingCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's target bookkeeping payload follows its orientation. -/
theorem TraceLocalizationAtom.targetObject_traceBookkeepingCount
    (atom : TraceLocalizationAtom) :
    atom.targetObject.traceBookkeepingCount =
      match atom with
      | TraceLocalizationAtom.forward input =>
          input.targetObject.traceBookkeepingCount
      | TraceLocalizationAtom.inverse input =>
          input.sourceObject.traceBookkeepingCount :=
  match atom with
  | forward input => rfl
  | inverse input => rfl

/-- A formal atom's source imported count is counted by its source certificate ledger. -/
theorem TraceLocalizationAtom.sourceObject_importedRectangleCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.importedRectangleCount =
      atom.sourceObject.certificateLedger.importedRectangleCount :=
  rfl

/-- A formal atom's target imported count is counted by its target certificate ledger. -/
theorem TraceLocalizationAtom.targetObject_importedRectangleCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.targetObject.importedRectangleCount =
      atom.targetObject.certificateLedger.importedRectangleCount :=
  rfl

/-- A formal atom's source bookkeeping is counted by its source certificate ledger. -/
theorem TraceLocalizationAtom.sourceObject_traceBookkeepingCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.traceBookkeepingCount =
      atom.sourceObject.certificateLedger.traceBookkeepingCount :=
  rfl

/-- A formal atom's target bookkeeping is counted by its target certificate ledger. -/
theorem TraceLocalizationAtom.targetObject_traceBookkeepingCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.targetObject.traceBookkeepingCount =
      atom.targetObject.certificateLedger.traceBookkeepingCount :=
  rfl

/-- A formal atom's source rewrite steps are counted by its source certificate ledger. -/
theorem TraceLocalizationAtom.sourceObject_rewriteStepCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.sourceObject.rewriteStepCount =
      atom.sourceObject.certificateLedger.rewriteStepCount :=
  rfl

/-- A formal atom's target rewrite steps are counted by its target certificate ledger. -/
theorem TraceLocalizationAtom.targetObject_rewriteStepCount_eq_certificateLedger_count
    (atom : TraceLocalizationAtom) :
    atom.targetObject.rewriteStepCount =
      atom.targetObject.certificateLedger.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

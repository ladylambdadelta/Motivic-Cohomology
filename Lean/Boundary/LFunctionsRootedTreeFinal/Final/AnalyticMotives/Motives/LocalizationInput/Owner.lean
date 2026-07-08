import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Generators.Owner

/-!
# Concrete localization inputs

This file owns the concrete list syntax of generator maps inverted by
localization and stabilization steps.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Concrete generator maps selected for analytic motive localization and stabilization. -/
inductive TraceLocalizationInput where
  | descentChannel (source target : QTraceExpression)
  | descentRefinement (source target : QTraceExpression)
  | descentSchedule (source target : QTraceExpression)
  | intervalStokes (source target : QTraceExpression)
  | intervalFubini (source target : QTraceExpression)
  | tateWeightDrop (source target : QTraceExpression)
  deriving Repr

/-- The source trace expression of a localization input. -/
def TraceLocalizationInput.sourceExpression :
    TraceLocalizationInput → QTraceExpression
  | descentChannel source _ => source
  | descentRefinement source _ => source
  | descentSchedule source _ => source
  | intervalStokes source _ => source
  | intervalFubini source _ => source
  | tateWeightDrop source _ => source

/-- The target trace expression of a localization input. -/
def TraceLocalizationInput.targetExpression :
    TraceLocalizationInput → QTraceExpression
  | descentChannel _ target => target
  | descentRefinement _ target => target
  | descentSchedule _ target => target
  | intervalStokes _ target => target
  | intervalFubini _ target => target
  | tateWeightDrop _ target => target

/-- The source trace-correspondence object of a localization input. -/
def TraceLocalizationInput.sourceObject
    (input : TraceLocalizationInput) :
    TraceCorQObject :=
  CertifiedResidueChannelPresentation.ofSource input.sourceExpression

/-- The target trace-correspondence object of a localization input. -/
def TraceLocalizationInput.targetObject
    (input : TraceLocalizationInput) :
    TraceCorQObject :=
  CertifiedResidueChannelPresentation.ofSource input.targetExpression

/-- The source object of a localization input has the input source expression. -/
theorem TraceLocalizationInput.sourceObject_source
    (input : TraceLocalizationInput) :
    input.sourceObject.source =
      input.sourceExpression :=
  match input with
  | descentChannel source target => rfl
  | descentRefinement source target => rfl
  | descentSchedule source target => rfl
  | intervalStokes source target => rfl
  | intervalFubini source target => rfl
  | tateWeightDrop source target => rfl

/-- The target object of a localization input has the input target expression. -/
theorem TraceLocalizationInput.targetObject_source
    (input : TraceLocalizationInput) :
    input.targetObject.source =
      input.targetExpression :=
  match input with
  | descentChannel source target => rfl
  | descentRefinement source target => rfl
  | descentSchedule source target => rfl
  | intervalStokes source target => rfl
  | intervalFubini source target => rfl
  | tateWeightDrop source target => rfl

/-- The source object carries the canonical component certificates for its source expression. -/
theorem TraceLocalizationInput.sourceObject_certificateLedger
    (input : TraceLocalizationInput) :
    input.sourceObject.certificateLedger =
      [
        ResidueChannelCertificateAtom.sourceExpression input.sourceExpression,
        ResidueChannelCertificateAtom.residueLedger ResidueLedger.empty,
        ResidueChannelCertificateAtom.channelList ResidueChannelExpressionList.empty,
        ResidueChannelCertificateAtom.traceSchedule TraceSchedule.empty
      ] :=
  match input with
  | descentChannel source target => rfl
  | descentRefinement source target => rfl
  | descentSchedule source target => rfl
  | intervalStokes source target => rfl
  | intervalFubini source target => rfl
  | tateWeightDrop source target => rfl

/-- The target object carries the canonical component certificates for its target expression. -/
theorem TraceLocalizationInput.targetObject_certificateLedger
    (input : TraceLocalizationInput) :
    input.targetObject.certificateLedger =
      [
        ResidueChannelCertificateAtom.sourceExpression input.targetExpression,
        ResidueChannelCertificateAtom.residueLedger ResidueLedger.empty,
        ResidueChannelCertificateAtom.channelList ResidueChannelExpressionList.empty,
        ResidueChannelCertificateAtom.traceSchedule TraceSchedule.empty
      ] :=
  match input with
  | descentChannel source target => rfl
  | descentRefinement source target => rfl
  | descentSchedule source target => rfl
  | intervalStokes source target => rfl
  | intervalFubini source target => rfl
  | tateWeightDrop source target => rfl

/-- The source object imported payload is counted by its canonical certificates. -/
theorem TraceLocalizationInput.sourceObject_importedRectangleCount
    (input : TraceLocalizationInput) :
    input.sourceObject.importedRectangleCount =
      input.sourceObject.certificateLedger.importedRectangleCount :=
  rfl

/-- The source object imported rectangles are extracted from its canonical certificates. -/
theorem TraceLocalizationInput.sourceObject_importedRectangles
    (input : TraceLocalizationInput) :
    input.sourceObject.importedRectangles =
      input.sourceObject.certificateLedger.importedRectangles :=
  rfl

/-- The source object imported count is the length of its rectangle list. -/
theorem TraceLocalizationInput.sourceObject_importedRectangleCount_eq_length_importedRectangles
    (input : TraceLocalizationInput) :
    input.sourceObject.importedRectangleCount =
      input.sourceObject.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    input.sourceObject

/-- The target object imported payload is counted by its canonical certificates. -/
theorem TraceLocalizationInput.targetObject_importedRectangleCount
    (input : TraceLocalizationInput) :
    input.targetObject.importedRectangleCount =
      input.targetObject.certificateLedger.importedRectangleCount :=
  rfl

/-- The target object imported rectangles are extracted from its canonical certificates. -/
theorem TraceLocalizationInput.targetObject_importedRectangles
    (input : TraceLocalizationInput) :
    input.targetObject.importedRectangles =
      input.targetObject.certificateLedger.importedRectangles :=
  rfl

/-- The target object imported count is the length of its rectangle list. -/
theorem TraceLocalizationInput.targetObject_importedRectangleCount_eq_length_importedRectangles
    (input : TraceLocalizationInput) :
    input.targetObject.importedRectangleCount =
      input.targetObject.importedRectangles.length :=
  TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    input.targetObject

/-- The source object rewrite-step payload is counted by its canonical certificates. -/
theorem TraceLocalizationInput.sourceObject_rewriteStepCount
    (input : TraceLocalizationInput) :
    input.sourceObject.rewriteStepCount =
      input.sourceObject.certificateLedger.rewriteStepCount :=
  rfl

/-- The target object rewrite-step payload is counted by its canonical certificates. -/
theorem TraceLocalizationInput.targetObject_rewriteStepCount
    (input : TraceLocalizationInput) :
    input.targetObject.rewriteStepCount =
      input.targetObject.certificateLedger.rewriteStepCount :=
  rfl

/-- The representable source presheaf of a localization input. -/
def TraceLocalizationInput.sourcePresheaf
    (input : TraceLocalizationInput) :
    TraceCorQPresheaf :=
  TraceCorQPresheaf.representable input.sourceObject

/-- The representable target presheaf of a localization input. -/
def TraceLocalizationInput.targetPresheaf
    (input : TraceLocalizationInput) :
    TraceCorQPresheaf :=
  TraceCorQPresheaf.representable input.targetObject

/-- Evaluate a concrete localization input as its representable-presheaf map. -/
def TraceLocalizationInput.map
    (input : TraceLocalizationInput) :
    TraceCorQPresheafHom input.sourcePresheaf input.targetPresheaf :=
  match input with
  | descentChannel source target =>
      TraceDescentGenerator.channelMap source target
  | descentRefinement source target =>
      TraceDescentGenerator.refinementMap source target
  | descentSchedule source target =>
      TraceDescentGenerator.scheduleMap source target
  | intervalStokes source target =>
      TraceIntervalHomotopyGenerator.stokesMap source target
  | intervalFubini source target =>
      TraceIntervalHomotopyGenerator.fubiniMap source target
  | tateWeightDrop source target =>
      TraceTateStabilizationGenerator.weightDropMap source target

/-- Evaluate a concrete localization input as its underlying trace-correspondence morphism. -/
def TraceLocalizationInput.traceHom
    (input : TraceLocalizationInput) :
    input.sourceObject ⟶ input.targetObject :=
  match input with
  | descentChannel source target =>
      (TraceRewriteGenerator.channel source target).traceHom
  | descentRefinement source target =>
      (TraceRewriteGenerator.refinement source target).traceHom
  | descentSchedule source target =>
      (TraceRewriteGenerator.schedule source target).traceHom
  | intervalStokes source target =>
      (TraceRewriteGenerator.stokes source target).traceHom
  | intervalFubini source target =>
      (TraceRewriteGenerator.fubini source target).traceHom
  | tateWeightDrop source target =>
      (TraceRewriteGenerator.weightDrop source target).traceHom

/-- A localization input map is the representable map of its trace hom. -/
theorem TraceLocalizationInput.map_eq_representableMap
    (input : TraceLocalizationInput) :
    input.map =
      TraceCorQPresheaf.representableMap input.traceHom :=
  match input with
  | descentChannel source target => rfl
  | descentRefinement source target => rfl
  | descentSchedule source target => rfl
  | intervalStokes source target => rfl
  | intervalFubini source target => rfl
  | tateWeightDrop source target => rfl

/-- The trace preimage of a localization input map is its trace hom. -/
theorem TraceLocalizationInput.map_preimage
    (input : TraceLocalizationInput) :
    TraceCorQPresheaf.representablePreimage input.map =
      input.traceHom :=
  match input with
  | descentChannel source target =>
      TraceDescentGenerator.channelMap_preimage source target
  | descentRefinement source target =>
      TraceDescentGenerator.refinementMap_preimage source target
  | descentSchedule source target =>
      TraceDescentGenerator.scheduleMap_preimage source target
  | intervalStokes source target =>
      TraceIntervalHomotopyGenerator.stokesMap_preimage source target
  | intervalFubini source target =>
      TraceIntervalHomotopyGenerator.fubiniMap_preimage source target
  | tateWeightDrop source target =>
      TraceTateStabilizationGenerator.weightDropMap_preimage source target

/-- A descent-channel input evaluates to the descent channel map. -/
theorem TraceLocalizationInput.map_descentChannel
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).map =
      TraceDescentGenerator.channelMap source target :=
  rfl

/-- A descent-refinement input evaluates to the descent refinement map. -/
theorem TraceLocalizationInput.map_descentRefinement
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).map =
      TraceDescentGenerator.refinementMap source target :=
  rfl

/-- A descent-schedule input evaluates to the descent schedule map. -/
theorem TraceLocalizationInput.map_descentSchedule
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).map =
      TraceDescentGenerator.scheduleMap source target :=
  rfl

/-- An interval-Stokes input evaluates to the interval Stokes map. -/
theorem TraceLocalizationInput.map_intervalStokes
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).map =
      TraceIntervalHomotopyGenerator.stokesMap source target :=
  rfl

/-- An interval-Fubini input evaluates to the interval Fubini map. -/
theorem TraceLocalizationInput.map_intervalFubini
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).map =
      TraceIntervalHomotopyGenerator.fubiniMap source target :=
  rfl

/-- A Tate-weight-drop input evaluates to the Tate weight-drop map. -/
theorem TraceLocalizationInput.map_tateWeightDrop
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).map =
      TraceTateStabilizationGenerator.weightDropMap source target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

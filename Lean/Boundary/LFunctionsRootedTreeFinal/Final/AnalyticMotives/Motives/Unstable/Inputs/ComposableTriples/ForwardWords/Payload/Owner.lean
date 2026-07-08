import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ComposableTriples.ForwardWords.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.Payload.TraceCalculus.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Composition.Payload.TraceCalculus.Owner

/-!
# Payload of triple forward words

This file records the endpoint payload carried by the two concrete
parenthesizations of the unstable forward word composite of a composable triple.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The left-associated unstable forward word composite of a composable triple. -/
def TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceLocalizationWordClass.comp
    (TraceLocalizationWordClass.comp
      triple.first.unstableForward
      (match triple.first_middle_eq with
      | rfl => triple.second.unstableForward))
    (match triple.second_middle_eq with
    | rfl => triple.third.unstableForward)

/-- The right-associated unstable forward word composite of a composable triple. -/
def TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord
    (triple : TraceLocalizationInputComposableTriple) :
    TraceLocalizationWordClass
      triple.first.sourceObject
      triple.third.targetObject :=
  TraceLocalizationWordClass.comp
    triple.first.unstableForward
    (TraceLocalizationWordClass.comp
      (match triple.first_middle_eq with
      | rfl => triple.second.unstableForward)
      (match triple.second_middle_eq with
      | rfl => triple.third.unstableForward))

/-- The left-associated triple forward word keeps the first input source rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceImportedRectangles
              (TraceLocalizationWordClass.comp
                triple.first.unstableForward
                triple.second.unstableForward)
              triple.third.unstableForward)
            (TraceLocalizationWordClass.comp_sourceImportedRectangles
              triple.first.unstableForward
              triple.second.unstableForward)

/-- The left-associated triple forward word keeps the third input target rectangles. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetImportedRectangles
            (TraceLocalizationWordClass.comp
              triple.first.unstableForward
              triple.second.unstableForward)
            triple.third.unstableForward

/-- The right-associated triple forward word keeps the first input source rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceImportedRectangles =
      triple.first.unstableForward.sourceImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceImportedRectangles
            triple.first.unstableForward
            (TraceLocalizationWordClass.comp
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The right-associated triple forward word keeps the third input target rectangles. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetImportedRectangles
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetImportedRectangles =
      triple.third.unstableForward.targetImportedRectangles :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetImportedRectangles
              triple.first.unstableForward
              (TraceLocalizationWordClass.comp
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationWordClass.comp_targetImportedRectangles
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The left-associated triple forward word keeps the first input source certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceCertificateLedger
              (TraceLocalizationWordClass.comp
                triple.first.unstableForward
                triple.second.unstableForward)
              triple.third.unstableForward)
            (TraceLocalizationWordClass.comp_sourceCertificateLedger
              triple.first.unstableForward
              triple.second.unstableForward)

/-- The left-associated triple forward word keeps the third input target certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetCertificateLedger
            (TraceLocalizationWordClass.comp
              triple.first.unstableForward
              triple.second.unstableForward)
            triple.third.unstableForward

/-- The right-associated triple forward word keeps the first input source certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceCertificateLedger =
      triple.first.unstableForward.sourceCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceCertificateLedger
            triple.first.unstableForward
            (TraceLocalizationWordClass.comp
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The right-associated triple forward word keeps the third input target certificate ledger. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetCertificateLedger
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetCertificateLedger =
      triple.third.unstableForward.targetCertificateLedger :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetCertificateLedger
              triple.first.unstableForward
              (TraceLocalizationWordClass.comp
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationWordClass.comp_targetCertificateLedger
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The left-associated triple forward word keeps the first input source bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
              (TraceLocalizationWordClass.comp
                triple.first.unstableForward
                triple.second.unstableForward)
              triple.third.unstableForward)
            (TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
              triple.first.unstableForward
              triple.second.unstableForward)

/-- The left-associated triple forward word keeps the third input target bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
            (TraceLocalizationWordClass.comp
              triple.first.unstableForward
              triple.second.unstableForward)
            triple.third.unstableForward

/-- The right-associated triple forward word keeps the first input source bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceTraceBookkeepingCount =
      triple.first.unstableForward.sourceTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceTraceBookkeepingCount
            triple.first.unstableForward
            (TraceLocalizationWordClass.comp
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The right-associated triple forward word keeps the third input target bookkeeping count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetTraceBookkeepingCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetTraceBookkeepingCount =
      triple.third.unstableForward.targetTraceBookkeepingCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
              triple.first.unstableForward
              (TraceLocalizationWordClass.comp
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationWordClass.comp_targetTraceBookkeepingCount
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The left-associated triple forward word keeps the first input source rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_sourceRewriteStepCount
              (TraceLocalizationWordClass.comp
                triple.first.unstableForward
                triple.second.unstableForward)
              triple.third.unstableForward)
            (TraceLocalizationWordClass.comp_sourceRewriteStepCount
              triple.first.unstableForward
              triple.second.unstableForward)

/-- The left-associated triple forward word keeps the third input target rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.leftAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.leftAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_targetRewriteStepCount
            (TraceLocalizationWordClass.comp
              triple.first.unstableForward
              triple.second.unstableForward)
            triple.third.unstableForward

/-- The right-associated triple forward word keeps the first input source rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_sourceRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.sourceRewriteStepCount =
      triple.first.unstableForward.sourceRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          TraceLocalizationWordClass.comp_sourceRewriteStepCount
            triple.first.unstableForward
            (TraceLocalizationWordClass.comp
              triple.second.unstableForward
              triple.third.unstableForward)

/-- The right-associated triple forward word keeps the third input target rewrite-step count. -/
theorem TraceLocalizationInputComposableTriple.rightAssociatedUnstableForwardWord_targetRewriteStepCount
    (triple : TraceLocalizationInputComposableTriple) :
    triple.rightAssociatedUnstableForwardWord.targetRewriteStepCount =
      triple.third.unstableForward.targetRewriteStepCount :=
  match triple.first_middle_eq with
  | rfl =>
      match triple.second_middle_eq with
      | rfl =>
          Eq.trans
            (TraceLocalizationWordClass.comp_targetRewriteStepCount
              triple.first.unstableForward
              (TraceLocalizationWordClass.comp
                triple.second.unstableForward
                triple.third.unstableForward))
            (TraceLocalizationWordClass.comp_targetRewriteStepCount
              triple.second.unstableForward
              triple.third.unstableForward)

end AnalyticMotives
end LFunctions
end Boundary

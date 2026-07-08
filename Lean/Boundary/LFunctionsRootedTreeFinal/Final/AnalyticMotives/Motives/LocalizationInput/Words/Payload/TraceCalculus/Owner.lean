import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.FormalInverses.Payload.Owner

/-!
# Trace-calculus payload for localization words

This file records endpoint certificate ledgers, trace-bookkeeping counts, and
rewrite-step counts for formal localization words.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source endpoint certificate ledger carried by a word. -/
def TraceLocalizationWord.sourceCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    ResidueChannelCertificateLedger :=
  source.certificateLedger

/-- The target endpoint certificate ledger carried by a word. -/
def TraceLocalizationWord.targetCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    ResidueChannelCertificateLedger :=
  target.certificateLedger

/-- The appended endpoint certificate ledger carried by a word. -/
def TraceLocalizationWord.endpointCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    word.sourceCertificateLedger
    word.targetCertificateLedger

/-- The source endpoint trace-bookkeeping count carried by a word. -/
def TraceLocalizationWord.sourceTraceBookkeepingCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  source.traceBookkeepingCount

/-- The target endpoint trace-bookkeeping count carried by a word. -/
def TraceLocalizationWord.targetTraceBookkeepingCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  target.traceBookkeepingCount

/-- The endpoint trace-bookkeeping count carried by a word. -/
def TraceLocalizationWord.endpointTraceBookkeepingCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  word.sourceTraceBookkeepingCount +
    word.targetTraceBookkeepingCount

/-- The source endpoint rewrite-step count carried by a word. -/
def TraceLocalizationWord.sourceRewriteStepCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  source.rewriteStepCount

/-- The target endpoint rewrite-step count carried by a word. -/
def TraceLocalizationWord.targetRewriteStepCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  target.rewriteStepCount

/-- The endpoint rewrite-step count carried by a word. -/
def TraceLocalizationWord.endpointRewriteStepCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    Nat :=
  word.sourceRewriteStepCount +
    word.targetRewriteStepCount

/-- The identity word source endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizationWord.identity_sourceCertificateLedger
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).sourceCertificateLedger =
      object.certificateLedger :=
  rfl

/-- The identity word target endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizationWord.identity_targetCertificateLedger
    (object : TraceCorQObject) :
    (TraceLocalizationWord.identity object).targetCertificateLedger =
      object.certificateLedger :=
  rfl

/-- A one-atom word source endpoint ledger is the atom source ledger. -/
theorem TraceLocalizationWord.ofAtom_sourceCertificateLedger
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).sourceCertificateLedger =
      atom.sourceObject.certificateLedger :=
  rfl

/-- A one-atom word target endpoint ledger is the atom target ledger. -/
theorem TraceLocalizationWord.ofAtom_targetCertificateLedger
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).targetCertificateLedger =
      atom.targetObject.certificateLedger :=
  rfl

/-- A one-atom word source bookkeeping is the atom source bookkeeping payload. -/
theorem TraceLocalizationWord.ofAtom_sourceTraceBookkeepingCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).sourceTraceBookkeepingCount =
      atom.sourceObject.traceBookkeepingCount :=
  rfl

/-- A one-atom word target bookkeeping is the atom target bookkeeping payload. -/
theorem TraceLocalizationWord.ofAtom_targetTraceBookkeepingCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).targetTraceBookkeepingCount =
      atom.targetObject.traceBookkeepingCount :=
  rfl

/-- A one-atom word source rewrite-step count is the atom source rewrite payload. -/
theorem TraceLocalizationWord.ofAtom_sourceRewriteStepCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).sourceRewriteStepCount =
      atom.sourceObject.rewriteStepCount :=
  rfl

/-- A one-atom word target rewrite-step count is the atom target rewrite payload. -/
theorem TraceLocalizationWord.ofAtom_targetRewriteStepCount
    (atom : TraceLocalizationAtom) :
    (TraceLocalizationWord.ofAtom atom).targetRewriteStepCount =
      atom.targetObject.rewriteStepCount :=
  rfl

/-- Appending an atom preserves the source endpoint certificate ledger. -/
theorem TraceLocalizationWord.appendAtom_sourceCertificateLedger
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).sourceCertificateLedger =
      word.sourceCertificateLedger :=
  rfl

/-- Appending an atom changes the target endpoint certificate ledger to the new target. -/
theorem TraceLocalizationWord.appendAtom_targetCertificateLedger
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).targetCertificateLedger =
      target.certificateLedger :=
  rfl

/-- Appending an atom preserves the source endpoint bookkeeping count. -/
theorem TraceLocalizationWord.appendAtom_sourceTraceBookkeepingCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).sourceTraceBookkeepingCount =
      word.sourceTraceBookkeepingCount :=
  rfl

/-- Appending an atom changes the target bookkeeping count to the new target. -/
theorem TraceLocalizationWord.appendAtom_targetTraceBookkeepingCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).targetTraceBookkeepingCount =
      target.traceBookkeepingCount :=
  rfl

/-- Appending an atom preserves the source endpoint rewrite-step count. -/
theorem TraceLocalizationWord.appendAtom_sourceRewriteStepCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).sourceRewriteStepCount =
      word.sourceRewriteStepCount :=
  rfl

/-- Appending an atom changes the target rewrite-step count to the new target. -/
theorem TraceLocalizationWord.appendAtom_targetRewriteStepCount
    {source middle target : TraceCorQObject}
    (word : TraceLocalizationWord source middle)
    (atom : TraceLocalizationAtom)
    (middle_eq : middle = atom.sourceObject)
    (target_eq : atom.targetObject = target) :
    (TraceLocalizationWord.appendAtom
      word
      atom
      middle_eq
      target_eq).targetRewriteStepCount =
      target.rewriteStepCount :=
  rfl

/-- Concatenation keeps the left word's source endpoint certificate ledger. -/
theorem TraceLocalizationWord.comp_sourceCertificateLedger
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).sourceCertificateLedger =
      left.sourceCertificateLedger :=
  rfl

/-- Concatenation keeps the right word's target endpoint certificate ledger. -/
theorem TraceLocalizationWord.comp_targetCertificateLedger
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).targetCertificateLedger =
      right.targetCertificateLedger :=
  rfl

/-- Concatenation keeps the left word's source endpoint bookkeeping count. -/
theorem TraceLocalizationWord.comp_sourceTraceBookkeepingCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).sourceTraceBookkeepingCount =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Concatenation keeps the right word's target endpoint bookkeeping count. -/
theorem TraceLocalizationWord.comp_targetTraceBookkeepingCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).targetTraceBookkeepingCount =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Concatenation keeps the left word's source endpoint rewrite-step count. -/
theorem TraceLocalizationWord.comp_sourceRewriteStepCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).sourceRewriteStepCount =
      left.sourceRewriteStepCount :=
  rfl

/-- Concatenation keeps the right word's target endpoint rewrite-step count. -/
theorem TraceLocalizationWord.comp_targetRewriteStepCount
    {first second third : TraceCorQObject}
    (left : TraceLocalizationWord first second)
    (right : TraceLocalizationWord second third) :
    (TraceLocalizationWord.comp left right).targetRewriteStepCount =
      right.targetRewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

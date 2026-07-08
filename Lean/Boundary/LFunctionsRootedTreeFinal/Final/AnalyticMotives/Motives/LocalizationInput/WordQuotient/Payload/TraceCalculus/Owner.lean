import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.Words.Payload.TraceCalculus.Owner

/-!
# Trace-calculus payload for localization word classes

This file records endpoint certificate ledgers, trace-bookkeeping counts, and
rewrite-step counts for quotient classes of formal localization words.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The source endpoint certificate ledger carried by a word class. -/
def TraceLocalizationWordClass.sourceCertificateLedger
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    ResidueChannelCertificateLedger :=
  source.certificateLedger

/-- The target endpoint certificate ledger carried by a word class. -/
def TraceLocalizationWordClass.targetCertificateLedger
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    ResidueChannelCertificateLedger :=
  target.certificateLedger

/-- The appended endpoint certificate ledger carried by a word class. -/
def TraceLocalizationWordClass.endpointCertificateLedger
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    wordClass.sourceCertificateLedger
    wordClass.targetCertificateLedger

/-- The source endpoint trace-bookkeeping count carried by a word class. -/
def TraceLocalizationWordClass.sourceTraceBookkeepingCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  source.traceBookkeepingCount

/-- The target endpoint trace-bookkeeping count carried by a word class. -/
def TraceLocalizationWordClass.targetTraceBookkeepingCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  target.traceBookkeepingCount

/-- The endpoint trace-bookkeeping count carried by a word class. -/
def TraceLocalizationWordClass.endpointTraceBookkeepingCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  wordClass.sourceTraceBookkeepingCount +
    wordClass.targetTraceBookkeepingCount

/-- The source endpoint rewrite-step count carried by a word class. -/
def TraceLocalizationWordClass.sourceRewriteStepCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  source.rewriteStepCount

/-- The target endpoint rewrite-step count carried by a word class. -/
def TraceLocalizationWordClass.targetRewriteStepCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  target.rewriteStepCount

/-- The endpoint rewrite-step count carried by a word class. -/
def TraceLocalizationWordClass.endpointRewriteStepCount
    {source target : TraceCorQObject}
    (wordClass : TraceLocalizationWordClass source target) :
    Nat :=
  wordClass.sourceRewriteStepCount +
    wordClass.targetRewriteStepCount

/-- A represented word class has the same source endpoint ledger as its representative. -/
theorem TraceLocalizationWordClass.ofWord_sourceCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).sourceCertificateLedger =
      word.sourceCertificateLedger :=
  rfl

/-- A represented word class has the same target endpoint ledger as its representative. -/
theorem TraceLocalizationWordClass.ofWord_targetCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).targetCertificateLedger =
      word.targetCertificateLedger :=
  rfl

/-- A represented word class has the same endpoint ledger as its representative. -/
theorem TraceLocalizationWordClass.ofWord_endpointCertificateLedger
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).endpointCertificateLedger =
      word.endpointCertificateLedger :=
  rfl

/-- A represented word class has the same source bookkeeping count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_sourceTraceBookkeepingCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).sourceTraceBookkeepingCount =
      word.sourceTraceBookkeepingCount :=
  rfl

/-- A represented word class has the same target bookkeeping count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_targetTraceBookkeepingCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).targetTraceBookkeepingCount =
      word.targetTraceBookkeepingCount :=
  rfl

/-- A represented word class has the same source rewrite-step count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_sourceRewriteStepCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).sourceRewriteStepCount =
      word.sourceRewriteStepCount :=
  rfl

/-- A represented word class has the same target rewrite-step count as its representative. -/
theorem TraceLocalizationWordClass.ofWord_targetRewriteStepCount
    {source target : TraceCorQObject}
    (word : TraceLocalizationWord source target) :
    (TraceLocalizationWordClass.ofWord word).targetRewriteStepCount =
      word.targetRewriteStepCount :=
  rfl

/-- The identity word class source endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizationWordClass.identity_sourceCertificateLedger
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).sourceCertificateLedger =
      object.certificateLedger :=
  rfl

/-- The identity word class target endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizationWordClass.identity_targetCertificateLedger
    (object : TraceCorQObject) :
    (TraceLocalizationWordClass.identity object).targetCertificateLedger =
      object.certificateLedger :=
  rfl

/-- A forward-input word class source endpoint ledger is the input source ledger. -/
theorem TraceLocalizationWordClass.ofInputForward_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).sourceCertificateLedger =
      input.sourceObject.certificateLedger :=
  rfl

/-- A forward-input word class target endpoint ledger is the input target ledger. -/
theorem TraceLocalizationWordClass.ofInputForward_targetCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).targetCertificateLedger =
      input.targetObject.certificateLedger :=
  rfl

/-- A forward-input word class source bookkeeping is the input source bookkeeping. -/
theorem TraceLocalizationWordClass.ofInputForward_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).sourceTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  rfl

/-- A forward-input word class target bookkeeping is the input target bookkeeping. -/
theorem TraceLocalizationWordClass.ofInputForward_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).targetTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  rfl

/-- A forward-input word class source rewrite steps are the input source rewrite steps. -/
theorem TraceLocalizationWordClass.ofInputForward_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).sourceRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  rfl

/-- A forward-input word class target rewrite steps are the input target rewrite steps. -/
theorem TraceLocalizationWordClass.ofInputForward_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputForward input).targetRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  rfl

/-- An inverse-input word class source endpoint ledger is the input target ledger. -/
theorem TraceLocalizationWordClass.ofInputInverse_sourceCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).sourceCertificateLedger =
      input.targetObject.certificateLedger :=
  rfl

/-- An inverse-input word class target endpoint ledger is the input source ledger. -/
theorem TraceLocalizationWordClass.ofInputInverse_targetCertificateLedger
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).targetCertificateLedger =
      input.sourceObject.certificateLedger :=
  rfl

/-- An inverse-input word class source bookkeeping is the input target bookkeeping. -/
theorem TraceLocalizationWordClass.ofInputInverse_sourceTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).sourceTraceBookkeepingCount =
      input.targetObject.traceBookkeepingCount :=
  rfl

/-- An inverse-input word class target bookkeeping is the input source bookkeeping. -/
theorem TraceLocalizationWordClass.ofInputInverse_targetTraceBookkeepingCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).targetTraceBookkeepingCount =
      input.sourceObject.traceBookkeepingCount :=
  rfl

/-- An inverse-input word class source rewrite steps are the input target rewrite steps. -/
theorem TraceLocalizationWordClass.ofInputInverse_sourceRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).sourceRewriteStepCount =
      input.targetObject.rewriteStepCount :=
  rfl

/-- An inverse-input word class target rewrite steps are the input source rewrite steps. -/
theorem TraceLocalizationWordClass.ofInputInverse_targetRewriteStepCount
    (input : TraceLocalizationInput) :
    (TraceLocalizationWordClass.ofInputInverse input).targetRewriteStepCount =
      input.sourceObject.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

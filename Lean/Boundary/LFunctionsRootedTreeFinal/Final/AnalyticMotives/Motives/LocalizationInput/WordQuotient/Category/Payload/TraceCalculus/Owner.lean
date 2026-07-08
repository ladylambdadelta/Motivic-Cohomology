import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.Owner

/-!
# Trace-calculus payload in the localized word category

This file exposes endpoint trace-bookkeeping and rewrite-step payload through
the localized word-category wrapper.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic certificate ledger carried by a localized-word object. -/
def TraceLocalizedWordObject.certificateLedger
    (object : TraceLocalizedWordObject) :
    ResidueChannelCertificateLedger :=
  object.underlying.certificateLedger

/-- Trace-bookkeeping payload carried by a localized-word object. -/
def TraceLocalizedWordObject.traceBookkeepingCount
    (object : TraceLocalizedWordObject) :
    Nat :=
  object.underlying.traceBookkeepingCount

/-- Rewrite-step payload carried by a localized-word object. -/
def TraceLocalizedWordObject.rewriteStepCount
    (object : TraceLocalizedWordObject) :
    Nat :=
  object.underlying.rewriteStepCount

/-- The object constructor preserves trace-bookkeeping payload. -/
theorem TraceLocalizedWordObject.ofTraceObject_traceBookkeepingCount
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).traceBookkeepingCount =
      object.traceBookkeepingCount :=
  rfl

/-- The object constructor preserves rewrite-step payload. -/
theorem TraceLocalizedWordObject.ofTraceObject_rewriteStepCount
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).rewriteStepCount =
      object.rewriteStepCount :=
  rfl

/-- The object constructor preserves analytic certificate ledgers. -/
theorem TraceLocalizedWordObject.ofTraceObject_certificateLedger
    (object : TraceCorQObject) :
    (TraceLocalizedWordObject.ofTraceObject object).certificateLedger =
      object.certificateLedger :=
  rfl

/-- Source endpoint trace-bookkeeping payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.sourceTraceBookkeepingCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  source.traceBookkeepingCount

/-- Target endpoint trace-bookkeeping payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.targetTraceBookkeepingCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  target.traceBookkeepingCount

/-- Endpoint trace-bookkeeping payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.endpointTraceBookkeepingCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  hom.sourceTraceBookkeepingCount +
    hom.targetTraceBookkeepingCount

/-- Source endpoint rewrite-step payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.sourceRewriteStepCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  source.rewriteStepCount

/-- Target endpoint rewrite-step payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.targetRewriteStepCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  target.rewriteStepCount

/-- Endpoint rewrite-step payload carried by a localized-word hom. -/
def TraceLocalizedWordHom.endpointRewriteStepCount
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    Nat :=
  hom.sourceRewriteStepCount +
    hom.targetRewriteStepCount

/-- Source endpoint certificate ledger carried by a localized-word hom. -/
def TraceLocalizedWordHom.sourceCertificateLedger
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    ResidueChannelCertificateLedger :=
  source.certificateLedger

/-- Target endpoint certificate ledger carried by a localized-word hom. -/
def TraceLocalizedWordHom.targetCertificateLedger
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    ResidueChannelCertificateLedger :=
  target.certificateLedger

/-- Endpoint certificate ledger carried by a localized-word hom. -/
def TraceLocalizedWordHom.endpointCertificateLedger
    {source target : TraceLocalizedWordObject}
    (hom : TraceLocalizedWordHom source target) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    hom.sourceCertificateLedger
    hom.targetCertificateLedger

/-- Identity hom source endpoint bookkeeping is the object's bookkeeping payload. -/
theorem TraceLocalizedWordHom.id_sourceTraceBookkeepingCount
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.sourceTraceBookkeepingCount
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.traceBookkeepingCount :=
  rfl

/-- Identity hom target endpoint bookkeeping is the object's bookkeeping payload. -/
theorem TraceLocalizedWordHom.id_targetTraceBookkeepingCount
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.targetTraceBookkeepingCount
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.traceBookkeepingCount :=
  rfl

/-- Identity hom source endpoint rewrite-step count is the object's rewrite payload. -/
theorem TraceLocalizedWordHom.id_sourceRewriteStepCount
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.sourceRewriteStepCount
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.rewriteStepCount :=
  rfl

/-- Identity hom target endpoint rewrite-step count is the object's rewrite payload. -/
theorem TraceLocalizedWordHom.id_targetRewriteStepCount
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.targetRewriteStepCount
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.rewriteStepCount :=
  rfl

/-- Identity hom source endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizedWordHom.id_sourceCertificateLedger
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.sourceCertificateLedger
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.certificateLedger :=
  rfl

/-- Identity hom target endpoint ledger is the object's certificate ledger. -/
theorem TraceLocalizedWordHom.id_targetCertificateLedger
    (object : TraceLocalizedWordObject) :
    TraceLocalizedWordHom.targetCertificateLedger
        (TraceLocalizationWordClass.identity object.underlying :
          TraceLocalizedWordHom object object) =
      object.certificateLedger :=
  rfl

/-- Composition keeps the left hom source endpoint bookkeeping payload. -/
theorem TraceLocalizedWordHom.comp_sourceTraceBookkeepingCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.sourceTraceBookkeepingCount
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      left.sourceTraceBookkeepingCount :=
  rfl

/-- Composition keeps the right hom target endpoint bookkeeping payload. -/
theorem TraceLocalizedWordHom.comp_targetTraceBookkeepingCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.targetTraceBookkeepingCount
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      right.targetTraceBookkeepingCount :=
  rfl

/-- Composition keeps the left hom source endpoint rewrite-step payload. -/
theorem TraceLocalizedWordHom.comp_sourceRewriteStepCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.sourceRewriteStepCount
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      left.sourceRewriteStepCount :=
  rfl

/-- Composition keeps the right hom target endpoint rewrite-step payload. -/
theorem TraceLocalizedWordHom.comp_targetRewriteStepCount
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.targetRewriteStepCount
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      right.targetRewriteStepCount :=
  rfl

/-- Composition keeps the left hom source endpoint certificate ledger. -/
theorem TraceLocalizedWordHom.comp_sourceCertificateLedger
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.sourceCertificateLedger
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      left.sourceCertificateLedger :=
  rfl

/-- Composition keeps the right hom target endpoint certificate ledger. -/
theorem TraceLocalizedWordHom.comp_targetCertificateLedger
    {first second third : TraceLocalizedWordObject}
    (left : TraceLocalizedWordHom first second)
    (right : TraceLocalizedWordHom second third) :
    TraceLocalizedWordHom.targetCertificateLedger
        (TraceLocalizationWordClass.comp left right :
          TraceLocalizedWordHom first third) =
      right.targetCertificateLedger :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

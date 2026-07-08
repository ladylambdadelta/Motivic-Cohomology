import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Payload.TraceCalculus.Owner

/-!
# Trace-calculus hom payload in the unstable envelope

This file exposes endpoint certificate-ledger, trace-bookkeeping, and
rewrite-step payload carried by arbitrary unstable analytic-motive homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Source endpoint trace-bookkeeping payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.sourceTraceBookkeepingCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.sourceTraceBookkeepingCount hom

/-- Target endpoint trace-bookkeeping payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.targetTraceBookkeepingCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.targetTraceBookkeepingCount hom

/-- Endpoint trace-bookkeeping payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.endpointTraceBookkeepingCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.endpointTraceBookkeepingCount hom

/-- Source endpoint rewrite-step payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.sourceRewriteStepCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.sourceRewriteStepCount hom

/-- Target endpoint rewrite-step payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.targetRewriteStepCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.targetRewriteStepCount hom

/-- Endpoint rewrite-step payload carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.endpointRewriteStepCount
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    Nat :=
  TraceLocalizedWordHom.endpointRewriteStepCount hom

/-- Source endpoint certificate ledger carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.sourceCertificateLedger
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    ResidueChannelCertificateLedger :=
  TraceLocalizedWordHom.sourceCertificateLedger hom

/-- Target endpoint certificate ledger carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.targetCertificateLedger
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    ResidueChannelCertificateLedger :=
  TraceLocalizedWordHom.targetCertificateLedger hom

/-- Endpoint certificate ledger carried by an unstable hom. -/
def TraceUnstableAnalyticMotiveHom.endpointCertificateLedger
    {source target : TraceUnstableAnalyticMotive}
    (hom : TraceUnstableAnalyticMotiveHom source target) :
    ResidueChannelCertificateLedger :=
  TraceLocalizedWordHom.endpointCertificateLedger hom

end AnalyticMotives
end LFunctions
end Boundary

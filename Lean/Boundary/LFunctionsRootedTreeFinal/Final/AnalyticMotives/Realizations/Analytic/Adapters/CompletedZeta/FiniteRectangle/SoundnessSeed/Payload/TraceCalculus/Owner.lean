import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleRelationWitness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Owner

/-!
# Completed-zeta zero-pole quotient trace-calculus payload

This file records trace-bookkeeping and rewrite-step payload projections for
the completed-zeta zero-pole quotient input, quotient candidate, and support
witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero-pole quotient input certificate ledger splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_certificateLedger_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientInput.certificateLedger =
      ResidueChannelCertificateLedger.append
        completedZetaZeroPoleTraceCorQQuotientInput.formalSum.certificateLedger
        completedZetaZeroPoleTraceCorQQuotientInput.ledger.certificateLedger :=
  TraceCorQQuotientInput.certificateLedger_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientInput

/-- The zero-pole quotient input bookkeeping splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_traceBookkeepingCount_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientInput.traceBookkeepingCount =
      completedZetaZeroPoleTraceCorQQuotientInput.formalSum.traceBookkeepingCount +
        completedZetaZeroPoleTraceCorQQuotientInput.ledger.traceBookkeepingCount :=
  TraceCorQQuotientInput.traceBookkeepingCount_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientInput

/-- The zero-pole quotient input rewrite-step payload splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientInput_rewriteStepCount_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientInput.rewriteStepCount =
      completedZetaZeroPoleTraceCorQQuotientInput.formalSum.rewriteStepCount +
        completedZetaZeroPoleTraceCorQQuotientInput.ledger.rewriteStepCount :=
  TraceCorQQuotientInput.rewriteStepCount_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientInput

/-- The zero-pole quotient candidate certificate ledger splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_certificateLedger_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientCandidate.certificateLedger =
      ResidueChannelCertificateLedger.append
        completedZetaZeroPoleTraceCorQQuotientCandidate.formalSum.certificateLedger
        completedZetaZeroPoleTraceCorQQuotientCandidate.ledger.certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientCandidate

/-- The zero-pole quotient candidate bookkeeping splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_traceBookkeepingCount_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientCandidate.traceBookkeepingCount =
      completedZetaZeroPoleTraceCorQQuotientCandidate.formalSum.traceBookkeepingCount +
        completedZetaZeroPoleTraceCorQQuotientCandidate.ledger.traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientCandidate

/-- The zero-pole quotient candidate rewrite-step payload splits into formal sum and relation ledger. -/
theorem completedZetaZeroPoleTraceCorQQuotientCandidate_rewriteStepCount_eq_formalSum_ledger :
    completedZetaZeroPoleTraceCorQQuotientCandidate.rewriteStepCount =
      completedZetaZeroPoleTraceCorQQuotientCandidate.formalSum.rewriteStepCount +
        completedZetaZeroPoleTraceCorQQuotientCandidate.ledger.rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    completedZetaZeroPoleTraceCorQQuotientCandidate

/-- The zero-pole relation support candidate certificate ledger splits into support and relation ledger. -/
theorem completedZetaZeroPoleRelationSupportCandidate_certificateLedger_eq_formalSum_ledger :
    completedZetaZeroPoleRelationSupportCandidate.certificateLedger =
      ResidueChannelCertificateLedger.append
        completedZetaZeroPoleRelationSupportCandidate.formalSum.certificateLedger
        completedZetaZeroPoleRelationSupportCandidate.ledger.certificateLedger :=
  TraceCorQQuotientCandidate.certificateLedger_eq_formalSum_ledger
    completedZetaZeroPoleRelationSupportCandidate

/-- The zero-pole relation support candidate bookkeeping splits into support and relation ledger. -/
theorem completedZetaZeroPoleRelationSupportCandidate_traceBookkeepingCount_eq_formalSum_ledger :
    completedZetaZeroPoleRelationSupportCandidate.traceBookkeepingCount =
      completedZetaZeroPoleRelationSupportCandidate.formalSum.traceBookkeepingCount +
        completedZetaZeroPoleRelationSupportCandidate.ledger.traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    completedZetaZeroPoleRelationSupportCandidate

/-- The zero-pole relation support candidate rewrite-step payload splits into support and relation ledger. -/
theorem completedZetaZeroPoleRelationSupportCandidate_rewriteStepCount_eq_formalSum_ledger :
    completedZetaZeroPoleRelationSupportCandidate.rewriteStepCount =
      completedZetaZeroPoleRelationSupportCandidate.formalSum.rewriteStepCount +
        completedZetaZeroPoleRelationSupportCandidate.ledger.rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    completedZetaZeroPoleRelationSupportCandidate

/-- The zero-pole support witness keeps exactly its singleton relation-ledger certificates. -/
theorem completedZetaZeroPoleRelationSupportWitness_certificateLedger_eq_ledger :
    completedZetaZeroPoleRelationSupportWitness.certificateLedger =
      completedZetaZeroPoleRelationSupportWitness.ledger.certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    completedZetaZeroPoleRelationSupportWitness

/-- The zero-pole support witness keeps exactly its singleton relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleRelationSupportWitness_traceBookkeepingCount_eq_ledger :
    completedZetaZeroPoleRelationSupportWitness.traceBookkeepingCount =
      completedZetaZeroPoleRelationSupportWitness.ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    completedZetaZeroPoleRelationSupportWitness

/-- The zero-pole support witness keeps exactly its singleton relation-ledger rewrite steps. -/
theorem completedZetaZeroPoleRelationSupportWitness_rewriteStepCount_eq_ledger :
    completedZetaZeroPoleRelationSupportWitness.rewriteStepCount =
      completedZetaZeroPoleRelationSupportWitness.ledger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    completedZetaZeroPoleRelationSupportWitness

/-- The transported zero-pole support witness keeps exactly its relation-ledger certificates. -/
theorem completedZetaZeroPoleQuotientCandidateSupportWitness_certificateLedger_eq_ledger :
    completedZetaZeroPoleQuotientCandidateSupportWitness.certificateLedger =
      completedZetaZeroPoleQuotientCandidateSupportWitness.ledger.certificateLedger :=
  TraceCorQRelationWitness.certificateLedger_eq_relationLedger
    completedZetaZeroPoleQuotientCandidateSupportWitness

/-- The transported zero-pole support witness keeps exactly its relation-ledger bookkeeping. -/
theorem completedZetaZeroPoleQuotientCandidateSupportWitness_traceBookkeepingCount_eq_ledger :
    completedZetaZeroPoleQuotientCandidateSupportWitness.traceBookkeepingCount =
      completedZetaZeroPoleQuotientCandidateSupportWitness.ledger.traceBookkeepingCount :=
  TraceCorQRelationWitness.traceBookkeepingCount_eq_ledger
    completedZetaZeroPoleQuotientCandidateSupportWitness

/-- The transported zero-pole support witness keeps exactly its relation-ledger rewrite steps. -/
theorem completedZetaZeroPoleQuotientCandidateSupportWitness_rewriteStepCount_eq_ledger :
    completedZetaZeroPoleQuotientCandidateSupportWitness.rewriteStepCount =
      completedZetaZeroPoleQuotientCandidateSupportWitness.ledger.rewriteStepCount :=
  TraceCorQRelationWitness.rewriteStepCount_eq_ledger
    completedZetaZeroPoleQuotientCandidateSupportWitness

end AnalyticMotives
end LFunctions
end Boundary

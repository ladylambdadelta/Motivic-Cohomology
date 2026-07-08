import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Candidates.ImportedRectangles.Owner

/-!
# Payload facts for named-coherence support candidates

This file records bookkeeping and rewrite-step payload facts for named
coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support candidate splits trace bookkeeping into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.fubini source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.residueChannel source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.stokesResidue source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.refinement source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.associativity source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.leftIdentity source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate splits trace bookkeeping. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_traceBookkeepingCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).traceBookkeepingCount =
      support.traceBookkeepingCount +
        (TraceCorQRelationLedger.rightIdentity source target support).traceBookkeepingCount :=
  TraceCorQQuotientCandidate.traceBookkeepingCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

/-- A Fubini support candidate splits rewrite-step count into support and ledger payload. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.fubini source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)

/-- A schedule-exchange support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.scheduleExchange source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)

/-- A residue-channel support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.residueChannel source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)

/-- A Stokes-residue support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.stokesResidue source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)

/-- A refinement support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.refinement source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.refinementSupportCandidate source target support)

/-- An associativity support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.associativity source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.associativitySupportCandidate source target support)

/-- A left-identity support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.leftIdentity source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)

/-- A right-identity support candidate splits rewrite-step count. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_rewriteStepCount
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).rewriteStepCount =
      support.rewriteStepCount +
        (TraceCorQRelationLedger.rightIdentity source target support).rewriteStepCount :=
  TraceCorQQuotientCandidate.rewriteStepCount_eq_formalSum_ledger
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)

end AnalyticMotives
end LFunctions
end Boundary

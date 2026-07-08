import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Candidates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Payload.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Payload.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Inputs.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Payload.CertificateLedgers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Payload.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Public.Generators.NamedCoherence.Payload.Lengths.Owner

/-!
# Public named-coherence relation witnesses

This file exposes named-coherence support candidates, support witnesses, and
witness-ledger facts under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support candidates. -/
def TraceCorQ.relationGenerator_fubiniSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.fubiniSupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support candidates. -/
def TraceCorQ.relationGenerator_scheduleExchangeSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support candidates. -/
def TraceCorQ.relationGenerator_residueChannelSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.residueChannelSupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support candidates. -/
def TraceCorQ.relationGenerator_stokesResidueSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.stokesResidueSupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes refinement support candidates. -/
def TraceCorQ.relationGenerator_refinementSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.refinementSupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes associativity support candidates. -/
def TraceCorQ.relationGenerator_associativitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.associativitySupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support candidates. -/
def TraceCorQ.relationGenerator_leftIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.leftIdentitySupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support candidates. -/
def TraceCorQ.relationGenerator_rightIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  TraceCorQRelationGenerator.rightIdentitySupportCandidate
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support witnesses. -/
def TraceCorQ.relationGenerator_fubiniSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.fubiniSupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.fubiniSupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support witnesses. -/
def TraceCorQ.relationGenerator_scheduleExchangeSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support witnesses. -/
def TraceCorQ.relationGenerator_residueChannelSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.residueChannelSupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.residueChannelSupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support witnesses. -/
def TraceCorQ.relationGenerator_stokesResidueSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.stokesResidueSupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes refinement support witnesses. -/
def TraceCorQ.relationGenerator_refinementSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.refinementSupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.refinementSupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes associativity support witnesses. -/
def TraceCorQ.relationGenerator_associativitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.associativitySupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.associativitySupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support witnesses. -/
def TraceCorQ.relationGenerator_leftIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.leftIdentitySupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support witnesses. -/
def TraceCorQ.relationGenerator_rightIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.rightIdentitySupportCandidate source target support)
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness source target support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  TraceCorQRelationGenerator.fubiniSupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness source target support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness source target support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  TraceCorQRelationGenerator.residueChannelSupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness source target support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  TraceCorQRelationGenerator.stokesResidueSupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness source target support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  TraceCorQRelationGenerator.refinementSupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness source target support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  TraceCorQRelationGenerator.associativitySupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness source target support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  TraceCorQRelationGenerator.leftIdentitySupportWitness_ledger
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-witness ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness source target support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  TraceCorQRelationGenerator.rightIdentitySupportWitness_ledger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner

/-!
# Projection facts for named-coherence support candidates

This file owns the formal-sum and singleton-ledger projections of the named
coherence support candidates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A Fubini support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A Fubini support candidate has the singleton Fubini relation ledger. -/
theorem TraceCorQRelationGenerator.fubiniSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  rfl

/-- A schedule-exchange support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A schedule-exchange support candidate has the singleton schedule-exchange ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  rfl

/-- A residue-channel support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A residue-channel support candidate has the singleton residue-channel ledger. -/
theorem TraceCorQRelationGenerator.residueChannelSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  rfl

/-- A Stokes-residue support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A Stokes-residue support candidate has the singleton Stokes-residue ledger. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  rfl

/-- A refinement support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A refinement support candidate has the singleton refinement ledger. -/
theorem TraceCorQRelationGenerator.refinementSupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  rfl

/-- An associativity support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- An associativity support candidate has the singleton associativity ledger. -/
theorem TraceCorQRelationGenerator.associativitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  rfl

/-- A left-identity support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A left-identity support candidate has the singleton left-identity ledger. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  rfl

/-- A right-identity support candidate has the supplied formal support. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A right-identity support candidate has the singleton right-identity ledger. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportCandidate_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportCandidate
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

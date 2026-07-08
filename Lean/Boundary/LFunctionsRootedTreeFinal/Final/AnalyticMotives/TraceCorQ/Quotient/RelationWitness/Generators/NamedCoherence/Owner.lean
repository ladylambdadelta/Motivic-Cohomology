import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.NamedCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.NamedCoherence.Owner

/-!
# Named-coherence relation witnesses

This file turns the named coherence relation generators into their canonical
finite quotient-relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The support candidate of a Fubini coherence relation. -/
def TraceCorQRelationGenerator.fubiniSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.fubini
    source
    target
    support).supportCandidate

/-- The support candidate of a schedule-exchange coherence relation. -/
def TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.scheduleExchange
    source
    target
    support).supportCandidate

/-- The support candidate of a residue-channel coherence relation. -/
def TraceCorQRelationGenerator.residueChannelSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.residueChannel
    source
    target
    support).supportCandidate

/-- The support candidate of a Stokes-residue coherence relation. -/
def TraceCorQRelationGenerator.stokesResidueSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.stokesResidue
    source
    target
    support).supportCandidate

/-- The support candidate of a refinement coherence relation. -/
def TraceCorQRelationGenerator.refinementSupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.refinement
    source
    target
    support).supportCandidate

/-- The support candidate of an associativity coherence relation. -/
def TraceCorQRelationGenerator.associativitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.associativity
    source
    target
    support).supportCandidate

/-- The support candidate of a left-identity coherence relation. -/
def TraceCorQRelationGenerator.leftIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.leftIdentity
    source
    target
    support).supportCandidate

/-- The support candidate of a right-identity coherence relation. -/
def TraceCorQRelationGenerator.rightIdentitySupportCandidate
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientCandidate :=
  (TraceCorQRelationGenerator.rightIdentity
    source
    target
    support).supportCandidate

/-- A Fubini coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.fubiniSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.fubiniSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.fubini
    source
    target
    support).supportWitness

/-- A schedule-exchange coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.scheduleExchangeSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.scheduleExchangeSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.scheduleExchange
    source
    target
    support).supportWitness

/-- A residue-channel coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.residueChannelSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.residueChannelSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.residueChannel
    source
    target
    support).supportWitness

/-- A Stokes-residue coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.stokesResidueSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.stokesResidueSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.stokesResidue
    source
    target
    support).supportWitness

/-- A refinement coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.refinementSupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.refinementSupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.refinement
    source
    target
    support).supportWitness

/-- An associativity coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.associativitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.associativitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.associativity
    source
    target
    support).supportWitness

/-- A left-identity coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.leftIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.leftIdentitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.leftIdentity
    source
    target
    support).supportWitness

/-- A right-identity coherence relation kills its formal support. -/
def TraceCorQRelationGenerator.rightIdentitySupportWitness
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQRelationWitness
      (TraceCorQRelationGenerator.rightIdentitySupportCandidate
        source
        target
        support)
      TraceCorQQuotientCandidate.empty :=
  (TraceCorQRelationGenerator.rightIdentity
    source
    target
    support).supportWitness

/-- The Fubini support witness has the singleton Fubini relation ledger. -/
theorem TraceCorQRelationGenerator.fubiniSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  rfl

/-- The schedule-exchange support witness has the singleton schedule-exchange ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  rfl

/-- The residue-channel support witness has the singleton residue-channel ledger. -/
theorem TraceCorQRelationGenerator.residueChannelSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  rfl

/-- The Stokes-residue support witness has the singleton Stokes-residue ledger. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  rfl

/-- The refinement support witness has the singleton refinement ledger. -/
theorem TraceCorQRelationGenerator.refinementSupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  rfl

/-- The associativity support witness has the singleton associativity ledger. -/
theorem TraceCorQRelationGenerator.associativitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  rfl

/-- The left-identity support witness has the singleton left-identity ledger. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  rfl

/-- The right-identity support witness has the singleton right-identity ledger. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportWitness_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportWitness
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

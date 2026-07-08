import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Owner

/-!
# Public named-coherence support inputs

This file exposes named-coherence support inputs and their formal-sum and
singleton-ledger projections under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes Fubini support inputs. -/
def TraceCorQ.relationGenerator_fubiniSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.fubiniSupportInput
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support inputs. -/
def TraceCorQ.relationGenerator_scheduleExchangeSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support inputs. -/
def TraceCorQ.relationGenerator_residueChannelSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.residueChannelSupportInput
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support inputs. -/
def TraceCorQ.relationGenerator_stokesResidueSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.stokesResidueSupportInput
    source
    target
    support

/-- The trace-correspondence root exposes refinement support inputs. -/
def TraceCorQ.relationGenerator_refinementSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.refinementSupportInput
    source
    target
    support

/-- The trace-correspondence root exposes associativity support inputs. -/
def TraceCorQ.relationGenerator_associativitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.associativitySupportInput
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support inputs. -/
def TraceCorQ.relationGenerator_leftIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.leftIdentitySupportInput
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support inputs. -/
def TraceCorQ.relationGenerator_rightIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.rightIdentitySupportInput
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-input formal sums. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.fubiniSupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input formal sums. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input formal sums. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.residueChannelSupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input formal sums. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input formal sums. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.refinementSupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input formal sums. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.associativitySupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input formal sums. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input formal sums. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).formalSum =
      support :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_formalSum
    source
    target
    support

/-- The trace-correspondence root exposes Fubini support-input ledgers. -/
theorem TraceCorQ.relationGenerator_fubiniSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  TraceCorQRelationGenerator.fubiniSupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes schedule-exchange support-input ledgers. -/
theorem TraceCorQ.relationGenerator_scheduleExchangeSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes residue-channel support-input ledgers. -/
theorem TraceCorQ.relationGenerator_residueChannelSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  TraceCorQRelationGenerator.residueChannelSupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes Stokes-residue support-input ledgers. -/
theorem TraceCorQ.relationGenerator_stokesResidueSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  TraceCorQRelationGenerator.stokesResidueSupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes refinement support-input ledgers. -/
theorem TraceCorQ.relationGenerator_refinementSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  TraceCorQRelationGenerator.refinementSupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes associativity support-input ledgers. -/
theorem TraceCorQ.relationGenerator_associativitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  TraceCorQRelationGenerator.associativitySupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes left-identity support-input ledgers. -/
theorem TraceCorQ.relationGenerator_leftIdentitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  TraceCorQRelationGenerator.leftIdentitySupportInput_ledger
    source
    target
    support

/-- The trace-correspondence root exposes right-identity support-input ledgers. -/
theorem TraceCorQ.relationGenerator_rightIdentitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  TraceCorQRelationGenerator.rightIdentitySupportInput_ledger
    source
    target
    support

end AnalyticMotives
end LFunctions
end Boundary

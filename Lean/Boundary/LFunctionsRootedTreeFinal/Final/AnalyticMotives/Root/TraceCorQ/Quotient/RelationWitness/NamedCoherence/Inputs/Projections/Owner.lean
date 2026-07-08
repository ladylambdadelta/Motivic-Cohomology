import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Inputs.Owner

/-!
# Top-root named-coherence input projections

This file exposes formal-support and singleton-ledger projections for
named-coherence support inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes Fubini support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.fubiniSupportInput
    source
    target
    support

/-- The top root exposes schedule-exchange support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.scheduleExchangeSupportInput
    source
    target
    support

/-- The top root exposes residue-channel support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.residueChannelSupportInput
    source
    target
    support

/-- The top root exposes Stokes-residue support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.stokesResidueSupportInput
    source
    target
    support

/-- The top root exposes refinement support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.refinementSupportInput
    source
    target
    support

/-- The top root exposes associativity support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.associativitySupportInput
    source
    target
    support

/-- The top root exposes left-identity support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.leftIdentitySupportInput
    source
    target
    support

/-- The top root exposes right-identity support inputs. -/
def AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  TraceCorQRelationGenerator.rightIdentitySupportInput
    source
    target
    support

/-- The top root exposes the formal support of a Fubini support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_formalSum
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

/-- The top root exposes the formal support of a schedule-exchange support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_formalSum
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

/-- The top root exposes the formal support of a residue-channel support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_formalSum
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

/-- The top root exposes the formal support of a Stokes-residue support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_formalSum
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

/-- The top root exposes the formal support of a refinement support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_formalSum
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

/-- The top root exposes the formal support of an associativity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_formalSum
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

/-- The top root exposes the formal support of a left-identity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_formalSum
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

/-- The top root exposes the formal support of a right-identity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_formalSum
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

/-- The top root exposes the singleton ledger of a Fubini support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_fubiniSupportInput_ledger
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

/-- The top root exposes the singleton ledger of a schedule-exchange support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_scheduleExchangeSupportInput_ledger
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

/-- The top root exposes the singleton ledger of a residue-channel support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_residueChannelSupportInput_ledger
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

/-- The top root exposes the singleton ledger of a Stokes-residue support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_stokesResidueSupportInput_ledger
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

/-- The top root exposes the singleton ledger of a refinement support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_refinementSupportInput_ledger
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

/-- The top root exposes the singleton ledger of an associativity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_associativitySupportInput_ledger
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

/-- The top root exposes the singleton ledger of a left-identity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_leftIdentitySupportInput_ledger
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

/-- The top root exposes the singleton ledger of a right-identity support input. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_rightIdentitySupportInput_ledger
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

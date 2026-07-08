import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Generators.NamedCoherence.Owner

/-!
# Named-coherence support inputs

This file exposes the pre-candidate quotient inputs attached to named coherence
relation generators.  Each input is the supplied formal support equipped with
the singleton named relation ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The support input of a Fubini coherence relation. -/
def TraceCorQRelationGenerator.fubiniSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.fubini
    source
    target
    support).supportQuotientInput

/-- The support input of a schedule-exchange coherence relation. -/
def TraceCorQRelationGenerator.scheduleExchangeSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.scheduleExchange
    source
    target
    support).supportQuotientInput

/-- The support input of a residue-channel coherence relation. -/
def TraceCorQRelationGenerator.residueChannelSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.residueChannel
    source
    target
    support).supportQuotientInput

/-- The support input of a Stokes-residue coherence relation. -/
def TraceCorQRelationGenerator.stokesResidueSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.stokesResidue
    source
    target
    support).supportQuotientInput

/-- The support input of a refinement coherence relation. -/
def TraceCorQRelationGenerator.refinementSupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.refinement
    source
    target
    support).supportQuotientInput

/-- The support input of an associativity coherence relation. -/
def TraceCorQRelationGenerator.associativitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.associativity
    source
    target
    support).supportQuotientInput

/-- The support input of a left-identity coherence relation. -/
def TraceCorQRelationGenerator.leftIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.leftIdentity
    source
    target
    support).supportQuotientInput

/-- The support input of a right-identity coherence relation. -/
def TraceCorQRelationGenerator.rightIdentitySupportInput
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    TraceCorQQuotientInput :=
  (TraceCorQRelationGenerator.rightIdentity
    source
    target
    support).supportQuotientInput

/-- A Fubini support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A schedule-exchange support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A residue-channel support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A Stokes-residue support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A refinement support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- An associativity support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A left-identity support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A right-identity support input has the supplied formal support. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_formalSum
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).formalSum =
      support :=
  rfl

/-- A Fubini support input has the singleton Fubini ledger. -/
theorem TraceCorQRelationGenerator.fubiniSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.fubiniSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.fubini source target support :=
  rfl

/-- A schedule-exchange support input has the singleton schedule-exchange ledger. -/
theorem TraceCorQRelationGenerator.scheduleExchangeSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.scheduleExchangeSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.scheduleExchange source target support :=
  rfl

/-- A residue-channel support input has the singleton residue-channel ledger. -/
theorem TraceCorQRelationGenerator.residueChannelSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.residueChannelSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.residueChannel source target support :=
  rfl

/-- A Stokes-residue support input has the singleton Stokes-residue ledger. -/
theorem TraceCorQRelationGenerator.stokesResidueSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.stokesResidueSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.stokesResidue source target support :=
  rfl

/-- A refinement support input has the singleton refinement ledger. -/
theorem TraceCorQRelationGenerator.refinementSupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.refinementSupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.refinement source target support :=
  rfl

/-- An associativity support input has the singleton associativity ledger. -/
theorem TraceCorQRelationGenerator.associativitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.associativitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.associativity source target support :=
  rfl

/-- A left-identity support input has the singleton left-identity ledger. -/
theorem TraceCorQRelationGenerator.leftIdentitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.leftIdentitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.leftIdentity source target support :=
  rfl

/-- A right-identity support input has the singleton right-identity ledger. -/
theorem TraceCorQRelationGenerator.rightIdentitySupportInput_ledger
    (source target : TraceRewritePath)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.rightIdentitySupportInput
      source
      target
      support).ledger =
      TraceCorQRelationLedger.rightIdentity source target support :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

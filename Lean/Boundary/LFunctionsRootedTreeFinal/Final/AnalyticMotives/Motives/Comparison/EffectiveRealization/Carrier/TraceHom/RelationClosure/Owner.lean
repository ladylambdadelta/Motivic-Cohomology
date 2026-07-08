import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationGenerator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Algebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationClosure.Compatibility.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationClosure.FormalSum.Owner

/-!
# Relation-closure carriers for analytic effective realization

This file exposes finite relation-closure derivations between raw quotient
candidates.  These derivations are the concrete proof trees carried by raw
relation witnesses.  Child files expose compatibility and formal-sum
normalization constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual finite relation-closure derivation. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureCarrier
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger left right :=
  derivation

/-- Reflexive relation-closure derivation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureRefl
    (ledger : TraceCorQRelationLedger)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure ledger candidate candidate :=
  TraceCorQRelationClosure.reflDerivation ledger candidate

/-- Empty-ledger reflexive relation-closure derivation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureEmptyRefl
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationClosure
      TraceCorQRelationLedger.empty
      candidate
      candidate :=
  TraceCorQRelationClosure.emptyRefl candidate

/-- Primitive relation-generator step derivation at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureStep
    (ledger : TraceCorQRelationLedger)
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append
        (TraceCorQRelationLedger.singleton relation)
        ledger)
      (TraceCorQQuotientInput.ofFormalSumLedger
        relation.support
        (TraceCorQRelationLedger.singleton relation))
      TraceCorQQuotientCandidate.empty :=
  TraceCorQRelationClosure.stepDerivation ledger relation

/-- Symmetry for relation-closure derivations at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureSymm
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure ledger right left :=
  TraceCorQRelationClosure.symmDerivation
    ledger
    left
    right
    derivation

/-- Transitivity for relation-closure derivations at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureTrans
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append firstLedger secondLedger)
      left
      right :=
  TraceCorQRelationClosure.transDerivation
    firstLedger
    secondLedger
    left
    middle
    right
    first
    second

/-- The relation-closure carrier is definitionally the supplied derivation. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureCarrier_eq
    {ledger : TraceCorQRelationLedger}
    {left right : TraceCorQQuotientCandidate}
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureCarrier derivation =
      derivation :=
  rfl

/-- The comparison primitive step is the existing primitive step derivation. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureStep_eq_step
    (ledger : TraceCorQRelationLedger)
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureStep
      ledger
      relation =
      TraceCorQRelationClosure.step ledger relation :=
  TraceCorQRelationClosure.stepDerivation_eq_step
    ledger
    relation

/-- Empty-ledger reflexivity is the existing empty reflexive derivation. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureEmptyRefl_eq
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureEmptyRefl candidate =
      TraceCorQRelationClosure.emptyRefl candidate :=
  rfl

/-- Symmetry at the comparison boundary is the existing symmetry constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureSymm_eq
    (ledger : TraceCorQRelationLedger)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureSymm
      ledger
      left
      right
      derivation =
      TraceCorQRelationClosure.symm ledger left right derivation :=
  rfl

/-- Transitivity at the comparison boundary is the existing transitivity constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureTrans_eq
    (firstLedger secondLedger : TraceCorQRelationLedger)
    (left middle right : TraceCorQQuotientCandidate)
    (first : TraceCorQRelationClosure firstLedger left middle)
    (second : TraceCorQRelationClosure secondLedger middle right) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureTrans
      firstLedger
      secondLedger
      left
      middle
      right
      first
      second =
      TraceCorQRelationClosure.trans
        firstLedger
        secondLedger
        left
        middle
        right
        first
        second :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

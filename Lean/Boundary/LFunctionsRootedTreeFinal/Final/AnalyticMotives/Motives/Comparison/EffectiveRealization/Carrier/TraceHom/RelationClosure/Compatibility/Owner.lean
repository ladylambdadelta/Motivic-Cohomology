import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationClosure.Owner

/-!
# Compatibility relation-closure carriers for analytic effective realization

This file exposes additive, scalar, and composition compatibility constructors
for finite relation-closure derivations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Additive compatibility for relation-closure derivations at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureAddCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation :
      TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation :
      TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.add left₁ right₁)
      (TraceCorQQuotientCandidate.add left₂ right₂) :=
  TraceCorQRelationClosure.addCongrDerivation
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- Scalar compatibility for relation-closure derivations at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureSmulCongr
    (ledger : TraceCorQRelationLedger)
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceCorQRelationClosure
      ledger
      (TraceCorQQuotientCandidate.smul coefficient left)
      (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQRelationClosure.smulCongrDerivation
    ledger
    coefficient
    left
    right
    derivation

/-- Composition compatibility for relation-closure derivations at the comparison boundary. -/
def TraceAnalyticEffectiveRealization.traceHomRelationClosureCompCongr
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation :
      TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation :
      TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceCorQRelationClosure
      (TraceCorQRelationLedger.append leftLedger rightLedger)
      (TraceCorQQuotientCandidate.comp left₁ right₁)
      (TraceCorQQuotientCandidate.comp left₂ right₂) :=
  TraceCorQRelationClosure.compCongrDerivation
    leftLedger
    rightLedger
    left₁
    left₂
    right₁
    right₂
    leftDerivation
    rightDerivation

/-- Additive compatibility at the boundary is the existing additive constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureAddCongr_eq
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation :
      TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation :
      TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureAddCongr
      leftLedger
      rightLedger
      left₁
      left₂
      right₁
      right₂
      leftDerivation
      rightDerivation =
      TraceCorQRelationClosure.addCongr
        leftLedger
        rightLedger
        left₁
        left₂
        right₁
        right₂
        leftDerivation
        rightDerivation :=
  rfl

/-- Scalar compatibility at the boundary is the existing scalar constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureSmulCongr_eq
    (ledger : TraceCorQRelationLedger)
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate)
    (derivation : TraceCorQRelationClosure ledger left right) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureSmulCongr
      ledger
      coefficient
      left
      right
      derivation =
      TraceCorQRelationClosure.smulCongr
        ledger
        coefficient
        left
        right
        derivation :=
  rfl

/-- Composition compatibility at the boundary is the existing composition constructor. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationClosureCompCongr_eq
    (leftLedger rightLedger : TraceCorQRelationLedger)
    (left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate)
    (leftDerivation :
      TraceCorQRelationClosure leftLedger left₁ left₂)
    (rightDerivation :
      TraceCorQRelationClosure rightLedger right₁ right₂) :
    TraceAnalyticEffectiveRealization.traceHomRelationClosureCompCongr
      leftLedger
      rightLedger
      left₁
      left₂
      right₁
      right₂
      leftDerivation
      rightDerivation =
      TraceCorQRelationClosure.compCongr
        leftLedger
        rightLedger
        left₁
        left₂
        right₁
        right₂
        leftDerivation
        rightDerivation :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.Owner

/-!
# Core quotient inputs for Q-linear trace correspondences

This file owns the raw pre-quotient input type, its projections, payload
accessors, and primitive empty, additive, scalar, and composition constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The pre-quotient input for a trace-correspondence quotient construction. -/
abbrev TraceCorQQuotientInput :=
  TraceCorQFormalSum × TraceCorQRelationLedger

/-- The formal Q-linear sum carried by a quotient input. -/
def TraceCorQQuotientInput.formalSum
    (input : TraceCorQQuotientInput) :
    TraceCorQFormalSum :=
  input.1

/-- The relation ledger carried by a quotient input. -/
def TraceCorQQuotientInput.ledger
    (input : TraceCorQQuotientInput) :
    TraceCorQRelationLedger :=
  input.2

/-- The analytic certificate ledger carried by a quotient input. -/
def TraceCorQQuotientInput.certificateLedger
    (input : TraceCorQQuotientInput) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.append
    input.formalSum.certificateLedger
    input.ledger.certificateLedger

/-- The imported finite-rectangle payload carried by a quotient input. -/
def TraceCorQQuotientInput.importedRectangleCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a quotient input. -/
def TraceCorQQuotientInput.importedRectangles
    (input : TraceCorQQuotientInput) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  input.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a quotient input. -/
def TraceCorQQuotientInput.traceBookkeepingCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a quotient input. -/
def TraceCorQQuotientInput.rewriteStepCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.certificateLedger.rewriteStepCount

/-- Build a quotient input from a formal sum and relation ledger. -/
def TraceCorQQuotientInput.ofFormalSumLedger
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    TraceCorQQuotientInput :=
  (formalSum, ledger)

/-- The empty quotient input has zero formal sum and empty relation ledger. -/
def TraceCorQQuotientInput.empty : TraceCorQQuotientInput :=
  (TraceCorQFormalSum.zero, TraceCorQRelationLedger.empty)

/-- Add quotient inputs by adding formal sums and appending relation ledgers. -/
def TraceCorQQuotientInput.add
    (left right : TraceCorQQuotientInput) :
    TraceCorQQuotientInput :=
  (TraceCorQFormalSum.add left.formalSum right.formalSum,
    TraceCorQRelationLedger.append left.ledger right.ledger)

/-- Scale a quotient input by scaling its formal sum and keeping its ledger. -/
def TraceCorQQuotientInput.smul
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput :=
  (TraceCorQFormalSum.smul coefficient input.formalSum,
    input.ledger)

/-- Compose quotient inputs by composing formal sums and appending ledgers. -/
def TraceCorQQuotientInput.comp
    (left right : TraceCorQQuotientInput) :
    TraceCorQQuotientInput :=
  (TraceCorQFormalSum.comp left.formalSum right.formalSum,
    TraceCorQRelationLedger.append left.ledger right.ledger)

end AnalyticMotives
end LFunctions
end Boundary

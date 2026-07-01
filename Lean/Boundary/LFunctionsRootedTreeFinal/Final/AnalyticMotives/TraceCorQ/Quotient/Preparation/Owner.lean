import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.Owner

/-!
# Quotient preparation for Q-linear trace correspondences

This file owns the raw input package for a later quotient construction.

A quotient input is a formal Q-linear trace-correspondence sum together with
the finite relation ledger available to reduce it.  This file does not impose
an equivalence relation and does not define quotient morphisms.
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

/-- The formal sum projection of a built quotient input. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_formalSum
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger).formalSum =
      formalSum :=
  rfl

/-- The ledger projection of a built quotient input. -/
theorem TraceCorQQuotientInput.ofFormalSumLedger_ledger
    (formalSum : TraceCorQFormalSum)
    (ledger : TraceCorQRelationLedger) :
    (TraceCorQQuotientInput.ofFormalSumLedger formalSum ledger).ledger =
      ledger :=
  rfl

/-- The empty quotient input has zero formal sum. -/
theorem TraceCorQQuotientInput.empty_formalSum :
    TraceCorQQuotientInput.empty.formalSum =
      TraceCorQFormalSum.zero :=
  rfl

/-- The empty quotient input has empty relation ledger. -/
theorem TraceCorQQuotientInput.empty_ledger :
    TraceCorQQuotientInput.empty.ledger =
      TraceCorQRelationLedger.empty :=
  rfl

/-- The formal sum of a quotient-input sum is the sum of formal sums. -/
theorem TraceCorQQuotientInput.add_formalSum
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  rfl

/-- The ledger of a quotient-input sum is the appended ledger. -/
theorem TraceCorQQuotientInput.add_ledger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.add left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The formal sum of a scaled quotient input is the scaled formal sum. -/
theorem TraceCorQQuotientInput.smul_formalSum
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).formalSum =
      TraceCorQFormalSum.smul coefficient input.formalSum :=
  rfl

/-- Scaling a quotient input preserves its relation ledger. -/
theorem TraceCorQQuotientInput.smul_ledger
    (coefficient : Rat)
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.smul coefficient input).ledger =
      input.ledger :=
  rfl

/-- The formal sum of a quotient-input composition is the composed formal sum. -/
theorem TraceCorQQuotientInput.comp_formalSum
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  rfl

/-- The ledger of a quotient-input composition is the appended ledger. -/
theorem TraceCorQQuotientInput.comp_ledger
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The formal-sum projection of left-distributed quotient-input composition. -/
theorem TraceCorQQuotientInput.add_comp_formalSum
    (left right tail : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.add left right)
      tail).formalSum =
      TraceCorQFormalSum.add
        (TraceCorQQuotientInput.comp left tail).formalSum
        (TraceCorQQuotientInput.comp right tail).formalSum :=
  TraceCorQFormalSum.add_comp
    left.formalSum
    right.formalSum
    tail.formalSum

/-- The formal-sum projection of right-distributed quotient-input composition. -/
theorem TraceCorQQuotientInput.comp_add_formalSum_perm
    (left right tail : TraceCorQQuotientInput) :
    List.Perm
      (TraceCorQQuotientInput.comp
        left
        (TraceCorQQuotientInput.add right tail)).formalSum
      (TraceCorQFormalSum.add
        (TraceCorQQuotientInput.comp left right).formalSum
        (TraceCorQQuotientInput.comp left tail).formalSum) :=
  TraceCorQFormalSum.comp_add_perm
    left.formalSum
    right.formalSum
    tail.formalSum

/-- The formal-sum projection of scalar compatibility on the left of composition. -/
theorem TraceCorQQuotientInput.smul_comp_formalSum
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.smul coefficient left)
      right).formalSum =
      (TraceCorQQuotientInput.smul
        coefficient
        (TraceCorQQuotientInput.comp left right)).formalSum :=
  TraceCorQFormalSum.smul_comp
    coefficient
    left.formalSum
    right.formalSum

/-- The formal-sum projection of scalar compatibility on the right of composition. -/
theorem TraceCorQQuotientInput.comp_smul_formalSum
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      left
      (TraceCorQQuotientInput.smul coefficient right)).formalSum =
      (TraceCorQQuotientInput.smul
        coefficient
        (TraceCorQQuotientInput.comp left right)).formalSum :=
  TraceCorQFormalSum.comp_smul
    coefficient
    left.formalSum
    right.formalSum

/-- Scaling the empty quotient input gives the empty quotient input. -/
theorem TraceCorQQuotientInput.smul_empty
    (coefficient : Rat) :
    TraceCorQQuotientInput.smul
      coefficient
      TraceCorQQuotientInput.empty =
      TraceCorQQuotientInput.empty :=
  Prod.ext
    (TraceCorQFormalSum.smul_zero coefficient)
    rfl

/-- Scaling distributes over quotient-input addition. -/
theorem TraceCorQQuotientInput.smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.smul
      coefficient
      (TraceCorQQuotientInput.add left right) =
      TraceCorQQuotientInput.add
        (TraceCorQQuotientInput.smul coefficient left)
        (TraceCorQQuotientInput.smul coefficient right) :=
  Prod.ext
    (TraceCorQFormalSum.smul_add
      coefficient
      left.formalSum
      right.formalSum)
    rfl

/-- Scaling a quotient input by one leaves it unchanged. -/
theorem TraceCorQQuotientInput.one_smul
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.smul 1 input =
      input :=
  Prod.ext
    (TraceCorQFormalSum.one_smul input.formalSum)
    rfl

/-- Successive scalar multiplications of quotient inputs compose by multiplying scalars. -/
theorem TraceCorQQuotientInput.smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.smul
      leftCoefficient
      (TraceCorQQuotientInput.smul rightCoefficient input) =
      TraceCorQQuotientInput.smul
        (leftCoefficient * rightCoefficient)
        input :=
  Prod.ext
    (TraceCorQFormalSum.smul_smul
      leftCoefficient
      rightCoefficient
      input.formalSum)
    rfl

/-- Adding the empty quotient input on the left leaves a quotient input unchanged. -/
theorem TraceCorQQuotientInput.empty_add
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.add
      TraceCorQQuotientInput.empty
      input =
      input :=
  rfl

/-- Adding the empty quotient input on the right leaves a quotient input unchanged. -/
theorem TraceCorQQuotientInput.add_empty
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.add
      input
      TraceCorQQuotientInput.empty =
      input :=
  Prod.ext
    (TraceCorQFormalSum.add_zero input.formalSum)
    (TraceCorQRelationLedger.append_empty input.ledger)

/-- Addition of quotient inputs is associative. -/
theorem TraceCorQQuotientInput.add_assoc
    (first second third : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.add
      (TraceCorQQuotientInput.add first second)
      third =
      TraceCorQQuotientInput.add
        first
        (TraceCorQQuotientInput.add second third) :=
  Prod.ext
    (TraceCorQFormalSum.add_assoc
      first.formalSum
      second.formalSum
      third.formalSum)
    (TraceCorQRelationLedger.append_assoc
      first.ledger
      second.ledger
      third.ledger)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Quotient candidates for Q-linear trace correspondences

This file owns raw candidate representatives for a later quotient
construction.

A candidate is only a quotient input viewed as a representative.  No
equivalence relation is imposed here.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A raw candidate representative for a future quotient trace correspondence. -/
abbrev TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput

/-- The quotient input represented by a candidate. -/
def TraceCorQQuotientCandidate.input
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientInput :=
  candidate

/-- Build a quotient candidate from a quotient input. -/
def TraceCorQQuotientCandidate.ofInput
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientCandidate :=
  input

/-- The formal sum represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.formalSum
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQFormalSum :=
  candidate.input.formalSum

/-- The relation ledger represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.ledger
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationLedger :=
  candidate.input.ledger

/-- The empty quotient candidate. -/
def TraceCorQQuotientCandidate.empty :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.empty

/-- Add quotient candidates by adding their quotient inputs. -/
def TraceCorQQuotientCandidate.add
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.add left.input right.input

/-- Scale a quotient candidate by scaling its quotient input. -/
def TraceCorQQuotientCandidate.smul
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.smul coefficient candidate.input

/-- Compose quotient candidates by composing their quotient inputs. -/
def TraceCorQQuotientCandidate.comp
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.comp left.input right.input

/-- Building a candidate from an input has that input. -/
theorem TraceCorQQuotientCandidate.ofInput_input
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).input =
      input :=
  rfl

/-- The empty candidate has empty input. -/
theorem TraceCorQQuotientCandidate.empty_input :
    TraceCorQQuotientCandidate.empty.input =
      TraceCorQQuotientInput.empty :=
  rfl

/-- The formal sum of a candidate built from an input is the input formal sum. -/
theorem TraceCorQQuotientCandidate.ofInput_formalSum
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).formalSum =
      input.formalSum :=
  rfl

/-- The ledger of a candidate built from an input is the input ledger. -/
theorem TraceCorQQuotientCandidate.ofInput_ledger
    (input : TraceCorQQuotientInput) :
    (TraceCorQQuotientCandidate.ofInput input).ledger =
      input.ledger :=
  rfl

/-- The input of a candidate sum is the sum of the inputs. -/
theorem TraceCorQQuotientCandidate.add_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).input =
      TraceCorQQuotientInput.add left.input right.input :=
  rfl

/-- The formal sum of a candidate sum is the sum of formal sums. -/
theorem TraceCorQQuotientCandidate.add_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).formalSum =
      TraceCorQFormalSum.add left.formalSum right.formalSum :=
  rfl

/-- The ledger of a candidate sum is the appended ledger. -/
theorem TraceCorQQuotientCandidate.add_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.add left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The input of a scaled candidate is the scaled input. -/
theorem TraceCorQQuotientCandidate.smul_input
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).input =
      TraceCorQQuotientInput.smul coefficient candidate.input :=
  rfl

/-- The formal sum of a scaled candidate is the scaled formal sum. -/
theorem TraceCorQQuotientCandidate.smul_formalSum
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).formalSum =
      TraceCorQFormalSum.smul coefficient candidate.formalSum :=
  rfl

/-- Scaling a candidate preserves its relation ledger. -/
theorem TraceCorQQuotientCandidate.smul_ledger
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.smul coefficient candidate).ledger =
      candidate.ledger :=
  rfl

/-- The input of a candidate composition is the composition of inputs. -/
theorem TraceCorQQuotientCandidate.comp_input
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).input =
      TraceCorQQuotientInput.comp left.input right.input :=
  rfl

/-- The formal sum of a candidate composition is the composed formal sum. -/
theorem TraceCorQQuotientCandidate.comp_formalSum
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).formalSum =
      TraceCorQFormalSum.comp left.formalSum right.formalSum :=
  rfl

/-- The ledger of a candidate composition is the appended ledger. -/
theorem TraceCorQQuotientCandidate.comp_ledger
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp left right).ledger =
      TraceCorQRelationLedger.append left.ledger right.ledger :=
  rfl

/-- The formal-sum projection of left-distributed candidate composition. -/
theorem TraceCorQQuotientCandidate.add_comp_formalSum
    (left right tail : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.add left right)
      tail).formalSum =
      TraceCorQFormalSum.add
        (TraceCorQQuotientCandidate.comp left tail).formalSum
        (TraceCorQQuotientCandidate.comp right tail).formalSum :=
  TraceCorQFormalSum.add_comp
    left.formalSum
    right.formalSum
    tail.formalSum

/-- The formal-sum projection of right-distributed candidate composition. -/
theorem TraceCorQQuotientCandidate.comp_add_formalSum_perm
    (left right tail : TraceCorQQuotientCandidate) :
    List.Perm
      (TraceCorQQuotientCandidate.comp
        left
        (TraceCorQQuotientCandidate.add right tail)).formalSum
      (TraceCorQFormalSum.add
        (TraceCorQQuotientCandidate.comp left right).formalSum
        (TraceCorQQuotientCandidate.comp left tail).formalSum) :=
  TraceCorQFormalSum.comp_add_perm
    left.formalSum
    right.formalSum
    tail.formalSum

/-- The formal-sum projection of scalar compatibility on the left of composition. -/
theorem TraceCorQQuotientCandidate.smul_comp_formalSum
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.smul coefficient left)
      right).formalSum =
      (TraceCorQQuotientCandidate.smul
        coefficient
        (TraceCorQQuotientCandidate.comp left right)).formalSum :=
  TraceCorQQuotientInput.smul_comp_formalSum
    coefficient
    left.input
    right.input

/-- The formal-sum projection of scalar compatibility on the right of composition. -/
theorem TraceCorQQuotientCandidate.comp_smul_formalSum
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      left
      (TraceCorQQuotientCandidate.smul coefficient right)).formalSum =
      (TraceCorQQuotientCandidate.smul
        coefficient
        (TraceCorQQuotientCandidate.comp left right)).formalSum :=
  TraceCorQQuotientInput.comp_smul_formalSum
    coefficient
    left.input
    right.input

/-- Scaling the empty candidate gives the empty candidate. -/
theorem TraceCorQQuotientCandidate.smul_empty
    (coefficient : Rat) :
    TraceCorQQuotientCandidate.smul
      coefficient
      TraceCorQQuotientCandidate.empty =
      TraceCorQQuotientCandidate.empty :=
  TraceCorQQuotientInput.smul_empty coefficient

/-- Scaling distributes over quotient-candidate addition. -/
theorem TraceCorQQuotientCandidate.smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.smul
      coefficient
      (TraceCorQQuotientCandidate.add left right) =
      TraceCorQQuotientCandidate.add
        (TraceCorQQuotientCandidate.smul coefficient left)
        (TraceCorQQuotientCandidate.smul coefficient right) :=
  TraceCorQQuotientInput.smul_add
    coefficient
    left.input
    right.input

/-- Scaling a candidate by one leaves it unchanged. -/
theorem TraceCorQQuotientCandidate.one_smul
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.smul 1 candidate =
      candidate :=
  TraceCorQQuotientInput.one_smul candidate.input

/-- Successive scalar multiplications of candidates compose by multiplying scalars. -/
theorem TraceCorQQuotientCandidate.smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.smul
      leftCoefficient
      (TraceCorQQuotientCandidate.smul rightCoefficient candidate) =
      TraceCorQQuotientCandidate.smul
        (leftCoefficient * rightCoefficient)
        candidate :=
  TraceCorQQuotientInput.smul_smul
    leftCoefficient
    rightCoefficient
    candidate.input

/-- Adding the empty candidate on the left leaves a candidate unchanged. -/
theorem TraceCorQQuotientCandidate.empty_add
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.add
      TraceCorQQuotientCandidate.empty
      candidate =
      candidate :=
  rfl

/-- Adding the empty candidate on the right leaves a candidate unchanged. -/
theorem TraceCorQQuotientCandidate.add_empty
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.add
      candidate
      TraceCorQQuotientCandidate.empty =
      candidate :=
  TraceCorQQuotientInput.add_empty candidate.input

/-- Addition of quotient candidates is associative. -/
theorem TraceCorQQuotientCandidate.add_assoc
    (first second third : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.add
      (TraceCorQQuotientCandidate.add first second)
      third =
      TraceCorQQuotientCandidate.add
        first
        (TraceCorQQuotientCandidate.add second third) :=
  TraceCorQQuotientInput.add_assoc
    first.input
    second.input
    third.input

end AnalyticMotives
end LFunctions
end Boundary

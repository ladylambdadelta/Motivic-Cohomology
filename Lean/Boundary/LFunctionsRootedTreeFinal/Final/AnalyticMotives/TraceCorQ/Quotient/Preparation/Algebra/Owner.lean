import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Algebraic laws for quotient inputs

This file owns the algebraic compatibility laws for the pre-quotient input
package: distributivity, scalar compatibility, unit laws, and associativity.
The base preparation owner keeps the input package and payload accounting.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- Scaling the left side of quotient-input composition gives the scaled composed input. -/
theorem TraceCorQQuotientInput.smul_comp
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.smul coefficient left)
      right =
      TraceCorQQuotientInput.smul
        coefficient
        (TraceCorQQuotientInput.comp left right) :=
  Prod.ext
    (TraceCorQFormalSum.smul_comp
      coefficient
      left.formalSum
      right.formalSum)
    rfl

/-- Scaling the left side of quotient-input composition preserves rewrite-step payload. -/
theorem TraceCorQQuotientInput.smul_comp_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      (TraceCorQQuotientInput.smul coefficient left)
      right).rewriteStepCount =
      (TraceCorQQuotientInput.comp left right).rewriteStepCount :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.rewriteStepCount
      (TraceCorQQuotientInput.smul_comp coefficient left right))
    (TraceCorQQuotientInput.smul_rewriteStepCount
      coefficient
      (TraceCorQQuotientInput.comp left right))

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

/-- Scaling the right side of quotient-input composition gives the scaled composed input. -/
theorem TraceCorQQuotientInput.comp_smul
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    TraceCorQQuotientInput.comp
      left
      (TraceCorQQuotientInput.smul coefficient right) =
      TraceCorQQuotientInput.smul
        coefficient
        (TraceCorQQuotientInput.comp left right) :=
  Prod.ext
    (TraceCorQFormalSum.comp_smul
      coefficient
      left.formalSum
      right.formalSum)
    rfl

/-- Scaling the right side of quotient-input composition preserves rewrite-step payload. -/
theorem TraceCorQQuotientInput.comp_smul_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientInput) :
    (TraceCorQQuotientInput.comp
      left
      (TraceCorQQuotientInput.smul coefficient right)).rewriteStepCount =
      (TraceCorQQuotientInput.comp left right).rewriteStepCount :=
  Eq.trans
    (congrArg
      TraceCorQQuotientInput.rewriteStepCount
      (TraceCorQQuotientInput.comp_smul coefficient left right))
    (TraceCorQQuotientInput.smul_rewriteStepCount
      coefficient
      (TraceCorQQuotientInput.comp left right))

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

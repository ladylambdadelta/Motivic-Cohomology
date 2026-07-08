import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Smul.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Comp.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Candidates.Public.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Owner

/-!
# Quotient candidate laws for Q-linear trace correspondences

This file owns composition, scalar, and additive laws for raw quotient
candidate representatives.  Basic projection and payload facts live in the
`Projections` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- Scaling the left side of candidate composition gives the scaled composed candidate. -/
theorem TraceCorQQuotientCandidate.smul_comp
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.smul coefficient left)
      right =
      TraceCorQQuotientCandidate.smul
        coefficient
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotientInput.smul_comp
    coefficient
    left.input
    right.input

/-- Scaling the left side of candidate composition preserves rewrite-step payload. -/
theorem TraceCorQQuotientCandidate.smul_comp_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.smul coefficient left)
      right).rewriteStepCount =
      (TraceCorQQuotientCandidate.comp left right).rewriteStepCount :=
  TraceCorQQuotientInput.smul_comp_rewriteStepCount
    coefficient
    left.input
    right.input

/-- Scaling the left side of candidate composition preserves imported payload. -/
theorem TraceCorQQuotientCandidate.smul_comp_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.smul coefficient left)
      right).importedRectangleCount =
      (TraceCorQQuotientCandidate.comp left right).importedRectangleCount :=
  TraceCorQQuotientInput.smul_comp_importedRectangleCount
    coefficient
    left.input
    right.input

/-- Scaling the left side of candidate composition preserves imported rectangles. -/
theorem TraceCorQQuotientCandidate.smul_comp_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      (TraceCorQQuotientCandidate.smul coefficient left)
      right).importedRectangles =
      (TraceCorQQuotientCandidate.comp left right).importedRectangles :=
  TraceCorQQuotientInput.smul_comp_importedRectangles
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

/-- Scaling the right side of candidate composition gives the scaled composed candidate. -/
theorem TraceCorQQuotientCandidate.comp_smul
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate.comp
      left
      (TraceCorQQuotientCandidate.smul coefficient right) =
      TraceCorQQuotientCandidate.smul
        coefficient
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotientInput.comp_smul
    coefficient
    left.input
    right.input

/-- Scaling the right side of candidate composition preserves rewrite-step payload. -/
theorem TraceCorQQuotientCandidate.comp_smul_rewriteStepCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      left
      (TraceCorQQuotientCandidate.smul coefficient right)).rewriteStepCount =
      (TraceCorQQuotientCandidate.comp left right).rewriteStepCount :=
  TraceCorQQuotientInput.comp_smul_rewriteStepCount
    coefficient
    left.input
    right.input

/-- Scaling the right side of candidate composition preserves imported payload. -/
theorem TraceCorQQuotientCandidate.comp_smul_importedRectangleCount
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      left
      (TraceCorQQuotientCandidate.smul coefficient right)).importedRectangleCount =
      (TraceCorQQuotientCandidate.comp left right).importedRectangleCount :=
  TraceCorQQuotientInput.comp_smul_importedRectangleCount
    coefficient
    left.input
    right.input

/-- Scaling the right side of candidate composition preserves imported rectangles. -/
theorem TraceCorQQuotientCandidate.comp_smul_importedRectangles
    (coefficient : Rat)
    (left right : TraceCorQQuotientCandidate) :
    (TraceCorQQuotientCandidate.comp
      left
      (TraceCorQQuotientCandidate.smul coefficient right)).importedRectangles =
      (TraceCorQQuotientCandidate.comp left right).importedRectangles :=
  TraceCorQQuotientInput.comp_smul_importedRectangles
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

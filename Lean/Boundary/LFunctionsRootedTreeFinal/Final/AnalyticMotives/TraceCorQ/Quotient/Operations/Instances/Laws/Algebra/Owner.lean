import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Instances.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Rearrangement.Owner

/-!
# Standard-notation algebra laws for quotient trace correspondences

This file restates the proved concrete quotient laws using the standard
operation notation introduced by the operation instances.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Zero is a left identity for standard quotient addition. -/
theorem TraceCorQQuotient.std_zero_add
    (candidateClass : TraceCorQQuotient) :
    (0 : TraceCorQQuotient) + candidateClass =
      candidateClass :=
  TraceCorQQuotient.zero_add candidateClass

/-- Zero is a right identity for standard quotient addition. -/
theorem TraceCorQQuotient.std_add_zero
    (candidateClass : TraceCorQQuotient) :
    candidateClass + (0 : TraceCorQQuotient) =
      candidateClass :=
  TraceCorQQuotient.add_zero candidateClass

/-- Standard quotient addition is associative. -/
theorem TraceCorQQuotient.std_add_assoc
    (first second third : TraceCorQQuotient) :
    (first + second) + third =
      first + (second + third) :=
  TraceCorQQuotient.add_assoc first second third

/-- Standard quotient addition is commutative. -/
theorem TraceCorQQuotient.std_add_comm
    (left right : TraceCorQQuotient) :
    left + right =
      right + left :=
  TraceCorQQuotient.add_comm left right

/-- Standard quotient negation sends zero to zero. -/
theorem TraceCorQQuotient.std_neg_zero :
    -(0 : TraceCorQQuotient) =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.neg_zero

/-- Standard quotient negation is involutive. -/
theorem TraceCorQQuotient.std_neg_neg
    (candidateClass : TraceCorQQuotient) :
    -(-candidateClass) =
      candidateClass :=
  TraceCorQQuotient.neg_neg candidateClass

/-- Standard quotient negation distributes over standard addition. -/
theorem TraceCorQQuotient.std_neg_add
    (left right : TraceCorQQuotient) :
    -(left + right) =
      -left + -right :=
  TraceCorQQuotient.neg_add left right

/-- Standard quotient negation gives a left additive inverse. -/
theorem TraceCorQQuotient.std_neg_add_self
    (candidateClass : TraceCorQQuotient) :
    -candidateClass + candidateClass =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.neg_add_self candidateClass

/-- Standard quotient negation gives a right additive inverse. -/
theorem TraceCorQQuotient.std_add_neg_self
    (candidateClass : TraceCorQQuotient) :
    candidateClass + -candidateClass =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.add_neg_self candidateClass

/-- Standard quotient addition cancels a common left summand. -/
theorem TraceCorQQuotient.std_add_left_cancel
    (left right tail : TraceCorQQuotient)
    (left_right_eq_left_tail : left + right = left + tail) :
    right = tail :=
  TraceCorQQuotient.add_left_cancel
    left
    right
    tail
    left_right_eq_left_tail

/-- Standard quotient addition cancels a common right summand. -/
theorem TraceCorQQuotient.std_add_right_cancel
    (left right tail : TraceCorQQuotient)
    (left_tail_eq_right_tail : left + tail = right + tail) :
    left = right :=
  TraceCorQQuotient.add_right_cancel
    left
    right
    tail
    left_tail_eq_right_tail

/-- Standard quotient subtraction unfolds to addition of the negative. -/
theorem TraceCorQQuotient.std_sub_eq_add_neg
    (left right : TraceCorQQuotient) :
    left - right =
      left + -right :=
  TraceCorQQuotient.sub_eq_add_neg left right

/-- Standard quotient self-subtraction is zero. -/
theorem TraceCorQQuotient.std_sub_self
    (candidateClass : TraceCorQQuotient) :
    candidateClass - candidateClass =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.sub_self candidateClass

/-- Equal standard quotient classes have zero subtraction. -/
theorem TraceCorQQuotient.std_sub_eq_zero_of_eq
    (left right : TraceCorQQuotient)
    (left_eq_right : left = right) :
    left - right =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.sub_eq_zero_of_eq
    left
    right
    left_eq_right

/-- Zero standard quotient subtraction detects equality. -/
theorem TraceCorQQuotient.std_eq_of_sub_eq_zero
    (left right : TraceCorQQuotient)
    (left_sub_right_eq_zero :
      left - right =
        (0 : TraceCorQQuotient)) :
    left = right :=
  TraceCorQQuotient.eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Move a right summand across a standard quotient equality. -/
theorem TraceCorQQuotient.std_left_eq_sub_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_add_right_eq_tail : left + right = tail) :
    left = tail - right :=
  TraceCorQQuotient.left_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- Move a left summand across a standard quotient equality. -/
theorem TraceCorQQuotient.std_right_eq_sub_of_add_eq
    (left right tail : TraceCorQQuotient)
    (left_add_right_eq_tail : left + right = tail) :
    right = tail - left :=
  TraceCorQQuotient.right_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- Rebuild a standard quotient sum from a left-subtraction solution. -/
theorem TraceCorQQuotient.std_add_eq_of_left_eq_sub
    (left right tail : TraceCorQQuotient)
    (left_eq_tail_sub_right : left = tail - right) :
    left + right = tail :=
  TraceCorQQuotient.add_eq_of_left_eq_sub
    left
    right
    tail
    left_eq_tail_sub_right

/-- Rebuild a standard quotient sum from a right-subtraction solution. -/
theorem TraceCorQQuotient.std_add_eq_of_right_eq_sub
    (left right tail : TraceCorQQuotient)
    (right_eq_tail_sub_left : right = tail - left) :
    left + right = tail :=
  TraceCorQQuotient.add_eq_of_right_eq_sub
    left
    right
    tail
    right_eq_tail_sub_left

/-- Standard quotient addition distributes over subtraction on the right. -/
theorem TraceCorQQuotient.std_add_sub
    (left right tail : TraceCorQQuotient) :
    left + (right - tail) =
      left + right - tail :=
  TraceCorQQuotient.add_sub_reassociate left right tail

/-- Standard quotient subtraction distributes over addition on the right. -/
theorem TraceCorQQuotient.std_sub_add
    (left right tail : TraceCorQQuotient) :
    left - right + tail =
      left + tail - right :=
  TraceCorQQuotient.sub_add_reassociate left right tail

/-- Standard quotient subtraction associates over a second subtraction. -/
theorem TraceCorQQuotient.std_sub_sub
    (left right tail : TraceCorQQuotient) :
    left - right - tail =
      left - (right + tail) :=
  TraceCorQQuotient.sub_sub_reassociate left right tail

/-- Standard quotient subtraction cancels a common right-hand subtrahend. -/
theorem TraceCorQQuotient.std_sub_right_cancel
    (left right tail : TraceCorQQuotient)
    (left_sub_tail_eq_right_sub_tail :
      left - tail = right - tail) :
    left = right :=
  TraceCorQQuotient.sub_right_cancel
    left
    right
    tail
    left_sub_tail_eq_right_sub_tail

/-- Standard quotient subtraction cancels a common left-hand minuend. -/
theorem TraceCorQQuotient.std_sub_left_cancel
    (left right tail : TraceCorQQuotient)
    (left_sub_right_eq_left_sub_tail :
      left - right = left - tail) :
    right = tail :=
  TraceCorQQuotient.sub_left_cancel
    left
    right
    tail
    left_sub_right_eq_left_sub_tail

/-- Standard scalar multiplication sends zero to zero. -/
theorem TraceCorQQuotient.std_smul_zero
    (coefficient : Rat) :
    coefficient • (0 : TraceCorQQuotient) =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.smul_zero coefficient

/-- Standard scalar multiplication by zero gives zero. -/
theorem TraceCorQQuotient.std_zero_smul
    (candidateClass : TraceCorQQuotient) :
    (0 : Rat) • candidateClass =
      (0 : TraceCorQQuotient) :=
  TraceCorQQuotient.zero_smul candidateClass

/-- Standard scalar multiplication by one is the identity. -/
theorem TraceCorQQuotient.std_one_smul
    (candidateClass : TraceCorQQuotient) :
    (1 : Rat) • candidateClass =
      candidateClass :=
  TraceCorQQuotient.one_smul candidateClass

/-- Standard scalar multiplication distributes over standard quotient addition. -/
theorem TraceCorQQuotient.std_smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    coefficient • (left + right) =
      coefficient • left + coefficient • right :=
  TraceCorQQuotient.smul_add coefficient left right

/-- Standard scalar multiplication commutes with standard quotient negation. -/
theorem TraceCorQQuotient.std_smul_neg
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    coefficient • (-candidateClass) =
      -(coefficient • candidateClass) :=
  TraceCorQQuotient.smul_neg coefficient candidateClass

/-- Standard scalar multiplication distributes over standard quotient subtraction. -/
theorem TraceCorQQuotient.std_smul_sub
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    coefficient • (left - right) =
      coefficient • left - coefficient • right :=
  TraceCorQQuotient.smul_sub coefficient left right

/-- Standard scalar multiplication is additive in the scalar coefficient. -/
theorem TraceCorQQuotient.std_add_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    (leftCoefficient + rightCoefficient) • candidateClass =
      leftCoefficient • candidateClass +
        rightCoefficient • candidateClass :=
  TraceCorQQuotient.add_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- Standard scalar multiplication respects negation in the scalar coefficient. -/
theorem TraceCorQQuotient.std_neg_smul
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    (-coefficient) • candidateClass =
      -(coefficient • candidateClass) :=
  TraceCorQQuotient.neg_smul coefficient candidateClass

/-- Standard scalar multiplication is subtractive in the scalar coefficient. -/
theorem TraceCorQQuotient.std_sub_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    (leftCoefficient - rightCoefficient) • candidateClass =
      leftCoefficient • candidateClass -
        rightCoefficient • candidateClass :=
  TraceCorQQuotient.sub_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- Standard successive scalar multiplications compose by multiplying scalars. -/
theorem TraceCorQQuotient.std_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    leftCoefficient • (rightCoefficient • candidateClass) =
      (leftCoefficient * rightCoefficient) • candidateClass :=
  TraceCorQQuotient.smul_smul
    leftCoefficient
    rightCoefficient
    candidateClass

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Rearrangement.Owner

/-!
# Standard-notation algebra laws for typed trace-correspondence homs

This file restates the proved concrete typed hom laws using the standard
operation notation introduced by the operation instances.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Zero is a left identity for standard typed hom addition. -/
theorem TraceCorQHom.std_zero_add
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (0 : TraceCorQHom source target) + hom =
      hom :=
  TraceCorQHom.zero_add hom

/-- Zero is a right identity for standard typed hom addition. -/
theorem TraceCorQHom.std_add_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom + (0 : TraceCorQHom source target) =
      hom :=
  TraceCorQHom.add_zero hom

/-- Standard typed hom addition is associative. -/
theorem TraceCorQHom.std_add_assoc
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    (first + second) + third =
      first + (second + third) :=
  TraceCorQHom.add_assoc first second third

/-- Standard typed hom addition is commutative. -/
theorem TraceCorQHom.std_add_comm
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left + right =
      right + left :=
  TraceCorQHom.add_comm left right

/-- Standard typed hom negation sends zero to zero. -/
theorem TraceCorQHom.std_neg_zero
    (source target : TraceCorQObject) :
    -(0 : TraceCorQHom source target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.neg_zero source target

/-- Standard typed hom negation is involutive. -/
theorem TraceCorQHom.std_neg_neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    -(-hom) =
      hom :=
  TraceCorQHom.neg_neg hom

/-- Standard typed hom negation distributes over standard addition. -/
theorem TraceCorQHom.std_neg_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    -(left + right) =
      -left + -right :=
  TraceCorQHom.neg_add left right

/-- Standard typed hom negation gives a left additive inverse. -/
theorem TraceCorQHom.std_neg_add_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    -hom + hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.neg_add_self hom

/-- Standard typed hom negation gives a right additive inverse. -/
theorem TraceCorQHom.std_add_neg_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom + -hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.add_neg_self hom

/-- Standard typed hom addition cancels a common left summand. -/
theorem TraceCorQHom.std_add_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_right_eq_left_tail : left + right = left + tail) :
    right = tail :=
  TraceCorQHom.add_left_cancel
    left
    right
    tail
    left_right_eq_left_tail

/-- Standard typed hom addition cancels a common right summand. -/
theorem TraceCorQHom.std_add_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_tail_eq_right_tail : left + tail = right + tail) :
    left = right :=
  TraceCorQHom.add_right_cancel
    left
    right
    tail
    left_tail_eq_right_tail

/-- Standard typed hom subtraction unfolds to addition of the negative. -/
theorem TraceCorQHom.std_sub_eq_add_neg
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left - right =
      left + -right :=
  TraceCorQHom.sub_eq_add_neg left right

/-- Standard typed hom self-subtraction is zero. -/
theorem TraceCorQHom.std_sub_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom - hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.sub_self hom

/-- Equal standard typed homs have zero subtraction. -/
theorem TraceCorQHom.std_sub_eq_zero_of_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_eq_right : left = right) :
    left - right =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.sub_eq_zero_of_eq
    left
    right
    left_eq_right

/-- Zero standard typed hom subtraction detects equality. -/
theorem TraceCorQHom.std_eq_of_sub_eq_zero
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_sub_right_eq_zero :
      left - right =
        (0 : TraceCorQHom source target)) :
    left = right :=
  TraceCorQHom.eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- Move a right summand across a standard typed hom equality. -/
theorem TraceCorQHom.std_left_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail : left + right = tail) :
    left = tail - right :=
  TraceCorQHom.left_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- Move a left summand across a standard typed hom equality. -/
theorem TraceCorQHom.std_right_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail : left + right = tail) :
    right = tail - left :=
  TraceCorQHom.right_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- Rebuild a standard typed hom sum from a left-subtraction solution. -/
theorem TraceCorQHom.std_add_eq_of_left_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_sub_right : left = tail - right) :
    left + right = tail :=
  TraceCorQHom.add_eq_of_left_eq_sub
    left
    right
    tail
    left_eq_tail_sub_right

/-- Rebuild a standard typed hom sum from a right-subtraction solution. -/
theorem TraceCorQHom.std_add_eq_of_right_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (right_eq_tail_sub_left : right = tail - left) :
    left + right = tail :=
  TraceCorQHom.add_eq_of_right_eq_sub
    left
    right
    tail
    right_eq_tail_sub_left

/-- Standard typed hom addition distributes over subtraction on the right. -/
theorem TraceCorQHom.std_add_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left + (right - tail) =
      left + right - tail :=
  TraceCorQHom.add_sub_reassociate left right tail

/-- Standard typed hom subtraction distributes over addition on the right. -/
theorem TraceCorQHom.std_sub_add
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left - right + tail =
      left + tail - right :=
  TraceCorQHom.sub_add_reassociate left right tail

/-- Standard typed hom subtraction associates over a second subtraction. -/
theorem TraceCorQHom.std_sub_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left - right - tail =
      left - (right + tail) :=
  TraceCorQHom.sub_sub_reassociate left right tail

/-- Standard typed hom subtraction cancels a common right-hand subtrahend. -/
theorem TraceCorQHom.std_sub_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_tail_eq_right_sub_tail :
      left - tail = right - tail) :
    left = right :=
  TraceCorQHom.sub_right_cancel
    left
    right
    tail
    left_sub_tail_eq_right_sub_tail

/-- Standard typed hom subtraction cancels a common left-hand minuend. -/
theorem TraceCorQHom.std_sub_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_right_eq_left_sub_tail :
      left - right = left - tail) :
    right = tail :=
  TraceCorQHom.sub_left_cancel
    left
    right
    tail
    left_sub_right_eq_left_sub_tail

/-- Standard scalar multiplication sends zero to zero. -/
theorem TraceCorQHom.std_smul_zero
    (source target : TraceCorQObject)
    (coefficient : Rat) :
    coefficient • (0 : TraceCorQHom source target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.smul_zero source target coefficient

/-- Standard scalar multiplication by zero gives zero. -/
theorem TraceCorQHom.std_zero_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (0 : Rat) • hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.zero_smul hom

/-- Standard scalar multiplication by one is the identity. -/
theorem TraceCorQHom.std_one_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (1 : Rat) • hom =
      hom :=
  TraceCorQHom.one_smul hom

/-- Standard scalar multiplication distributes over standard typed hom addition. -/
theorem TraceCorQHom.std_smul_add
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    coefficient • (left + right) =
      coefficient • left + coefficient • right :=
  TraceCorQHom.smul_add coefficient left right

/-- Standard scalar multiplication commutes with standard typed hom negation. -/
theorem TraceCorQHom.std_smul_neg
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    coefficient • (-hom) =
      -(coefficient • hom) :=
  TraceCorQHom.smul_neg coefficient hom

/-- Standard scalar multiplication distributes over standard typed hom subtraction. -/
theorem TraceCorQHom.std_smul_sub
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    coefficient • (left - right) =
      coefficient • left - coefficient • right :=
  TraceCorQHom.smul_sub coefficient left right

/-- Standard scalar multiplication is additive in the scalar coefficient. -/
theorem TraceCorQHom.std_add_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    (leftCoefficient + rightCoefficient) • hom =
      leftCoefficient • hom + rightCoefficient • hom :=
  TraceCorQHom.add_smul
    leftCoefficient
    rightCoefficient
    hom

/-- Standard scalar multiplication respects negation in the scalar coefficient. -/
theorem TraceCorQHom.std_neg_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    (-coefficient) • hom =
      -(coefficient • hom) :=
  TraceCorQHom.neg_smul coefficient hom

/-- Standard scalar multiplication is subtractive in the scalar coefficient. -/
theorem TraceCorQHom.std_sub_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    (leftCoefficient - rightCoefficient) • hom =
      leftCoefficient • hom -
        rightCoefficient • hom :=
  TraceCorQHom.sub_smul
    leftCoefficient
    rightCoefficient
    hom

/-- Standard successive scalar multiplications compose by multiplying scalars. -/
theorem TraceCorQHom.std_smul_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    leftCoefficient • (rightCoefficient • hom) =
      (leftCoefficient * rightCoefficient) • hom :=
  TraceCorQHom.smul_smul
    leftCoefficient
    rightCoefficient
    hom

end AnalyticMotives
end LFunctions
end Boundary

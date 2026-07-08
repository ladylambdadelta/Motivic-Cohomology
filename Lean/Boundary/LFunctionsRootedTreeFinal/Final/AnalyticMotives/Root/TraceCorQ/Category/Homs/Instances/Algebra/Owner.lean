import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Instances.Laws.Algebra.Owner

/-!
# Public standard-notation algebra for typed trace homs

This file exposes the fixed-endpoint additive and rational-linear laws for
typed trace-correspondence homs using standard operation notation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes zero as a left identity for standard typed hom addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_zero_add
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (0 : TraceCorQHom source target) + hom =
      hom :=
  TraceCorQHom.std_zero_add hom

/-- The top root exposes zero as a right identity for standard typed hom addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom + (0 : TraceCorQHom source target) =
      hom :=
  TraceCorQHom.std_add_zero hom

/-- The top root exposes associativity for standard typed hom addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_assoc
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    (first + second) + third =
      first + (second + third) :=
  TraceCorQHom.std_add_assoc
    first
    second
    third

/-- The top root exposes commutativity for standard typed hom addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_comm
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left + right =
      right + left :=
  TraceCorQHom.std_add_comm
    left
    right

/-- The top root exposes standard negation of zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_neg_zero
    (source target : TraceCorQObject) :
    -(0 : TraceCorQHom source target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_neg_zero
    source
    target

/-- The top root exposes involutivity of standard typed hom negation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_neg_neg
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    -(-hom) =
      hom :=
  TraceCorQHom.std_neg_neg hom

/-- The top root exposes standard negation over addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_neg_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    -(left + right) =
      -left + -right :=
  TraceCorQHom.std_neg_add
    left
    right

/-- The top root exposes the standard left additive inverse law. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_neg_add_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    -hom + hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_neg_add_self hom

/-- The top root exposes the standard right additive inverse law. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_neg_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom + -hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_add_neg_self hom

/-- The top root exposes standard left-addition cancellation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_right_eq_left_tail : left + right = left + tail) :
    right = tail :=
  TraceCorQHom.std_add_left_cancel
    left
    right
    tail
    left_right_eq_left_tail

/-- The top root exposes standard right-addition cancellation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_tail_eq_right_tail : left + tail = right + tail) :
    left = right :=
  TraceCorQHom.std_add_right_cancel
    left
    right
    tail
    left_tail_eq_right_tail

/-- The top root exposes standard subtraction as addition of the negative. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_eq_add_neg
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    left - right =
      left + -right :=
  TraceCorQHom.std_sub_eq_add_neg
    left
    right

/-- The top root exposes standard self-subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    hom - hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_sub_self hom

/-- The top root exposes that equal homs have zero subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_eq_zero_of_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_eq_right : left = right) :
    left - right =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_sub_eq_zero_of_eq
    left
    right
    left_eq_right

/-- The top root exposes equality detected by zero subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_eq_of_sub_eq_zero
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_sub_right_eq_zero :
      left - right =
        (0 : TraceCorQHom source target)) :
    left = right :=
  TraceCorQHom.std_eq_of_sub_eq_zero
    left
    right
    left_sub_right_eq_zero

/-- The top root exposes moving a right summand across a standard equality. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_left_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail : left + right = tail) :
    left = tail - right :=
  TraceCorQHom.std_left_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- The top root exposes moving a left summand across a standard equality. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_right_eq_sub_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_add_right_eq_tail : left + right = tail) :
    right = tail - left :=
  TraceCorQHom.std_right_eq_sub_of_add_eq
    left
    right
    tail
    left_add_right_eq_tail

/-- The top root exposes rebuilding a sum from a left-subtraction solution. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_eq_of_left_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_sub_right : left = tail - right) :
    left + right = tail :=
  TraceCorQHom.std_add_eq_of_left_eq_sub
    left
    right
    tail
    left_eq_tail_sub_right

/-- The top root exposes rebuilding a sum from a right-subtraction solution. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_eq_of_right_eq_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (right_eq_tail_sub_left : right = tail - left) :
    left + right = tail :=
  TraceCorQHom.std_add_eq_of_right_eq_sub
    left
    right
    tail
    right_eq_tail_sub_left

/-- The top root exposes standard addition-subtraction reassociation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left + (right - tail) =
      left + right - tail :=
  TraceCorQHom.std_add_sub
    left
    right
    tail

/-- The top root exposes standard subtraction-addition reassociation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_add
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left - right + tail =
      left + tail - right :=
  TraceCorQHom.std_sub_add
    left
    right
    tail

/-- The top root exposes standard double-subtraction reassociation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_sub
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    left - right - tail =
      left - (right + tail) :=
  TraceCorQHom.std_sub_sub
    left
    right
    tail

/-- The top root exposes cancellation of a common right-hand subtrahend. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_right_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_tail_eq_right_sub_tail :
      left - tail = right - tail) :
    left = right :=
  TraceCorQHom.std_sub_right_cancel
    left
    right
    tail
    left_sub_tail_eq_right_sub_tail

/-- The top root exposes cancellation of a common left-hand minuend. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_left_cancel
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_sub_right_eq_left_sub_tail :
      left - right = left - tail) :
    right = tail :=
  TraceCorQHom.std_sub_left_cancel
    left
    right
    tail
    left_sub_right_eq_left_sub_tail

/-- The top root exposes standard scalar multiplication of zero. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_smul_zero
    (source target : TraceCorQObject)
    (coefficient : Rat) :
    coefficient • (0 : TraceCorQHom source target) =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_smul_zero
    source
    target
    coefficient

/-- The top root exposes standard zero scalar multiplication. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_zero_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (0 : Rat) • hom =
      (0 : TraceCorQHom source target) :=
  TraceCorQHom.std_zero_smul hom

/-- The top root exposes standard one scalar multiplication. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_one_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    (1 : Rat) • hom =
      hom :=
  TraceCorQHom.std_one_smul hom

/-- The top root exposes standard scalar multiplication over addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_smul_add
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    coefficient • (left + right) =
      coefficient • left + coefficient • right :=
  TraceCorQHom.std_smul_add
    coefficient
    left
    right

/-- The top root exposes standard scalar multiplication over negation. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_smul_neg
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    coefficient • (-hom) =
      -(coefficient • hom) :=
  TraceCorQHom.std_smul_neg
    coefficient
    hom

/-- The top root exposes standard scalar multiplication over subtraction. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_smul_sub
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    coefficient • (left - right) =
      coefficient • left - coefficient • right :=
  TraceCorQHom.std_smul_sub
    coefficient
    left
    right

/-- The top root exposes additivity in the scalar coefficient. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_add_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    (leftCoefficient + rightCoefficient) • hom =
      leftCoefficient • hom + rightCoefficient • hom :=
  TraceCorQHom.std_add_smul
    leftCoefficient
    rightCoefficient
    hom

/-- The top root exposes negation in the scalar coefficient. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_neg_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    (-coefficient) • hom =
      -(coefficient • hom) :=
  TraceCorQHom.std_neg_smul
    coefficient
    hom

/-- The top root exposes subtraction in the scalar coefficient. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_sub_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    (leftCoefficient - rightCoefficient) • hom =
      leftCoefficient • hom -
        rightCoefficient • hom :=
  TraceCorQHom.std_sub_smul
    leftCoefficient
    rightCoefficient
    hom

/-- The top root exposes composition of successive scalar multiplications. -/
theorem AnalyticMotivesRoot.traceCorQHom_std_smul_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    leftCoefficient • (rightCoefficient • hom) =
      (leftCoefficient * rightCoefficient) • hom :=
  TraceCorQHom.std_smul_smul
    leftCoefficient
    rightCoefficient
    hom

end AnalyticMotives
end LFunctions
end Boundary

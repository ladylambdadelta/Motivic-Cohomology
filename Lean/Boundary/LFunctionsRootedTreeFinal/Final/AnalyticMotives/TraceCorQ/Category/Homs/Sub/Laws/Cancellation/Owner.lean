import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Owner

/-!
# Cancellation laws for typed hom subtraction

This file collects derived typed hom subtraction cancellation and solver laws.
The primitive inverse and cancellation facts live in `Sub.Laws.Owner`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- If a typed hom is a sum, subtracting the left summand leaves the right summand. -/
theorem TraceCorQHom.sub_left_summand_eq_right
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_right_add_tail :
      left = TraceCorQHom.add right tail) :
    TraceCorQHom.sub left right = tail :=
  Eq.symm
    (TraceCorQHom.right_eq_sub_of_add_eq
      right
      tail
      left
      (Eq.symm left_eq_right_add_tail))

/-- If a typed hom is a sum, subtracting the right summand leaves the left summand. -/
theorem TraceCorQHom.sub_right_summand_eq_left
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_right_add_tail :
      left = TraceCorQHom.add right tail) :
    TraceCorQHom.sub left tail = right :=
  Eq.symm
    (TraceCorQHom.left_eq_sub_of_add_eq
      right
      tail
      left
      (Eq.symm left_eq_right_add_tail))

/-- A typed hom subtraction equality follows from equality after adding the subtrahend. -/
theorem TraceCorQHom.sub_eq_of_add_eq
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target)
    (left_eq_tail_add_right :
      left = TraceCorQHom.add tail right) :
    TraceCorQHom.sub left right = tail :=
  TraceCorQHom.sub_right_summand_eq_left
    left
    tail
    right
    left_eq_tail_add_right

end AnalyticMotives
end LFunctions
end Boundary

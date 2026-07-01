import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner

/-!
# Rearrangement laws for quotient subtraction

This file collects higher-level quotient subtraction rearrangements that are
derived from the basic additive inverse and subtraction laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociate a quotient sum whose left summand is a subtraction. -/
theorem TraceCorQQuotient.sub_add_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.add left tail)
        right :=
  Eq.trans
    (congrArg
      (fun leftMinusRight =>
        TraceCorQQuotient.add leftMinusRight tail)
      (TraceCorQQuotient.sub_eq_add_neg left right))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add left (TraceCorQQuotient.neg right)))
        (Eq.symm (TraceCorQQuotient.add_zero tail)))
      (Eq.trans
        (TraceCorQQuotient.add_add_add_comm
          left
          (TraceCorQQuotient.neg right)
          tail
          TraceCorQQuotient.zero)
        (Eq.trans
          (congrArg
            (TraceCorQQuotient.add (TraceCorQQuotient.add left tail))
            (TraceCorQQuotient.add_zero (TraceCorQQuotient.neg right)))
        (Eq.symm
          (TraceCorQQuotient.sub_eq_add_neg
            (TraceCorQQuotient.add left tail)
            right)))))

/-- Reassociate a quotient sum whose right summand is a subtraction. -/
theorem TraceCorQQuotient.add_sub_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.add
      left
      (TraceCorQQuotient.sub right tail) =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.add left right)
        tail :=
  Eq.trans
    (TraceCorQQuotient.add_comm left (TraceCorQQuotient.sub right tail))
    (Eq.trans
      (TraceCorQQuotient.sub_add_reassociate right tail left)
      (congrArg
        (fun leftRight =>
          TraceCorQQuotient.sub leftRight tail)
        (TraceCorQQuotient.add_comm right left)))

/-- Reassociate quotient subtraction of a sum as iterated subtraction. -/
theorem TraceCorQQuotient.sub_sum_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add left tail)
      right =
      TraceCorQQuotient.add
        (TraceCorQQuotient.sub left right)
        tail :=
  Eq.symm
    (TraceCorQQuotient.sub_add_reassociate left right tail)

/-- Reassociate iterated quotient subtraction as subtraction by a sum. -/
theorem TraceCorQQuotient.sub_sub_reassociate
    (left right tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.sub left right)
      tail =
      TraceCorQQuotient.sub
        left
        (TraceCorQQuotient.add right tail) :=
  Eq.symm
    (TraceCorQQuotient.sub_add left right tail)

end AnalyticMotives
end LFunctions
end Boundary

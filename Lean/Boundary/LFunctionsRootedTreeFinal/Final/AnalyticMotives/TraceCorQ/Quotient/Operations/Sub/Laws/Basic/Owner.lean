import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Owner

/-!
# Basic subtraction laws for quotient trace correspondences

This file owns the primitive zero, self, and equality-detection laws for
quotient subtraction, proved directly from `left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtracting zero on the right leaves a quotient class unchanged. -/
theorem TraceCorQQuotient.sub_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass TraceCorQQuotient.zero =
      candidateClass :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      candidateClass
      TraceCorQQuotient.zero)
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add candidateClass)
        TraceCorQQuotient.neg_zero)
      (TraceCorQQuotient.add_zero candidateClass))

/-- Zero minus a quotient class is its negative. -/
theorem TraceCorQQuotient.zero_sub
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub TraceCorQQuotient.zero candidateClass =
      TraceCorQQuotient.neg candidateClass :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      TraceCorQQuotient.zero
      candidateClass)
    (TraceCorQQuotient.zero_add
      (TraceCorQQuotient.neg candidateClass))

/-- A quotient class minus itself is zero. -/
theorem TraceCorQQuotient.sub_self
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.sub candidateClass candidateClass =
      TraceCorQQuotient.zero :=
  Eq.trans
    (TraceCorQQuotient.sub_eq_add_neg
      candidateClass
      candidateClass)
    (TraceCorQQuotient.add_neg_self candidateClass)

/-- Equal quotient classes have zero subtraction. -/
theorem TraceCorQQuotient.sub_eq_zero_of_eq
    (left right : TraceCorQQuotient)
    (left_eq_right : left = right) :
    TraceCorQQuotient.sub left right =
      TraceCorQQuotient.zero :=
  Eq.trans
    (congrArg
      (fun leftClass =>
        TraceCorQQuotient.sub leftClass right)
      left_eq_right)
    (TraceCorQQuotient.sub_self right)

/-- Zero subtraction detects equality of quotient classes. -/
theorem TraceCorQQuotient.eq_of_sub_eq_zero
    (left right : TraceCorQQuotient)
    (left_sub_right_eq_zero :
      TraceCorQQuotient.sub left right =
        TraceCorQQuotient.zero) :
    left = right :=
  Eq.trans
    (Eq.symm (TraceCorQQuotient.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQQuotient.add left)
        (Eq.symm (TraceCorQQuotient.neg_add_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQQuotient.add_assoc
            left
            (TraceCorQQuotient.neg right)
            right))
        (Eq.trans
          (congrArg
            (fun leftMinusRight =>
              TraceCorQQuotient.add leftMinusRight right)
            (Eq.trans
              (Eq.symm
                (TraceCorQQuotient.sub_eq_add_neg left right))
              left_sub_right_eq_zero))
          (TraceCorQQuotient.zero_add right))))

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Rearrangement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Full.Owner

/-!
# Subtraction distribution normal forms for quotient trace correspondences

This file owns longer-sum subtraction normalizers.  Subtraction from a sum is
normalized by pushing the subtraction to the final summand and right-associating
the additive spine.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Push subtraction from a left-associated three-summand quotient sum to the final summand. -/
theorem TraceCorQQuotient.add_add_sub
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.sub third tail)) :=
  Eq.trans
    (TraceCorQQuotient.add_sub
      (TraceCorQQuotient.add first second)
      third
      tail)
    (TraceCorQQuotient.add_assoc
      first
      second
      (TraceCorQQuotient.sub third tail))

/-- Push subtraction from a right-associated three-summand quotient sum to the final summand. -/
theorem TraceCorQQuotient.add_add_sub_right
    (first second third tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third))
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.sub third tail)) :=
  Eq.trans
    (TraceCorQQuotient.add_sub
      first
      (TraceCorQQuotient.add second third)
      tail)
    (congrArg
      (TraceCorQQuotient.add first)
      (TraceCorQQuotient.add_sub second third tail))

/-- Push subtraction from a fully left-associated four-summand quotient sum. -/
theorem TraceCorQQuotient.add_add_add_sub
    (first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add
          (TraceCorQQuotient.add first second)
          third)
        fourth)
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add
            third
            (TraceCorQQuotient.sub fourth tail))) :=
  Eq.trans
    (TraceCorQQuotient.add_sub
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third)
      fourth
      tail)
    (TraceCorQQuotient.add_assoc_four_left
      first
      second
      third
      (TraceCorQQuotient.sub fourth tail))

/-- Push subtraction from a fully right-associated four-summand quotient sum. -/
theorem TraceCorQQuotient.add_add_add_sub_right
    (first second third fourth tail : TraceCorQQuotient) :
    TraceCorQQuotient.sub
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)))
      tail =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add
            third
            (TraceCorQQuotient.sub fourth tail))) :=
  Eq.trans
    (TraceCorQQuotient.add_sub
      first
      (TraceCorQQuotient.add
        second
        (TraceCorQQuotient.add third fourth))
      tail)
    (congrArg
      (TraceCorQQuotient.add first)
      (TraceCorQQuotient.add_add_sub_right second third fourth tail))

end AnalyticMotives
end LFunctions
end Boundary

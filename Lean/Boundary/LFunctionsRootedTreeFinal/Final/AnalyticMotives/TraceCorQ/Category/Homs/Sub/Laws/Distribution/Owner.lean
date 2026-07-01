import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Rearrangement.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Full.Owner

/-!
# Subtraction distribution normal forms for typed trace-correspondence homs

This file owns longer-sum subtraction normalizers for typed homs.  Subtraction
from a sum is normalized by pushing the subtraction to the final summand and
right-associating the additive spine.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Push subtraction from a left-associated three-summand typed hom sum. -/
theorem TraceCorQHom.add_add_sub
    {source target : TraceCorQObject}
    (first second third tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      tail =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.sub third tail)) :=
  Eq.trans
    (TraceCorQHom.add_sub
      (TraceCorQHom.add first second)
      third
      tail)
    (TraceCorQHom.add_assoc
      first
      second
      (TraceCorQHom.sub third tail))

/-- Push subtraction from a right-associated three-summand typed hom sum. -/
theorem TraceCorQHom.add_add_sub_right
    {source target : TraceCorQObject}
    (first second third tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third))
      tail =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.sub third tail)) :=
  Eq.trans
    (TraceCorQHom.add_sub
      first
      (TraceCorQHom.add second third)
      tail)
    (congrArg
      (TraceCorQHom.add first)
      (TraceCorQHom.add_sub second third tail))

/-- Push subtraction from a fully left-associated four-summand typed hom sum. -/
theorem TraceCorQHom.add_add_add_sub
    {source target : TraceCorQObject}
    (first second third fourth tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add
        (TraceCorQHom.add
          (TraceCorQHom.add first second)
          third)
        fourth)
      tail =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add
            third
            (TraceCorQHom.sub fourth tail))) :=
  Eq.trans
    (TraceCorQHom.add_sub
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third)
      fourth
      tail)
    (TraceCorQHom.add_assoc_four_left
      first
      second
      third
      (TraceCorQHom.sub fourth tail))

/-- Push subtraction from a fully right-associated four-summand typed hom sum. -/
theorem TraceCorQHom.add_add_add_sub_right
    {source target : TraceCorQObject}
    (first second third fourth tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add third fourth)))
      tail =
      TraceCorQHom.add
        first
        (TraceCorQHom.add
          second
          (TraceCorQHom.add
            third
            (TraceCorQHom.sub fourth tail))) :=
  Eq.trans
    (TraceCorQHom.add_sub
      first
      (TraceCorQHom.add
        second
        (TraceCorQHom.add third fourth))
      tail)
    (congrArg
      (TraceCorQHom.add first)
      (TraceCorQHom.add_add_sub_right second third fourth tail))

end AnalyticMotives
end LFunctions
end Boundary

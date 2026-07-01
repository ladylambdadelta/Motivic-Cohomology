import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Owner

/-!
# Rearrangement laws for typed hom subtraction

This file collects higher-level typed hom subtraction rearrangements that are
derived from the basic additive inverse and subtraction laws.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Reassociate a typed hom sum whose left summand is a subtraction. -/
theorem TraceCorQHom.sub_add_reassociate
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        (TraceCorQHom.add left tail)
        right :=
  Eq.trans
    (congrArg
      (fun leftMinusRight =>
        TraceCorQHom.add leftMinusRight tail)
      (TraceCorQHom.sub_eq_add_neg left right))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add
          (TraceCorQHom.add left (TraceCorQHom.neg right)))
        (Eq.symm (TraceCorQHom.add_zero tail)))
      (Eq.trans
        (TraceCorQHom.add_add_add_comm
          left
          (TraceCorQHom.neg right)
          tail
          (TraceCorQHom.zero source target))
        (Eq.trans
          (congrArg
            (TraceCorQHom.add (TraceCorQHom.add left tail))
            (TraceCorQHom.add_zero (TraceCorQHom.neg right)))
          (Eq.symm
            (TraceCorQHom.sub_eq_add_neg
              (TraceCorQHom.add left tail)
              right)))))

/-- Reassociate a typed hom sum whose right summand is a subtraction. -/
theorem TraceCorQHom.add_sub_reassociate
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.add
      left
      (TraceCorQHom.sub right tail) =
      TraceCorQHom.sub
        (TraceCorQHom.add left right)
        tail :=
  Eq.trans
    (TraceCorQHom.add_comm left (TraceCorQHom.sub right tail))
    (Eq.trans
      (TraceCorQHom.sub_add_reassociate right tail left)
      (congrArg
        (fun leftRight =>
          TraceCorQHom.sub leftRight tail)
        (TraceCorQHom.add_comm right left)))

/-- Reassociate typed hom subtraction of a sum as iterated subtraction. -/
theorem TraceCorQHom.sub_sum_reassociate
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.add left tail)
      right =
      TraceCorQHom.add
        (TraceCorQHom.sub left right)
        tail :=
  Eq.symm
    (TraceCorQHom.sub_add_reassociate left right tail)

/-- Reassociate iterated typed hom subtraction as subtraction by a sum. -/
theorem TraceCorQHom.sub_sub_reassociate
    {source target : TraceCorQObject}
    (left right tail : TraceCorQHom source target) :
    TraceCorQHom.sub
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        left
        (TraceCorQHom.add right tail) :=
  Eq.symm
    (TraceCorQHom.sub_add left right tail)

end AnalyticMotives
end LFunctions
end Boundary

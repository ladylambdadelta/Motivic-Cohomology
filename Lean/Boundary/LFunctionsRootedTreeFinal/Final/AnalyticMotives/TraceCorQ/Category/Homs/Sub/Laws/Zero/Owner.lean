import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Neg.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Sub.Laws.Owner

/-!
# Zero and self laws for typed hom subtraction

This file owns the first subtraction laws derived directly from
`left + neg right`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Subtracting zero on the right leaves a typed hom unchanged. -/
theorem TraceCorQHom.sub_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom (TraceCorQHom.zero source target) =
      hom :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg
      hom
      (TraceCorQHom.zero source target))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add hom)
        (TraceCorQHom.neg_zero source target))
      (TraceCorQHom.add_zero hom))

/-- Zero minus a typed hom is its negative. -/
theorem TraceCorQHom.zero_sub
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub (TraceCorQHom.zero source target) hom =
      TraceCorQHom.neg hom :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg
      (TraceCorQHom.zero source target)
      hom)
    (TraceCorQHom.zero_add (TraceCorQHom.neg hom))

/-- A typed hom minus itself is zero. -/
theorem TraceCorQHom.sub_self
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.sub hom hom =
      TraceCorQHom.zero source target :=
  Eq.trans
    (TraceCorQHom.sub_eq_add_neg hom hom)
    (TraceCorQHom.add_neg_self hom)

/-- Equal typed homs have zero subtraction. -/
theorem TraceCorQHom.sub_eq_zero_of_eq
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_eq_right : left = right) :
    TraceCorQHom.sub left right =
      TraceCorQHom.zero source target :=
  Eq.trans
    (congrArg
      (fun leftHom =>
        TraceCorQHom.sub leftHom right)
      left_eq_right)
    (TraceCorQHom.sub_self right)

/-- Zero subtraction detects equality of typed homs. -/
theorem TraceCorQHom.eq_of_sub_eq_zero
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target)
    (left_sub_right_eq_zero :
      TraceCorQHom.sub left right =
        TraceCorQHom.zero source target) :
    left = right :=
  Eq.trans
    (Eq.symm (TraceCorQHom.add_zero left))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add left)
        (Eq.symm (TraceCorQHom.neg_add_self right)))
      (Eq.trans
        (Eq.symm
          (TraceCorQHom.add_assoc
            left
            (TraceCorQHom.neg right)
            right))
        (Eq.trans
          (congrArg
            (fun leftMinusRight =>
              TraceCorQHom.add leftMinusRight right)
            (Eq.trans
              (Eq.symm
                (TraceCorQHom.sub_eq_add_neg left right))
              left_sub_right_eq_zero))
          (TraceCorQHom.zero_add right))))

end AnalyticMotives
end LFunctions
end Boundary

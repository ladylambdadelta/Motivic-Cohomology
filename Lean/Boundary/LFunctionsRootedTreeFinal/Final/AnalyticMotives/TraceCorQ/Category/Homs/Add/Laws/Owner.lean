import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Owner

/-!
# Additive laws for typed trace-correspondence hom classes

This file proves the typed hom additive laws by reflecting the ambient quotient
additive laws back through the fixed-endpoint hom quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero typed hom is a left unit for typed hom addition. -/
theorem TraceCorQHom.zero_add
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.zero source target)
      hom =
      hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add
        (TraceCorQHom.zero source target)
        hom)
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.add
              leftClass
              (TraceCorQHom.ambient hom))
          (TraceCorQHom.ambient_zero source target))
        (TraceCorQQuotient.zero_add
          (TraceCorQHom.ambient hom))))

/-- The zero typed hom is a right unit for typed hom addition. -/
theorem TraceCorQHom.add_zero
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.add
      hom
      (TraceCorQHom.zero source target) =
      hom :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add
        hom
        (TraceCorQHom.zero source target))
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.add
              (TraceCorQHom.ambient hom)
              rightClass)
          (TraceCorQHom.ambient_zero source target))
        (TraceCorQQuotient.add_zero
          (TraceCorQHom.ambient hom))))

/-- Typed hom addition is associative. -/
theorem TraceCorQHom.add_assoc
    {source target : TraceCorQObject}
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      third =
      TraceCorQHom.add
        first
        (TraceCorQHom.add second third) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add
        (TraceCorQHom.add first second)
        third)
      (Eq.trans
        (congrArg
          (fun firstSecondClass =>
            TraceCorQQuotient.add
              firstSecondClass
              (TraceCorQHom.ambient third))
          (TraceCorQHom.ambient_add first second))
        (Eq.trans
          (TraceCorQQuotient.add_assoc
            (TraceCorQHom.ambient first)
            (TraceCorQHom.ambient second)
            (TraceCorQHom.ambient third))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                first
                (TraceCorQHom.add second third))
              (congrArg
                (fun secondThirdClass =>
                  TraceCorQQuotient.add
                    (TraceCorQHom.ambient first)
                    secondThirdClass)
                (TraceCorQHom.ambient_add second third)))))))

/-- Typed hom addition is commutative. -/
theorem TraceCorQHom.add_comm
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.add left right =
      TraceCorQHom.add right left :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_add left right)
      (Eq.trans
        (TraceCorQQuotient.add_comm
          (TraceCorQHom.ambient left)
          (TraceCorQHom.ambient right))
        (Eq.symm
          (TraceCorQHom.ambient_add right left))))

/-- Reassociate four typed hom summands by swapping the middle two terms. -/
theorem TraceCorQHom.add_add_add_comm
    {source target : TraceCorQObject}
    (first second third fourth : TraceCorQHom source target) :
    TraceCorQHom.add
      (TraceCorQHom.add first second)
      (TraceCorQHom.add third fourth) =
      TraceCorQHom.add
        (TraceCorQHom.add first third)
        (TraceCorQHom.add second fourth) :=
  Eq.trans
    (TraceCorQHom.add_assoc
      first
      second
      (TraceCorQHom.add third fourth))
    (Eq.trans
      (congrArg
        (TraceCorQHom.add first)
        (Eq.symm
          (TraceCorQHom.add_assoc second third fourth)))
      (Eq.trans
        (congrArg
          (fun middle =>
            TraceCorQHom.add
              first
              (TraceCorQHom.add middle fourth))
          (TraceCorQHom.add_comm second third))
        (Eq.trans
          (congrArg
            (TraceCorQHom.add first)
            (TraceCorQHom.add_assoc third second fourth))
          (Eq.symm
            (TraceCorQHom.add_assoc
              first
              third
              (TraceCorQHom.add second fourth))))))

end AnalyticMotives
end LFunctions
end Boundary

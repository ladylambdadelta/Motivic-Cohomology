import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner

/-!
# Additive linearity of typed trace-correspondence composition

This file proves that typed composition distributes over typed hom addition on
both sides.  The proofs reflect the ambient quotient distributivity laws back
to the fixed-endpoint typed hom quotients.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Typed composition is left-distributive over typed hom addition. -/
theorem TraceCorQHom.add_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.add left right)
      tail =
      TraceCorQHom.add
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        (TraceCorQHom.add left right)
        tail)
      (Eq.trans
        (congrArg
          (fun leftRightClass =>
            TraceCorQQuotient.comp
              leftRightClass
              (TraceCorQHom.ambient tail))
          (TraceCorQHom.ambient_add left right))
        (Eq.trans
          (TraceCorQQuotient.add_comp
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right)
            (TraceCorQHom.ambient tail))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                (TraceCorQHom.comp left tail)
                (TraceCorQHom.comp right tail))
              (Eq.trans
                (congrArg
                  (fun leftClass =>
                    TraceCorQQuotient.add
                      leftClass
                      (TraceCorQHom.ambient
                        (TraceCorQHom.comp right tail)))
                  (TraceCorQHom.ambient_comp left tail))
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.comp
                        (TraceCorQHom.ambient left)
                        (TraceCorQHom.ambient tail))
                      rightClass)
                  (TraceCorQHom.ambient_comp right tail))))))))

/-- Typed composition is right-distributive over typed hom addition. -/
theorem TraceCorQHom.comp_add
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.add right tail) =
      TraceCorQHom.add
        (TraceCorQHom.comp left right)
        (TraceCorQHom.comp left tail) :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        left
        (TraceCorQHom.add right tail))
      (Eq.trans
        (congrArg
          (fun rightTailClass =>
            TraceCorQQuotient.comp
              (TraceCorQHom.ambient left)
              rightTailClass)
          (TraceCorQHom.ambient_add right tail))
        (Eq.trans
          (TraceCorQQuotient.comp_add
            (TraceCorQHom.ambient left)
            (TraceCorQHom.ambient right)
            (TraceCorQHom.ambient tail))
          (Eq.symm
            (Eq.trans
              (TraceCorQHom.ambient_add
                (TraceCorQHom.comp left right)
                (TraceCorQHom.comp left tail))
              (Eq.trans
                (congrArg
                  (fun rightClass =>
                    TraceCorQQuotient.add
                      rightClass
                      (TraceCorQHom.ambient
                        (TraceCorQHom.comp left tail)))
                  (TraceCorQHom.ambient_comp left right))
                (congrArg
                  (fun tailClass =>
                    TraceCorQQuotient.add
                      (TraceCorQQuotient.comp
                        (TraceCorQHom.ambient left)
                        (TraceCorQHom.ambient right))
                      tailClass)
                  (TraceCorQHom.ambient_comp left tail))))))))

end AnalyticMotives
end LFunctions
end Boundary

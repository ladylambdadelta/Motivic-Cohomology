import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Sub.Laws.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Add.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Linearity.Smul.Owner

/-!
# Subtractive linearity of typed trace-correspondence composition

This file proves that typed composition distributes over typed subtraction on
both sides.  The proof uses the concrete definition of subtraction as addition
of a negative, together with the already-proved additive and scalar linearity
of composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Typed composition is left-distributive over typed hom subtraction. -/
theorem TraceCorQHom.sub_comp
    {source middle target : TraceCorQObject}
    (left right : TraceCorQHom source middle)
    (tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.sub left right)
      tail =
      TraceCorQHom.sub
        (TraceCorQHom.comp left tail)
        (TraceCorQHom.comp right tail) :=
  Eq.trans
    (congrArg
      (fun leftRight =>
        TraceCorQHom.comp leftRight tail)
      (TraceCorQHom.sub_eq_add_neg left right))
    (Eq.trans
      (TraceCorQHom.add_comp
        left
        (TraceCorQHom.neg right)
        tail)
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQHom.add
              (TraceCorQHom.comp left tail)
              rightClass)
          (TraceCorQHom.smul_comp (-1) right tail))
        (Eq.symm
          (TraceCorQHom.sub_eq_add_neg
            (TraceCorQHom.comp left tail)
            (TraceCorQHom.comp right tail)))))

/-- Typed composition is right-distributive over typed hom subtraction. -/
theorem TraceCorQHom.comp_sub
    {source middle target : TraceCorQObject}
    (left : TraceCorQHom source middle)
    (right tail : TraceCorQHom middle target) :
    TraceCorQHom.comp
      left
      (TraceCorQHom.sub right tail) =
      TraceCorQHom.sub
        (TraceCorQHom.comp left right)
        (TraceCorQHom.comp left tail) :=
  Eq.trans
    (congrArg
      (TraceCorQHom.comp left)
      (TraceCorQHom.sub_eq_add_neg right tail))
    (Eq.trans
      (TraceCorQHom.comp_add
        left
        right
        (TraceCorQHom.neg tail))
      (Eq.trans
        (congrArg
          (fun tailClass =>
            TraceCorQHom.add
              (TraceCorQHom.comp left right)
              tailClass)
          (TraceCorQHom.comp_smul (-1) left tail))
        (Eq.symm
          (TraceCorQHom.sub_eq_add_neg
            (TraceCorQHom.comp left right)
            (TraceCorQHom.comp left tail)))))

end AnalyticMotives
end LFunctions
end Boundary

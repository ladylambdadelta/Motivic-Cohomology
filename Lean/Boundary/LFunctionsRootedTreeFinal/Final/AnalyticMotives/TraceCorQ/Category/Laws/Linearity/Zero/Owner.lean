import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Laws.Owner

/-!
# Zero laws for typed trace-correspondence composition

This file proves that typed composition absorbs the zero typed hom on both
sides.  The proofs reflect the ambient quotient zero-composition laws back to
the fixed-endpoint typed hom quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composing the zero typed hom on the left gives zero. -/
theorem TraceCorQHom.zero_comp
    {source middle target : TraceCorQObject}
    (hom : TraceCorQHom middle target) :
    TraceCorQHom.comp
      (TraceCorQHom.zero source middle)
      hom =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        (TraceCorQHom.zero source middle)
        hom)
      (Eq.trans
        (congrArg
          (fun leftClass =>
            TraceCorQQuotient.comp
              leftClass
              (TraceCorQHom.ambient hom))
          (TraceCorQHom.ambient_zero source middle))
        (Eq.trans
          (TraceCorQQuotient.zero_comp
            (TraceCorQHom.ambient hom))
          (Eq.symm
            (TraceCorQHom.ambient_zero source target)))))

/-- Composing the zero typed hom on the right gives zero. -/
theorem TraceCorQHom.comp_zero
    {source middle target : TraceCorQObject}
    (hom : TraceCorQHom source middle) :
    TraceCorQHom.comp
      hom
      (TraceCorQHom.zero middle target) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.eq_of_ambient_eq
    (Eq.trans
      (TraceCorQHom.ambient_comp
        hom
        (TraceCorQHom.zero middle target))
      (Eq.trans
        (congrArg
          (fun rightClass =>
            TraceCorQQuotient.comp
              (TraceCorQHom.ambient hom)
              rightClass)
          (TraceCorQHom.ambient_zero middle target))
        (Eq.trans
          (TraceCorQQuotient.comp_zero
            (TraceCorQHom.ambient hom))
          (Eq.symm
            (TraceCorQHom.ambient_zero source target)))))

end AnalyticMotives
end LFunctions
end Boundary

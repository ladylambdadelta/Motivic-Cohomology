import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner

/-!
# Unit reassociation for typed trace-correspondence composition

This file owns the associativity edge needed by full two-sided identity
normalization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Move the source identity across a right-associated target identity. -/
theorem TraceCorQHom.left_id_right_id_reassociate
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.comp (TraceCorQHom.id source) hom)
      (TraceCorQHom.id target) =
      TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.comp hom (TraceCorQHom.id target)) :=
  TraceCorQHom.comp_assoc
    (TraceCorQHom.id source)
    hom
    (TraceCorQHom.id target)

end AnalyticMotives
end LFunctions
end Boundary

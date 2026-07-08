import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Full.Owner

/-!
# Public full identity normalization for typed trace correspondences

This file exposes the two-sided unit normal forms for typed Q-linear trace
correspondences at the top root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes idempotence of the typed trace identity. -/
theorem AnalyticMotivesRoot.traceCorQHom_id_comp_id
    (object : TraceCorQObject) :
    TraceCorQHom.comp
      (TraceCorQHom.id object)
      (TraceCorQHom.id object) =
      TraceCorQHom.id object :=
  TraceCorQHom.id_comp_id
    object

/-- The top root normalizes a hom with both source and target identities attached. -/
theorem AnalyticMotivesRoot.traceCorQHom_left_id_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.id source)
      (TraceCorQHom.comp hom (TraceCorQHom.id target)) =
      hom :=
  TraceCorQHom.left_id_right_id
    hom

/-- The top root normalizes a left-associated hom with source and target identities. -/
theorem AnalyticMotivesRoot.traceCorQHom_left_id_comp_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.comp (TraceCorQHom.id source) hom)
      (TraceCorQHom.id target) =
      hom :=
  TraceCorQHom.left_id_comp_right_id
    hom

/-- The top root compares the two two-sided unit parenthesizations. -/
theorem AnalyticMotivesRoot.traceCorQHom_left_id_right_id_eq_left_id_comp_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.comp hom (TraceCorQHom.id target)) =
      TraceCorQHom.comp
        (TraceCorQHom.comp (TraceCorQHom.id source) hom)
        (TraceCorQHom.id target) :=
  TraceCorQHom.left_id_right_id_eq_left_id_comp_right_id
    hom

end AnalyticMotives
end LFunctions
end Boundary

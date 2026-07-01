import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Full.Associativity.Owner

/-!
# Full identity normalization for typed trace-correspondence composition

This file owns reusable unit-normalization wrappers for typed
trace-correspondence composition.  These lemmas keep later category-level code
from reopening the singleton and formal-sum identity proofs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The identity composed with itself is the identity. -/
theorem TraceCorQHom.id_comp_id
    (object : TraceCorQObject) :
    TraceCorQHom.comp
      (TraceCorQHom.id object)
      (TraceCorQHom.id object) =
      TraceCorQHom.id object :=
  TraceCorQHom.left_id
    (TraceCorQHom.id object)

/-- Normalize a hom with both its source and target identities attached. -/
theorem TraceCorQHom.left_id_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.id source)
      (TraceCorQHom.comp hom (TraceCorQHom.id target)) =
      hom :=
  Eq.trans
    (TraceCorQHom.left_id
      (TraceCorQHom.comp hom (TraceCorQHom.id target)))
    (TraceCorQHom.right_id hom)

/-- Normalize a left-associated hom with source and target identities attached. -/
theorem TraceCorQHom.left_id_comp_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
      (TraceCorQHom.comp (TraceCorQHom.id source) hom)
      (TraceCorQHom.id target) =
      hom :=
  Eq.trans
    (congrArg
      (fun normalized =>
        TraceCorQHom.comp normalized (TraceCorQHom.id target))
      (TraceCorQHom.left_id hom))
    (TraceCorQHom.right_id hom)

/-- The right-associated two-sided unit form is the reverse of the left-associated one. -/
theorem TraceCorQHom.left_id_right_id_eq_left_id_comp_right_id
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.comp
        (TraceCorQHom.id source)
        (TraceCorQHom.comp hom (TraceCorQHom.id target)) =
      TraceCorQHom.comp
        (TraceCorQHom.comp (TraceCorQHom.id source) hom)
        (TraceCorQHom.id target) :=
  Eq.symm
    (TraceCorQHom.left_id_right_id_reassociate hom)

end AnalyticMotives
end LFunctions
end Boundary

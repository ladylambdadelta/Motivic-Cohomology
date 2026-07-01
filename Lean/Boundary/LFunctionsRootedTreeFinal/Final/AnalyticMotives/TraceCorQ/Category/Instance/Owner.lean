import Mathlib.CategoryTheory.Category.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Associativity.Typed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Laws.Identity.Typed.Owner

/-!
# Category instance for typed trace correspondences

This file packages the typed hom quotient, identity, composition, and proved
laws into a `CategoryTheory.Category` instance on `TraceCorQObject`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The category of typed Q-linear analytic trace correspondences. -/
instance traceCorQCategory :
    CategoryTheory.Category TraceCorQObject where
  Hom := TraceCorQHom
  id := TraceCorQHom.id
  comp := fun left right => TraceCorQHom.comp left right
  id_comp := fun hom => TraceCorQHom.left_id hom
  comp_id := fun hom => TraceCorQHom.right_id hom
  assoc := fun left middle right =>
    TraceCorQHom.comp_assoc left middle right

end AnalyticMotives
end LFunctions
end Boundary

import Mathlib.CategoryTheory.Category.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Laws.Owner

/-!
# Category instance for the analytic additive envelope

This file packages finite trace-family matrix homs, sparse identities, matrix
composition, and the proved identity and associativity laws as a category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic additive envelope of Q-linear trace correspondences. -/
instance traceAnalyticAdditiveCategory :
    CategoryTheory.Category TraceAnalyticAdditiveCategoryObject where
  Hom := TraceAnalyticAdditiveCategoryHom
  id := TraceAnalyticAdditiveCategory.id
  comp := fun left right =>
    TraceAnalyticAdditiveCategory.comp left right
  id_comp := fun hom =>
    TraceAnalyticAdditiveCategory.comp_id_left hom
  comp_id := fun hom =>
    TraceAnalyticAdditiveCategory.comp_id_right hom
  assoc := fun left middle right =>
    TraceAnalyticAdditiveCategory.comp_assoc left middle right

end AnalyticMotives
end LFunctions
end Boundary

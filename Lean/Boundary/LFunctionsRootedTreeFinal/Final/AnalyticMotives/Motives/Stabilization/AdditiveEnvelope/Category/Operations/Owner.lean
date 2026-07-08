import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homs.Algebra.Owner

/-!
# Category operations for the analytic additive envelope

This file names the object, hom, identity, and composition operations of the
finite-family matrix category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The object type of the analytic additive envelope category. -/
abbrev TraceAnalyticAdditiveCategoryObject :=
  TraceAnalyticAdditiveObject

/-- The hom type of the analytic additive envelope category. -/
abbrev TraceAnalyticAdditiveCategoryHom
    (source target : TraceAnalyticAdditiveCategoryObject) :=
  TraceAnalyticAdditiveHom source target

/-- Identity in the analytic additive envelope category. -/
def TraceAnalyticAdditiveCategory.id
    (object : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom object object :=
  TraceAnalyticAdditiveHom.id object

/-- Composition in the analytic additive envelope category. -/
def TraceAnalyticAdditiveCategory.comp
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveHom.comp left right

/-- The category identity is the identity matrix. -/
theorem TraceAnalyticAdditiveCategory.id_eq
    (object : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.id object =
      TraceAnalyticAdditiveHom.id object :=
  rfl

/-- The category composition is matrix composition. -/
theorem TraceAnalyticAdditiveCategory.comp_eq
    {source middle target : TraceAnalyticAdditiveCategoryObject}
    (left : TraceAnalyticAdditiveCategoryHom source middle)
    (right : TraceAnalyticAdditiveCategoryHom middle target) :
    TraceAnalyticAdditiveCategory.comp left right =
      TraceAnalyticAdditiveHom.comp left right :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

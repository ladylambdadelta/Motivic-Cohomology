import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Maps.Entries.Owner

/-!
# Category-level direct-sum maps

This file exposes direct-sum projections and inclusions through the
additive-envelope category hom names.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Category-level projection from a binary direct sum to its left summand. -/
def TraceAnalyticAdditiveCategory.leftDirectSumProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      (TraceAnalyticAdditiveObject.directSum left right)
      left :=
  TraceAnalyticAdditiveObject.leftDirectSumProjection left right

/-- Category-level projection from a binary direct sum to its right summand. -/
def TraceAnalyticAdditiveCategory.rightDirectSumProjection
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      (TraceAnalyticAdditiveObject.directSum left right)
      right :=
  TraceAnalyticAdditiveObject.rightDirectSumProjection left right

/-- Category-level inclusion of the left summand into a binary direct sum. -/
def TraceAnalyticAdditiveCategory.leftDirectSumInclusion
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      left
      (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveObject.leftDirectSumInclusion left right

/-- Category-level inclusion of the right summand into a binary direct sum. -/
def TraceAnalyticAdditiveCategory.rightDirectSumInclusion
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom
      right
      (TraceAnalyticAdditiveObject.directSum left right) :=
  TraceAnalyticAdditiveObject.rightDirectSumInclusion left right

/-- The category-level left projection is the underlying left projection matrix. -/
theorem TraceAnalyticAdditiveCategory.leftDirectSumProjection_eq
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.leftDirectSumProjection left right =
      TraceAnalyticAdditiveObject.leftDirectSumProjection left right :=
  rfl

/-- The category-level right projection is the underlying right projection matrix. -/
theorem TraceAnalyticAdditiveCategory.rightDirectSumProjection_eq
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.rightDirectSumProjection left right =
      TraceAnalyticAdditiveObject.rightDirectSumProjection left right :=
  rfl

/-- The category-level left inclusion is the underlying left inclusion matrix. -/
theorem TraceAnalyticAdditiveCategory.leftDirectSumInclusion_eq
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.leftDirectSumInclusion left right =
      TraceAnalyticAdditiveObject.leftDirectSumInclusion left right :=
  rfl

/-- The category-level right inclusion is the underlying right inclusion matrix. -/
theorem TraceAnalyticAdditiveCategory.rightDirectSumInclusion_eq
    (left right : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.rightDirectSumInclusion left right =
      TraceAnalyticAdditiveObject.rightDirectSumInclusion left right :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

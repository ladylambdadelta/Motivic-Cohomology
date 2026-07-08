import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Operations.Owner

/-!
# Additive operations in the analytic additive-envelope category

This file exposes zero, addition, negation, and rational scalar multiplication
for category-level matrix homs between finite analytic trace families.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Zero category hom in the analytic additive envelope. -/
def TraceAnalyticAdditiveCategory.zeroHom
    (source target : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveHom.zero source target

/-- Addition of category homs in the analytic additive envelope. -/
def TraceAnalyticAdditiveCategory.addHom
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveHom.add left right

/-- Negation of category homs in the analytic additive envelope. -/
def TraceAnalyticAdditiveCategory.negHom
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveHom.neg hom

/-- Rational scalar multiplication of category homs in the analytic additive envelope. -/
def TraceAnalyticAdditiveCategory.smulHom
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategoryHom source target :=
  TraceAnalyticAdditiveHom.smul coefficient hom

/-- The category-level zero hom is the zero matrix hom. -/
theorem TraceAnalyticAdditiveCategory.zeroHom_eq
    (source target : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.zeroHom source target =
      TraceAnalyticAdditiveHom.zero source target :=
  rfl

/-- Category-level hom addition is matrix-hom addition. -/
theorem TraceAnalyticAdditiveCategory.addHom_eq
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom left right =
      TraceAnalyticAdditiveHom.add left right :=
  rfl

/-- Category-level hom negation is matrix-hom negation. -/
theorem TraceAnalyticAdditiveCategory.negHom_eq
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.negHom hom =
      TraceAnalyticAdditiveHom.neg hom :=
  rfl

/-- Category-level hom scalar multiplication is matrix-hom scalar multiplication. -/
theorem TraceAnalyticAdditiveCategory.smulHom_eq
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom coefficient hom =
      TraceAnalyticAdditiveHom.smul coefficient hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

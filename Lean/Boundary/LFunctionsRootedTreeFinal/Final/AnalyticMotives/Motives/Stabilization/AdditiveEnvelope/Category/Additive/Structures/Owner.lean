import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Category.Additive.Laws.Owner

/-!
# Additive and rational hom structures for the analytic additive envelope

This file exposes the standard additive commutative group and rational module
structures on fixed-endpoint category homs, and relates the named category-level
operations to those structures.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Fixed-endpoint category homs form an additive commutative group. -/
def TraceAnalyticAdditiveCategory.addCommGroupStructure
    (source target : TraceAnalyticAdditiveCategoryObject) :
    AddCommGroup (TraceAnalyticAdditiveCategoryHom source target) :=
  TraceAnalyticAdditiveHom.addCommGroupStructure source target

/-- Fixed-endpoint category homs form a rational module. -/
def TraceAnalyticAdditiveCategory.ratModuleStructure
    (source target : TraceAnalyticAdditiveCategoryObject) :
    Module Rat (TraceAnalyticAdditiveCategoryHom source target) :=
  TraceAnalyticAdditiveHom.ratModuleStructure source target

/-- The named category zero hom is standard zero. -/
theorem TraceAnalyticAdditiveCategory.zeroHom_eq_zero
    (source target : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticAdditiveCategory.zeroHom source target =
      0 :=
  TraceAnalyticAdditiveHom.zero_eq_zero source target

/-- Named category hom addition is standard addition. -/
theorem TraceAnalyticAdditiveCategory.addHom_eq_add
    {source target : TraceAnalyticAdditiveCategoryObject}
    (left right : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.addHom left right =
      left + right :=
  TraceAnalyticAdditiveHom.add_eq_add left right

/-- Named category hom negation is standard negation. -/
theorem TraceAnalyticAdditiveCategory.negHom_eq_neg
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.negHom hom =
      -hom :=
  TraceAnalyticAdditiveHom.neg_eq_neg hom

/-- Named category hom scalar multiplication is standard scalar multiplication. -/
theorem TraceAnalyticAdditiveCategory.smulHom_eq_smul
    (coefficient : Rat)
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : TraceAnalyticAdditiveCategoryHom source target) :
    TraceAnalyticAdditiveCategory.smulHom coefficient hom =
      coefficient • hom :=
  TraceAnalyticAdditiveHom.smul_eq_smul coefficient hom

end AnalyticMotives
end LFunctions
end Boundary

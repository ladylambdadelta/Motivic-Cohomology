import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.HasShift.Owner

/-!
# Compatibility of induced bounded shifts with ambient analytic shifts

The bounded stable shift instance is induced from the fully faithful inclusion
into the ambient analytic comparison source.  This file records the resulting
component formulas after applying that inclusion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The induced bounded zero-shift hom includes to the ambient zero-shift
hom. -/
theorem inducedShiftZero_inclusion_hom_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((shiftFunctorZero
        TraceAnalyticDMgmComparisonSource.BoundedStable ℤ).hom.app
          object) =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).hom.app
        object.object) :=
  CategoryTheory.Functor.FullyFaithful.hasShift.map_zero_hom_app
    (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
      TraceAnalyticDMgmComparisonSource.boundedStableObject)
    (fun degree =>
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
    (fun degree =>
      eqToIso
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftFunctor_comp_inclusion degree))
    object

/-- The induced bounded zero-shift inverse includes to the ambient zero-shift
inverse. -/
theorem inducedShiftZero_inclusion_inv_app
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((shiftFunctorZero
        TraceAnalyticDMgmComparisonSource.BoundedStable ℤ).inv.app
          object) =
      ((shiftFunctorZero TraceAnalyticDMgmComparisonSource ℤ).inv.app
        object.object) :=
  CategoryTheory.Functor.FullyFaithful.hasShift.map_zero_inv_app
    (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
      TraceAnalyticDMgmComparisonSource.boundedStableObject)
    (fun degree =>
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
    (fun degree =>
      eqToIso
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftFunctor_comp_inclusion degree))
    object

/-- The induced bounded add-shift hom includes to the ambient add-shift hom. -/
theorem inducedShiftAdd_inclusion_hom_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((shiftFunctorAdd
        TraceAnalyticDMgmComparisonSource.BoundedStable first second).hom.app
          object) =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).hom.app
        object.object) :=
  CategoryTheory.Functor.FullyFaithful.hasShift.map_add_hom_app
    (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
      TraceAnalyticDMgmComparisonSource.boundedStableObject)
    (fun degree =>
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
    (fun degree =>
      eqToIso
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftFunctor_comp_inclusion degree))
    first
    second
    object

/-- The induced bounded add-shift inverse includes to the ambient add-shift
inverse. -/
theorem inducedShiftAdd_inclusion_inv_app
    (first second : ℤ)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion.map
      ((shiftFunctorAdd
        TraceAnalyticDMgmComparisonSource.BoundedStable first second).inv.app
          object) =
      ((shiftFunctorAdd TraceAnalyticDMgmComparisonSource first second).inv.app
        object.object) :=
  CategoryTheory.Functor.FullyFaithful.hasShift.map_add_inv_app
    (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
      TraceAnalyticDMgmComparisonSource.boundedStableObject)
    (fun degree =>
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
    (fun degree =>
      eqToIso
        (TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftFunctor_comp_inclusion degree))
    first
    second
    object

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

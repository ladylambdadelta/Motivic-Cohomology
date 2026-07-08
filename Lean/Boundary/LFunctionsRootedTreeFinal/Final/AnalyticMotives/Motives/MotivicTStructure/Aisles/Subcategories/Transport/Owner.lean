import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Monotone.Owner

/-!
# Transport lifts for analytic motivic aisle subcategories

This file lifts ambient functors that are pointwise equal to the standard
subcategory inclusion back into the concrete aisle and coaisle subcategories.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An ambient functor pointwise equal to the aisle inclusion lifts to the
aisle. -/
abbrev TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Aisle cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Aisle cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Aisle cut ⥤
      TraceAnalyticMotivicTStructure.Aisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE cut)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.aisleLE_transport
        cut
        (Eq.symm (object_eq object))
        object.property)

/-- An ambient functor pointwise equal to the coaisle inclusion lifts to the
coaisle. -/
abbrev TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Coaisle cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Coaisle cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Coaisle cut ⥤
      TraceAnalyticMotivicTStructure.Coaisle cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE cut)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.coaisleGE_transport
        cut
        (Eq.symm (object_eq object))
        object.property)

/-- The aisle transport lift has the given ambient functor after inclusion. -/
theorem TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq_comp_inclusion
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Aisle cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Aisle cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Aisle.liftOfPointwiseEq
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion cut =
      functor :=
  rfl

/-- The coaisle transport lift has the given ambient functor after inclusion. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq_comp_inclusion
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Coaisle cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Coaisle cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Coaisle.liftOfPointwiseEq
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion cut =
      functor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

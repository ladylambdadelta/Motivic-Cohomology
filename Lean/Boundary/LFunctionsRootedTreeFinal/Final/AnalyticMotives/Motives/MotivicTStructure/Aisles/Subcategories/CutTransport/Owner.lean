import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.CutTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Subcategories.Transport.Owner

/-!
# Cut-transport lifts for analytic motivic aisle subcategories

This file lifts ambient functors pointwise equal to an aisle or coaisle
inclusion across a monotone cut change.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An ambient functor pointwise equal to a lower-aisle inclusion lifts to a
larger aisle. -/
abbrev TraceAnalyticMotivicTStructure.Aisle.liftToLargerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (functor :
      TraceAnalyticMotivicTStructure.Aisle lower ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Aisle lower) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Aisle lower ⥤
      TraceAnalyticMotivicTStructure.Aisle upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.aisleLE upper)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.aisleLE_cutTransport
        cut_le
        (Eq.symm (object_eq object))
        object.property)

/-- An ambient functor pointwise equal to an upper-coaisle inclusion lifts to a
lower coaisle. -/
abbrev TraceAnalyticMotivicTStructure.Coaisle.liftToLowerOfPointwiseEq
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (functor :
      TraceAnalyticMotivicTStructure.Coaisle upper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Coaisle upper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Coaisle upper ⥤
      TraceAnalyticMotivicTStructure.Coaisle lower :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.coaisleGE lower)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.coaisleGE_cutTransport
        cut_le
        (Eq.symm (object_eq object))
        object.property)

/-- The larger-aisle cut-transport lift has the given ambient functor after
inclusion. -/
theorem TraceAnalyticMotivicTStructure.Aisle.liftToLargerOfPointwiseEq_comp_inclusion
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (functor :
      TraceAnalyticMotivicTStructure.Aisle lower ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Aisle lower) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Aisle.liftToLargerOfPointwiseEq
        cut_le
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Aisle.inclusion upper =
      functor :=
  rfl

/-- The lower-coaisle cut-transport lift has the given ambient functor after
inclusion. -/
theorem TraceAnalyticMotivicTStructure.Coaisle.liftToLowerOfPointwiseEq_comp_inclusion
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    (functor :
      TraceAnalyticMotivicTStructure.Coaisle upper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Coaisle upper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Coaisle.liftToLowerOfPointwiseEq
        cut_le
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Coaisle.inclusion lower =
      functor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

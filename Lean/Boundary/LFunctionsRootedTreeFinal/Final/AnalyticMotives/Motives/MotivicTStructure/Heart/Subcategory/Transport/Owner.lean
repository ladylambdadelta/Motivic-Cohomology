import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Owner

/-!
# Transport lifts for the analytic motivic heart subcategory

This file lifts ambient functors that are pointwise equal to the standard heart
inclusion back into the concrete cutwise heart subcategory.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An ambient functor pointwise equal to the heart inclusion lifts to the
heart. -/
abbrev TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Heart cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Heart cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Heart cut ⥤
      TraceAnalyticMotivicTStructure.Heart cut :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.heartAt cut)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.heartAt_transport
        cut
        (Eq.symm (object_eq object))
        object.property)

/-- The heart transport lift has the given ambient functor after inclusion. -/
theorem TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq_comp_inclusion
    {cut : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Heart cut ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Heart cut) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Heart.liftOfPointwiseEq
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Heart.inclusion cut =
      functor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

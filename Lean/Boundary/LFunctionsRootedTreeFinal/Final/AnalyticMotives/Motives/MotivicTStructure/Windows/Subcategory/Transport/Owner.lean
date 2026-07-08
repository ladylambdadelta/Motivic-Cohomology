import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Transport.Owner

/-!
# Transport lifts for analytic motivic window subcategories

This file lifts ambient functors that are pointwise equal to a window inclusion
back into the corresponding concrete window subcategory.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An ambient functor pointwise equal to the window inclusion lifts to the
same window. -/
abbrev TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
    {lower upper : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Window lower upper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Window lower upper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Window lower upper ⥤
      TraceAnalyticMotivicTStructure.Window lower upper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.window lower upper)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.window_transport
        lower
        upper
        (Eq.symm (object_eq object))
        object.property)

/-- The window transport lift has the given ambient functor after inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq_comp_inclusion
    {lower upper : ℤ}
    (functor :
      TraceAnalyticMotivicTStructure.Window lower upper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object : TraceAnalyticMotivicTStructure.Window lower upper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion lower upper =
      functor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.CutTransport.Owner

/-!
# Cut-transport lifts for analytic motivic window subcategories

This file lifts ambient functors from an inner window into any wider outer
window when the ambient functor is pointwise equal to the inner-window
inclusion.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- An ambient functor pointwise equal to an inner-window inclusion lifts to
any wider enclosing window. -/
abbrev TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (functor :
      TraceAnalyticMotivicTStructure.Window innerLower innerUpper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object :
        TraceAnalyticMotivicTStructure.Window innerLower innerUpper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Window innerLower innerUpper ⥤
      TraceAnalyticMotivicTStructure.Window outerLower outerUpper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.window outerLower outerUpper)
    functor
    (fun object =>
      TraceAnalyticMotivicTStructure.window_cutTransport
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        (Eq.symm (object_eq object))
        object.property)

/-- The wider-window pointwise-equality lift has the given ambient functor
after the outer-window inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq_comp_inclusion
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (functor :
      TraceAnalyticMotivicTStructure.Window innerLower innerUpper ⥤
        TraceAnalyticDMgmComparisonSource)
    (object_eq :
      (object :
        TraceAnalyticMotivicTStructure.Window innerLower innerUpper) →
        functor.obj object = object.object) :
    TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        functor
        object_eq ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion
          outerLower
          outerUpper =
      functor :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

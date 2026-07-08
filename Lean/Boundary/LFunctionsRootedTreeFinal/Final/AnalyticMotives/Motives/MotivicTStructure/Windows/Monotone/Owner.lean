import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Owner

/-!
# Monotonicity for analytic motivic windows

This file proves that widening a window preserves membership and upgrades that
fact to inclusions between the corresponding full subcategories.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Window membership is preserved when the lower bound is decreased and the
upper bound is increased. -/
theorem TraceAnalyticMotivicTStructure.window_mono
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window innerLower innerUpper object) :
    TraceAnalyticMotivicTStructure.window outerLower outerUpper object :=
  TraceAnalyticMotivicTStructure.window_intro
    (TraceAnalyticMotivicTStructure.coaisleGE_mono
      outerLower_le_innerLower
      (TraceAnalyticMotivicTStructure.window_coaisle membership))
    (TraceAnalyticMotivicTStructure.aisleLE_mono
      innerUpper_le_outerUpper
      (TraceAnalyticMotivicTStructure.window_aisle membership))

/-- A narrower window includes into any wider enclosing window. -/
abbrev TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper) :
    TraceAnalyticMotivicTStructure.Window innerLower innerUpper ⥤
      TraceAnalyticMotivicTStructure.Window outerLower outerUpper :=
  CategoryTheory.FullSubcategory.lift
    (TraceAnalyticMotivicTStructure.window outerLower outerUpper)
    (TraceAnalyticMotivicTStructure.Window.inclusion
      innerLower
      innerUpper)
    (fun object =>
      TraceAnalyticMotivicTStructure.window_mono
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        object.property)

/-- The wider-window inclusion preserves the ambient object. -/
theorem TraceAnalyticMotivicTStructure.Window.inclusionOfBounds_obj
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    (object :
      TraceAnalyticMotivicTStructure.Window innerLower innerUpper) :
    (TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_innerLower
        innerUpper_le_outerUpper).obj object =
      ⟨
        object.object,
        TraceAnalyticMotivicTStructure.window_mono
          outerLower_le_innerLower
          innerUpper_le_outerUpper
          object.property
      ⟩ :=
  rfl

/-- Wider-window inclusion followed by ambient inclusion is the original
inner-window inclusion. -/
theorem TraceAnalyticMotivicTStructure.Window.inclusionOfBounds_comp_inclusion
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper) :
    TraceAnalyticMotivicTStructure.Window.inclusionOfBounds
        outerLower_le_innerLower
        innerUpper_le_outerUpper ⋙
        TraceAnalyticMotivicTStructure.Window.inclusion
          outerLower
          outerUpper =
      TraceAnalyticMotivicTStructure.Window.inclusion
        innerLower
        innerUpper :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

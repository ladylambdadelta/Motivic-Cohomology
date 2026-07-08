import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.CutTransport.Owner

/-!
# Cut-transport compatibility for heart-to-window interval functors

This file records how heart-to-window interval functors interact with
wider-window cut transport.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mapping a heart object into an inner window and then applying the
wider-window cut-transport lift is the same as mapping it directly into the
outer window. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_comp_liftToWiderOfPointwiseEq
    {outerLower innerLower center innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerLower_le_center : innerLower ≤ center)
    (center_le_innerUpper : center ≤ innerUpper)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        innerLower_le_center
        center_le_innerUpper ⋙
        TraceAnalyticMotivicTStructure.Window.liftToWiderOfPointwiseEq
          outerLower_le_innerLower
          innerUpper_le_outerUpper
          (TraceAnalyticMotivicTStructure.Window.inclusion
            innerLower
            innerUpper)
          (fun object => Eq.refl object.object) =
      TraceAnalyticMotivicTStructure.Heart.toWindow
        (le_trans outerLower_le_innerLower innerLower_le_center)
        (le_trans center_le_innerUpper innerUpper_le_outerUpper) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Subcategory.Window.Interval.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Subcategory.Transport.Owner

/-!
# Transport compatibility for heart-to-window interval functors

This file records how heart-to-window interval functors interact with
reflexive pointwise-equality transport of the target window.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Heart-to-window followed by the reflexive window transport lift is the
original heart-to-window functor. -/
theorem TraceAnalyticMotivicTStructure.Heart.toWindow_comp_liftOfPointwiseEq_refl
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper) :
    TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper ⋙
        TraceAnalyticMotivicTStructure.Window.liftOfPointwiseEq
          (TraceAnalyticMotivicTStructure.Window.inclusion lower upper)
          (fun object => Eq.refl object.object) =
      TraceAnalyticMotivicTStructure.Heart.toWindow
        lower_le_center
        center_le_upper :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

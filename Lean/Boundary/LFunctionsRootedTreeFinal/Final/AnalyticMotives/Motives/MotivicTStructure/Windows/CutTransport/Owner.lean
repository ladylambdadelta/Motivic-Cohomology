import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Shift.Owner

/-!
# Cut transport for analytic motivic windows

This file combines interval widening with equality transport for concrete
analytic motivic window membership.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Window membership transports along equality while widening the interval. -/
theorem TraceAnalyticMotivicTStructure.window_cutTransport
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.window innerLower innerUpper source) :
    TraceAnalyticMotivicTStructure.window outerLower outerUpper target :=
  TraceAnalyticMotivicTStructure.window_transport
    outerLower
    outerUpper
    object_eq
    (TraceAnalyticMotivicTStructure.window_mono
      outerLower_le_innerLower
      innerUpper_le_outerUpper
      membership)

/-- Window cut transport by reflexive equality is window monotonicity. -/
theorem TraceAnalyticMotivicTStructure.window_cutTransport_refl
    {outerLower innerLower innerUpper outerUpper : ℤ}
    (outerLower_le_innerLower : outerLower ≤ innerLower)
    (innerUpper_le_outerUpper : innerUpper ≤ outerUpper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window innerLower innerUpper object) :
    TraceAnalyticMotivicTStructure.window_cutTransport
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        (Eq.refl object)
        membership =
      TraceAnalyticMotivicTStructure.window_mono
        outerLower_le_innerLower
        innerUpper_le_outerUpper
        membership :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Windows.Monotone.Owner

/-!
# Transport for analytic motivic windows

This file proves that concrete analytic motivic window membership transports
along equality of stable comparison-source objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Window membership transports along equality of objects. -/
theorem TraceAnalyticMotivicTStructure.window_transport
    (lower upper : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.window lower upper source) :
    TraceAnalyticMotivicTStructure.window lower upper target :=
  TraceAnalyticMotivicTStructure.window_intro
    (TraceAnalyticMotivicTStructure.coaisleGE_transport
      lower
      object_eq
      (TraceAnalyticMotivicTStructure.window_coaisle membership))
    (TraceAnalyticMotivicTStructure.aisleLE_transport
      upper
      object_eq
      (TraceAnalyticMotivicTStructure.window_aisle membership))

/-- Window membership is invariant under equality of objects. -/
theorem TraceAnalyticMotivicTStructure.window_iff_of_eq
    (lower upper : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target) :
    TraceAnalyticMotivicTStructure.window lower upper source ↔
      TraceAnalyticMotivicTStructure.window lower upper target :=
  Iff.intro
    (fun membership =>
      TraceAnalyticMotivicTStructure.window_transport
        lower
        upper
        object_eq
        membership)
    (fun membership =>
      TraceAnalyticMotivicTStructure.window_transport
        lower
        upper
        (Eq.symm object_eq)
        membership)

/-- Transporting window membership by reflexive equality is the original
membership. -/
theorem TraceAnalyticMotivicTStructure.window_transport_refl
    (lower upper : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.window lower upper object) :
    TraceAnalyticMotivicTStructure.window_transport
        lower
        upper
        (Eq.refl object)
        membership =
      membership :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

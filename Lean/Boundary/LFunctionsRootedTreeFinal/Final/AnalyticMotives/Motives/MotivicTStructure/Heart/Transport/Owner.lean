import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Heart.Owner

/-!
# Transport for the concrete analytic motivic heart

This file transports cutwise heart membership using the concrete aisle and
coaisle transport theorems.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Heart membership transports along equality of stable comparison-source
objects. -/
theorem TraceAnalyticMotivicTStructure.heartAt_transport
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.heartAt cut source) :
    TraceAnalyticMotivicTStructure.heartAt cut target :=
  TraceAnalyticMotivicTStructure.heartAt_intro
    (TraceAnalyticMotivicTStructure.aisleLE_transport
      cut
      object_eq
      (TraceAnalyticMotivicTStructure.heartAt_aisle membership))
    (TraceAnalyticMotivicTStructure.coaisleGE_transport
      cut
      object_eq
      (TraceAnalyticMotivicTStructure.heartAt_coaisle membership))

/-- Heart membership is invariant under equality of stable comparison-source
objects. -/
theorem TraceAnalyticMotivicTStructure.heartAt_iff_of_eq
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target) :
    TraceAnalyticMotivicTStructure.heartAt cut source ↔
      TraceAnalyticMotivicTStructure.heartAt cut target :=
  Iff.intro
    (fun membership =>
      TraceAnalyticMotivicTStructure.heartAt_transport
        cut
        object_eq
        membership)
    (fun membership =>
      TraceAnalyticMotivicTStructure.heartAt_transport
        cut
        (Eq.symm object_eq)
        membership)

/-- Heart membership at an exact cut gives membership in any enclosing
aisle/coaisle window. -/
theorem TraceAnalyticMotivicTStructure.heartAt_window
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.heartAt center object) :
    TraceAnalyticMotivicTStructure.aisleLE upper object ∧
      TraceAnalyticMotivicTStructure.coaisleGE lower object :=
  And.intro
    (TraceAnalyticMotivicTStructure.aisleLE_mono
      center_le_upper
      (TraceAnalyticMotivicTStructure.heartAt_aisle membership))
    (TraceAnalyticMotivicTStructure.coaisleGE_mono
      lower_le_center
      (TraceAnalyticMotivicTStructure.heartAt_coaisle membership))

/-- Heart membership transports along equality and into any enclosing
aisle/coaisle window. -/
theorem TraceAnalyticMotivicTStructure.heartAt_window_transport
    {lower center upper : ℤ}
    (lower_le_center : lower ≤ center)
    (center_le_upper : center ≤ upper)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.heartAt center source) :
    TraceAnalyticMotivicTStructure.aisleLE upper target ∧
      TraceAnalyticMotivicTStructure.coaisleGE lower target :=
  TraceAnalyticMotivicTStructure.heartAt_window
    lower_le_center
    center_le_upper
    (TraceAnalyticMotivicTStructure.heartAt_transport
      center
      object_eq
      membership)

end AnalyticMotives
end LFunctions
end Boundary

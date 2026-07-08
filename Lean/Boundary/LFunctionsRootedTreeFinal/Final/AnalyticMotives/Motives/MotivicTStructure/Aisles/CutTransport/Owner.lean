import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Transport.Owner

/-!
# Cut transport for analytic motivic aisles and coaisles

This file combines cut monotonicity with equality transport for the concrete
analytic motivic aisle and coaisle predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Aisle membership transports along equality while enlarging the cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_cutTransport
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE lower source) :
    TraceAnalyticMotivicTStructure.aisleLE upper target :=
  TraceAnalyticMotivicTStructure.aisleLE_transport
    upper
    object_eq
    (TraceAnalyticMotivicTStructure.aisleLE_mono
      cut_le
      membership)

/-- Coaisle membership transports along equality while lowering the cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_cutTransport
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE upper source) :
    TraceAnalyticMotivicTStructure.coaisleGE lower target :=
  TraceAnalyticMotivicTStructure.coaisleGE_transport
    lower
    object_eq
    (TraceAnalyticMotivicTStructure.coaisleGE_mono
      cut_le
      membership)

/-- Aisle cut transport with reflexive object equality is monotonicity. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_cutTransport_refl
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE lower object) :
    TraceAnalyticMotivicTStructure.aisleLE_cutTransport
        cut_le
        (Eq.refl object)
        membership =
      TraceAnalyticMotivicTStructure.aisleLE_mono
        cut_le
        membership :=
  rfl

/-- Coaisle cut transport with reflexive object equality is monotonicity. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_cutTransport_refl
    {lower upper : ℤ}
    (cut_le : lower ≤ upper)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE upper object) :
    TraceAnalyticMotivicTStructure.coaisleGE_cutTransport
        cut_le
        (Eq.refl object)
        membership =
      TraceAnalyticMotivicTStructure.coaisleGE_mono
        cut_le
        membership :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

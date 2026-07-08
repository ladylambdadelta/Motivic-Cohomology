import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Aisles.Monotone.Owner

/-!
# Transport for analytic motivic aisle and coaisle membership

This file proves that concrete analytic motivic aisle and coaisle membership
transport along equality of stable comparison-source objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Aisle membership transports along equality of objects. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_transport
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE cut source) :
    TraceAnalyticMotivicTStructure.aisleLE cut target :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.aisleLE cut object)
    object_eq
    membership

/-- Coaisle membership transports along equality of objects. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_transport
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target)
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE cut source) :
    TraceAnalyticMotivicTStructure.coaisleGE cut target :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.coaisleGE cut object)
    object_eq
    membership

/-- Aisle membership is invariant under equality of objects. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_iff_of_eq
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target) :
    TraceAnalyticMotivicTStructure.aisleLE cut source ↔
      TraceAnalyticMotivicTStructure.aisleLE cut target :=
  Iff.intro
    (fun membership =>
      TraceAnalyticMotivicTStructure.aisleLE_transport
        cut
        object_eq
        membership)
    (fun membership =>
      TraceAnalyticMotivicTStructure.aisleLE_transport
        cut
        (Eq.symm object_eq)
        membership)

/-- Coaisle membership is invariant under equality of objects. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_iff_of_eq
    (cut : ℤ)
    {source target : TraceAnalyticDMgmComparisonSource}
    (object_eq : source = target) :
    TraceAnalyticMotivicTStructure.coaisleGE cut source ↔
      TraceAnalyticMotivicTStructure.coaisleGE cut target :=
  Iff.intro
    (fun membership =>
      TraceAnalyticMotivicTStructure.coaisleGE_transport
        cut
        object_eq
        membership)
    (fun membership =>
      TraceAnalyticMotivicTStructure.coaisleGE_transport
        cut
        (Eq.symm object_eq)
        membership)

/-- Transporting aisle membership by reflexive equality is the original
membership. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_transport_refl
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.aisleLE cut object) :
    TraceAnalyticMotivicTStructure.aisleLE_transport
        cut
        (Eq.refl object)
        membership =
      membership :=
  rfl

/-- Transporting coaisle membership by reflexive equality is the original
membership. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_transport_refl
    (cut : ℤ)
    {object : TraceAnalyticDMgmComparisonSource}
    (membership :
      TraceAnalyticMotivicTStructure.coaisleGE cut object) :
    TraceAnalyticMotivicTStructure.coaisleGE_transport
        cut
        (Eq.refl object)
        membership =
      membership :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Projections.Owner

/-!
# Object identities for iso-closed heart projections

This file records the object-level ambient inclusion identities for the
iso-closed heart projections to the iso-closed aisle and coaisle.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Projecting an iso-closed heart object to the iso-closed aisle and then
including it recovers the heart object's ambient comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.AisleIsoClosed.inclusion cut).obj
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisleObject object) =
      object.object :=
  rfl

/-- Projecting an iso-closed heart object to the iso-closed coaisle and then
including it recovers the heart object's ambient comparison-source object. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle_inclusion_obj
    {cut : ℤ}
    (object : TraceAnalyticMotivicTStructure.HeartIsoClosed cut) :
    (TraceAnalyticMotivicTStructure.CoaisleIsoClosed.inclusion cut).obj
        (TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisleObject
          object) =
      object.object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

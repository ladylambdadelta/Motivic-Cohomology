import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Projections.Owner

/-!
# Composition identities for iso-closed heart projections

This file records that the iso-closed heart-to-aisle and heart-to-coaisle
projection functors recover the iso-closed heart inclusion after composing
with the corresponding ambient inclusions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Iso-closed heart-to-aisle followed by iso-closed aisle inclusion is the
iso-closed heart inclusion. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.toAisle cut ⋙
        TraceAnalyticMotivicTStructure.AisleIsoClosed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut :=
  rfl

/-- Iso-closed heart-to-coaisle followed by iso-closed coaisle inclusion is the
iso-closed heart inclusion. -/
theorem TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle_comp_inclusion
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.HeartIsoClosed.toCoaisle cut ⋙
        TraceAnalyticMotivicTStructure.CoaisleIsoClosed.inclusion cut =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.inclusion cut :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

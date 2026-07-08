import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Owner

/-!
# Horn fillers in the analytic stable motive quasicategory

This owner file exposes the actual infinity-categorical operation supplied by
the simplicial nerve presentation: every inner horn in the analytic stable
motive nerve has a simplex filling.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open Simplicial

/-- Every inner horn in the analytic stable motive nerve has a simplex
filler. -/
theorem TraceAnalyticStableMotiveQuasicategory.innerHornFilling
    {dimension : ℕ}
    {missingFace : Fin (dimension + 1)}
    (positive : 0 < missingFace)
    (interior : missingFace < Fin.last dimension)
    (horn :
      Λ[dimension, missingFace] ⟶
        TraceAnalyticStableMotiveQuasicategory) :
    ∃ simplex :
      Δ[dimension] ⟶ TraceAnalyticStableMotiveQuasicategory,
      horn = hornInclusion dimension missingFace ≫ simplex :=
  SSet.Quasicategory.hornFilling
    positive
    interior
    horn

/-- The owner quasicategory structure is the source of the inner-horn
filling operation. -/
theorem TraceAnalyticStableMotiveQuasicategory.innerHornFilling_eq
    {dimension : ℕ}
    {missingFace : Fin (dimension + 1)}
    (positive : 0 < missingFace)
    (interior : missingFace < Fin.last dimension)
    (horn :
      Λ[dimension, missingFace] ⟶
        TraceAnalyticStableMotiveQuasicategory) :
    TraceAnalyticStableMotiveQuasicategory.innerHornFilling
        positive
        interior
        horn =
      SSet.Quasicategory.hornFilling
        positive
        interior
        horn :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

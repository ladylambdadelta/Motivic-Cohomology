import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.Owner

/-!
# Monotonicity of bounded distinguished triangles

Increasing the numeric weight bound changes only the chosen bounded
representatives of the first two vertices.  The underlying distinguished
triangle is unchanged.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound the first two bounded representatives of a bounded distinguished triangle. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle lower) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle upper where
  first := boundedTriangle.first.rebound bound_le
  second := boundedTriangle.second.rebound bound_le
  triangle := boundedTriangle.triangle
  distinguished := boundedTriangle.distinguished

/-- Rebounding preserves the first bounded representative up to the bound change. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rebound_first
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle lower) :
    (boundedTriangle.rebound bound_le).first =
      boundedTriangle.first.rebound bound_le :=
  rfl

/-- Rebounding preserves the second bounded representative up to the bound change. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rebound_second
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle lower) :
    (boundedTriangle.rebound bound_le).second =
      boundedTriangle.second.rebound bound_le :=
  rfl

/-- Rebounding does not change the underlying distinguished triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rebound_triangle
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle lower) :
    (boundedTriangle.rebound bound_le).triangle =
      boundedTriangle.triangle :=
  rfl

/-- Rebounding preserves the distinguished-triangle witness. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle.rebound_distinguished
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (boundedTriangle :
      TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle lower) :
    (boundedTriangle.rebound bound_le).triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  boundedTriangle.distinguished

end AnalyticMotives
end LFunctions
end Boundary

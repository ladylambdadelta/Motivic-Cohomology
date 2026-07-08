import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.HomotopyCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Triangulated.Owner

/-!
# The quotient functor into the stable-infinity homotopy category

This file exposes the exact functorial behavior of the quotient functor whose
target is the homotopy category presented by the analytic stable-infinity
model.  The proofs are the already constructed Verdier quotient theorems,
seen through the homotopy-category identification.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The quotient functor into the homotopy category of the stable analytic
infinity model is triangulated. -/
def homotopyQuotientFunctorIsTriangulated :
    (TraceAnalyticStableInfinityCategory
      .homotopyQuotientFunctor).IsTriangulated :=
  TraceAnalyticStableMotiveCategory.quotientFunctorIsTriangulated

/-- The homotopy quotient functor's triangulated structure is the Verdier
quotient functor's triangulated structure. -/
theorem homotopyQuotientFunctorIsTriangulated_eq_stable :
    TraceAnalyticStableInfinityCategory
        .homotopyQuotientFunctorIsTriangulated =
      TraceAnalyticStableMotiveCategory.quotientFunctorIsTriangulated :=
  rfl

/-- The quotient into the stable-infinity homotopy category sends additive
distinguished triangles to distinguished triangles in that homotopy category. -/
theorem homotopyQuotientFunctor_map_distinguished
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    (TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle ∈
      TraceAnalyticStableInfinityCategory
        .homotopyCategoryDistinguishedTriangles :=
  TraceAnalyticStableMotiveCategory
    .quotientFunctor_map_distinguished triangle distinguished

/-- The stable-infinity homotopy quotient image of an additive distinguished
triangle has zero first two-fold composite. -/
theorem comp_zero₁₂_of_homotopyQuotient_distinguished
    (triangle :
      Pretriangulated.Triangle TraceAnalyticAdditiveHomotopyCategory)
    (distinguished :
      triangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles) :
    ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₁ ≫
      ((TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
        .mapTriangle.obj triangle).mor₂ =
        0 :=
  TraceAnalyticStableMotiveCategory
    .comp_zero₁₂_of_quotient_distinguished triangle distinguished

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Isomorphism.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Cofiber.Owner

/-!
# Short complexes attached to distinguished analytic stable triangles

This owner file exposes the short complex carried by a distinguished analytic
stable triangle and specializes it to the chosen cofiber triangle of a
morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to a distinguished analytic stable triangle. -/
def TraceAnalyticStableMotiveQuasicategory.shortComplexOfDistinguishedTriangle
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  Pretriangulated.shortComplexOfDistTriangle triangle distinguished

/-- The first map of the short complex attached to a distinguished triangle
is the first map of that triangle. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.shortComplexOfDistinguishedTriangle_f
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    (TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle
      triangle
      distinguished).f =
      triangle.mor₁ :=
  rfl

/-- The second map of the short complex attached to a distinguished triangle
is the second map of that triangle. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.shortComplexOfDistinguishedTriangle_g
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    (TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle
      triangle
      distinguished).g =
      triangle.mor₂ :=
  rfl

/-- The short complex attached to the chosen cofiber triangle of a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism)

/-- The first map of the chosen cofiber short complex is the original
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplex morphism).f =
      morphism :=
  rfl

/-- The second map of the chosen cofiber short complex is the chosen cofiber
cocone map. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplex morphism).g =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

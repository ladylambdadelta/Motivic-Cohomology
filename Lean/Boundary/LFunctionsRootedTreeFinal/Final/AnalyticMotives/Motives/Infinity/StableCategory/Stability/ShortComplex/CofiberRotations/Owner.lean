import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.InvRotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Rotation.Owner

/-!
# Short complexes for rotated cofiber triangles

This owner file specializes the distinguished-triangle short-complex
construction to the rotated and inverse-rotated cofiber triangles of a
morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to the rotated chosen cofiber triangle. -/
def TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
      morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle_distinguished morphism)

/-- The first map of the rotated cofiber short complex is the chosen cofiber
cocone map. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplex morphism).f =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism :=
  rfl

/-- The second map of the rotated cofiber short complex is the chosen cofiber
boundary map. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplex morphism).g =
      TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism :=
  rfl

/-- The short complex attached to the inverse-rotated chosen cofiber
triangle. -/
def TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
      morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle_distinguished morphism)

/-- The first map of the inverse-rotated cofiber short complex is the
shifted negative boundary followed by the unit comparison. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplex morphism).f =
      -((TraceAnalyticStableMotiveQuasicategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the inverse-rotated cofiber short complex is the
original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplex morphism).g =
      morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

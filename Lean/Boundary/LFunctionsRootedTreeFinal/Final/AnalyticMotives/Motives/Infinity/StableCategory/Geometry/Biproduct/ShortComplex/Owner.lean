import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Short complexes for binary biproduct triangles

This owner file specializes the distinguished-triangle short-complex
construction to binary biproduct and binary product triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to the binary biproduct triangle of two
analytic stable motives. -/
def TraceAnalyticStableMotiveQuasicategory.binaryBiproductShortComplex
    (left right : StableInfinityOwner.PresentedCategory) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductTriangle left right)
    (TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductTriangle_distinguished left right)

/-- The first map of the binary biproduct short complex is the first map of
the binary biproduct triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.binaryBiproductShortComplex_f
    (left right : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductShortComplex left right).f =
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle left right).mor₁ :=
  rfl

/-- The second map of the binary biproduct short complex is the second map of
the binary biproduct triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.binaryBiproductShortComplex_g
    (left right : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticStableMotiveQuasicategory
      .binaryBiproductShortComplex left right).g =
      (TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle left right).mor₂ :=
  rfl

/-- The short complex attached to the binary product triangle of two analytic
stable motives. -/
def TraceAnalyticStableMotiveQuasicategory.binaryProductShortComplex
    (left right : StableInfinityOwner.PresentedCategory) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory
      .binaryProductTriangle left right)
    (TraceAnalyticStableMotiveQuasicategory
      .binaryProductTriangle_distinguished left right)

/-- The first map of the binary product short complex is the first map of the
binary product triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.binaryProductShortComplex_f
    (left right : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticStableMotiveQuasicategory
      .binaryProductShortComplex left right).f =
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle left right).mor₁ :=
  rfl

/-- The second map of the binary product short complex is the second map of
the binary product triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.binaryProductShortComplex_g
    (left right : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticStableMotiveQuasicategory
      .binaryProductShortComplex left right).g =
      (TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle left right).mor₂ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

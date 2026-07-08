import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Subcategories.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Vertices.Owner

/-!
# Truncation-triangle vertices as homological subcategory objects

This file packages the first and third vertices of the analytic derived
truncation triangle as objects of the concrete homological aisle and coaisle.
-/

noncomputable section

open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The lower vertex of the analytic derived truncation triangle, regarded as
an object of the appropriate homological aisle. -/
def abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalAisle
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut) :=
  ⟨(TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₁,
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₁_homologicalLE
        cut
        complex
        hshortExact⟩

/-- The upper vertex of the analytic derived truncation triangle, regarded as
an object of the appropriate homological coaisle. -/
def abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut :=
  ⟨(TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle
        cut
        complex
        hshortExact).obj₃,
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₃_homologicalGE
        cut
        complex
        hshortExact⟩

/-- Including the lower aisle object recovers the first vertex of the derived
truncation triangle. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject_inclusion
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject
            cut
            complex
            hshortExact) =
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₁ :=
  rfl

/-- Including the upper coaisle object recovers the third vertex of the derived
truncation triangle. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject_inclusion
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut).obj
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject
            cut
            complex
            hshortExact) =
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact).obj₃ :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

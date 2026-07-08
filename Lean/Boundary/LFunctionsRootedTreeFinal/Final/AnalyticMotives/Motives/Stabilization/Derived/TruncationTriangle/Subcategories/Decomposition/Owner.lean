import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Subcategories.Owner

/-!
# Homological-subcategory form of the derived truncation triangle

This file rewrites the analytic derived truncation triangle using the lower
aisle object and upper coaisle object as its first and third vertices.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The ambient derived object underlying the lower aisle vertex of the
analytic derived truncation triangle. -/
def abelianEnvelopeCochainDecompositionDerivedLowerVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory :=
  (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).obj
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangleLowerAisleObject
          cut
          complex
          hshortExact)

/-- The ambient derived object underlying the upper coaisle vertex of the
analytic derived truncation triangle. -/
def abelianEnvelopeCochainDecompositionDerivedUpperVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory :=
  (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion cut).obj
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangleUpperCoaisleObject
          cut
          complex
          hshortExact)

/-- The middle vertex of the analytic derived truncation triangle. -/
def abelianEnvelopeCochainDecompositionDerivedMiddleVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticDerivedMotiveCategory :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      hshortExact).obj₂

/-- The lower map from the aisle vertex to the middle vertex. -/
def abelianEnvelopeCochainDecompositionDerivedLowerMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedLowerVertex
          cut
          complex
          hshortExact ⟶
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedMiddleVertex
          cut
          complex
          hshortExact :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      hshortExact).mor₁

/-- The upper map from the middle vertex to the coaisle vertex. -/
def abelianEnvelopeCochainDecompositionDerivedUpperMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedMiddleVertex
          cut
          complex
          hshortExact ⟶
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedUpperVertex
          cut
          complex
          hshortExact :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      hshortExact).mor₂

/-- The connecting map from the coaisle vertex to the shifted aisle vertex. -/
def abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedUpperVertex
          cut
          complex
          hshortExact ⟶
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedLowerVertex
          cut
          complex
          hshortExact)⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      hshortExact).mor₃

/-- The analytic derived truncation triangle written with its aisle and
coaisle vertices exposed through the full-subcategory inclusions. -/
def abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  Triangle.mk
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedLowerMap
        cut
        complex
        hshortExact)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedUpperMap
        cut
        complex
        hshortExact)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
        cut
        complex
        hshortExact)

/-- The subcategory-exposed truncation triangle is definitionally the original
derived truncation triangle. -/
theorem abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
          cut
          complex
          hshortExact =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          hshortExact :=
  rfl

/-- The subcategory-exposed analytic derived truncation triangle is
distinguished. -/
theorem abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangle
          cut
          complex
          hshortExact ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle_distinguished
      cut
      complex
      hshortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

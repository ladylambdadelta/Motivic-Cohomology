import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.HomotopyMap.Owner

/-!
# Verdier inversion criterion for the normalized cone comparison

This file identifies the actual mapping-cone triangle of the normalized
cone-to-upper comparison map and proves that nullity of its third vertex puts
the comparison map in the Verdier inverted morphism class.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The additive homotopy mapping-cone triangle of the normalized
cone-to-upper comparison map. -/
def additiveNormalizedConeComparisonTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  CochainComplex.mappingCone.triangleh
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex)

/-- The first morphism of the cone-comparison triangle is the additive
homotopy cone-to-upper comparison map. -/
theorem additiveNormalizedConeComparisonTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle
      cut
      complex).mor₁ =
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex :=
  rfl

/-- The cone-comparison triangle is distinguished in the additive homotopy
category. -/
theorem additiveNormalizedConeComparisonTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle
        cut
        complex ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.mappingCone_triangle_distinguished
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
      cut
      complex)

/-- If the cone of the normalized additive cone-to-upper comparison is null,
then that comparison map belongs to the Verdier inverted morphism class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_nullCone
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (nullCone :
      TraceAnalyticStableNullSubcategory.P
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle
          cut
          complex).obj₃) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  Eq.subst
    (motive :=
      fun hom =>
        TraceAnalyticStableNullSubcategory.invertedMorphisms hom)
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle_mor₁
      cut
      complex)
    (TraceAnalyticStableNullSubcategory.inverted_firstMap_of_triangle
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle_distinguished
        cut
        complex)
      nullCone)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

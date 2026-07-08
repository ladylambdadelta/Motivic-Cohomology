import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.ConeVertex.Owner

/-!
# Stable truncation cone vertex

This file names the third vertex and remaining two morphisms of the stable
lower-inclusion triangle.  These are the concrete objects and maps that must
be compared with the upper truncation side of the decomposition triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The cone vertex of the stable lower-inclusion truncation triangle. -/
def stableLowerInclusionConeVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticStableMotiveCategory :=
  (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
    cut
    complex).obj₃

/-- The second morphism of the stable lower-inclusion truncation triangle. -/
def stableLowerInclusionConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
      TraceAnalyticMotivicTStructure.stableLowerInclusionConeVertex
        cut
        complex :=
  (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
    cut
    complex).mor₂

/-- The connecting morphism from the cone vertex to the shifted lower
truncation. -/
def stableLowerInclusionConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionConeVertex
        cut
        complex ⟶
      (TraceAnalyticMotivicTStructure.stableTruncLE cut complex)⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
    cut
    complex).mor₃

/-- Projection formula for the stable lower-inclusion cone vertex. -/
theorem stableLowerInclusionConeVertex_eq_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionConeVertex
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).obj₃ :=
  rfl

/-- The third vertex of the stable lower-inclusion triangle is the named cone
vertex. -/
theorem stableLowerInclusionTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).obj₃ =
      TraceAnalyticMotivicTStructure.stableLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- Projection formula for the stable lower-inclusion cone map. -/
theorem stableLowerInclusionConeMap_eq_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionConeMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).mor₂ :=
  rfl

/-- The second map of the stable lower-inclusion triangle is the named cone
map. -/
theorem stableLowerInclusionTriangle_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).mor₂ =
      TraceAnalyticMotivicTStructure.stableLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The stable lower-inclusion cone map is the Verdier quotient image of the
additive lower-inclusion cone map. -/
theorem stableLowerInclusionConeMap_eq_mapOf_additiveLowerInclusionConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionConeMap
        cut
        complex =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveLowerInclusionConeMap
          cut
          complex) :=
  rfl

/-- Projection formula for the stable lower-inclusion connecting map. -/
theorem stableLowerInclusionConnectingMap_eq_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableLowerInclusionConnectingMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).mor₃ :=
  rfl

/-- The third map of the stable lower-inclusion triangle is the named
connecting map. -/
theorem stableLowerInclusionTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableLowerInclusionTriangle
        cut
        complex).mor₃ =
      TraceAnalyticMotivicTStructure.stableLowerInclusionConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

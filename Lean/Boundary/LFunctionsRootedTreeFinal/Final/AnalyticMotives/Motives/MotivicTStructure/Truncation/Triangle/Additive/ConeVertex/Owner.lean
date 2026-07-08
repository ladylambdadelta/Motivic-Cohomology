import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Owner

/-!
# Additive truncation cone vertex

This file names the third vertex and remaining two morphisms of the additive
lower-inclusion mapping-cone triangle.  These are the additive-level data from
which the cone-to-upper comparison should be proved before Verdier
localization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The cone vertex of the additive lower-inclusion truncation triangle. -/
def additiveLowerInclusionConeVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
    cut
    complex).obj₃

/-- The cone map from the original complex to the additive lower-inclusion
cone vertex. -/
def additiveLowerInclusionConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
        cut
        complex :=
  (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
    cut
    complex).mor₂

/-- The additive connecting morphism from the cone vertex to the shifted lower
truncation. -/
def additiveLowerInclusionConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
        cut
        complex ⟶
      (TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex)⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
    cut
    complex).mor₃

/-- Projection formula for the additive lower-inclusion cone vertex. -/
theorem additiveLowerInclusionConeVertex_eq_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).obj₃ :=
  rfl

/-- The third vertex of the additive lower-inclusion triangle is the named
cone vertex. -/
theorem additiveLowerInclusionTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).obj₃ =
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- Projection formula for the additive lower-inclusion cone map. -/
theorem additiveLowerInclusionConeMap_eq_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerInclusionConeMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).mor₂ :=
  rfl

/-- The second map of the additive lower-inclusion triangle is the named cone
map. -/
theorem additiveLowerInclusionTriangle_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).mor₂ =
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- Projection formula for the additive lower-inclusion connecting map. -/
theorem additiveLowerInclusionConnectingMap_eq_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerInclusionConnectingMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).mor₃ :=
  rfl

/-- The third map of the additive lower-inclusion triangle is the named
connecting map. -/
theorem additiveLowerInclusionTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex).mor₃ =
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

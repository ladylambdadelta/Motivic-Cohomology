import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.ConeVertex.Owner

/-!
# Additive lower-inclusion truncation short complex

This file extracts the short complex attached to the additive lower-inclusion
distinguished triangle and exposes its object and morphism projections.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The short complex attached to the additive lower-inclusion distinguished
triangle. -/
def additiveLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle_distinguished
      cut
      complex)

/-- The first object of the additive lower-inclusion short complex is the
homotopy lower truncation. -/
theorem additiveLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticMotivicTStructure.homotopyTruncLE cut complex :=
  rfl

/-- The second object of the additive lower-inclusion short complex is the
original complex in the homotopy category. -/
theorem additiveLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex :=
  rfl

/-- The third object of the additive lower-inclusion short complex is the named
cone vertex. -/
theorem additiveLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- The first map of the additive lower-inclusion short complex is the homotopy
lower truncation inclusion. -/
theorem additiveLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap
        cut
        complex :=
  TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle_mor₁
    cut
    complex

/-- The second map of the additive lower-inclusion short complex is the named
cone map. -/
theorem additiveLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.additiveLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The additive lower-inclusion map followed by its cone map is zero. -/
theorem additiveLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.additiveLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.Owner

/-!
# Degreewise bounded representative truncation triangles

This file records the stable truncation triangle available for a concrete
degreewise iso-closure bounded cochain representative.  It is the owner-level
bridge between the analytic cochain-decomposition triangle and the
degreewise-bounded stable source: the lower and upper truncation vertices are
proved to remain in the degreewise-bounded stable predicate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The lower vertex of the transported truncation triangle is degreewise
iso-closure bounded whenever the input representative is. -/
theorem degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_bounded
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex).obj₁ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_raw_obj₁ cut complex))
    (TraceAnalyticMotivicTStructure
      .stableTruncLE_degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex
        bounded)

/-- The upper vertex of the transported truncation triangle is degreewise
iso-closure bounded whenever the input representative is. -/
theorem degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_bounded
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex).obj₃ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_raw_obj₃ cut complex))
    (TraceAnalyticMotivicTStructure
      .stableTruncGE_degreewiseIsoClosureBoundedStableObject
        cut
        complex
        bounded)

/-- The lower vertex of the transported truncation triangle satisfies the
degreewise support-based `LE` predicate. -/
theorem degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_supportedLE
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEAmbient
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex).obj₁ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_raw_obj₁ cut complex))
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .stableTruncLE_mem_supportedLEAmbient
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex
        bounded)

/-- The upper vertex of the transported truncation triangle satisfies the
degreewise support-based `GE` predicate. -/
theorem degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_supportedGE
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEAmbient
        cut
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex).obj₃ :=
  Eq.subst
    (motive := fun object =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient cut object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_raw_obj₃ cut complex))
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .stableTruncGE_mem_supportedGEAmbient
        cut
        complex
        bounded)

/-- Concrete stable truncation-triangle certificate for a degreewise
iso-closure bounded cochain representative. -/
theorem degreewiseRepresentative_stableCochainDecompositionTriangle_certificate
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex).obj₁ ∧
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportedLEAmbient
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle cut complex).obj₁ ∧
      TraceAnalyticDMgmComparisonSource
          .degreewiseIsoClosureBoundedStableObject
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle cut complex).obj₃ ∧
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
            .supportedGEAmbient
              cut
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle cut complex).obj₃ ∧
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex).obj₂ =
            TraceAnalyticDMgmComparisonSource.objectOf
              (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ∧
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle cut complex) ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_bounded
        cut
        complex
        bounded)
    (And.intro
      (TraceAnalyticMotivicTStructure
        .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_supportedLE
          cut
          complex
          bounded)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_bounded
            cut
            complex
            bounded)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_supportedGE
              cut
              complex
              bounded)
          (And.intro
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle_raw_obj₂ cut complex)
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle_distinguished
                cut
                complex)))))

/-- Existential form of the degreewise representative stable truncation
triangle, with the chosen lower and upper vertices explicitly bounded. -/
theorem degreewiseRepresentative_exists_bounded_stable_truncation_triangle
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource),
      TraceAnalyticDMgmComparisonSource
          .degreewiseIsoClosureBoundedStableObject lower ∧
        TraceAnalyticDMgmComparisonSource
            .degreewiseIsoClosureBoundedStableObject upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDMgmComparisonSource.objectOf
                  (TraceAnalyticAdditiveHomotopyCategory.objectOf complex))
            (secondMap :
              TraceAnalyticDMgmComparisonSource.objectOf
                  (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let triangle :
      Triangle TraceAnalyticStableMotiveCategory :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex
  Exists.intro
    triangle.obj₁
    (Exists.intro
      triangle.obj₃
      (And.intro
        (TraceAnalyticMotivicTStructure
          .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₁_bounded
            cut
            complex
            bounded)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .degreewiseRepresentative_stableCochainDecompositionTriangle_obj₃_bounded
              cut
              complex
              bounded)
          (Exists.intro
            triangle.mor₁
            (Exists.intro
              triangle.mor₂
              (Exists.intro
                triangle.mor₃
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle_distinguished
                    cut
                    complex)))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

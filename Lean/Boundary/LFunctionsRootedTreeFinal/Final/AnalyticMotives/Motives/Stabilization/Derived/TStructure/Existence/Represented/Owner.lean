import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Subcategories.Decomposition.FromDegreewise.Owner

/-!
# Represented-object truncation existence for the derived analytic t-structure

This file packages the degreewise-exact analytic truncation calculus in the
existential shape required by the truncation-existence field of a t-structure,
for represented derived analytic motives.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness of the analytic Yoneda truncation sequence gives the
represented-object derived truncation-existence statement at `cut`. -/
theorem representedDerived_exists_truncation_triangle_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap :
              lower ⟶
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
                    cut
                    complex
                    hdegree).obj₂)
            (secondMap :
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
                  cut
                  complex
                  hdegree).obj₂ ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  ⟨TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedLowerVertex
        cut
        complex
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
            cut
            complex
            hdegree),
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDerivedUpperVertex
        cut
        complex
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
            cut
            complex
            hdegree),
    And.intro
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₁_homologicalLE
          cut
          complex
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
              cut
              complex
              hdegree))
      (And.intro
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDerivedTriangle_obj₃_homologicalGE
            cut
            complex
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
                cut
                complex
                hdegree))
        ⟨TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedLowerMap
              cut
              complex
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
                  cut
                  complex
                  hdegree),
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedUpperMap
              cut
              complex
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
                  cut
                  complex
                  hdegree),
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedConnectingMapFromSubcategories
              cut
              complex
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
                  cut
                  complex
                  hdegree),
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionDerivedSubcategoryTriangleOfDegreewise_distinguished
              cut
              complex
              hdegree⟩)⟩

/-- The represented-object truncation-existence theorem at cut `0`, in the
adjacent `≤ 0` and `≥ 1` field shape after the normalization
`decompositionLowerCut 1 = 0`. -/
theorem representedDerived_exists_triangle_zero_one_of_degreewise
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper ∧
          ∃ (firstMap :
              lower ⟶
                (TraceAnalyticMotivicTStructure
                  .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
                    1
                    complex
                    hdegree).obj₂)
            (secondMap :
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
                  1
                  complex
                  hdegree).obj₂ ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .representedDerived_exists_truncation_triangle_of_degreewise
      1
      complex
      hdegree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

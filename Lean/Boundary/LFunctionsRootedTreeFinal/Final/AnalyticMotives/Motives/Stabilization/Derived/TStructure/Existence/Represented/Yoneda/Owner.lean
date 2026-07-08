import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Owner

/-!
# Yoneda-represented truncation existence for the derived analytic t-structure

This file rewrites the represented-object truncation existence theorem with
middle vertex the derived object represented by the Yoneda abelian-envelope
cochain complex of the input additive complex.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness gives a truncation triangle for the derived object
represented by the Yoneda abelian-envelope cochain complex of `complex`. -/
theorem yonedaRepresentedDerived_exists_truncation_triangle_of_degreewise
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
                TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex))
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .representedDerived_exists_truncation_triangle_of_degreewise
      cut
      complex
      hdegree

/-- The normalized adjacent truncation triangle for the derived object
represented by the Yoneda abelian-envelope cochain complex of `complex`. -/
theorem yonedaRepresentedDerived_exists_triangle_zero_one_of_degreewise
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
                TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex))
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .yonedaRepresentedDerived_exists_truncation_triangle_of_degreewise
      1
      complex
      hdegree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

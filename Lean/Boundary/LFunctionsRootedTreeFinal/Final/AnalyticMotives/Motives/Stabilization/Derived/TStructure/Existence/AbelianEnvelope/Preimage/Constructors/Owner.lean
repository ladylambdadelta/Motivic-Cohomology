import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.Componentwise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.FromProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.AbelianEnvelope.Preimage.Owner

/-!
# Concrete constructors for preimage truncation existence

This file composes the intrinsic abelian-envelope exactness assembly theorems
with the arbitrary-object cochain-preimage truncation theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Degreewise intrinsic exactness plus degreewise mono and epi fields for the
canonical cochain preimage give the object-level truncation triangle for an
arbitrary derived analytic motive. -/
theorem cochainPreimage_exists_truncation_triangle_of_degreewise_exact_mono_epi
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory
                .cochainPreimage object)).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hmono :
      ∀ degree : ℤ,
        Mono
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory
                  .cochainPreimage object)).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory
                  .cochainPreimage object)).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle
      cut
      object
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
          cut
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hexact
          hmono
          hepi)

/-- Probe-degree intrinsic exactness plus probe-degree mono and epi fields for
the canonical cochain preimage give the object-level truncation triangle for an
arbitrary derived analytic motive. -/
theorem cochainPreimage_exists_truncation_triangle_of_degreewise_exact_probe_mono_epi
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory
                .cochainPreimage object)).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hmono :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Mono
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).f))
    (hepi :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle
      cut
      object
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
          cut
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hexact
          hmono
          hepi)

/-- Probe-degree lower-tail/off-tail casewise intrinsic exactness, lower-tail
monicity, and off-tail epicity for the canonical cochain preimage give the
object-level truncation triangle for an arbitrary derived analytic motive. -/
theorem cochainPreimage_exists_truncation_triangle_of_probeDegree_casewise
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle
      cut
      object
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

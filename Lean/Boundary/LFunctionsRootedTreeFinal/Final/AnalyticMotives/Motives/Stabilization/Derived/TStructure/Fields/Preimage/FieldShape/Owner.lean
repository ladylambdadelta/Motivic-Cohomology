import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.AbelianEnvelope.Preimage.FieldShape.Owner

/-!
# Field-shape constructor surface for canonical cochain-preimage truncations

This file exposes the normalized Mathlib-field-order truncation existence
constructors for arbitrary derived objects through their canonical
abelian-envelope cochain preimage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

/-- Intrinsic short exactness for the canonical cochain preimage gives the
adjacent Mathlib-field-order truncation triangle for an arbitrary derived
analytic motive. -/
theorem derivedTStructure_cochainPreimage_exists_triangle_zero_one_fieldShape
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_triangle_zero_one_fieldShape
      object
      hshortExact

/-- Degreewise intrinsic exactness plus degreewise mono and epi fields for the
canonical cochain preimage give the adjacent Mathlib-field-order truncation
triangle for an arbitrary derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_mono_epi
    (object : TraceAnalyticDerivedMotiveCategory)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
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
                1
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
                1
                (TraceAnalyticDerivedMotiveCategory
                  .cochainPreimage object)).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_mono_epi
      object
      hexact
      hmono
      hepi

/-- Degreewise intrinsic exactness plus probe-degree mono and epi fields for
the canonical cochain preimage give the adjacent Mathlib-field-order
truncation triangle for an arbitrary derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_probe_mono_epi
    (object : TraceAnalyticDerivedMotiveCategory)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
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
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).f))
    (hepi :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_probe_mono_epi
      object
      hexact
      hmono
      hepi

/-- Probe-degree lower-tail/off-tail casewise intrinsic exactness,
lower-tail monicity, and off-tail epicity for the canonical cochain preimage
give the arbitrary-cut Mathlib-field-order truncation triangle for an arbitrary
derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
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
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
      cut
      object
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Probe-degree lower-tail/off-tail casewise intrinsic exactness,
lower-tail monicity, and off-tail epicity for the canonical cochain preimage
give the adjacent Mathlib-field-order truncation triangle for an arbitrary
derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_exists_triangle_zero_one_fieldShape_of_probeDegree_casewise
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .derivedTStructure_cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
      1
      object
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary

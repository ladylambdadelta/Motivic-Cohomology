import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.AbelianEnvelope.Preimage.Constructors.Owner

/-!
# Field-shape preimage truncation existence

This file rewrites the arbitrary-object cochain-preimage truncation theorem in
the binder order used by Mathlib's `TStructure.exists_triangle_zero_one` field.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic short exactness for the canonical cochain preimage gives the
Mathlib-field-order truncation triangle for an arbitrary derived analytic
motive. -/
theorem cochainPreimage_exists_truncation_triangle_fieldShape
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
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
  Exists.elim
    (TraceAnalyticMotivicTStructure
      .cochainPreimage_exists_truncation_triangle
        cut
        object
        hshortExact)
    (fun lower lowerResult =>
      Exists.elim lowerResult
        (fun upper membershipAndTriangle =>
          And.elim membershipAndTriangle
            (fun lowerMembership upperAndTriangle =>
              And.elim upperAndTriangle
                (fun upperMembership triangleExists =>
                  Exists.elim triangleExists
                    (fun firstMap secondAndConnecting =>
                      Exists.elim secondAndConnecting
                        (fun secondMap connectingAndDistinguished =>
                          Exists.elim connectingAndDistinguished
                            (fun connectingMap distinguished =>
                              Exists.intro
                                lower
                                (Exists.intro
                                  upper
                                  (Exists.intro
                                    lowerMembership
                                    (Exists.intro
                                      upperMembership
                                      (Exists.intro
                                        firstMap
                                        (Exists.intro
                                          secondMap
                                          (Exists.intro
                                            connectingMap
                                            distinguished))))))))))))

/-- Normalized intrinsic short exactness for the canonical cochain preimage
gives the exact Mathlib `exists_triangle_zero_one` field shape for an arbitrary
derived analytic motive. -/
theorem cochainPreimage_exists_triangle_zero_one_fieldShape
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
    .cochainPreimage_exists_truncation_triangle_fieldShape
      1
      object
      hshortExact

/-- Degreewise exactness, mono, and epi fields for the canonical cochain
preimage give the exact Mathlib field shape for arbitrary-object truncation
existence. -/
theorem cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_mono_epi
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
    .cochainPreimage_exists_triangle_zero_one_fieldShape
      object
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hexact
          hmono
          hepi)

/-- Degreewise exactness, together with probe-degree mono and epi fields for
the canonical cochain preimage, gives the exact Mathlib field shape for
arbitrary-object truncation existence. -/
theorem cochainPreimage_exists_triangle_zero_one_fieldShape_of_degreewise_exact_probe_mono_epi
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
    .cochainPreimage_exists_triangle_zero_one_fieldShape
      object
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hexact
          hmono
          hepi)

/-- Probe-degree lower-tail/off-tail casewise intrinsic exactness,
lower-tail monicity, and off-tail epicity for the canonical cochain preimage
give the exact Mathlib field shape for arbitrary-object truncation existence. -/
theorem cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
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
    .cochainPreimage_exists_truncation_triangle_fieldShape
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

/-- Probe-degree lower-tail/off-tail casewise intrinsic exactness,
lower-tail monicity, and off-tail epicity for the canonical cochain preimage
give the exact adjacent Mathlib field shape for arbitrary-object truncation
existence. -/
theorem cochainPreimage_exists_triangle_zero_one_fieldShape_of_probeDegree_casewise
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
    .cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
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

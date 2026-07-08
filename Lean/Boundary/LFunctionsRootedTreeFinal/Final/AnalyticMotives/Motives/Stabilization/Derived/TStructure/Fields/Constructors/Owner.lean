import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.CochainShortExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.Degreewise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.ProbeDegreeCasewise.Owner

/-!
# Constructor field surface for represented derived analytic truncations

This file exposes the concrete constructor routes into the public represented
Yoneda truncation predicate used by the derived analytic t-structure field
surface.
-/

noncomputable section

open CategoryTheory
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives
namespace TraceAnalyticMotivicTStructure

/-- Constructor field from degreewise short exactness to the public Yoneda
truncation representative predicate. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOfDegreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (degreewiseShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfDegreewise
      cut
      complex
      hasHomology
      degreewiseShortExact

/-- Normalized constructor field from degreewise short exactness to the public
Yoneda truncation representative predicate at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOneOfDegreewise
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (degreewiseShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      1
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOneOfDegreewise
      complex
      hasHomology
      degreewiseShortExact

/-- Constructor field from cochain-level short exactness to the public Yoneda
truncation representative predicate. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOfCochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (cochainShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfCochainShortExact
      cut
      complex
      hasHomology
      cochainShortExact

/-- Normalized constructor field from cochain-level short exactness to the
public Yoneda truncation representative predicate at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOneOfCochainShortExact
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (cochainShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex)) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      1
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOneOfCochainShortExact
      complex
      hasHomology
      cochainShortExact

/-- Constructor field from probe-degree analytic data to the public Yoneda
truncation representative predicate. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOfProbeDegreeCasewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfProbeDegreeCasewise
      cut
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Normalized constructor field from probe-degree analytic data to the public
Yoneda truncation representative predicate at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentativeOneOfProbeDegreeCasewise
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              (1 - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                (1 - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                degree).g) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      1
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOneOfProbeDegreeCasewise
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

end TraceAnalyticMotivicTStructure
end AnalyticMotives
end LFunctions
end Boundary

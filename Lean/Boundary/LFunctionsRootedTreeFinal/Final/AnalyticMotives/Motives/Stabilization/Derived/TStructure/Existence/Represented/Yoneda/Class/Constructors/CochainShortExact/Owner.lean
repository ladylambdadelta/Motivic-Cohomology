import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.Degreewise.Owner

/-!
# Cochain short-exact constructors for Yoneda truncation representatives

This file turns cochain-level short exactness of the analytic abelian-envelope
truncation sequence into the public `HasYonedaTruncationRepresentative`
predicate by using the proved equivalence with degreewise short exactness.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Cochain-level short exactness of the analytic truncation sequence gives
the public Yoneda truncation representative predicate for the represented
derived object. -/
theorem hasYonedaTruncationRepresentativeOfCochainShortExact
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
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfDegreewise
      cut
      complex
      hasHomology
      ((TraceAnalyticAbelianCochainComplex
        .shortExact_iff_degreewise_shortExact
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionShortComplex
              cut
              complex)).mp cochainShortExact)

/-- Normalized cut-`1` constructor from cochain-level short exactness. -/
theorem hasYonedaTruncationRepresentativeOneOfCochainShortExact
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
    .hasYonedaTruncationRepresentativeOfCochainShortExact
      1
      complex
      hasHomology
      cochainShortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

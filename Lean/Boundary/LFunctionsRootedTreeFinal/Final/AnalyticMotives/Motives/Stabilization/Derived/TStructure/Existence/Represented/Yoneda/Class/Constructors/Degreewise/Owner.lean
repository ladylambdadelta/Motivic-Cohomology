import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Owner

/-!
# Degreewise constructors for Yoneda truncation representatives

This file turns the concrete degreewise analytic truncation exactness input
into the public `HasYonedaTruncationRepresentative` predicate for the derived
object represented by the corresponding Yoneda abelian-envelope cochain
complex.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness of the analytic truncation sequence gives the public
Yoneda truncation representative predicate for the represented derived
object. -/
theorem hasYonedaTruncationRepresentativeOfDegreewise
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
  Nonempty.intro
    (TraceAnalyticMotivicTStructure
      .yonedaTruncationRepresentativeOfDegreewise
        cut
        complex
        hasHomology
        degreewiseShortExact)

/-- Normalized cut-`1` constructor for the public Yoneda truncation
representative predicate of a represented derived object. -/
theorem hasYonedaTruncationRepresentativeOneOfDegreewise
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
  TraceAnalyticMotivicTStructure.hasYonedaTruncationRepresentativeOfDegreewise
    1
    complex
    hasHomology
    degreewiseShortExact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

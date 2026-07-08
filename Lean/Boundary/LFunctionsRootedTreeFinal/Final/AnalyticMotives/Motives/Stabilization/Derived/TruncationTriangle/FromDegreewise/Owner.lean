import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Owner

/-!
# Derived truncation triangle from degreewise exactness

This file turns degreewise short exactness of the Yoneda abelian-envelope
truncation sequence into the distinguished derived truncation triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The cochain-level short exactness witness assembled from degreewise short
exactness for the Yoneda abelian-envelope truncation sequence. -/
def abelianEnvelopeCochainDecompositionShortExactFromDegreewise
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
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortComplex cut complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionShortExact_of_degreewise
      cut
      complex
      hdegree

/-- The derived truncation triangle obtained directly from degreewise short
exactness. -/
def abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
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
    Triangle TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

/-- The degreewise-derived truncation triangle is the short-exact-sequence
derived triangle for the assembled cochain-level short exactness witness. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise_eq
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
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
          cut
          complex
          hdegree =
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangle
          cut
          complex
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
              cut
              complex
              hdegree) :=
  rfl

/-- Degreewise short exactness gives a distinguished derived analytic
truncation triangle. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise_distinguished
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
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangleOfDegreewise
          cut
          complex
          hdegree ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle_distinguished
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromDegreewise
          cut
          complex
          hdegree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

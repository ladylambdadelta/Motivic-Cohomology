import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Evaluation.ProbeDegree.Owner

/-!
# Intrinsic probe-degree exactness from cochain exactness

This file specializes the abelian cochain-complex probe-degree evaluation
theorem to the intrinsic abelian-envelope normalized truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the intrinsic abelian-envelope truncation decomposition is exact as a
short complex of cochain complexes, then its iterated degree/probe evaluation is
exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionExact_iteratedProbeDegreeEvaluation
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (((TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  TraceAnalyticAbelianCochainComplex.exact_probeDegreeEvaluation
    probe
    degree
    hexact

/-- If the intrinsic abelian-envelope truncation decomposition is short exact as
a short complex of cochain complexes, then its iterated degree/probe evaluation
is short exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (((TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).ShortExact :=
  TraceAnalyticAbelianCochainComplex.shortExact_probeDegreeEvaluation
    probe
    degree
    hshortExact

/-- If the intrinsic abelian-envelope truncation decomposition is short exact as
a short complex of cochain complexes, then its iterated degree/probe evaluation
is exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_iteratedProbeDegreeEvaluation_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (((TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  (abelianEnvelopeIntrinsicCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
    cut
    complex
    probe
    degree
    hshortExact).exact

/-- The named intrinsic probe-degree short complex agrees definitionally with
the iterated degree evaluation followed by analytic probe evaluation. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).map
        (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe) :=
  rfl

/-- If the intrinsic abelian-envelope truncation decomposition is short exact as
a short complex of cochain complexes, then the named intrinsic probe-degree
short complex is short exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).ShortExact :=
  Eq.ndrec
    (motive := fun shortComplex => shortComplex.ShortExact)
    (abelianEnvelopeIntrinsicCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
      cut
      complex
      probe
      degree
      hshortExact)
    (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
      cut
      complex
      probe
      degree).symm

/-- If the intrinsic abelian-envelope truncation decomposition is exact as a
short complex of cochain complexes, then the named intrinsic probe-degree short
complex is exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_cochainExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  Eq.ndrec
    (motive := fun shortComplex => shortComplex.Exact)
    (abelianEnvelopeIntrinsicCochainDecompositionExact_iteratedProbeDegreeEvaluation
      cut
      complex
      probe
      degree
      hexact)
    (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
      cut
      complex
      probe
      degree).symm

/-- If the intrinsic abelian-envelope truncation decomposition is short exact as
a short complex of cochain complexes, then the named intrinsic probe-degree
short complex is exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_cochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            cut
            complex)) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    hshortExact).exact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

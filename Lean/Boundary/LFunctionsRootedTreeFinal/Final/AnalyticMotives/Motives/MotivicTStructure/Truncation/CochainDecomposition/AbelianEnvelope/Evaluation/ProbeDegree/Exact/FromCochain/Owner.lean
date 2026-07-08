import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Evaluation.ProbeDegree.Owner

/-!
# Probe-degree exactness from cochain short exactness

This file specializes the abelian cochain-complex evaluation theorem to the
actual Yoneda image of the normalized truncation decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the Yoneda abelian-envelope truncation decomposition is exact as a short
complex of cochain complexes, then its iterated degree/probe evaluation is exact
in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionExact_iteratedProbeDegreeEvaluation
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
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

/-- If the Yoneda abelian-envelope truncation decomposition is short exact as a
short complex of cochain complexes, then its iterated degree/probe evaluation is
short exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
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

/-- If the Yoneda abelian-envelope truncation decomposition is short exact as a
short complex of cochain complexes, then its iterated degree/probe evaluation is
exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionShortExact_iteratedProbeDegreeEvaluation_exact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).map
      (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe)).Exact :=
  (abelianEnvelopeCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
    cut
    complex
    probe
    degree
    hshortExact).exact

/-- The named composed probe-degree short complex agrees definitionally with
the iterated degree evaluation followed by analytic probe evaluation. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree =
      ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).map
        (TraceAnalyticAdditiveAbelianEnvelope.evaluation probe) :=
  rfl

/-- If the Yoneda abelian-envelope truncation decomposition is short exact as a
short complex of cochain complexes, then the named composed probe-degree short
complex is short exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  Eq.ndrec
    (motive := fun shortComplex => shortComplex.ShortExact)
    (abelianEnvelopeCochainDecompositionShortExact_iteratedProbeDegreeEvaluation
      cut
      complex
      probe
      degree
      hshortExact)
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
      cut
      complex
      probe
      degree).symm

/-- If the Yoneda abelian-envelope truncation decomposition is short exact as a
short complex of cochain complexes, then the named composed probe-degree short
complex is exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_cochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    hshortExact).exact

/-- If the Yoneda abelian-envelope truncation decomposition is exact as a short
complex of cochain complexes, then the named composed probe-degree short
complex is exact in `ModuleCat Rat`. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_cochainExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  Eq.ndrec
    (motive := fun shortComplex => shortComplex.Exact)
    (abelianEnvelopeCochainDecompositionExact_iteratedProbeDegreeEvaluation
      cut
      complex
      probe
      degree
      hexact)
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_eq_iteratedMap
      cut
      complex
      probe
      degree).symm

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

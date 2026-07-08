import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.ProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.IsIso.CaseSplit.Owner

/-!
# Degreewise abelian-envelope exactness from probe-degree isomorphism formulas

This file lifts the concrete probe-degree lower-tail and off-lower-tail
isomorphism formulas to degreewise exactness of the abelian-envelope
truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Concrete lower-tail and off-lower-tail probe-degree isomorphism formulas
prove degreewise exactness of the Yoneda abelian-envelope truncation short
complex. -/
theorem abelianEnvelopeCochainDecompositionDegreeExact_of_probeDegreeIsoHom_caseSplit
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerIso :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (lowerTail : ℕ),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₁ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₂)
    (lowerMap :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (lowerTail : ℕ),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f =
          (lowerIso probe lowerTail).hom)
    (offIso :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (degree : ℤ),
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₂ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₃)
    (offMap :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject)
        (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g =
          (offIso probe degree hnone).hom)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex).map
      (HomologicalComplex.eval
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        degree)).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDegreeExact_of_probeDegreeExact
      cut
      complex
      (fun probe degree =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionProbeDegreeExact_of_isoHom_caseSplit
            cut
            complex
            probe
            (lowerIso probe)
            (lowerMap probe)
            (offIso probe)
            (offMap probe)
            degree)
      degree

/-- Concrete lower-tail and off-lower-tail probe-degree isomorphism formulas
prove cochain-level exactness of the Yoneda abelian-envelope truncation short
complex. -/
theorem abelianEnvelopeCochainDecompositionExact_of_probeDegreeIsoHom_caseSplit
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (lowerIso :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (lowerTail : ℕ),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₁ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).X₂)
    (lowerMap :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (lowerTail : ℕ),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f =
          (lowerIso probe lowerTail).hom)
    (offIso :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject) (degree : ℤ),
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₂ ≅
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).X₃)
    (offMap :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject)
        (degree : ℤ)
        (hnone :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none),
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g =
          (offIso probe degree hnone).hom) :
    TraceAnalyticAbelianCochainComplex.exact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionExact_of_degreewise
      cut
      complex
      (fun degree =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDegreeExact_of_probeDegreeIsoHom_caseSplit
            cut
            complex
            lowerIso
            lowerMap
            offIso
            offMap
            degree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

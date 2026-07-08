import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.EpiMono.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Support.Owner

/-!
# Probe-degree evaluation of the abelian-envelope truncation short complex

This file reduces the abelian-envelope truncation short complex to concrete
Q-module short complexes by evaluating first at a cochain degree and then at an
analytic additive probe, and exposes the support, exactness, epi/mono, and
short-exactness calculus for those evaluated complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Evaluation of an abelian-envelope analytic cochain complex at a cochain
degree and analytic additive probe. -/
def abelianEnvelopeCochainProbeDegreeEvaluation
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    TraceAnalyticAbelianCochainComplex ⥤ ModuleCat Rat :=
  HomologicalComplex.eval
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      degree ⋙
    TraceAnalyticAdditiveAbelianEnvelope.evaluation probe

/-- Probe-degree evaluation sends a complex to the value of its degree object
at the probe. -/
theorem abelianEnvelopeCochainProbeDegreeEvaluation_obj
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainProbeDegreeEvaluation
      probe
      degree).obj complex =
      (complex.X degree).obj (Opposite.op probe) :=
  rfl

/-- Probe-degree evaluation sends a chain map to its degree component evaluated
at the probe. -/
theorem abelianEnvelopeCochainProbeDegreeEvaluation_map
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainProbeDegreeEvaluation
      probe
      degree).map hom =
      (hom.f degree).app (Opposite.op probe) :=
  rfl

/-- The Q-module short complex obtained by evaluating the abelian-envelope
truncation decomposition at one analytic probe and cochain degree. -/
def abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    ShortComplex (ModuleCat Rat) :=
  (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
    cut
    complex).map
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainProbeDegreeEvaluation
        probe
        degree)

/-- The first Q-module in the probe-degree short complex is the represented
hom module into the lower truncation degree object. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).X₁ =
      ModuleCat.of Rat
        (probe ⟶
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex).X degree) :=
  rfl

/-- The middle Q-module in the probe-degree short complex is the represented
hom module into the original degree object. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).X₂ =
      ModuleCat.of Rat
        (probe ⟶ complex.X degree) :=
  rfl

/-- The third Q-module in the probe-degree short complex is the represented
hom module into the upper truncation degree object. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).X₃ =
      ModuleCat.of Rat
        (probe ⟶
          (TraceAnalyticMotivicTStructure.additiveTruncGE
            cut
            complex).X degree) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

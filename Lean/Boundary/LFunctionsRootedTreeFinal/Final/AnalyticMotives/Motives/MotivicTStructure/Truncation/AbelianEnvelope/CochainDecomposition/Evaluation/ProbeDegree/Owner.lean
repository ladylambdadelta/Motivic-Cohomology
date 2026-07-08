import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.ShortComplex.Owner

/-!
# Probe-degree evaluation of the intrinsic abelian-envelope decomposition

This file evaluates the intrinsic abelian-envelope truncation short complex at
a cochain degree and then at an analytic additive probe, producing concrete
Q-module short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Evaluation of an abelian-envelope analytic cochain complex at a cochain
degree and analytic additive probe. -/
def abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    TraceAnalyticAbelianCochainComplex ⥤ ModuleCat Rat :=
  HomologicalComplex.eval
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      degree ⋙
    TraceAnalyticAdditiveAbelianEnvelope.evaluation probe

/-- Intrinsic probe-degree evaluation sends a complex to the value of its
degree object at the probe. -/
theorem abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation_obj
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation
        probe
        degree).obj complex =
      (complex.X degree).obj (Opposite.op probe) :=
  rfl

/-- Intrinsic probe-degree evaluation sends a chain map to its degree component
evaluated at the probe. -/
theorem abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation_map
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    {source target : TraceAnalyticAbelianCochainComplex}
    (hom : source ⟶ target) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation
        probe
        degree).map hom =
      (hom.f degree).app (Opposite.op probe) :=
  rfl

/-- The Q-module short complex obtained by evaluating the intrinsic
abelian-envelope truncation decomposition at one analytic probe and cochain
degree. -/
def abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    ShortComplex (ModuleCat Rat) :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
      cut
      complex).map
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainProbeDegreeEvaluation
        probe
        degree)

/-- The first Q-module in the intrinsic probe-degree short complex is the lower
truncation degree object evaluated at the probe. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₁ =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeDecompositionTruncLE cut complex).X degree).obj
        (Opposite.op probe) :=
  rfl

/-- The middle Q-module in the intrinsic probe-degree short complex is the
original degree object evaluated at the probe. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₂ =
      (complex.X degree).obj (Opposite.op probe) :=
  rfl

/-- The third Q-module in the intrinsic probe-degree short complex is the upper
truncation degree object evaluated at the probe. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).X₃ =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGE cut complex).X degree).obj
        (Opposite.op probe) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

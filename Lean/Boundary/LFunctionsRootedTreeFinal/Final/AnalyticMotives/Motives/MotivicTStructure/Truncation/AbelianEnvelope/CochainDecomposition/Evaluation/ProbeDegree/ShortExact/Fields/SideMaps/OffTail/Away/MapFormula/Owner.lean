import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ArithmeticBridge.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner

/-!
# Off-tail upper-away map normal form

This file owns the component formula identifying the intrinsic off-tail upper
map with the evaluated inverse of Mathlib's nonboundary upper-truncation
isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- In an off-lower-tail degree strictly above the upper boundary, the
intrinsic second evaluated map is the evaluated inverse of Mathlib's
nonboundary upper-truncation isomorphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_g_eq_truncGEXIso_inv_app
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut < degree) :
    let tail : ℕ := Int.toNat (degree - cut)
    let htail :
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
          some tail :=
      TraceAnalyticMotivicTStructure
        .truncGEEmbedding_r_eq_some_of_cut_le_degree
          cut
          degree
          hdegree.le
    let hnonboundary :
        ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
          tail :=
      TraceAnalyticMotivicTStructure
        .truncGEEmbedding_not_boundary_of_cut_le_degree_ne
          cut
          degree
          hdegree.le
          hdegree.ne'
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g =
      ((_root_.HomologicalComplex.truncGEXIso
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        (ComplexShape.Embedding.f_eq_of_r_eq_some
          (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        htail)
        hnonboundary).inv).app (Opposite.op probe) := by
  let tail : ℕ := Int.toNat (degree - cut)
  let htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_r_eq_some_of_cut_le_degree
        cut
        degree
        hdegree.le
  let hdegreeFormula :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      htail
  let hnonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_not_boundary_of_cut_le_degree_ne
        cut
        degree
        hdegree.le
        hdegree.ne'
  let componentFormula :
      (TraceAnalyticMotivicTStructure.truncGEProjectionMap
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        complex).f degree =
        (_root_.HomologicalComplex.truncGEXIso
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          hdegreeFormula
          hnonboundary).inv :=
    TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_not_boundary
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      complex
      tail
      degree
      hdegreeFormula
      hnonboundary
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_g
        cut
        complex
        probe
        degree)
    (congrArg
      (fun component => component.app (Opposite.op probe))
      componentFormula)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.FromIsIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Away.MapFormula.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ArithmeticBridge.Owner

/-!
# Off-tail upper-away intrinsic upper-map isomorphism

This file owns the nonboundary fact that the intrinsic upper map is an
isomorphism after probe-degree evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- In an off-lower-tail degree strictly above the upper boundary, the
intrinsic second evaluated map is an isomorphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_isIso_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut < degree) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
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
  Eq.ndrec
    (motive := fun map =>
      IsIso map)
    inferInstance
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_g_eq_truncGEXIso_inv_app
        cut
        complex
        probe
        degree
        hnone
        hdegree).symm

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

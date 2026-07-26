import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner

/-!
# Positive lower-tail map normal form

This file owns the component formula identifying the intrinsic positive
lower-tail lower map with the evaluated inverse of the nonboundary truncation
isomorphism on the opposite complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- At positive normalized lower-tail degrees, the intrinsic first evaluated
map is the evaluated nonboundary lower-truncation isomorphism component. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_f_eq_unop_truncGEXIso_inv_app
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (Nat.succ lowerTail : ℤ))).f =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex).f
          (cut - 1 - (Nat.succ lowerTail : ℤ))).app
        (Opposite.op probe) := by
  rfl

/-- At positive normalized lower-tail degrees, the evaluated abelian-envelope
lower inclusion component is an isomorphism. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_app_of_lowerTail_succ_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    IsIso
      (((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex).f
          (cut - 1 - (Nat.succ lowerTail : ℤ))).app
        (Opposite.op probe)) :=
  let degree : ℤ := cut - 1 - (Nat.succ lowerTail : ℤ)
  let lowerCut : ℤ :=
    TraceAnalyticMotivicTStructure.decompositionLowerCut cut
  let embedding :=
    (TraceAnalyticMotivicTStructure.truncLEEmbedding lowerCut).op
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding lowerCut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE lowerCut
  let htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding lowerCut).r degree =
        some (Nat.succ lowerTail) :=
    TraceAnalyticMotivicTStructure
      .truncLEEmbedding_r_eq_some_of_decompositionLowerTail
        cut
        (Nat.succ lowerTail)
  let hdegree :
      embedding.f (Nat.succ lowerTail) = degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncLEEmbedding lowerCut)
      htail
  let hnonboundary :
      ¬ embedding.BoundaryGE (Nat.succ lowerTail) :=
    TraceAnalyticMotivicTStructure
      .truncLEEmbeddingOp_not_boundary_of_decompositionLowerTail_succ
        cut
        lowerTail
  let projectionFormula :
      (TraceAnalyticMotivicTStructure.truncGEProjectionMap
        embedding
        (HomologicalComplex.op complex)).f degree =
        (_root_.HomologicalComplex.truncGEXIso
          (HomologicalComplex.op complex)
          embedding
          hdegree
          hnonboundary).inv :=
    TraceAnalyticMotivicTStructure.truncGEProjectionMap_f_of_not_boundary
      embedding
      (HomologicalComplex.op complex)
      (Nat.succ lowerTail)
      degree
      hdegree
      hnonboundary
  letI :
      IsIso
        ((TraceAnalyticMotivicTStructure.truncGEProjectionMap
          embedding
          (HomologicalComplex.op complex)).f degree) :=
    Eq.ndrec
      (motive := fun map => IsIso map)
      (show
        IsIso
          ((_root_.HomologicalComplex.truncGEXIso
            (HomologicalComplex.op complex)
            embedding
            hdegree
            hnonboundary).inv) from inferInstance)
      projectionFormula.symm
  inferInstance

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

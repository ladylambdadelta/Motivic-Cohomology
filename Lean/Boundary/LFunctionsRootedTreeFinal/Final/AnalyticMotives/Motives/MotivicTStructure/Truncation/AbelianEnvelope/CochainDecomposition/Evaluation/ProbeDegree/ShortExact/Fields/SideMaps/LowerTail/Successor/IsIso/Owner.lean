import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.FromIsIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Successor.MapFormula.Owner

/-!
# Positive lower-tail intrinsic lower-map isomorphism

This file owns the nonboundary fact that the intrinsic lower map is an
isomorphism after probe-degree evaluation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- At positive normalized lower-tail degrees, the intrinsic first evaluated
map is an isomorphism. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_isIso_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (Nat.succ lowerTail : ℤ))).f :=
  letI :
      IsIso
        (((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex).f
            (cut - 1 - (Nat.succ lowerTail : ℤ))).app
          (Opposite.op probe)) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap_f_app_of_lowerTail_succ_isIso
        cut
        complex
        probe
        lowerTail
  Eq.ndrec
    (motive := fun map =>
      IsIso map)
    (show
      IsIso
        (((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex).f
            (cut - 1 - (Nat.succ lowerTail : ℤ))).app
          (Opposite.op probe)) from inferInstance)
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_f_eq_unop_truncGEXIso_inv_app
        cut
        complex
        probe
        lowerTail).symm

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.DegreewiseSplitting.OffLowerTail.ArithmeticBridge.Owner

/-!
# Off-tail arithmetic for intrinsic probe-degree short exactness

This file owns the integer bridge from absence in the paired lower-tail
embedding to the upper-boundary/upper-away dichotomy.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- A degree strictly below the upper cut lies in the paired lower-tail
embedding. -/
theorem abelianEnvelopeIntrinsicCochainDecomposition_lowerEmbedding_r_eq_some_of_degree_lt_cut
    (cut degree : ℤ)
    (hdegree : degree < cut) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
      some (Int.toNat (cut - 1 - degree)) :=
  let degree_le_lowerCut :
      degree ≤ cut - 1 :=
    le_sub_one_of_lt hdegree
  let difference_nonnegative :
      0 ≤ cut - 1 - degree :=
    sub_nonneg.mpr degree_le_lowerCut
  let tail_cast :
      ((Int.toNat (cut - 1 - degree) : ℕ) : ℤ) =
        cut - 1 - degree :=
    Int.toNat_of_nonneg difference_nonnegative
  let embedded_degree_core :
      (cut - 1) - ((Int.toNat (cut - 1 - degree) : ℕ) : ℤ) =
        degree :=
    Eq.trans
      (congrArg
        (fun tail : ℤ => (cut - 1) - tail)
        tail_cast)
      (sub_sub_cancel (cut - 1) degree)
  let embedded_degree :
      TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
          ((Int.toNat (cut - 1 - degree) : ℕ) : ℤ) =
        degree :=
    Eq.trans
      (congrArg
        (fun lowerCut : ℤ =>
          lowerCut - ((Int.toNat (cut - 1 - degree) : ℕ) : ℤ))
        (TraceAnalyticMotivicTStructure.decompositionLowerCut_eq cut))
      embedded_degree_core
  ComplexShape.Embedding.r_eq_some
    (TraceAnalyticMotivicTStructure.truncLEEmbedding
      (TraceAnalyticMotivicTStructure.decompositionLowerCut cut))
    embedded_degree

/-- A degree outside the paired lower-tail embedding cannot lie below the
upper boundary cut. -/
theorem abelianEnvelopeIntrinsicCochainDecomposition_not_degree_lt_cut_of_offTail
    (cut degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    ¬ degree < cut :=
  fun hdegree =>
    let hsome :
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
            degree =
          some (Int.toNat (cut - 1 - degree)) :=
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecomposition_lowerEmbedding_r_eq_some_of_degree_lt_cut
          cut
          degree
          hdegree
    Option.noConfusion
      (Eq.trans hnone.symm hsome)

/-- A degree outside the paired lower-tail embedding is either the upper
boundary degree or lies strictly above it. -/
theorem abelianEnvelopeIntrinsicCochainDecomposition_offTail_eq_or_cut_lt
    (cut degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    degree = cut ∨ cut < degree :=
  match lt_trichotomy degree cut with
  | Or.inl hlt =>
      False.elim
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecomposition_not_degree_lt_cut_of_offTail
            cut
            degree
            hnone
            hlt)
  | Or.inr hnotLt =>
      match hnotLt with
      | Or.inl heq =>
          Or.inl heq
      | Or.inr hgt =>
          Or.inr hgt

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

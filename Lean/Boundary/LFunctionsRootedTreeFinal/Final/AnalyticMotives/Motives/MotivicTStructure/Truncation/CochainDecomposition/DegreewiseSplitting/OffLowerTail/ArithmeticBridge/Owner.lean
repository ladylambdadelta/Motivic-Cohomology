import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.LowerInclusion.Owner

/-!
# Arithmetic bridge for off-lower-tail degrees

This file records the integer support calculations that identify the
complement of the normalized lower tail with the nonboundary part of the upper
tail.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- A degree above the upper cut belongs to the upper-tail embedding, with
tail index `degree - cut`. -/
theorem truncGEEmbedding_r_eq_some_of_cut_le_degree
    (cut degree : ℤ)
    (hdegree : cut ≤ degree) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
      some (Int.toNat (degree - cut)) :=
  let diffNonnegative :
      0 ≤ degree - cut :=
    sub_nonneg.mpr hdegree
  let tailCast :
      ((Int.toNat (degree - cut) : ℕ) : ℤ) =
        degree - cut :=
    Int.toNat_of_nonneg diffNonnegative
  let embeddedDegree :
      cut + ((Int.toNat (degree - cut) : ℕ) : ℤ) =
        degree :=
    Eq.trans
      (congrArg
        (fun term => cut + term)
        tailCast)
      (Eq.trans
        (add_comm cut (degree - cut))
        (Int.sub_add_cancel degree cut))
  ComplexShape.Embedding.r_eq_some
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    embeddedDegree

/-- The upper-tail index obtained from a degree at or above the cut is
nonboundary exactly when the degree is not the cut. -/
theorem truncGEEmbedding_not_boundary_of_cut_le_degree_ne
    (cut degree : ℤ)
    (hdegree : cut ≤ degree)
    (hne : degree ≠ cut) :
    ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
      (Int.toNat (degree - cut)) :=
  fun hboundary =>
    let tail_eq_zero :
        Int.toNat (degree - cut) = 0 :=
      (ComplexShape.boundaryGE_embeddingUpIntGE_iff
        cut
        (Int.toNat (degree - cut))).1 hboundary
    let embedded_eq :
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f
            (Int.toNat (degree - cut)) =
          degree :=
      ComplexShape.Embedding.f_eq_of_r_eq_some
        (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        (TraceAnalyticMotivicTStructure
          .truncGEEmbedding_r_eq_some_of_cut_le_degree
            cut
            degree
            hdegree)
    let boundaryDegree :
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f 0 =
          degree :=
      Eq.subst
        (motive := fun tail =>
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
            degree)
        tail_eq_zero
        embedded_eq
    let zeroTailDegree :
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f 0 =
          cut :=
      Eq.trans
        rfl
        (Int.add_zero cut)
    hne
      (Eq.trans
        (Eq.symm boundaryDegree)
        zeroTailDegree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

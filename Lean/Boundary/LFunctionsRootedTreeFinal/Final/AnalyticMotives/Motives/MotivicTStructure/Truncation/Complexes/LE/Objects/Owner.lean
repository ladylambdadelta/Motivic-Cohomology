import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Owner

/-!
# Degree objects of lower analytic truncations

The lower truncation is the unop of an upper truncation of the opposite
complex.  This file records the corresponding object-level normal forms for
the lower truncation in the cases needed before the boundary arithmetic is
peeled: zero off the lower tail, and the original object on nonboundary
lower-tail degrees.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Opposite

namespace TraceAnalyticMotivicTStructure

/-- Outside the embedded lower tail, the concrete lower truncation has zero
degree object. -/
theorem additiveTruncLE_X_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).X degree =
      0 :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  let opposite_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE
          cut
          complex).X degree =
        0 :=
    TraceAnalyticMotivicTStructure.truncGE_X_of_r_eq_none
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
      (HomologicalComplex.op complex)
      degree
      htail
  Eq.trans
    rfl
    (congrArg Opposite.unop opposite_eq)

/-- On a nonboundary lower-tail degree, the concrete lower truncation has the
original degree object. -/
theorem additiveTruncLE_X_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex).X degree =
      complex.X degree :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  let opposite_eq :
      (TraceAnalyticMotivicTStructure.additiveTruncLEOppositeGE
          cut
          complex).X degree =
        (HomologicalComplex.op complex).X degree :=
    TraceAnalyticMotivicTStructure.truncGE_X_of_not_boundary
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
      (HomologicalComplex.op complex)
      degree
      tail
      htail
      hboundary
  Eq.trans
    rfl
    (Eq.trans
      (congrArg Opposite.unop opposite_eq)
      rfl)

/-- The opposite lower-tail boundary can occur only at tail `0`. -/
theorem truncLEEmbeddingOp_boundary_tail_eq_zero
    (cut : ℤ)
    (tail : ℕ)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    tail = 0 :=
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  match tail with
  | 0 => rfl
  | Nat.succ previous =>
      False.elim
        ((ComplexShape.Embedding.not_boundaryGE_next
          (e := (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op)
          (j := previous)
          (k := Nat.succ previous)
          (ComplexShape.up_mk previous (Nat.succ previous) rfl))
          hboundary)

/-- The lower-truncation boundary tail lies over the cut degree. -/
theorem truncLEEmbedding_boundary_degree_eq
    (cut degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail) :
    degree = cut :=
  let tail_eq_zero :
      tail = 0 :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOp_boundary_tail_eq_zero
      cut
      tail
      hboundary
  let f_eq_degree :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
      htail
  Eq.trans
    (Eq.symm f_eq_degree)
    (Eq.subst
      (motive := fun n =>
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f n =
          cut)
      tail_eq_zero
      (Eq.trans
        rfl
        (Int.sub_zero cut)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

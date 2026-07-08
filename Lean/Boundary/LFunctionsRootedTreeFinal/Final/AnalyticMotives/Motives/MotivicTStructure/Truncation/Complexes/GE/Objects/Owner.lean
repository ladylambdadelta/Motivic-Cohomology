import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Owner

/-!
# Degree objects of upper analytic truncations

This file exposes the object-level normal forms for Mathlib's upper
truncation as used by analytic motives.  These formulas are the input for the
boundedness theorem: outside the upper tail the object is zero, at the
boundary it is the opcycles object, and away from the boundary it is the
original degree object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Outside the embedded upper tail, the extended upper truncation has zero
degree object. -/
theorem truncGE_X_of_r_eq_none
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (htail : embedding.r degree = none) :
    (complex.truncGE embedding).X degree =
      0 :=
  match h : embedding.r degree with
  | none => rfl
  | some tail =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))

/-- At a boundary tail degree, the extended upper truncation has the opcycles
degree object. -/
theorem truncGE_X_of_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (tail : ι)
    (htail : embedding.r degree = some tail)
    (hboundary : embedding.BoundaryGE tail) :
    (complex.truncGE embedding).X degree =
      complex.opcycles degree :=
  match h : embedding.r degree with
  | none =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))
  | some actualTail =>
      match Option.some.inj (Eq.trans h.symm htail) with
      | rfl =>
          Eq.trans
            (dif_pos hboundary)
            (congrArg
              complex.opcycles
              (ComplexShape.Embedding.f_eq_of_r_eq_some
                (e := embedding)
                htail))

/-- Away from the boundary but still on the embedded upper tail, the extended
upper truncation has the original degree object. -/
theorem truncGE_X_of_not_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (tail : ι)
    (htail : embedding.r degree = some tail)
    (hboundary : ¬ embedding.BoundaryGE tail) :
    (complex.truncGE embedding).X degree =
      complex.X degree :=
  match h : embedding.r degree with
  | none =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))
  | some actualTail =>
      match Option.some.inj (Eq.trans h.symm htail) with
      | rfl =>
          Eq.trans
            (dif_neg hboundary)
            (congrArg
              complex.X
              (ComplexShape.Embedding.f_eq_of_r_eq_some
                (e := embedding)
                htail))

/-- Analytic upper truncation is zero outside the embedded upper tail. -/
theorem additiveTruncGE_X_of_r_eq_none
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        none) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X degree =
      0 :=
  TraceAnalyticMotivicTStructure.truncGE_X_of_r_eq_none
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    degree
    htail

/-- Analytic upper truncation has the opcycles object at the boundary. -/
theorem additiveTruncGE_X_of_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X degree =
      complex.opcycles degree :=
  TraceAnalyticMotivicTStructure.truncGE_X_of_boundary
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    degree
    tail
    htail
    hboundary

/-- Analytic upper truncation has the original degree object on nonboundary
upper-tail degrees. -/
theorem additiveTruncGE_X_of_not_boundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X degree =
      complex.X degree :=
  TraceAnalyticMotivicTStructure.truncGE_X_of_not_boundary
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    degree
    tail
    htail
    hboundary

/-- The analytic upper truncation boundary tail lies over the cut degree. -/
theorem truncGEEmbedding_boundary_degree_eq
    (cut degree : ℤ)
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    degree = cut :=
  let tail_eq_zero :
      tail = 0 :=
    (ComplexShape.boundaryGE_embeddingUpIntGE_iff cut tail).1 hboundary
  let f_eq_degree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      htail
  Eq.trans
    (Eq.symm f_eq_degree)
    (Eq.subst
      (motive := fun n =>
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f n =
          cut)
      tail_eq_zero
      (Eq.trans
        rfl
        (Int.add_zero cut)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

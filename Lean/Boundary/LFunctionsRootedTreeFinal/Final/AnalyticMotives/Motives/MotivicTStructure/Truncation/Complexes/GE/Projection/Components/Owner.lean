import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Owner

/-!
# Degreewise upper truncation projection components

This file owns the concrete degreewise formulas for the map from an additive
analytic complex to its upper truncation.  The boundary component is the
opcycles quotient map supplied by Mathlib's homological-complex truncation
calculus.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The category-polymorphic degreewise component of the projection
`K ⟶ truncGE(e, K)` for an upper-tail embedding.

Off the embedded upper tail it is the zero map into the zero extension.  At the
boundary it is the opcycles quotient map; away from the boundary it is the
inverse of Mathlib's truncation isomorphism. -/
def truncGEProjectionComponent
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι') :
    complex.X degree ⟶ (complex.truncGE embedding).X degree :=
  match htail : embedding.r degree with
  | none => 0
  | some tail =>
      have hdegree : embedding.f tail = degree :=
        ComplexShape.Embedding.f_eq_of_r_eq_some
          (e := embedding)
          htail
      if hboundary : embedding.BoundaryGE tail then
        complex.pOpcycles degree ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            embedding
            hdegree
            hboundary).inv
      else
        (_root_.HomologicalComplex.truncGEXIso
          complex
          embedding
          hdegree
          hboundary).inv

/-- On a degree outside the embedded upper tail, the projection component is
the zero map. -/
theorem truncGEProjectionComponent_of_r_eq_none
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (htail : embedding.r degree = none) :
    truncGEProjectionComponent
        embedding
        complex
        degree =
      0 :=
  match h : embedding.r degree with
  | none => rfl
  | some tail =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))

/-- At a boundary tail degree, the projection component is `pOpcycles` followed
by Mathlib's boundary truncation isomorphism. -/
theorem truncGEProjectionComponent_of_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (tail : ι)
    (htail : embedding.r degree = some tail)
    (hboundary : embedding.BoundaryGE tail) :
    truncGEProjectionComponent
        embedding
        complex
        degree =
      complex.pOpcycles degree ≫
        (_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          embedding
          (ComplexShape.Embedding.f_eq_of_r_eq_some
            (e := embedding)
            htail)
          hboundary).inv :=
  match h : embedding.r degree with
  | none =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))
  | some actualTail =>
      match Option.some.inj (Eq.trans h.symm htail) with
      | rfl =>
          dif_pos hboundary

/-- Away from the boundary but still on the embedded upper tail, the projection
component is the inverse of Mathlib's nonboundary truncation isomorphism. -/
theorem truncGEProjectionComponent_of_not_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (degree : ι')
    (tail : ι)
    (htail : embedding.r degree = some tail)
    (hboundary : ¬ embedding.BoundaryGE tail) :
    truncGEProjectionComponent
        embedding
        complex
        degree =
      (_root_.HomologicalComplex.truncGEXIso
        complex
        embedding
        (ComplexShape.Embedding.f_eq_of_r_eq_some
          (e := embedding)
          htail)
        hboundary).inv :=
  match h : embedding.r degree with
  | none =>
      False.elim
        (Option.noConfusion
          (Eq.trans htail.symm h))
  | some actualTail =>
      match Option.some.inj (Eq.trans h.symm htail) with
      | rfl =>
          dif_neg hboundary

end TraceAnalyticMotivicTStructure

/-- The degreewise component of the concrete projection from an analytic
additive complex to its upper truncation. -/
def TraceAnalyticMotivicTStructure.additiveTruncGEProjectionComponent
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (degree : ℤ) :
    complex.X degree ⟶
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
        degree :=
  TraceAnalyticMotivicTStructure.truncGEProjectionComponent
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    degree

end AnalyticMotives
end LFunctions
end Boundary

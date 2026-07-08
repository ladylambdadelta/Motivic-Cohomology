import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.BoundarySides.Owner

/-!
# Boundary reduction for restricted-core projection commutativity

This file reduces the boundary left side of the restricted-core projection
commutativity square to the explicit `fromOpcycles` differential formula, and
reduces the boundary right side to the corresponding ambient restricted
differential expression.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Boundary left side after expanding Mathlib's boundary truncation
differential. -/
theorem truncGEProjectionCoreBoundaryCommLeft_eq_fromOpcycles
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target)
    (hboundary : embedding.BoundaryGE source) :
    truncGEProjectionCoreBoundaryCommLeft
        embedding
        complex
        source
        target
        hboundary =
      (complex.pOpcycles (embedding.f source) ≫
          (_root_.HomologicalComplex.truncGE'XIsoOpcycles
            complex
            embedding
            rfl
            hboundary).inv) ≫
        ((_root_.HomologicalComplex.truncGE'XIsoOpcycles
            complex
            embedding
            rfl
            hboundary).hom ≫
          complex.fromOpcycles (embedding.f source) (embedding.f target) ≫
          (_root_.HomologicalComplex.truncGE'XIso
            complex
            embedding
            rfl
            (embedding.not_boundaryGE_next hrel)).inv) :=
  congrArg
    (fun differential =>
      (complex.pOpcycles (embedding.f source) ≫
          (_root_.HomologicalComplex.truncGE'XIsoOpcycles
            complex
            embedding
            rfl
            hboundary).inv) ≫
        differential)
    (_root_.HomologicalComplex.truncGE'_d_eq_fromOpcycles
      complex
      embedding
      hrel
      rfl
      rfl
      hboundary)

/-- Boundary right side after expanding the restricted differential. -/
theorem truncGEProjectionCoreBoundaryCommRight_eq_restrictionFormula
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreBoundaryCommRight
        embedding
        complex
        source
        target
        hrel =
      ((_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f source = embedding.f source)).hom ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        (_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f target = embedding.f target)).inv) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv :=
  congrArg
    (fun differential =>
      differential ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv)
    (_root_.HomologicalComplex.restriction_d_eq
      complex
      embedding
      rfl
      rfl)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

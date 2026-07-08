import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Components.Owner

/-!
# Boundary sides of restricted-core projection commutativity

This file names the two concrete morphism expressions appearing in the
boundary case of the restricted-core upper projection commutativity square.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Boundary left side:
the boundary core component followed by the truncated differential. -/
def truncGEProjectionCoreBoundaryCommLeft
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hboundary : embedding.BoundaryGE source) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  (complex.pOpcycles (embedding.f source) ≫
      (_root_.HomologicalComplex.truncGE'XIsoOpcycles
        complex
        embedding
        rfl
        hboundary).inv) ≫
    (complex.truncGE' embedding).d source target

/-- Boundary right side:
the restricted differential followed by the nonboundary target core component. -/
def truncGEProjectionCoreBoundaryCommRight
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  (complex.restriction embedding).d source target ≫
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv

/-- Projection formula for the boundary left side. -/
theorem truncGEProjectionCoreBoundaryCommLeft_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
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
        (complex.truncGE' embedding).d source target :=
  rfl

/-- Projection formula for the boundary right side. -/
theorem truncGEProjectionCoreBoundaryCommRight_eq
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
      (complex.restriction embedding).d source target ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

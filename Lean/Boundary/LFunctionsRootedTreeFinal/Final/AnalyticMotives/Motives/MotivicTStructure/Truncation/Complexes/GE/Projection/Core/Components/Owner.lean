import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Boundary.Owner

/-!
# Restricted-core upper projection components

Before the upper projection is extended across the zero side of the embedding,
it is a map from the restricted ambient complex to the unextended truncation
core.  Its boundary component is `pOpcycles`; its nonboundary component is the
identity transported through Mathlib's nonboundary truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The component of the restricted-core projection
`K.restriction e ⟶ K.truncGE' e`. -/
def truncGEProjectionCoreComponent
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι) :
    (complex.restriction embedding).X tail ⟶
      (complex.truncGE' embedding).X tail :=
  if hboundary : embedding.BoundaryGE tail then
    complex.pOpcycles (embedding.f tail) ≫
      (_root_.HomologicalComplex.truncGE'XIsoOpcycles
        complex
        embedding
        rfl
        hboundary).inv
  else
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      hboundary).inv

/-- At a boundary tail degree, the restricted-core projection component is
`pOpcycles` followed by the inverse boundary-core truncation isomorphism. -/
theorem truncGEProjectionCoreComponent_of_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (hboundary : embedding.BoundaryGE tail) :
    truncGEProjectionCoreComponent
        embedding
        complex
        tail =
      complex.pOpcycles (embedding.f tail) ≫
        (_root_.HomologicalComplex.truncGE'XIsoOpcycles
          complex
          embedding
          rfl
          hboundary).inv :=
  dif_pos hboundary

/-- Away from the boundary, the restricted-core projection component is the
inverse nonboundary-core truncation isomorphism. -/
theorem truncGEProjectionCoreComponent_of_not_boundary
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (tail : ι)
    (hboundary : ¬ embedding.BoundaryGE tail) :
    truncGEProjectionCoreComponent
        embedding
        complex
        tail =
      (_root_.HomologicalComplex.truncGE'XIso
        complex
        embedding
        rfl
        hboundary).inv :=
  dif_neg hboundary

/-- Analytic integer specialization of the restricted-core projection
component. -/
def additiveTruncGEProjectionCoreComponent
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ) :
    (complex.restriction
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).X tail ⟶
      (complex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)).X tail :=
  TraceAnalyticMotivicTStructure.truncGEProjectionCoreComponent
    (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
    complex
    tail

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

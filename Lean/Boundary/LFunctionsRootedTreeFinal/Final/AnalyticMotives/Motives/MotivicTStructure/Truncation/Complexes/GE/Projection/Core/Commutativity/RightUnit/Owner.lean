import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightReduction.Owner

/-!
# Right-side unit normal form

After replacing the two self restriction isomorphisms by identities, the
right-side expression is a unit-decorated ambient differential followed by the
target truncation isomorphism.  This file names that expression before the
final unit-law cancellation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The unit-decorated right-side expression after cancelling both
`restrictionXIso rfl` maps. -/
def truncGEProjectionCoreCommRightUnitDecorated
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
  ((𝟙 ((complex.restriction embedding).X source)) ≫
    complex.d (embedding.f source) (embedding.f target) ≫
    𝟙 (complex.X (embedding.f target))) ≫
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv

/-- Projection formula for the unit-decorated right-side expression. -/
theorem truncGEProjectionCoreCommRightUnitDecorated_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreCommRightUnitDecorated
        embedding
        complex
        source
        target
        hrel =
      ((𝟙 ((complex.restriction embedding).X source)) ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        𝟙 (complex.X (embedding.f target))) ≫
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

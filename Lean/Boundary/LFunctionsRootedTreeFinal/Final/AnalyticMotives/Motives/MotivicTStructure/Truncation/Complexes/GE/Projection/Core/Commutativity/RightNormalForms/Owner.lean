import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RestrictionCancellation.Owner

/-!
# Right-side normal forms for restricted-core projection commutativity

The right side after `restriction_d_eq` contains two self restriction
isomorphisms.  This file names that expanded right-side expression so the
subsequent unit-cancellation proof is isolated from the truncation formulas.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The expanded right-side normal form before cancelling
`restrictionXIso rfl` hom and inverse maps. -/
def truncGEProjectionCoreCommRightExpandedNormalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    (complex.restriction embedding).X source ⟶
      (complex.truncGE' embedding).X target :=
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
      (embedding.not_boundaryGE_next hrel)).inv

/-- Projection formula for the expanded right-side normal form. -/
theorem truncGEProjectionCoreCommRightExpandedNormalForm_eq
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    truncGEProjectionCoreCommRightExpandedNormalForm
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
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

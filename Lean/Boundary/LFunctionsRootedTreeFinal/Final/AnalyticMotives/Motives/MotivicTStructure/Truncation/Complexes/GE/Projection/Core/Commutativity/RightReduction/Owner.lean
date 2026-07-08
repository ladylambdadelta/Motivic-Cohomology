import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightNormalForms.Owner

/-!
# Right-side restriction-identity reductions

This file performs the two explicit identity substitutions in the expanded
right-side normal form: first the source `restrictionXIso rfl` hom map, then
the target `restrictionXIso rfl` inverse map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- Replacing the source `restrictionXIso rfl` hom by the identity in the
expanded right-side normal form. -/
theorem truncGEProjectionCoreCommRightExpanded_sourceRestrictionHomId
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
      ((𝟙 ((complex.restriction embedding).X source)) ≫
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
    (fun sourceHom =>
      (sourceHom ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        (_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f target = embedding.f target)).inv) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv)
    (TraceAnalyticMotivicTStructure.truncGEProjectionCoreRestrictionXIso_hom_id
      embedding
      complex
      source)

/-- Replacing the target `restrictionXIso rfl` inverse by the identity after
the source restriction hom has already been replaced by the identity. -/
theorem truncGEProjectionCoreCommRightExpanded_targetRestrictionInvId
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target) :
    ((𝟙 ((complex.restriction embedding).X source)) ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        (_root_.HomologicalComplex.restrictionXIso
          complex
          embedding
          (rfl : embedding.f target = embedding.f target)).inv) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv =
      ((𝟙 ((complex.restriction embedding).X source)) ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        𝟙 (complex.X (embedding.f target))) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv :=
  congrArg
    (fun targetInv =>
      ((𝟙 ((complex.restriction embedding).X source)) ≫
        complex.d (embedding.f source) (embedding.f target) ≫
        targetInv) ≫
        (_root_.HomologicalComplex.truncGE'XIso
          complex
          embedding
          rfl
          (embedding.not_boundaryGE_next hrel)).inv)
    (TraceAnalyticMotivicTStructure.truncGEProjectionCoreRestrictionXIso_inv_id
      embedding
      complex
      target)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

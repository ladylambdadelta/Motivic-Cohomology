import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NonboundaryCancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NormalForms.Owner

/-!
# Nonboundary left normal form

This file reduces the nonboundary left side of restricted-core upper projection
commutativity to the common ambient-differential normal form.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The expanded nonboundary left side reduces to the common normal form by
cancelling Mathlib's nonboundary truncation isomorphism. -/
theorem truncGEProjectionCoreNonboundaryCommLeft_eq_normalForm
    (embedding : ComplexShape.Embedding shape ambientShape)
    [embedding.IsTruncGE]
    (complex : HomologicalComplex C ambientShape)
    [∀ degree, complex.HasHomology degree]
    (source target : ι)
    (hrel : shape.Rel source target)
    (hsource : ¬ embedding.BoundaryGE source) :
    truncGEProjectionCoreNonboundaryCommLeft
        embedding
        complex
        source
        target
        hsource =
      truncGEProjectionCoreCommNormalForm
        embedding
        complex
        source
        target
        hrel :=
  let sourceIsoInv :
      (complex.restriction embedding).X source ⟶
        (complex.truncGE' embedding).X source :=
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      hsource).inv
  let sourceIsoHom :
      (complex.truncGE' embedding).X source ⟶
        (complex.restriction embedding).X source :=
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      hsource).hom
  let differential :
      (complex.restriction embedding).X source ⟶
        complex.X (embedding.f target) :=
    complex.d (embedding.f source) (embedding.f target)
  let targetIsoInv :
      complex.X (embedding.f target) ⟶
        (complex.truncGE' embedding).X target :=
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv
  let reassociateToCancel :
      sourceIsoInv ≫ (sourceIsoHom ≫ differential ≫ targetIsoInv) =
        ((sourceIsoInv ≫ sourceIsoHom) ≫ differential) ≫
          targetIsoInv :=
    Eq.trans
      (Eq.symm
        (Category.assoc sourceIsoInv sourceIsoHom
          (differential ≫ targetIsoInv)))
      (Category.assoc (sourceIsoInv ≫ sourceIsoHom) differential
        targetIsoInv)
  let isoCancellation :
      sourceIsoInv ≫ sourceIsoHom =
        𝟙 ((complex.restriction embedding).X source) :=
    truncGEProjectionCoreNonboundary_inv_hom_id
      embedding
      complex
      source
      hsource
  let cancelIso :
      ((sourceIsoInv ≫ sourceIsoHom) ≫ differential) ≫ targetIsoInv =
        ((𝟙 ((complex.restriction embedding).X source)) ≫ differential) ≫
          targetIsoInv :=
    congrArg
      (fun morphism => (morphism ≫ differential) ≫ targetIsoInv)
      isoCancellation
  let cancelLeftUnit :
      ((𝟙 ((complex.restriction embedding).X source)) ≫ differential) ≫
          targetIsoInv =
        differential ≫ targetIsoInv :=
    congrArg
      (fun morphism => morphism ≫ targetIsoInv)
      (Category.id_comp differential)
  Eq.trans
    (truncGEProjectionCoreNonboundaryCommLeft_eq_differential
      embedding
      complex
      source
      target
      hrel
      hsource)
    (Eq.trans
      reassociateToCancel
      (Eq.trans
        cancelIso
        (Eq.trans
          cancelLeftUnit
          (Eq.symm
            (truncGEProjectionCoreCommNormalForm_eq
              embedding
              complex
              source
              target
              hrel)))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

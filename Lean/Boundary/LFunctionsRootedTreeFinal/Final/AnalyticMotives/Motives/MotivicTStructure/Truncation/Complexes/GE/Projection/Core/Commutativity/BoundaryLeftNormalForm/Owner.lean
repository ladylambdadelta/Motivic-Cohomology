import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.BoundaryCancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NormalForms.Owner

/-!
# Boundary left normal form

This file reduces the boundary left side of restricted-core upper projection
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

/-- The expanded boundary left side reduces to the common normal form by
opcycles cancellation and categorical associativity. -/
theorem truncGEProjectionCoreBoundaryCommLeft_eq_normalForm
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
      truncGEProjectionCoreCommNormalForm
        embedding
        complex
        source
        target
        hrel :=
  let p :
      (complex.restriction embedding).X source ⟶
        complex.opcycles (embedding.f source) :=
    complex.pOpcycles (embedding.f source)
  let boundaryIsoInv :
      complex.opcycles (embedding.f source) ⟶
        (complex.truncGE' embedding).X source :=
    (_root_.HomologicalComplex.truncGE'XIsoOpcycles
      complex
      embedding
      rfl
      hboundary).inv
  let boundaryIsoHom :
      (complex.truncGE' embedding).X source ⟶
        complex.opcycles (embedding.f source) :=
    (_root_.HomologicalComplex.truncGE'XIsoOpcycles
      complex
      embedding
      rfl
      hboundary).hom
  let from :
      complex.opcycles (embedding.f source) ⟶
        complex.X (embedding.f target) :=
    complex.fromOpcycles (embedding.f source) (embedding.f target)
  let targetIsoInv :
      complex.X (embedding.f target) ⟶
        (complex.truncGE' embedding).X target :=
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv
  let reassociateToCancel :
      (p ≫ boundaryIsoInv) ≫
          (boundaryIsoHom ≫ from ≫ targetIsoInv) =
        ((p ≫ (boundaryIsoInv ≫ boundaryIsoHom)) ≫ from) ≫
          targetIsoInv :=
    Eq.trans
      (Eq.symm (Category.assoc (p ≫ boundaryIsoInv) boundaryIsoHom
        (from ≫ targetIsoInv)))
      (Eq.trans
        (congrArg
          (fun morphism => morphism ≫ (from ≫ targetIsoInv))
          (Category.assoc p boundaryIsoInv boundaryIsoHom))
        (Category.assoc (p ≫ (boundaryIsoInv ≫ boundaryIsoHom)) from
          targetIsoInv))
  let isoCancellation :
      boundaryIsoInv ≫ boundaryIsoHom =
        𝟙 (complex.opcycles (embedding.f source)) :=
    (_root_.HomologicalComplex.truncGE'XIsoOpcycles
      complex
      embedding
      rfl
      hboundary).inv_hom_id
  let cancelIso :
      ((p ≫ (boundaryIsoInv ≫ boundaryIsoHom)) ≫ from) ≫
          targetIsoInv =
        ((p ≫ 𝟙 (complex.opcycles (embedding.f source))) ≫ from) ≫
          targetIsoInv :=
    congrArg
      (fun morphism => ((p ≫ morphism) ≫ from) ≫ targetIsoInv)
      isoCancellation
  let cancelRightUnit :
      ((p ≫ 𝟙 (complex.opcycles (embedding.f source))) ≫ from) ≫
          targetIsoInv =
        (p ≫ from) ≫ targetIsoInv :=
    congrArg
      (fun morphism => (morphism ≫ from) ≫ targetIsoInv)
      (Category.comp_id p)
  let opcyclesCancellation :
      (p ≫ from) ≫ targetIsoInv =
        complex.d (embedding.f source) (embedding.f target) ≫
          targetIsoInv :=
    congrArg
      (fun morphism => morphism ≫ targetIsoInv)
      (truncGEProjectionCoreBoundary_p_fromOpcycles
        embedding
        complex
        source
        target)
  Eq.trans
    (truncGEProjectionCoreBoundaryCommLeft_eq_fromOpcycles
      embedding
      complex
      source
      target
      hrel
      hboundary)
    (Eq.trans
      reassociateToCancel
      (Eq.trans
        cancelIso
        (Eq.trans
          cancelRightUnit
          (Eq.trans
            opcyclesCancellation
            (Eq.symm
              (truncGEProjectionCoreCommNormalForm_eq
                embedding
                complex
                source
                target
                hrel))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

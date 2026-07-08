import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.RightUnit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Core.Commutativity.NormalForms.Owner

/-!
# Right-side unit cancellation

This file cancels the categorical identity morphisms left after the two
restriction isomorphisms have been replaced by identities.  The result is the
common normal form for the restricted-core projection commutativity square.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
variable {ι ι' : Type*} {shape : ComplexShape ι} {ambientShape : ComplexShape ι'}

/-- The unit-decorated right-side expression reduces to the common normal
form by the category unit laws. -/
theorem truncGEProjectionCoreCommRightUnitDecorated_eq_normalForm
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
      truncGEProjectionCoreCommNormalForm
        embedding
        complex
        source
        target
        hrel :=
  let differential :
      (complex.restriction embedding).X source ⟶ complex.X (embedding.f target) :=
    complex.d (embedding.f source) (embedding.f target)
  let targetIsoInv :
      complex.X (embedding.f target) ⟶
        (complex.truncGE' embedding).X target :=
    (_root_.HomologicalComplex.truncGE'XIso
      complex
      embedding
      rfl
      (embedding.not_boundaryGE_next hrel)).inv
  let rightUnit :
      ((𝟙 ((complex.restriction embedding).X source)) ≫
        differential ≫
        𝟙 (complex.X (embedding.f target))) =
        ((𝟙 ((complex.restriction embedding).X source)) ≫
          differential) :=
    Category.comp_id
      ((𝟙 ((complex.restriction embedding).X source)) ≫ differential)
  let leftUnit :
      ((𝟙 ((complex.restriction embedding).X source)) ≫
        differential) =
        differential :=
    Category.id_comp differential
  let unitCancellation :
      (((𝟙 ((complex.restriction embedding).X source)) ≫
        differential ≫
        𝟙 (complex.X (embedding.f target))) ≫
        targetIsoInv) =
        differential ≫ targetIsoInv :=
    congrArg
      (fun morphism => morphism ≫ targetIsoInv)
      (Eq.trans rightUnit leftUnit)
  Eq.trans
    (truncGEProjectionCoreCommRightUnitDecorated_eq
      embedding
      complex
      source
      target
      hrel)
    (Eq.trans
      unitCancellation
      (Eq.symm
        (truncGEProjectionCoreCommNormalForm_eq
          embedding
          complex
          source
          target
          hrel)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

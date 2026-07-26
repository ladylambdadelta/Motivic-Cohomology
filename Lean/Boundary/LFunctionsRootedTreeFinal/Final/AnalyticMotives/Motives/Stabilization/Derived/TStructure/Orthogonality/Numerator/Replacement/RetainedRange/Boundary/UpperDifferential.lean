import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Support.UpperProjection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Components

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The chosen right-boundary outgoing map becomes the displayed
short-complex `fromOpcycles` map after the chosen opcycles isomorphism. -/
theorem target_truncGEProjection_boundary_rightData_g'_transport
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    let displayedShortComplex :
        ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        0
        1
        2).obj targetComplex)
    let rightData :
        displayedShortComplex.RightHomologyData :=
      displayedShortComplex.homologyData.right
    rightData.opcyclesIso.hom ≫ rightData.g' =
      displayedShortComplex.fromOpcycles :=
  let displayedShortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).obj targetComplex)
  let rightData :
      displayedShortComplex.RightHomologyData :=
    displayedShortComplex.homologyData.right
  rightData.opcyclesIso_hom_comp_descQ

/-- The displayed upper short-complex `fromOpcycles` is transported from the
ambient homological-complex opcycles map. -/
theorem target_truncGEProjection_boundary_opcyclesSc'_fromOpcycles
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (targetComplex.opcyclesIsoSc'
        0
        1
        2
        rfl
        rfl).inv ≫
      targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) =
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).obj targetComplex).fromOpcycles :=
  targetComplex.opcyclesIsoSc'_inv_fromOpcycles
    0
    1
    2
    rfl
    rfl

/-- The upper boundary target differential, followed by the nonboundary
right-object transport, is the ambient `fromOpcycles` map after the boundary
opcycles transport. -/
theorem target_truncGEProjection_boundary_target_g_transport_core
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    let truncIso :
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
          1
          targetComplex).X (1 : ℤ) ≅
        targetComplex.opcycles (1 : ℤ) :=
      _root_.HomologicalComplex.truncGEXIsoOpcycles
        targetComplex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
        (Eq.trans rfl (Int.add_zero 1))
        ((ComplexShape.boundaryGE_embeddingUpIntGE_iff 1 0).2 rfl)
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_rightIso
          targetComplex).hom =
    truncIso.hom ≫ targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) :=
  let sourceTail : ℕ := 0
  let targetTail : ℕ := 1
  let tailRel :
      (ComplexShape.up ℕ).Rel sourceTail targetTail :=
    ComplexShape.up_mk 0 1 rfl
  let sourceDegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f sourceTail =
        (1 : ℤ) :=
    Eq.trans rfl (Int.add_zero 1)
  let targetDegree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f targetTail =
        (2 : ℤ) :=
    rfl
  let sourceBoundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        sourceTail :=
    (ComplexShape.boundaryGE_embeddingUpIntGE_iff 1 sourceTail).2 rfl
  let targetNonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        targetTail :=
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).not_boundaryGE_next
      tailRel
  let extendSourceIso :
      ((targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).extend
          (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          (1 : ℤ) ≅
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          sourceTail :=
    _root_.HomologicalComplex.extendXIso
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      sourceDegree
  let extendTargetIso :
      ((targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).extend
          (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          (2 : ℤ) ≅
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          targetTail :=
    _root_.HomologicalComplex.extendXIso
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      targetDegree
  let boundaryIso :
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          sourceTail ≅
      targetComplex.opcycles (1 : ℤ) :=
    _root_.HomologicalComplex.truncGE'XIsoOpcycles
      targetComplex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      sourceDegree
      sourceBoundary
  let targetIso :
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).X
          targetTail ≅
      targetComplex.X (2 : ℤ) :=
    _root_.HomologicalComplex.truncGE'XIso
      targetComplex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      targetDegree
      targetNonboundary
  let extendFormula :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
        1
        targetComplex).d (1 : ℤ) (2 : ℤ) =
      extendSourceIso.hom ≫
        (targetComplex.truncGE'
          (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).d
            sourceTail
            targetTail ≫
        extendTargetIso.inv :=
    _root_.HomologicalComplex.extend_d_eq
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      sourceDegree
      targetDegree
  let boundaryFormula :
      (targetComplex.truncGE'
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).d
          sourceTail
          targetTail =
      boundaryIso.hom ≫
        targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
        targetIso.inv :=
    _root_.HomologicalComplex.truncGE'_d_eq_fromOpcycles
      targetComplex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      tailRel
      sourceDegree
      targetDegree
      sourceBoundary
  let replaceBoundary :
      extendSourceIso.hom ≫
          (targetComplex.truncGE'
            (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)).d
              sourceTail
              targetTail ≫
          extendTargetIso.inv =
      extendSourceIso.hom ≫
          (boundaryIso.hom ≫
            targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
            targetIso.inv) ≫
          extendTargetIso.inv :=
    congrArg
      (fun morphism =>
        extendSourceIso.hom ≫ morphism ≫ extendTargetIso.inv)
      boundaryFormula
  let cancelTarget :
      (extendSourceIso.hom ≫
          (boundaryIso.hom ≫
            targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
            targetIso.inv) ≫
          extendTargetIso.inv) ≫
        (extendTargetIso.hom ≫ targetIso.hom) =
      (extendSourceIso.hom ≫ boundaryIso.hom) ≫
        targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) :=
    Eq.trans
      (Category.assoc
        (extendSourceIso.hom ≫
          (boundaryIso.hom ≫
            targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
            targetIso.inv))
        extendTargetIso.inv
        (extendTargetIso.hom ≫ targetIso.hom))
      (Eq.trans
        (congrArg
          (fun morphism =>
            (extendSourceIso.hom ≫
              (boundaryIso.hom ≫
                targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
                targetIso.inv)) ≫ morphism)
          (Iso.inv_hom_id_assoc extendTargetIso targetIso.hom))
        (Eq.trans
          (Category.assoc
            extendSourceIso.hom
            (boundaryIso.hom ≫
              targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ))
            targetIso.inv)
          (Eq.trans
            (congrArg
              (fun morphism => extendSourceIso.hom ≫ morphism)
              (Eq.trans
                (Category.assoc
                  boundaryIso.hom
                  (targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ))
                  targetIso.inv)
                (Eq.trans
                  (congrArg
                    (fun morphism => boundaryIso.hom ≫
                      targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) ≫
                      morphism)
                    (Iso.inv_hom_id targetIso))
                  (Category.comp_id
                    (boundaryIso.hom ≫
                      targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ))))))
            (Eq.symm
              (Category.assoc
                extendSourceIso.hom
                boundaryIso.hom
                (targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ)))))))
  Eq.trans
    (congrArg
      (fun morphism =>
        morphism ≫
          (TraceAnalyticDerivedMotiveCategory
            .target_truncGEProjection_boundary_target_rightIso
              targetComplex).hom)
      extendFormula)
    (Eq.trans
      (congrArg
        (fun morphism =>
          morphism ≫
            (TraceAnalyticDerivedMotiveCategory
              .target_truncGEProjection_boundary_target_rightIso
                targetComplex).hom)
        replaceBoundary)
      cancelTarget)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

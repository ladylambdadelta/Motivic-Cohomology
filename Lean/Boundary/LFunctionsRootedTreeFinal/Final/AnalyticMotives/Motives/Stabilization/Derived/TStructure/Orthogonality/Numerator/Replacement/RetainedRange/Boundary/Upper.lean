import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.UpperDifferential

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Upper target first-map compatibility at the transported opcycles model. -/
theorem target_truncGEProjection_boundary_target_first_comm_core
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_leftIso
          targetComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.f =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.f ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_middleIso
          targetComplex).hom :=
  let zeroSource :
      IsZero
        ((TraceAnalyticMotivicTStructure.additiveTruncGE
          1
          targetComplex).X (1 - 1 - (0 : ℤ))) :=
    TraceAnalyticMotivicTStructure
      .additiveTruncGE_X_isZero_of_decompositionLowerTail
        1
        targetComplex
        0
  let degree_eq :
      (1 : ℤ) - 1 - (0 : ℤ) = 0 :=
    rfl
  let sourceZero :
      IsZero
        ((TraceAnalyticMotivicTStructure.additiveTruncGE
          1
          targetComplex).X (0 : ℤ)) :=
    Eq.subst
      (motive := fun degree =>
        IsZero
          ((TraceAnalyticMotivicTStructure.additiveTruncGE
            1
            targetComplex).X degree))
      degree_eq
      zeroSource
  sourceZero.eq_of_src
    ((TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_leftIso
          targetComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.f)
    ((Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.f ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_middleIso
          targetComplex).hom)

/-- Upper target first-map compatibility. -/
theorem target_truncGEProjection_boundary_target_first_comm
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_leftIso
          targetComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.f =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.f ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_middleIso
          targetComplex).hom :=
  TraceAnalyticDerivedMotiveCategory
    .target_truncGEProjection_boundary_target_first_comm_core
      targetComplex

/-- Upper target second-map compatibility at the transported opcycles model. -/
theorem target_truncGEProjection_boundary_target_second_comm_core
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_middleIso
          targetComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.g =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_rightIso
          targetComplex).hom :=
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
  let scIso :
      targetComplex.opcycles (1 : ℤ) ≅
      displayedShortComplex.opcycles :=
    targetComplex.opcyclesIsoSc'
      0
      1
      2
      rfl
      rfl
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
  let rightDataTransport :
      rightData.opcyclesIso.hom ≫ rightData.g' =
        displayedShortComplex.fromOpcycles :=
    TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_rightData_g'_transport
        targetComplex
  let scInvTransport :
      scIso.inv ≫ targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) =
        displayedShortComplex.fromOpcycles :=
    TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_opcyclesSc'_fromOpcycles
        targetComplex
  let scHomTransport :
      scIso.hom ≫ displayedShortComplex.fromOpcycles =
        targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) :=
    Eq.trans
      (congrArg
        (fun morphism => scIso.hom ≫ morphism)
        (Eq.symm scInvTransport))
      (Eq.trans
        (Category.assoc
          scIso.hom
          scIso.inv
          (targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ)))
        (Eq.trans
          (congrArg
            (fun morphism =>
              morphism ≫ targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ))
            (Iso.hom_inv_id scIso))
          (Category.id_comp
            (targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ)))))
  let leftSide :
      (TraceAnalyticDerivedMotiveCategory
          .target_truncGEProjection_boundary_target_middleIso
            targetComplex).hom ≫
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetRightBoundaryModelMap targetComplex)).right.g =
      truncIso.hom ≫ targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) :=
    Eq.trans
      (Category.assoc
        truncIso.hom
        scIso.hom
        (rightData.opcyclesIso.hom ≫ rightData.g'))
      (Eq.trans
        (congrArg
          (fun morphism => truncIso.hom ≫ scIso.hom ≫ morphism)
          rightDataTransport)
        (congrArg
          (fun morphism => truncIso.hom ≫ morphism)
          scHomTransport))
  let rightSide :
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetBoundaryShortComplexMap targetComplex)).right.g ≫
        (TraceAnalyticDerivedMotiveCategory
          .target_truncGEProjection_boundary_target_rightIso
            targetComplex).hom =
      truncIso.hom ≫ targetComplex.fromOpcycles (1 : ℤ) (2 : ℤ) :=
    TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_g_transport_core
        targetComplex
  Eq.trans
    leftSide
    (Eq.symm rightSide)

/-- Upper target second-map compatibility. -/
theorem target_truncGEProjection_boundary_target_second_comm
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_middleIso
          targetComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.g =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_rightIso
          targetComplex).hom :=
  TraceAnalyticDerivedMotiveCategory
    .target_truncGEProjection_boundary_target_second_comm_core
      targetComplex

/-- The upper truncation boundary target short complex is the right-boundary
model of the original short complex. -/
theorem target_truncGEProjection_boundary_target_iso_rightBoundaryModel
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex)).right ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex)).right := by
  ShortComplex.isoMk
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_leftIso
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_middleIso
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_rightIso
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_first_comm
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_second_comm
        targetComplex)

/-- Upper arrow-square left component. -/
theorem target_truncGEProjection_boundary_arrow_square_tau_one
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex).τ₁ =
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom).τ₁ :=
  rfl

/-- Upper arrow-square middle component after opcycles quotient transport. -/
theorem target_truncGEProjection_boundary_arrow_square_tau_two_core
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex).τ₂ =
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom).τ₂ :=
  let tail : ℕ := 0
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        (1 : ℤ) :=
    Eq.trans rfl (Int.add_zero 1)
  let tail_boundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail :=
    (ComplexShape.boundaryGE_embeddingUpIntGE_iff 1 tail).2 rfl
  let displayedShortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    ((shortComplexFunctor'
      TraceAnalyticAdditiveAbelianEnvelope
      (ComplexShape.up ℤ)
      0
      1
      2).obj targetComplex)
  let truncIso :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
        1
        targetComplex).X (1 : ℤ) ≅
      targetComplex.opcycles (1 : ℤ) :=
    _root_.HomologicalComplex.truncGEXIsoOpcycles
      targetComplex
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      tail_degree
      tail_boundary
  let scIso :
      targetComplex.opcycles (1 : ℤ) ≅
      displayedShortComplex.opcycles :=
    targetComplex.opcyclesIsoSc'
      0
      1
      2
      rfl
      rfl
  let rightData :
      displayedShortComplex.RightHomologyData :=
    displayedShortComplex.homologyData.right
  let componentFormula :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex).f (1 : ℤ) =
      targetComplex.pOpcycles (1 : ℤ) ≫ truncIso.inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_boundary
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
        targetComplex
        tail
        (1 : ℤ)
        tail_degree
        tail_boundary
  let cancelTrunc :
      (targetComplex.pOpcycles (1 : ℤ) ≫ truncIso.inv) ≫
          (truncIso.hom ≫ scIso.hom ≫ rightData.opcyclesIso.hom) =
        targetComplex.pOpcycles (1 : ℤ) ≫
          scIso.hom ≫ rightData.opcyclesIso.hom :=
    Eq.trans
      (Category.assoc
        (targetComplex.pOpcycles (1 : ℤ))
        truncIso.inv
        (truncIso.hom ≫ scIso.hom ≫ rightData.opcyclesIso.hom))
      (Eq.trans
        (congrArg
          (fun morphism =>
            targetComplex.pOpcycles (1 : ℤ) ≫
              (morphism ≫ scIso.hom ≫ rightData.opcyclesIso.hom))
          (Iso.inv_hom_id truncIso))
        (Category.id_comp
          (targetComplex.pOpcycles (1 : ℤ) ≫
            scIso.hom ≫ rightData.opcyclesIso.hom)))
  let toDisplayedOpcycles :
      targetComplex.pOpcycles (1 : ℤ) ≫
          scIso.hom ≫ rightData.opcyclesIso.hom =
        displayedShortComplex.pOpcycles ≫ rightData.opcyclesIso.hom :=
    congrArg
      (fun morphism => morphism ≫ rightData.opcyclesIso.hom)
      (targetComplex.pOpcycles_opcyclesIsoSc'_hom
        0
        1
        2
        rfl
        rfl)
  let toRightData :
      displayedShortComplex.pOpcycles ≫ rightData.opcyclesIso.hom =
        rightData.p :=
    rightData.pOpcycles_comp_opcyclesIso_hom
  let rightSide :
      (TraceAnalyticDerivedMotiveCategory
          .targetBoundaryShortComplexMap targetComplex ≫
        (TraceAnalyticDerivedMotiveCategory
          .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
            targetComplex).hom).τ₂ =
        rightData.p :=
    Eq.trans
      (congrArg
        (fun component =>
          component ≫
            (truncIso.hom ≫ scIso.hom ≫ rightData.opcyclesIso.hom))
        componentFormula)
      (Eq.trans
        cancelTrunc
        (Eq.trans toDisplayedOpcycles toRightData))
  Eq.symm rightSide

/-- Upper arrow-square middle component. -/
theorem target_truncGEProjection_boundary_arrow_square_tau_two
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex).τ₂ =
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom).τ₂ :=
  TraceAnalyticDerivedMotiveCategory
    .target_truncGEProjection_boundary_arrow_square_tau_two_core
      targetComplex

/-- Upper arrow-square right component after nonboundary degree transport. -/
theorem target_truncGEProjection_boundary_arrow_square_tau_three_core
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex).τ₃ =
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom).τ₃ :=
  let tail : ℕ := 1
  let tail_eq_some :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).r (2 : ℤ) =
        some tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_r_eq_some_of_cut_le_degree
        1
        2
        (show (1 : ℤ) ≤ 2 from Int.reduceLE)
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        (2 : ℤ) :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
      tail_eq_some
  let tail_nonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail :=
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).not_boundaryGE_next
      (ComplexShape.up_mk 0 1 rfl)
  let componentFormula :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex).f (2 : ℤ) =
      (_root_.HomologicalComplex.truncGEXIso
        targetComplex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
        tail_degree
        tail_nonboundary).inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_not_boundary
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1)
        targetComplex
        tail
        (2 : ℤ)
        tail_degree
        tail_nonboundary
  let rightIso :
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetBoundaryShortComplexMap targetComplex)).right.X₃ ≅
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex)).right.X₃ :=
    TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_target_rightIso
        targetComplex
  let leftSide :
      ((Iso.refl
          (Arrow.mk
            (TraceAnalyticDerivedMotiveCategory
              .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
        TraceAnalyticDerivedMotiveCategory
          .targetRightBoundaryModelMap targetComplex).τ₃ =
        𝟙
          ((Arrow.mk
            (TraceAnalyticDerivedMotiveCategory
              .targetRightBoundaryModelMap targetComplex)).right.X₃) :=
    rfl
  let rightSide :
      (TraceAnalyticDerivedMotiveCategory
          .targetBoundaryShortComplexMap targetComplex ≫
        (TraceAnalyticDerivedMotiveCategory
          .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
            targetComplex).hom).τ₃ =
        𝟙
          ((Arrow.mk
            (TraceAnalyticDerivedMotiveCategory
              .targetRightBoundaryModelMap targetComplex)).right.X₃) :=
    Eq.trans
      (congrArg
        (fun component =>
          component ≫ rightIso.hom)
        componentFormula)
      (Iso.inv_hom_id rightIso)
  Eq.trans
    leftSide
    (Eq.symm rightSide)

/-- Upper arrow-square right component. -/
theorem target_truncGEProjection_boundary_arrow_square_tau_three
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex).τ₃ =
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom).τ₃ :=
  TraceAnalyticDerivedMotiveCategory
    .target_truncGEProjection_boundary_arrow_square_tau_three_core
      targetComplex

/-- The upper truncation boundary map commutes with the target short-complex
identification. -/
theorem target_truncGEProjection_boundary_arrow_square_rightBoundaryProjection
    (targetComplex : TraceAnalyticAbelianCochainComplex) :
    (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex =
    TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom := by
  ShortComplex.hom_ext
    ((Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .targetBoundaryShortComplexMap targetComplex)).left).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .targetRightBoundaryModelMap targetComplex)
    (TraceAnalyticDerivedMotiveCategory
        .targetBoundaryShortComplexMap targetComplex ≫
      (TraceAnalyticDerivedMotiveCategory
        .target_truncGEProjection_boundary_target_iso_rightBoundaryModel
          targetComplex).hom)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_arrow_square_tau_one
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_arrow_square_tau_two
        targetComplex)
    (TraceAnalyticDerivedMotiveCategory
      .target_truncGEProjection_boundary_arrow_square_tau_three
        targetComplex)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

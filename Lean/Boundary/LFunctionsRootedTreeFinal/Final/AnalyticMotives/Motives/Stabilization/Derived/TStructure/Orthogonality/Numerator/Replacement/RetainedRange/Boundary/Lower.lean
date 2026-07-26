import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Nonboundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Support.LowerInclusion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.Numerator.Replacement.RetainedRange.Boundary.Components

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The displayed source short complex used by the lower boundary lane. -/
def source_truncLEInclusion_boundary_displayedShortComplex
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
  ((shortComplexFunctor'
    TraceAnalyticAdditiveAbelianEnvelope
    (ComplexShape.up ℤ)
    (-1 : ℤ)
    0
    1).obj sourceComplex)

/-- The chosen left homology data of the displayed source short complex. -/
def source_truncLEInclusion_boundary_leftData
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_displayedShortComplex
        sourceComplex).LeftHomologyData :=
  (TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_displayedShortComplex
      sourceComplex).homologyData.left

/-- Tail zero maps to degree zero for the lower embedding at cut zero. -/
theorem truncLEEmbedding_zero_tail_zero_degree :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).f 0 =
      (0 : ℤ) :=
  Eq.trans rfl (Int.sub_zero 0)

/-- Tail zero is the opposite upper-boundary index for the lower embedding at
cut zero. -/
theorem truncLEEmbedding_zero_op_boundary_tail_zero :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op.BoundaryGE
      0 :=
  ComplexShape.Embedding.boundaryGE
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op
    (show
      (ComplexShape.up ℤ).symm.Rel
        (1 : ℤ)
        ((TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op.f 0) from
      rfl)
    (fun index hindex =>
      let degree_eq :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op.f index =
            (0 : ℤ) - (index : ℤ) :=
        rfl
      let shifted_eq :
          (0 : ℤ) - (index : ℤ) =
            (1 : ℤ) :=
        Eq.trans (Eq.symm degree_eq) hindex
      let nonpos :
          (0 : ℤ) - (index : ℤ) ≤ 0 :=
        sub_nonpos.mpr (Int.ofNat_nonneg index)
      let positive :
          (0 : ℤ) < (1 : ℤ) :=
        Int.reduceLT
      False.elim
        (not_lt_of_ge
          (Eq.subst
            (motive := fun value => value ≤ 0)
            shifted_eq
            nonpos)
          positive))

/-- The opposite upper truncation boundary object over degree zero. -/
def source_truncLEInclusion_boundary_oppositeBoundaryIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
      0
      sourceComplex).X (0 : ℤ) ≅
    (HomologicalComplex.op sourceComplex).opcycles (0 : ℤ) :=
  _root_.HomologicalComplex.truncGEXIsoOpcycles
    (HomologicalComplex.op sourceComplex)
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op
    TraceAnalyticDerivedMotiveCategory
      .truncLEEmbedding_zero_tail_zero_degree
    TraceAnalyticDerivedMotiveCategory
      .truncLEEmbedding_zero_op_boundary_tail_zero

/-- The opposite homological-complex opcycles object is the opposite of the
displayed source cycles object. -/
def source_truncLEInclusion_boundary_oppositeOpcyclesIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (HomologicalComplex.op sourceComplex).opcycles (0 : ℤ) ≅
    Opposite.op
      ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_displayedShortComplex
          sourceComplex).cycles) :=
  ((HomologicalComplex.op sourceComplex).opcyclesIsoSc'
      (1 : ℤ)
      (0 : ℤ)
      (-1 : ℤ)
      rfl
      rfl) ≪≫
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_displayedShortComplex
        sourceComplex).opcyclesOpIso

/-- The lower boundary object identifies with the displayed source cycles
object. -/
def source_truncLEInclusion_boundary_cyclesIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
      0
      sourceComplex).X (0 : ℤ) ≅
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_displayedShortComplex
        sourceComplex).cycles :=
  (TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_oppositeBoundaryIso
      sourceComplex).unop.symm ≪≫
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_oppositeOpcyclesIso
        sourceComplex).unop.symm

/-- The lower boundary cycles transport followed by the displayed cycles
inclusion is the degree-zero lower truncation inclusion component. -/
theorem source_truncLEInclusion_boundary_cyclesIso_hom_iCycles
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_cyclesIso
          sourceComplex).hom ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_displayedShortComplex
          sourceComplex).iCycles =
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
      0
      sourceComplex).f (0 : ℤ) :=
  let displayedShortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_displayedShortComplex
        sourceComplex
  let oppositeBoundaryIso :
      (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEOppositeGE
        0
        sourceComplex).X (0 : ℤ) ≅
      (HomologicalComplex.op sourceComplex).opcycles (0 : ℤ) :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_oppositeBoundaryIso
        sourceComplex
  let oppositeOpcyclesIso :
      (HomologicalComplex.op sourceComplex).opcycles (0 : ℤ) ≅
      Opposite.op displayedShortComplex.cycles :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_oppositeOpcyclesIso
        sourceComplex
  let projectionBoundary :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEOppositeGEProjectionMap
          0
          sourceComplex).f (0 : ℤ) =
      (HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ) ≫
        oppositeBoundaryIso.inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_boundary
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).op
        (HomologicalComplex.op sourceComplex)
        0
        (0 : ℤ)
        TraceAnalyticDerivedMotiveCategory
          .truncLEEmbedding_zero_tail_zero_degree
        TraceAnalyticDerivedMotiveCategory
          .truncLEEmbedding_zero_op_boundary_tail_zero
  let inclusionOp :
      ((TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
        0
        sourceComplex).f (0 : ℤ)).op =
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEOppositeGEProjectionMap
          0
          sourceComplex).f (0 : ℤ) :=
    rfl
  let opcyclesToCycles :
      (HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ) ≫
          oppositeOpcyclesIso.hom =
        displayedShortComplex.iCycles.op :=
    Eq.trans
      (Category.assoc
        ((HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ))
        ((HomologicalComplex.op sourceComplex).opcyclesIsoSc'
          (1 : ℤ)
          (0 : ℤ)
          (-1 : ℤ)
          rfl
          rfl).hom
        displayedShortComplex.opcyclesOpIso.hom)
      (Eq.trans
        (congrArg
          (fun morphism =>
            morphism ≫ displayedShortComplex.opcyclesOpIso.hom)
          ((HomologicalComplex.op sourceComplex).pOpcycles_opcyclesIsoSc'_hom
            (1 : ℤ)
            (0 : ℤ)
            (-1 : ℤ)
            rfl
            rfl))
        displayedShortComplex.op_pOpcycles_opcyclesOpIso_hom)
  let cyclesToOpcycles :
      displayedShortComplex.iCycles.op ≫ oppositeOpcyclesIso.inv =
        (HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ) :=
    Eq.trans
      (congrArg
        (fun morphism => morphism ≫ oppositeOpcyclesIso.inv)
        (Eq.symm opcyclesToCycles))
      (Eq.trans
        (Category.assoc
          ((HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ))
          oppositeOpcyclesIso.hom
          oppositeOpcyclesIso.inv)
        (Eq.trans
          (congrArg
            (fun morphism =>
              (HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ) ≫
                morphism)
            oppositeOpcyclesIso.hom_inv_id)
          (Category.comp_id
            ((HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ)))))
  let cyclesIsoHomOp :
      ((TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_cyclesIso
            sourceComplex).hom).op =
        oppositeOpcyclesIso.inv ≫ oppositeBoundaryIso.inv :=
    rfl
  let leftOp :
      ((TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_cyclesIso
            sourceComplex).hom ≫
        displayedShortComplex.iCycles).op =
      (HomologicalComplex.op sourceComplex).pOpcycles (0 : ℤ) ≫
        oppositeBoundaryIso.inv :=
    Eq.trans
      (op_comp
        (f :=
          (TraceAnalyticDerivedMotiveCategory
            .source_truncLEInclusion_boundary_cyclesIso
              sourceComplex).hom)
        (g := displayedShortComplex.iCycles))
      (Eq.trans
        (congrArg
          (fun morphism =>
            displayedShortComplex.iCycles.op ≫ morphism)
          cyclesIsoHomOp)
        (Eq.trans
          (Eq.symm
            (Category.assoc
              displayedShortComplex.iCycles.op
              oppositeOpcyclesIso.inv
              oppositeBoundaryIso.inv))
          (congrArg
            (fun morphism => morphism ≫ oppositeBoundaryIso.inv)
            cyclesToOpcycles)))
  Quiver.Hom.op_inj
    (Eq.trans
      leftOp
      (Eq.trans
        (Eq.symm projectionBoundary)
        (Eq.symm inclusionOp)))

/-- The degree `1` object is outside the lower-tail embedding at cut `0`. -/
theorem truncLEEmbedding_zero_r_one_eq_none :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).r (1 : ℤ) =
      none :=
  ComplexShape.Embedding.r_eq_none
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0)
    (1 : ℤ)
    (fun tail htail =>
      let hnonpos : (0 : ℤ) - (tail : ℤ) ≤ 0 :=
        sub_nonpos.mpr (Int.ofNat_nonneg tail)
      let hpositive : (0 : ℤ) < 1 :=
        Int.reduceLT
      False.elim
        (not_lt_of_ge hnonpos
          (Eq.subst
            (motive := fun degree => (0 : ℤ) < degree)
            (Eq.symm htail)
            hpositive)))

/-- Lower source left-object transport through the previous nonboundary degree. -/
def source_truncLEInclusion_boundary_source_leftIso_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₁ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left.X₁ :=
  letI :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex).f (-1 : ℤ)) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncLEInclusionMap_f_isIso_of_degree_lt_cut
        0
        sourceComplex
        (-1 : ℤ)
        (show (-1 : ℤ) < 0 from Int.reduceLT)
  asIso
    ((TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex).f (-1 : ℤ))

/-- Lower source left-object transport. -/
def source_truncLEInclusion_boundary_source_leftIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₁ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left.X₁ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_source_leftIso_core
      sourceComplex

/-- Lower source middle-object transport through concrete and chosen cycles. -/
def source_truncLEInclusion_boundary_source_middleIso_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₂ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left.X₂ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_cyclesIso
      sourceComplex ≪≫
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_leftData
        sourceComplex).cyclesIso

/-- The lower boundary middle transport followed by the chosen cycles
inclusion is the degree-zero lower truncation inclusion component. -/
theorem source_truncLEInclusion_boundary_middleIso_hom_i
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso_core
          sourceComplex).hom ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_leftData
          sourceComplex).i =
    (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
      0
      sourceComplex).f (0 : ℤ) :=
  Eq.trans
    (Category.assoc
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_cyclesIso
          sourceComplex).hom
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_leftData
          sourceComplex).cyclesIso.hom
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_leftData
          sourceComplex).i)
    (Eq.trans
      (congrArg
        (fun morphism =>
          (TraceAnalyticDerivedMotiveCategory
            .source_truncLEInclusion_boundary_cyclesIso
              sourceComplex).hom ≫ morphism)
        ((TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_leftData
            sourceComplex).cyclesIso_hom_comp_i))
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_cyclesIso_hom_iCycles
          sourceComplex))

/-- Lower source middle-object transport. -/
def source_truncLEInclusion_boundary_source_middleIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₂ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left.X₂ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_source_middleIso_core
      sourceComplex

/-- The lower boundary source keeps the right zero-side object. -/
def source_truncLEInclusion_boundary_source_rightIso
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₃ ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left.X₃ :=
  Iso.refl
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.X₃

/-- Lower source first-map compatibility at the transported cycles model. -/
theorem source_truncLEInclusion_boundary_source_first_comm_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_leftIso
          sourceComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceLeftBoundaryModelMap sourceComplex)).left.f =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso
          sourceComplex).hom :=
  let displayedShortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_displayedShortComplex
        sourceComplex
  let leftData : displayedShortComplex.LeftHomologyData :=
    TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_leftData
        sourceComplex
  let leftSide_i :
      ((TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_leftIso
            sourceComplex).hom ≫
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceLeftBoundaryModelMap sourceComplex)).left.f) ≫
          leftData.i =
        (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_leftIso
            sourceComplex).hom ≫
          displayedShortComplex.f :=
    Eq.trans
      (Category.assoc
        (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_leftIso
            sourceComplex).hom
        leftData.f'
        leftData.i)
      (congrArg
        (fun morphism =>
          (TraceAnalyticDerivedMotiveCategory
            .source_truncLEInclusion_boundary_source_leftIso
              sourceComplex).hom ≫ morphism)
        leftData.f'_i)
  let rightSide_i :
      ((Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
        (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_middleIso
            sourceComplex).hom) ≫
          leftData.i =
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
          (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
            0
            sourceComplex).f (0 : ℤ) :=
    Eq.trans
      (Category.assoc
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).left.f
        (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_middleIso
            sourceComplex).hom
        leftData.i)
      (congrArg
        (fun morphism =>
          (Arrow.mk
            (TraceAnalyticDerivedMotiveCategory
              .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
            morphism)
        (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_middleIso_hom_i
            sourceComplex))
  let map_comm :
      (TraceAnalyticDerivedMotiveCategory
          .source_truncLEInclusion_boundary_source_leftIso
            sourceComplex).hom ≫
        displayedShortComplex.f =
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
        (TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
          0
          sourceComplex).f (0 : ℤ) :=
    (TraceAnalyticDerivedMotiveCategory
      .sourceBoundaryShortComplexMap sourceComplex).comm₁₂
  (CategoryTheory.cancel_mono leftData.i).1
    (Eq.trans
      leftSide_i
      (Eq.trans map_comm (Eq.symm rightSide_i)))

/-- Lower source first-map compatibility. -/
theorem source_truncLEInclusion_boundary_source_first_comm
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_leftIso
          sourceComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceLeftBoundaryModelMap sourceComplex)).left.f =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.f ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso
          sourceComplex).hom :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_source_first_comm_core
      sourceComplex

/-- Lower source second-map compatibility at the transported cycles model. -/
theorem source_truncLEInclusion_boundary_source_second_comm_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso
          sourceComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceLeftBoundaryModelMap sourceComplex)).left.g =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_rightIso
          sourceComplex).hom :=
  let targetZero :
      IsZero
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
          0
          sourceComplex).X (1 : ℤ)) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLE_X_isZero_of_r_eq_none
        0
        sourceComplex
        (1 : ℤ)
        TraceAnalyticDerivedMotiveCategory
          .truncLEEmbedding_zero_r_one_eq_none
  targetZero.eq_of_tgt
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso
          sourceComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceLeftBoundaryModelMap sourceComplex)).left.g)
    ((Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_rightIso
          sourceComplex).hom)

/-- Lower source second-map compatibility. -/
theorem source_truncLEInclusion_boundary_source_second_comm
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_middleIso
          sourceComplex).hom ≫
      (Arrow.mk
        (TraceAnalyticDerivedMotiveCategory
          .sourceLeftBoundaryModelMap sourceComplex)).left.g =
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left.g ≫
      (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_rightIso
          sourceComplex).hom :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_source_second_comm_core
      sourceComplex

/-- The lower truncation boundary source short complex is the left-boundary
model of the original short complex. -/
theorem source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex)).left ≅
    (Arrow.mk
      (TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)).left := by
  ShortComplex.isoMk
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_leftIso
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_middleIso
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_rightIso
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_first_comm
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_source_second_comm
        sourceComplex)

/-- Lower arrow-square left component after previous-degree transport. -/
theorem source_truncLEInclusion_boundary_arrow_square_tau_one_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex).τ₁ =
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom).τ₁ :=
  rfl

/-- Lower arrow-square left component. -/
theorem source_truncLEInclusion_boundary_arrow_square_tau_one
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex).τ₁ =
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom).τ₁ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_arrow_square_tau_one_core
      sourceComplex

/-- Lower arrow-square middle component after cycles inclusion transport. -/
theorem source_truncLEInclusion_boundary_arrow_square_tau_two_core
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex).τ₂ =
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom).τ₂ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_middleIso_hom_i
      sourceComplex

/-- Lower arrow-square middle component. -/
theorem source_truncLEInclusion_boundary_arrow_square_tau_two
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex).τ₂ =
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom).τ₂ :=
  TraceAnalyticDerivedMotiveCategory
    .source_truncLEInclusion_boundary_arrow_square_tau_two_core
      sourceComplex

/-- Lower arrow-square right component. -/
theorem source_truncLEInclusion_boundary_arrow_square_tau_three
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex).τ₃ =
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom).τ₃ :=
  rfl

/-- The lower truncation boundary map commutes with the source short-complex
identification. -/
theorem source_truncLEInclusion_boundary_arrow_square_leftBoundaryInclusion
    (sourceComplex : TraceAnalyticAbelianCochainComplex) :
    (TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex =
    TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom := by
  ShortComplex.hom_ext
    ((TraceAnalyticDerivedMotiveCategory
        .source_truncLEInclusion_boundary_source_iso_leftBoundaryModel
          sourceComplex).hom ≫
      TraceAnalyticDerivedMotiveCategory
        .sourceLeftBoundaryModelMap sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
        .sourceBoundaryShortComplexMap sourceComplex ≫
      (Iso.refl
        (Arrow.mk
          (TraceAnalyticDerivedMotiveCategory
            .sourceBoundaryShortComplexMap sourceComplex)).right).hom)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_arrow_square_tau_one
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_arrow_square_tau_two
        sourceComplex)
    (TraceAnalyticDerivedMotiveCategory
      .source_truncLEInclusion_boundary_arrow_square_tau_three
        sourceComplex)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Projection.Map.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.Complexes.LE.Owner

/-!
# Nonboundary retained-range quasi-isomorphism facts

This file owns the strict-tail homology comparison for the lower and upper
truncation replacement maps.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- A cochain map is a quasi-isomorphism at one degree when the associated
three-term short-complex map is epi, iso, mono on its three displayed
components. -/
theorem quasiIsoAt_of_shortComplex_component_epi_iso_mono
    {source target : TraceAnalyticAbelianCochainComplex}
    (chainMap : source ⟶ target)
    (previous degree next : ℤ)
    (previousRelation : (ComplexShape.up ℤ).Rel previous degree)
    (nextRelation : (ComplexShape.up ℤ).Rel degree next)
    [Epi (chainMap.f previous)]
    [IsIso (chainMap.f degree)]
    [Mono (chainMap.f next)] :
    QuasiIsoAt chainMap degree :=
  (_root_.quasiIsoAt_iff'
    chainMap
    previous
    degree
    next
    ((ComplexShape.up ℤ).prev_eq' previousRelation)
    ((ComplexShape.up ℤ).next_eq' nextRelation)).mpr
    (ShortComplex.quasiIso_of_epi_of_isIso_of_mono
      ((shortComplexFunctor'
        TraceAnalyticAdditiveAbelianEnvelope
        (ComplexShape.up ℤ)
        previous
        degree
        next).map chainMap))

/-- Strictly above the upper cut, the upper-truncation projection component is
an isomorphism. -/
theorem abelianEnvelopeTruncGEProjectionMap_f_isIso_of_cut_lt_degree
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (cut_lt_degree : cut < degree) :
    IsIso
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap cut complex).f degree) :=
  let tail : ℕ := Int.toNat (degree - cut)
  let tail_eq_some :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).r degree =
        some tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_r_eq_some_of_cut_le_degree
        cut
        degree
        cut_lt_degree.le
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      tail_eq_some
  let tail_nonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail :=
    TraceAnalyticMotivicTStructure
      .truncGEEmbedding_not_boundary_of_cut_le_degree_ne
        cut
        degree
        cut_lt_degree.le
        cut_lt_degree.ne'
  let componentFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncGEProjectionMap cut complex).f degree =
        (_root_.HomologicalComplex.truncGEXIso
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          tail_degree
          tail_nonboundary).inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_not_boundary
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        complex
        tail
        degree
        tail_degree
        tail_nonboundary
  Eq.ndrec
    (motive := fun component => IsIso component)
    (show
      IsIso
        ((_root_.HomologicalComplex.truncGEXIso
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          tail_degree
          tail_nonboundary).inv) from inferInstance)
    componentFormula.symm

/-- At the upper cut, the upper-truncation projection component is epic: it is
the opcycles quotient map followed by an isomorphism. -/
theorem abelianEnvelopeTruncGEProjectionMap_f_epi_at_cut
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    Epi
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap cut complex).f cut) :=
  let tail : ℕ := 0
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut :=
    Eq.trans rfl (Int.add_zero cut)
  let tail_boundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE tail :=
    (ComplexShape.boundaryGE_embeddingUpIntGE_iff cut tail).2 rfl
  let componentFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncGEProjectionMap cut complex).f cut =
        complex.pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            tail_degree
            tail_boundary).inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_boundary
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        complex
        tail
        cut
        tail_degree
        tail_boundary
  Eq.ndrec
    (motive := fun component => Epi component)
    (show
      Epi
        (complex.pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            tail_degree
            tail_boundary).inv) from inferInstance)
    componentFormula.symm

/-- At and above the upper cut, the upper-truncation projection component is
epic. -/
theorem abelianEnvelopeTruncGEProjectionMap_f_epi_of_cut_le_degree
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (cut_le_degree : cut ≤ degree) :
    Epi
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap cut complex).f degree) :=
  Or.elim
    (lt_or_eq_of_le cut_le_degree)
    (fun cut_lt_degree =>
      letI :
          IsIso
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGEProjectionMap cut complex).f degree) :=
        TraceAnalyticDerivedMotiveCategory
          .abelianEnvelopeTruncGEProjectionMap_f_isIso_of_cut_lt_degree
            cut
            complex
            degree
            cut_lt_degree
      inferInstance)
    (fun cut_eq_degree =>
      Eq.subst
        (motive := fun retainedDegree =>
          Epi
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeTruncGEProjectionMap cut complex).f
                retainedDegree))
        cut_eq_degree
        (TraceAnalyticDerivedMotiveCategory
          .abelianEnvelopeTruncGEProjectionMap_f_epi_at_cut
            cut
            complex))

/-- Strictly above the upper cut, the upper-truncation projection component is
monic. -/
theorem abelianEnvelopeTruncGEProjectionMap_f_mono_of_cut_lt_degree
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (cut_lt_degree : cut < degree) :
    Mono
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap cut complex).f degree) :=
  letI :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncGEProjectionMap cut complex).f degree) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncGEProjectionMap_f_isIso_of_cut_lt_degree
        cut
        complex
        degree
        cut_lt_degree
  inferInstance

/-- Strictly below the lower cut, the concrete lower-tail embedding has the
expected tail coordinate. -/
theorem truncLEEmbedding_r_eq_some_of_degree_le_cut
    (cut degree : ℤ)
    (degree_le_cut : degree ≤ cut) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
      some (Int.toNat (cut - degree)) :=
  let tail : ℕ := Int.toNat (cut - degree)
  let nonnegative : 0 ≤ cut - degree :=
    sub_nonneg.mpr degree_le_cut
  let tail_cast : (tail : ℤ) = cut - degree :=
    Int.toNat_of_nonneg nonnegative
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f tail =
        degree :=
    Eq.trans
      (congrArg (fun value : ℤ => cut - value) tail_cast)
      (sub_sub_cancel cut degree)
  ComplexShape.Embedding.r_eq_some
    (e := TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
    tail_degree

/-- Strictly below the lower cut, the lower-tail embedding point is not the
opposite upper boundary point. -/
theorem truncLEEmbeddingOp_not_boundary_of_degree_lt_cut
    (cut degree : ℤ)
    (degree_lt_cut : degree < cut) :
    ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
      (Int.toNat (cut - degree)) :=
  fun boundary =>
    let tail_eq_zero :
        Int.toNat (cut - degree) = 0 :=
      TraceAnalyticMotivicTStructure.truncLEEmbeddingOp_boundary_tail_eq_zero
        cut
        (Int.toNat (cut - degree))
        boundary
    let nonnegative : 0 ≤ cut - degree :=
      sub_nonneg.mpr degree_lt_cut.le
    let tail_cast : ((Int.toNat (cut - degree) : ℤ)) = cut - degree :=
      Int.toNat_of_nonneg nonnegative
    let difference_zero : cut - degree = 0 :=
      Eq.trans (Eq.symm tail_cast) (congrArg Int.ofNat tail_eq_zero)
    let cut_eq_degree : cut = degree :=
      sub_eq_zero.mp difference_zero
    degree_lt_cut.ne cut_eq_degree.symm

/-- The zeroth lower-tail coordinate is the opposite upper-boundary coordinate
for the dual lower truncation. -/
theorem truncLEEmbeddingOp_boundary_zero
    (cut : ℤ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE 0 :=
  let boundarySource : ℤ := cut + 1
  let boundaryRelation :
      (ComplexShape.up ℤ).symm.Rel
        boundarySource
        ((TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f 0) :=
    rfl
  let boundarySource_not_mem :
      ∀ tail : ℕ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f tail ≠
          boundarySource :=
    fun tail image_eq_boundarySource =>
      let image_le_cut :
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.f tail ≤
            cut :=
        sub_le_self cut (Int.ofNat_nonneg tail)
      let boundarySource_le_cut : boundarySource ≤ cut :=
        Eq.subst
          (motive := fun value : ℤ => value ≤ cut)
          image_eq_boundarySource
          image_le_cut
      (not_lt_of_ge boundarySource_le_cut) (lt_add_one cut)
  ComplexShape.Embedding.boundaryGE
    (e := (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op)
    boundaryRelation
    boundarySource_not_mem

/-- The abelian-envelope lower inclusion component is the unopposite of the
opposite upper projection component. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_eq_unop_projection
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex).f degree =
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEOppositeGEProjectionMap cut complex).f degree).unop :=
  rfl

/-- Strictly below the lower cut, the lower-truncation inclusion component is
an isomorphism. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_isIso_of_degree_lt_cut
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (degree_lt_cut : degree < cut) :
    IsIso
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex).f degree) :=
  let tail : ℕ := Int.toNat (cut - degree)
  let tail_eq_some :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).r degree =
        some tail :=
    TraceAnalyticDerivedMotiveCategory
      .truncLEEmbedding_r_eq_some_of_degree_le_cut
        cut
        degree
        degree_lt_cut.le
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f tail =
        degree :=
    ComplexShape.Embedding.f_eq_of_r_eq_some
      (e := TraceAnalyticMotivicTStructure.truncLEEmbedding cut)
      tail_eq_some
  let tail_nonboundary :
      ¬ (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail :=
    TraceAnalyticDerivedMotiveCategory
      .truncLEEmbeddingOp_not_boundary_of_degree_lt_cut
        cut
        degree
        degree_lt_cut
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  let projectionFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEOppositeGEProjectionMap cut complex).f
          degree =
        (_root_.HomologicalComplex.truncGEXIso
          (HomologicalComplex.op complex)
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
          tail_degree
          tail_nonboundary).inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_not_boundary
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
        (HomologicalComplex.op complex)
        tail
        degree
        tail_degree
        tail_nonboundary
  let inclusionFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap cut complex).f degree =
        ((_root_.HomologicalComplex.truncGEXIso
          (HomologicalComplex.op complex)
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
          tail_degree
          tail_nonboundary).inv).unop :=
    Eq.trans
      (TraceAnalyticDerivedMotiveCategory
        .abelianEnvelopeTruncLEInclusionMap_f_eq_unop_projection
          cut
          complex
          degree)
      (congrArg Quiver.Hom.unop projectionFormula)
  Eq.ndrec
    (motive := fun component => IsIso component)
    (show
      IsIso
        (((_root_.HomologicalComplex.truncGEXIso
          (HomologicalComplex.op complex)
          (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
          tail_degree
          tail_nonboundary).inv).unop) from inferInstance)
    inclusionFormula.symm

/-- Strictly below the lower cut, the lower-truncation inclusion component is
epic. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_epi_of_degree_lt_cut
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (degree_lt_cut : degree < cut) :
    Epi
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex).f degree) :=
  letI :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap cut complex).f degree) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncLEInclusionMap_f_isIso_of_degree_lt_cut
        cut
        complex
        degree
        degree_lt_cut
  inferInstance

/-- Strictly below the lower cut, the lower-truncation inclusion component is
monic. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_mono_of_degree_lt_cut
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (degree_lt_cut : degree < cut) :
    Mono
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex).f degree) :=
  letI :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap cut complex).f degree) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncLEInclusionMap_f_isIso_of_degree_lt_cut
        cut
        complex
        degree
        degree_lt_cut
  inferInstance

/-- At the lower cut, the lower-truncation inclusion component is monic: it is
the unopposite of the opposite upper opcycles quotient followed by an
isomorphism. -/
theorem abelianEnvelopeTruncLEInclusionMap_f_mono_at_cut
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    Mono
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap cut complex).f cut) :=
  let tail : ℕ := 0
  let tail_degree :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).f tail =
        cut :=
    Eq.trans rfl (Int.sub_zero cut)
  let tail_boundary :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.BoundaryGE
        tail :=
    TraceAnalyticDerivedMotiveCategory
      .truncLEEmbeddingOp_boundary_zero
        cut
  letI :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op.IsTruncGE :=
    TraceAnalyticMotivicTStructure.truncLEEmbeddingOpIsTruncGE cut
  let projectionFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEOppositeGEProjectionMap cut complex).f cut =
        (HomologicalComplex.op complex).pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            (HomologicalComplex.op complex)
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
            tail_degree
            tail_boundary).inv :=
    TraceAnalyticMotivicTStructure
      .truncGEProjectionMap_f_of_boundary
        (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
        (HomologicalComplex.op complex)
        tail
        cut
        tail_degree
        tail_boundary
  let inclusionFormula :
      (TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap cut complex).f cut =
        ((HomologicalComplex.op complex).pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            (HomologicalComplex.op complex)
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
            tail_degree
            tail_boundary).inv).unop :=
    Eq.trans
      (TraceAnalyticDerivedMotiveCategory
        .abelianEnvelopeTruncLEInclusionMap_f_eq_unop_projection
          cut
          complex
          cut)
      (congrArg Quiver.Hom.unop projectionFormula)
  letI :
      Epi
        ((HomologicalComplex.op complex).pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            (HomologicalComplex.op complex)
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
            tail_degree
            tail_boundary).inv) :=
    inferInstance
  Eq.ndrec
    (motive := fun component => Mono component)
    (show
      Mono
        (((HomologicalComplex.op complex).pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            (HomologicalComplex.op complex)
            (TraceAnalyticMotivicTStructure.truncLEEmbedding cut).op
            tail_degree
            tail_boundary).inv).unop) from inferInstance)
    inclusionFormula.symm

/-- Strictly below the lower boundary, the lower-truncation inclusion is a
homology isomorphism by the nonboundary component formula. -/
theorem exactAt_source_truncLEInclusion_quasiIsoAt_below_zero
    (sourceComplex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (degree_lt_zero : degree < 0) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex)
      degree :=
  let sourceInclusion :
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
          0
          sourceComplex ⟶
        sourceComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncLEInclusionMap 0 sourceComplex
  let previous : ℤ := degree - 1
  let next : ℤ := degree + 1
  let previousRelation :
      (ComplexShape.up ℤ).Rel previous degree :=
    Int.sub_add_cancel degree 1
  let nextRelation :
      (ComplexShape.up ℤ).Rel degree next :=
    rfl
  let previous_lt_cut : previous < 0 :=
    lt_of_lt_of_le (sub_lt_self degree zero_lt_one) degree_lt_zero.le
  let next_le_cut : next ≤ 0 :=
    Int.add_one_le_iff.mpr degree_lt_zero
  letI : Epi (sourceInclusion.f previous) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncLEInclusionMap_f_epi_of_degree_lt_cut
        0
        sourceComplex
        previous
        previous_lt_cut
  letI : IsIso (sourceInclusion.f degree) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncLEInclusionMap_f_isIso_of_degree_lt_cut
        0
        sourceComplex
        degree
        degree_lt_zero
  letI : Mono (sourceInclusion.f next) :=
    Or.elim
      (lt_or_eq_of_le next_le_cut)
      (fun next_lt_cut =>
        TraceAnalyticDerivedMotiveCategory
          .abelianEnvelopeTruncLEInclusionMap_f_mono_of_degree_lt_cut
            0
            sourceComplex
            next
            next_lt_cut)
      (fun next_eq_cut =>
        Eq.subst
          (motive := fun retainedDegree =>
            Mono (sourceInclusion.f retainedDegree))
          next_eq_cut
          (TraceAnalyticDerivedMotiveCategory
            .abelianEnvelopeTruncLEInclusionMap_f_mono_at_cut
              0
              sourceComplex))
  TraceAnalyticDerivedMotiveCategory
    .quasiIsoAt_of_shortComplex_component_epi_iso_mono
      sourceInclusion
      previous
      degree
      next
      previousRelation
      nextRelation

/-- Strictly above the upper boundary, the upper-truncation projection is a
homology isomorphism by the nonboundary component formula. -/
theorem exactAt_target_truncGEProjection_quasiIsoAt_above_one
    (targetComplex : TraceAnalyticAbelianCochainComplex)
    (degree : ℤ)
    (one_lt_degree : 1 < degree) :
    QuasiIsoAt
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeTruncGEProjectionMap 1 targetComplex)
      degree :=
  let targetProjection :
      targetComplex ⟶
        TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE
          1
          targetComplex :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeTruncGEProjectionMap 1 targetComplex
  let previous : ℤ := degree - 1
  let next : ℤ := degree + 1
  let previousRelation :
      (ComplexShape.up ℤ).Rel previous degree :=
    Int.sub_add_cancel degree 1
  let nextRelation :
      (ComplexShape.up ℤ).Rel degree next :=
    rfl
  let previous_ge_cut : 1 ≤ previous :=
    Int.le_sub_one_iff.mpr one_lt_degree
  let next_gt_cut : 1 < next :=
    lt_trans one_lt_degree (lt_add_one degree)
  letI : Epi (targetProjection.f previous) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncGEProjectionMap_f_epi_of_cut_le_degree
        1
        targetComplex
        previous
        previous_ge_cut
  letI : IsIso (targetProjection.f degree) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncGEProjectionMap_f_isIso_of_cut_lt_degree
        1
        targetComplex
        degree
        one_lt_degree
  letI : Mono (targetProjection.f next) :=
    TraceAnalyticDerivedMotiveCategory
      .abelianEnvelopeTruncGEProjectionMap_f_mono_of_cut_lt_degree
        1
        targetComplex
        next
        next_gt_cut
  TraceAnalyticDerivedMotiveCategory
    .quasiIsoAt_of_shortComplex_component_epi_iso_mono
      targetProjection
      previous
      degree
      next
      previousRelation
      nextRelation

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.ChainLevel.Owner

/-!
# Homological orthogonality after postcomposition

This file owns the postcomposition form of adjacent homological
orthogonality for the derived analytic motive category.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- If the representative-conjugate of a morphism is zero, then the original
morphism is zero. -/
theorem morphism_eq_zero_of_iso_conjugate_eq_zero
    {source target sourceRepresentative targetRepresentative :
      TraceAnalyticDerivedMotiveCategory}
    (sourceIso : sourceRepresentative ≅ source)
    (targetIso : targetRepresentative ≅ target)
    (morphism : source ⟶ target)
    (conjugateZero :
      sourceIso.hom ≫ morphism ≫ targetIso.inv = 0) :
    morphism = 0 :=
  (IsIso.comp_left_eq_zero
    (f := sourceIso.hom)
    (g := morphism)).mp
    ((IsIso.comp_right_eq_zero
      (f := sourceIso.hom ≫ morphism)
      (g := targetIso.inv)).mp
      conjugateZero)

/-- The cochain preimage of a `≤ cut` object is again `≤ cut` after applying
the derived localization functor. -/
theorem objectOf_cochainPreimage_tStructureLE
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  (TraceAnalyticDerivedMotiveCategory.homologicalLE_iff_of_iso
    cut
    (TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso
      object)).mpr
    membership

/-- The cochain preimage of a `≥ cut` object is again `≥ cut` after applying
the derived localization functor. -/
theorem objectOf_cochainPreimage_tStructureGE
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  (TraceAnalyticDerivedMotiveCategory.homologicalGE_iff_of_iso
    cut
    (TraceAnalyticDerivedMotiveCategory.objectOfCochainPreimageIso
      object)).mpr
    membership

/-- A represented `≤ cut` derived object gives exactness of the source complex
above the cut. -/
theorem exactAt_above_of_objectOf_tStructureLE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE cut
        (TraceAnalyticDerivedMotiveCategory.objectOf complex)) :
    ∀ degree : ℤ,
      cut < degree →
        complex.ExactAt degree :=
  (TraceAnalyticDerivedMotiveCategory
    .homologicalLE_objectOf_iff_exactAt cut complex).mp
    membership

/-- A represented `≥ cut` derived object gives exactness of the target complex
below the cut. -/
theorem exactAt_below_of_objectOf_tStructureGE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE cut
        (TraceAnalyticDerivedMotiveCategory.objectOf complex)) :
    ∀ degree : ℤ,
      degree < cut →
        complex.ExactAt degree :=
  (TraceAnalyticDerivedMotiveCategory
    .homologicalGE_objectOf_iff_exactAt cut complex).mp
    membership

/-- Represented cochain complexes with adjacent homological bounds have no
derived morphisms from the `≤ 0` side to the `≥ 1` side. -/
theorem homologicalBounds_objectOf_morphism_eq_zero
    (sourceComplex targetComplex : TraceAnalyticAbelianCochainComplex)
    (morphism :
      TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex ⟶
        TraceAnalyticDerivedMotiveCategory.objectOf targetComplex)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0
        (TraceAnalyticDerivedMotiveCategory.objectOf sourceComplex))
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1
        (TraceAnalyticDerivedMotiveCategory.objectOf targetComplex)) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .exactAtBounds_objectOf_morphism_eq_zero
      sourceComplex
      targetComplex
      morphism
      (TraceAnalyticDerivedMotiveCategory
        .exactAt_above_of_objectOf_tStructureLE
          0
          sourceComplex
          sourceMembership)
      (TraceAnalyticDerivedMotiveCategory
        .exactAt_below_of_objectOf_tStructureGE
          1
          targetComplex
          targetMembership)


/-- Adjacent homological bounds force the cochain-preimage conjugate of a
derived morphism to vanish. -/
theorem homologicalBounds_cochainPreimage_conjugate_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    (TraceAnalyticDerivedMotiveCategory
        .objectOfCochainPreimageIso source).hom ≫
      morphism ≫
        (TraceAnalyticDerivedMotiveCategory
          .objectOfCochainPreimageIso target).inv =
      0 :=
  TraceAnalyticDerivedMotiveCategory
    .homologicalBounds_objectOf_morphism_eq_zero
      (TraceAnalyticDerivedMotiveCategory.cochainPreimage source)
      (TraceAnalyticDerivedMotiveCategory.cochainPreimage target)
      ((TraceAnalyticDerivedMotiveCategory
          .objectOfCochainPreimageIso source).hom ≫
        morphism ≫
          (TraceAnalyticDerivedMotiveCategory
            .objectOfCochainPreimageIso target).inv)
      (TraceAnalyticDerivedMotiveCategory
        .objectOf_cochainPreimage_tStructureLE
          0
          source
          sourceMembership)
      (TraceAnalyticDerivedMotiveCategory
        .objectOf_cochainPreimage_tStructureGE
          1
          target
          targetMembership)


/-- Adjacent homological bounds force the underlying morphism to vanish.

This is the owner-level zero-field theorem for the concrete homological
predicates. -/
theorem homologicalBounds_morphism_eq_zero
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    morphism = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_iso_conjugate_eq_zero
      (TraceAnalyticDerivedMotiveCategory
        .objectOfCochainPreimageIso source)
      (TraceAnalyticDerivedMotiveCategory
        .objectOfCochainPreimageIso target)
      morphism
      (TraceAnalyticDerivedMotiveCategory
        .homologicalBounds_cochainPreimage_conjugate_eq_zero
          morphism
          sourceMembership
          targetMembership)

/-- A zero morphism remains zero after precomposition by any probe map. -/
theorem postcomp_zero_of_morphism_eq_zero
    {probe source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (hom : probe ⟶ source)
    (morphismZero : morphism = 0) :
    hom ≫ morphism = 0 :=
  Eq.trans
    (congrArg
      (fun map => hom ≫ map)
      morphismZero)
    (comp_zero hom)

/-- A morphism from the homological `≤ 0` aisle to the homological `≥ 1`
coaisle vanishes after postcomposition with every probe map. -/
theorem homologicalBounds_postcompVanishing
    {source target : TraceAnalyticDerivedMotiveCategory}
    (morphism : source ⟶ target)
    (sourceMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source)
    (targetMembership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target) :
    ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
      ∀ hom : probe.unop ⟶ source,
        hom ≫ morphism = 0 :=
  fun probe hom =>
    TraceAnalyticDerivedMotiveCategory.postcomp_zero_of_morphism_eq_zero
      morphism
      hom
      (TraceAnalyticDerivedMotiveCategory.homologicalBounds_morphism_eq_zero
        morphism
        sourceMembership
        targetMembership)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary

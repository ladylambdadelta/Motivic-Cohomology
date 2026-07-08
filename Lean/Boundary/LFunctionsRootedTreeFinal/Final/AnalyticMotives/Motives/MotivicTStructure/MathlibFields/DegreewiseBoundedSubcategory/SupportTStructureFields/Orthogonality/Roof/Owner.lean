import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorIso.Solved.Unconjugated.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Roof reductions for support orthogonality

This file records the two elementary categorical reductions supplied by the
bounded roof calculus.  An isomorphism denominator transports upper support to
the roof vertex, and a solved roof expression is zero as soon as its numerator
is zero.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Upper support transports from a target representative to the roof vertex
across an isomorphism denominator. -/
theorem supportTStructureGE_one_of_denominatorIso
    {targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 targetRepresentative) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE 1 roof :=
  CategoryTheory.mem_of_isIso denominator target_mem

/-- Lower support transports backward from an object to its representative
across a representative isomorphism. -/
theorem supportTStructureLE_zero_of_sourceRepresentativeIso
    {sourceRepresentative source :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE 0 sourceRepresentative :=
  let fullIso :
      sourceRepresentative ≅ source where
    hom := sourceIso.hom
    inv := sourceIso.inv
    hom_inv_id := sourceIso.hom_inv_id
    inv_hom_id := sourceIso.inv_hom_id
  CategoryTheory.ClosedUnderIsomorphisms.of_iso
    fullIso.symm
    source_mem

/-- Upper support transports backward from an object to its representative
across a representative isomorphism. -/
theorem supportTStructureGE_one_of_targetRepresentativeIso
    {targetRepresentative target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (targetIso : targetRepresentative.object ≅ target.object)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE 1 targetRepresentative :=
  let fullIso :
      targetRepresentative ≅ target where
    hom := targetIso.hom
    inv := targetIso.inv
    hom_inv_id := targetIso.hom_inv_id
    inv_hom_id := targetIso.inv_hom_id
  CategoryTheory.ClosedUnderIsomorphisms.of_iso
    fullIso.symm
    target_mem

/-- A solved internal roof formula collapses to zero when the numerator is
zero. -/
theorem hom_eq_zero_of_solvedRoof_numerator_zero
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (numerator_zero : numerator = 0) :
    morphism = 0 :=
  let numerator_inv_zero :
      numerator ≫ inv denominator =
        (0 : sourceRepresentative ⟶ targetRepresentative) :=
    Eq.trans
      (congrArg
        (fun map => map ≫ inv denominator)
        numerator_zero)
      (Category.zero_comp (inv denominator))
  let left_zero :
      sourceIso.inv ≫ numerator ≫ inv denominator =
        (0 : source.object ⟶ targetRepresentative) :=
    Eq.trans
      (Eq.symm
        (Category.assoc sourceIso.inv numerator (inv denominator)))
      (Eq.trans
        (congrArg
          (fun map => sourceIso.inv ≫ map)
          numerator_inv_zero)
        (Category.comp_zero sourceIso.inv))
  let solved_rhs_zero :
      sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom =
        (0 : source.object ⟶ target.object) :=
    Eq.trans
      (congrArg
        (fun map => map ≫ targetIso.hom)
        left_zero)
      (Category.zero_comp targetIso.hom)
  Eq.trans solved solved_rhs_zero

/-- The solved roof calculus reduces support orthogonality of a morphism to
support orthogonality of its numerator, with support transported to the roof
through the isomorphism denominator. -/
theorem hom_eq_zero_of_solvedRoof_support_numerator_zero
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target)
    (numerator_zero :
      numerator = 0) :
    morphism = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .hom_eq_zero_of_solvedRoof_numerator_zero
      sourceIso
      targetIso
      denominator
      numerator
      morphism
      solved
      numerator_zero

/-- The source representative of a solved roof remains in support `LE 0`. -/
theorem solvedRoof_sourceRepresentative_mem_supportTStructureLE_zero
    {source sourceRepresentative :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE 0 sourceRepresentative :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureLE_zero_of_sourceRepresentativeIso
      sourceIso
      source_mem

/-- The roof vertex of a solved roof remains in support `GE 1`. -/
theorem solvedRoof_roof_mem_supportTStructureGE_one
    {target targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE 1 roof :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureGE_one_of_denominatorIso
      denominator
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE_one_of_targetRepresentativeIso
          targetIso
          target_mem)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

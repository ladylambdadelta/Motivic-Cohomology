import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorNullCone.DenominatorIso.Solved.Unconjugated.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Roof.Owner

/-!
# Null-cone roof reductions for support orthogonality

This file refines the roof-level support orthogonality reductions so that the
solved roof formula retains the analytic distinguished-triangle certificate for
the denominator.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The raw denominator of a null-cone solved roof belongs to the Verdier
inverted morphism class. -/
theorem nullConeSolvedRoof_rawDenominator_inverted
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      rawDenominator :=
  TraceAnalyticStableNullSubcategory.inverted_firstMap_of_triangle
    distinguished
    null

/-- The stable quotient image of the raw denominator of a null-cone solved roof
is an isomorphism. -/
theorem nullConeSolvedRoof_rawDenominator_quotient_isIso
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        rawDenominator) :=
  CategoryTheory.Localization.inverts
    TraceAnalyticDMgmComparisonSource.quotientFunctor
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .nullConeSolvedRoof_rawDenominator_inverted
        rawDenominator
        denominatorCoconeMap
        denominatorBoundary
        distinguished
        null)

/-- The transported internal denominator of a null-cone solved roof is an
isomorphism. -/
theorem nullConeSolvedRoof_denominator_isIso_of_eq
    {targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (denominator : targetRepresentative ⟶ roof)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (denominator_eq :
      denominator =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            rawDenominator ≫
          eqToHom (Eq.symm roof_eq)) :
    IsIso denominator :=
  let quotientDenominatorIso :
      IsIso
        (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
          rawDenominator) :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .nullConeSolvedRoof_rawDenominator_quotient_isIso
        rawDenominator
        denominatorCoconeMap
        denominatorBoundary
        distinguished
        null
  let roofTransportIso :
      IsIso (eqToHom (Eq.symm roof_eq)) :=
    (eqToIso (Eq.symm roof_eq)).isIso_hom
  let transportedIso :
      IsIso
        (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            rawDenominator ≫
          eqToHom (Eq.symm roof_eq)) :=
    IsIso.comp_isIso'
      quotientDenominatorIso
      roofTransportIso
  Eq.subst
    (motive := fun arrow => IsIso arrow)
    (Eq.symm denominator_eq)
    transportedIso

/-- A solved roof expression with a denominator coming from a raw distinguished
triangle with null cone collapses to zero when its numerator is zero. -/
theorem hom_eq_zero_of_nullConeSolvedRoof_numerator_zero
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (numerator_zero : numerator = 0) :
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

/-- A solved roof expression whose internal denominator is identified with the
transported raw denominator of a null-cone triangle collapses to zero when its
numerator is zero.  The denominator isomorphism is derived from the analytic
triangle certificate. -/
theorem hom_eq_zero_of_nullConeSolvedRoof_numerator_zero_of_denominator_eq
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (denominator_eq :
      denominator =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            rawDenominator ≫
          eqToHom (Eq.symm roof_eq))
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (numerator_zero : numerator = 0) :
    morphism = 0 :=
  let denominatorIso :
      IsIso denominator :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .nullConeSolvedRoof_denominator_isIso_of_eq
        denominator
        roof_eq
        rawDenominator
        denominatorCoconeMap
        denominatorBoundary
        distinguished
        null
        denominator_eq
  letI denominatorIsoField : IsIso denominator := denominatorIso
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .hom_eq_zero_of_nullConeSolvedRoof_numerator_zero
      sourceIso
      targetIso
      denominator
      numerator
      morphism
      roof_eq
      rawDenominator
      denominatorCoconeMap
      denominatorBoundary
      distinguished
      null
      solved
      numerator_zero

/-- The null-cone solved roof calculus reduces support orthogonality of a
morphism to support orthogonality of its numerator. -/
theorem hom_eq_zero_of_nullConeSolvedRoof_support_numerator_zero
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target)
    (numerator_zero : numerator = 0) :
    morphism = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .hom_eq_zero_of_nullConeSolvedRoof_numerator_zero
      sourceIso
      targetIso
      denominator
      numerator
      morphism
      roof_eq
      rawDenominator
      denominatorCoconeMap
      denominatorBoundary
      distinguished
      null
      solved
      numerator_zero

/-- The null-cone solved roof support reduction with the denominator
isomorphism derived from the raw analytic null-cone triangle. -/
theorem hom_eq_zero_of_nullConeSolvedRoof_support_numerator_zero_of_denominator_eq
    {source target sourceRepresentative targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    (numerator : sourceRepresentative ⟶ roof)
    (morphism : source ⟶ target)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (denominator_eq :
      denominator =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            rawDenominator ≫
          eqToHom (Eq.symm roof_eq))
    (solved :
      morphism =
        sourceIso.inv ≫ numerator ≫ inv denominator ≫ targetIso.hom)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target)
    (numerator_zero : numerator = 0) :
    morphism = 0 :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .hom_eq_zero_of_nullConeSolvedRoof_numerator_zero_of_denominator_eq
      sourceIso
      targetIso
      denominator
      numerator
      morphism
      roof_eq
      rawDenominator
      denominatorCoconeMap
      denominatorBoundary
      distinguished
      null
      denominator_eq
      solved
      numerator_zero

/-- The source representative of a null-cone solved roof remains in support
`LE 0`. -/
theorem nullConeSolvedRoof_sourceRepresentative_mem_supportTStructureLE_zero
    {source sourceRepresentative :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (sourceIso : sourceRepresentative.object ≅ source.object)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (source_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 source) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE 0 sourceRepresentative :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .solvedRoof_sourceRepresentative_mem_supportTStructureLE_zero
      sourceIso
      source_mem

/-- The roof vertex of a null-cone solved roof remains in support `GE 1`. -/
theorem nullConeSolvedRoof_roof_mem_supportTStructureGE_one
    {target targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    [IsIso denominator]
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE 1 roof :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .solvedRoof_roof_mem_supportTStructureGE_one
      targetIso
      denominator
      target_mem

/-- The roof vertex of a null-cone solved roof remains in support `GE 1`,
with the denominator isomorphism derived from the raw analytic null-cone
triangle. -/
theorem nullConeSolvedRoof_roof_mem_supportTStructureGE_one_of_denominator_eq
    {target targetRepresentative roof :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    {roofVertex denominatorCone :
      TraceAnalyticAdditiveHomotopyCategory}
    (targetIso : targetRepresentative.object ≅ target.object)
    (denominator : targetRepresentative ⟶ roof)
    (roof_eq :
      roof.object =
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex)
    (rawDenominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorCoconeMap : roofVertex ⟶ denominatorCone)
    (denominatorBoundary :
      denominatorCone ⟶
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          targetComplex)⟦(1 : ℤ)⟧)
    (distinguished :
      Triangle.mk
          rawDenominator
          denominatorCoconeMap
          denominatorBoundary ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (null : TraceAnalyticStableNullSubcategory.P denominatorCone)
    (denominator_eq :
      denominator =
        TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            rawDenominator ≫
          eqToHom (Eq.symm roof_eq))
    (target_mem :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 target) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE 1 roof :=
  let denominatorIso :
      IsIso denominator :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .nullConeSolvedRoof_denominator_isIso_of_eq
        denominator
        roof_eq
        rawDenominator
        denominatorCoconeMap
        denominatorBoundary
        distinguished
        null
        denominator_eq
  letI denominatorIsoField : IsIso denominator := denominatorIso
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .nullConeSolvedRoof_roof_mem_supportTStructureGE_one
      targetIso
      denominator
      roof_eq
      rawDenominator
      denominatorCoconeMap
      denominatorBoundary
      distinguished
      null
      target_mem

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

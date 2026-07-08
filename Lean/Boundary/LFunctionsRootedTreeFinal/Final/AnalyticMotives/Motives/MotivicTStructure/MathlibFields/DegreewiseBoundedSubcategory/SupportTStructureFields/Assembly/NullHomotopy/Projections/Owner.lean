import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.NullHomotopy.Owner

/-!
# Projections from the null-homotopy support t-structure

This file exposes the remaining Mathlib `TStructure` fields of the
null-homotopy support assembly.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The null-homotopy support t-structure supplies the `LE`
closed-under-isomorphism field. -/
theorem supportTStructureOfNullHomotopicIdentity_LE_closedUnderIsomorphisms
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).LE cut) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .LE_closedUnderIsomorphisms
        cut

/-- The null-homotopy support t-structure supplies the `GE`
closed-under-isomorphism field. -/
theorem supportTStructureOfNullHomotopicIdentity_GE_closedUnderIsomorphisms
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      ((TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).GE cut) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .GE_closedUnderIsomorphisms
        cut

/-- The null-homotopy support t-structure supplies the `LE_shift` field. -/
theorem supportTStructureOfNullHomotopicIdentity_LE_shift
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).LE
          sourceCut
          object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity
        nullHomotopicIdentity).LE
        targetCut
        (object⟦shift⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .LE_shift
        sourceCut
        shift
        targetCut
        cut_eq
        object
        membership

/-- The null-homotopy support t-structure supplies the `GE_shift` field. -/
theorem supportTStructureOfNullHomotopicIdentity_GE_shift
    (nullHomotopicIdentity :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          ∃ hom :
            ∀ i j,
              (ComplexShape.up ℤ).Rel j i →
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)).X i ⟶
                  (CochainComplex.mappingCone
                    (TraceAnalyticMotivicTStructure
                      .additiveNormalizedConeComparisonCochainMap
                        1
                        complex)).X j,
            𝟙
                (CochainComplex.mappingCone
                  (TraceAnalyticMotivicTStructure
                    .additiveNormalizedConeComparisonCochainMap
                      1
                      complex)) =
              _root_.HomologicalComplex.nullHomotopicMap' hom)
    (sourceCut shift targetCut : ℤ)
    (cut_eq : shift + targetCut = sourceCut)
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (membership :
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureOfNullHomotopicIdentity
          nullHomotopicIdentity).GE
          sourceCut
          object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfNullHomotopicIdentity
        nullHomotopicIdentity).GE
        targetCut
        (object⟦shift⟧) :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfNullHomotopicIdentity nullHomotopicIdentity)
      .GE_shift
        sourceCut
        shift
        targetCut
        cut_eq
        object
        membership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

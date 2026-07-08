import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Monotonicity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Truncation.Owner

/-!
# Support-based t-structure assembly

This file assembles Mathlib's `TStructure` record on the degreewise bounded
stable analytic source from the support-based field theorems.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The support-based motivic t-structure on the degreewise bounded stable
analytic source, assembled from concrete analytic support predicates. -/
def supportTStructureOfConeComparison
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    TStructure TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable where
  LE :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE
  GE :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE
  LE_closedUnderIsomorphisms :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE_closedUnderIsomorphisms
  GE_closedUnderIsomorphisms :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE_closedUnderIsomorphisms
  LE_shift :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE_shift
  GE_shift :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE_shift
  zero' :=
    fun hom source_mem target_mem =>
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructure_zero
          hom
          source_mem
          target_mem
  LE_zero_le :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureLE_zero_le
  GE_one_le :=
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureGE_one_le
  exists_triangle_zero_one :=
    fun object =>
      Exists.elim
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .exists_support_truncation_triangle_zero_one
            object
            coneComparison)
        (fun lower lowerData =>
          Exists.elim
            lowerData
            (fun upper upperData =>
              And.elim
                upperData
                (fun lower_mem upperAndTriangle =>
                  And.elim
                    upperAndTriangle
                    (fun upper_mem triangleData =>
                      Exists.elim
                        triangleData
                        (fun firstMap firstMapData =>
                          Exists.elim
                            firstMapData
                            (fun secondMap secondMapData =>
                              Exists.elim
                                secondMapData
                                (fun connectingMap distinguished =>
                                  Exists.intro
                                    lower
                                    (Exists.intro
                                      upper
                                      (Exists.intro
                                        lower_mem
                                        (Exists.intro
                                          upper_mem
                                          (Exists.intro
                                            firstMap
                                            (Exists.intro
                                              secondMap
                                              (Exists.intro
                                                connectingMap
                                                distinguished)))))))))))))

/-- The assembled support t-structure has the support `LE` predicate. -/
theorem supportTStructureOfConeComparison_LE
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).LE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE :=
  rfl

/-- The assembled support t-structure has the support `GE` predicate. -/
theorem supportTStructureOfConeComparison_GE
    (coneComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .stableNormalizedConeComparisonMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfConeComparison coneComparison).GE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

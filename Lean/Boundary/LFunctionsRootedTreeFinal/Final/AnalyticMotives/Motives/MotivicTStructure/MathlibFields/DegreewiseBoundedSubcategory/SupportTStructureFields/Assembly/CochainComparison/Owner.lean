import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Assembly.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.IdentityCone.Owner

/-!
# Support t-structure from cochain cone comparisons

This file connects the concrete cochain-level normalized cone-to-upper
comparison route to the support-based `TStructure` on the degreewise bounded
stable source.
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

/-- Cochain-level isomorphisms of the normalized cone-to-upper maps supply the
stable cone-comparison family used by the support truncation field. -/
theorem supportConeComparison_of_isIso_cochainMap
    (cochainComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex))
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        1
        complex) :=
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .additiveNormalizedConeComparisonCochainMap 1 complex) :=
    cochainComparison complex bounded
  TraceAnalyticMotivicTStructure
    .stableNormalizedConeComparisonMap_isIso_of_isIso_cochainMap
      1
      complex

/-- The support-based motivic t-structure assembled from concrete
cochain-level normalized cone-to-upper isomorphisms. -/
def supportTStructureOfCochainComparison
    (cochainComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex)) :
    TStructure TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfConeComparison
      (fun complex bounded =>
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportConeComparison_of_isIso_cochainMap
            cochainComparison
            complex
            bounded)

/-- The cochain-comparison support t-structure has the support `LE`
predicate. -/
theorem supportTStructureOfCochainComparison_LE
    (cochainComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfCochainComparison cochainComparison).LE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE :=
  rfl

/-- The cochain-comparison support t-structure has the support `GE`
predicate. -/
theorem supportTStructureOfCochainComparison_GE
    (cochainComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex)) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportTStructureOfCochainComparison cochainComparison).GE =
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE :=
  rfl

/-- The cochain-comparison support t-structure has the proved zero-one
truncation triangle field. -/
theorem supportTStructureOfCochainComparison_exists_triangle_zero_one
    (cochainComparison :
      ∀ {bound : Nat}
        (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison.sourceComplexDegreewiseIsoClosureBoundedBy
            complex
            bound →
          IsIso
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap 1 complex))
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfCochainComparison cochainComparison).LE 0 lower)
      (_ :
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .supportTStructureOfCochainComparison cochainComparison).GE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .distinguishedTriangles :=
  (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportTStructureOfCochainComparison cochainComparison)
      .exists_triangle_zero_one object

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

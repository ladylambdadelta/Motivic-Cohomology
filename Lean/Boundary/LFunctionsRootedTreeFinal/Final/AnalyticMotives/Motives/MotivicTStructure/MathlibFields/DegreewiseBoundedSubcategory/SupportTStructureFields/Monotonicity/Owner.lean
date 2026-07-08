import Mathlib.Tactic.Omega
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.Transport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Adjacent monotonicity for support-based t-structure predicates

This file proves the adjacent monotonicity fields for the support-based
degreewise bounded predicates by reducing them to concrete containment of the
integer lower and upper tail embeddings.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The lower-tail embedding at cut `0` lands inside the lower-tail embedding
at cut `1`, with index shifted by one. -/
theorem truncLEEmbedding_zero_image_in_truncLEEmbedding_one
    (index : ℕ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 1).f (index + 1) =
      (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).f index := by
  omega

/-- The upper-tail embedding at cut `1` lands inside the upper-tail embedding
at cut `0`, with index shifted by one. -/
theorem truncGEEmbedding_one_image_in_truncGEEmbedding_zero
    (index : ℕ) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 0).f (index + 1) =
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f index := by
  omega

/-- Complement implication for adjacent lower-tail support. -/
theorem truncLEEmbedding_zero_one_complement
    (degree : ℤ)
    (targetComplement :
      ∀ targetIndex,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 1).f targetIndex ≠
          degree)
    (sourceIndex : ℕ) :
    (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).f sourceIndex ≠
      degree :=
  fun sourceEq =>
    targetComplement
      (sourceIndex + 1)
      (Eq.trans
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .truncLEEmbedding_zero_image_in_truncLEEmbedding_one sourceIndex)
        sourceEq)

/-- Complement implication for adjacent upper-tail support. -/
theorem truncGEEmbedding_one_zero_complement
    (degree : ℤ)
    (targetComplement :
      ∀ targetIndex,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 0).f targetIndex ≠
          degree)
    (sourceIndex : ℕ) :
    (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f sourceIndex ≠
      degree :=
  fun sourceEq =>
    targetComplement
      (sourceIndex + 1)
      (Eq.trans
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .truncGEEmbedding_one_image_in_truncGEEmbedding_zero sourceIndex)
        sourceEq)

/-- Support-based adjacent `LE` monotonicity. -/
theorem supportTStructureLE_zero_le :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 0 ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureLE 1 :=
  fun object membership =>
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedLEIsoClosedAmbient_transport
        0
        1
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .truncLEEmbedding_zero_one_complement
        object.object
        membership

/-- Support-based adjacent `GE` monotonicity. -/
theorem supportTStructureGE_one_le :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 1 ≤
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportTStructureGE 0 :=
  fun object membership =>
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportedGEIsoClosedAmbient_transport
        1
        0
        TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .truncGEEmbedding_one_zero_complement
        object.object
        membership

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportPredicates.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Owner

/-!
# Concrete representatives as support-heart objects

This file packages degreewise bounded stable objects with concrete lower and
upper ambient support evidence as objects of the support heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Concrete ambient lower and upper support evidence produces support-heart
membership. -/
theorem supportHeart_of_supportedAmbient
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient cut object.object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut object :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportHeart_intro
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient_le_supportedLEIsoClosedAmbient
          cut
          lower)
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient_le_supportedGEIsoClosedAmbient
          cut
          upper)

/-- Package a degreewise bounded stable object with concrete lower and upper
support evidence as a support-heart object. -/
def SupportHeart.ofSupportedAmbient
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient cut object.object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut :=
  ⟨
    object,
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart_of_supportedAmbient lower upper
  ⟩

/-- The support-heart representative has the original degreewise bounded stable
object as its carried object. -/
theorem SupportHeart.ofSupportedAmbient_object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEAmbient cut object.object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.ofSupportedAmbient object lower upper).object =
      object :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

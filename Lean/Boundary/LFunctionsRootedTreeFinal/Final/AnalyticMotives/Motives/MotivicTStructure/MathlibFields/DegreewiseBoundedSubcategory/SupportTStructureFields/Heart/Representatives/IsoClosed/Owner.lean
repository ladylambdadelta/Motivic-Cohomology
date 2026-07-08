import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Heart.Representatives.Owner

/-!
# Iso-closed representatives as support-heart objects

This file packages degreewise bounded stable objects with iso-closed lower and
upper ambient support evidence as objects of the support heart.  This is the
representative surface used by the support t-structure fields themselves.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Iso-closed ambient lower and upper support evidence produces support-heart
membership. -/
theorem supportHeart_of_supportedIsoClosedAmbient
    {cut : ℤ}
    {object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient cut object.object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart cut object :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .supportHeart_intro
      lower
      upper

/-- Package a degreewise bounded stable object with iso-closed lower and upper
support evidence as a support-heart object. -/
def SupportHeart.ofSupportedIsoClosedAmbient
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient cut object.object) :
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart cut :=
  ⟨
    object,
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .supportHeart_of_supportedIsoClosedAmbient lower upper
  ⟩

/-- The iso-closed support-heart representative carries the original
degreewise bounded stable object. -/
theorem SupportHeart.ofSupportedIsoClosedAmbient_object
    {cut : ℤ}
    (object : TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable)
    (lower :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedLEIsoClosedAmbient cut object.object)
    (upper :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .supportedGEIsoClosedAmbient cut object.object) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .SupportHeart.ofSupportedIsoClosedAmbient object lower upper).object =
      object :=
  rfl

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Vertical.Owner

/-!
# Motive-root vertical pullback-pushforward operation lengths

This file mirrors the public vertical-composition count-as-list-length formulas
for the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root vertical northwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Motive-root vertical northeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_northeastCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Motive-root vertical southwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Motive-root vertical southeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicVerticalComp_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    target.certificateLedger.importedRectangleCount +
        first.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        first.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicVerticalComp_southeastCertificateLedgerRectangles_length
    morphism
    left
    right

end AnalyticMotives
end LFunctions
end Boundary

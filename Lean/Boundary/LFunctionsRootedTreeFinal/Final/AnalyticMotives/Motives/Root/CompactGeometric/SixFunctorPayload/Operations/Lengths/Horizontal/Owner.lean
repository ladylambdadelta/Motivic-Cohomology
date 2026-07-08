import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Owner

/-!
# Motive-root horizontal pullback-pushforward operation lengths

This file mirrors the public horizontal-composition count-as-list-length
formulas for the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root horizontal northwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Motive-root horizontal northeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_northeastCertificateLedgerRectangles_length
    left
    right
    probe

/-- Motive-root horizontal southwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Motive-root horizontal southeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    third.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (third.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicHorizontalComp_southeastCertificateLedgerRectangles_length
    left
    right
    probe

end AnalyticMotives
end LFunctions
end Boundary

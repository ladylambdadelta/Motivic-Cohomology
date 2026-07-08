import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Identity.Vertical.Owner

/-!
# Motive-root vertical-identity pullback-pushforward operation lengths

This file mirrors the public vertical-identity count-as-list-length formulas
for the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root vertical-identity northwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Motive-root vertical-identity northeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_northeastCertificateLedgerRectangles_length
    morphism
    probe

/-- Motive-root vertical-identity southwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southwestCertificateLedgerRectangles_length
    morphism
    probe

/-- Motive-root vertical-identity southeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityVertical_southeastCertificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary

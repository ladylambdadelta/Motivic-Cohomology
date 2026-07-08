import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.PublicOperations.Lengths.Identity.Horizontal.Owner

/-!
# Motive-root horizontal-identity pullback-pushforward operation lengths

This file mirrors the public horizontal-identity count-as-list-length formulas
for the compact pullback-pushforward square under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root horizontal-identity northwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northwestCertificateLedgerRectangles_length
    generator
    probe

/-- Motive-root horizontal-identity northeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_northeastCertificateLedgerRectangles_length
    generator
    probe

/-- Motive-root horizontal-identity southwest rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southwestCertificateLedgerRectangles_length
    generator
    probe

/-- Motive-root horizontal-identity southeast rectangle-count-as-length wrapper. -/
theorem TraceAnalyticMotive.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  TraceSixFunctorPullbackPushforward.publicIdentityHorizontal_southeastCertificateLedgerRectangles_length
    generator
    probe

end AnalyticMotives
end LFunctions
end Boundary

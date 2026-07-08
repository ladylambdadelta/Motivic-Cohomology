import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Horizontal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Vertical.Owner

/-!
# Motive-root compact pullback-pushforward operation lengths

This file collects motive-root count-as-list-length facades for compact
pullback-pushforward square operation payloads.  The aggregate surface exposes
the northwest count-as-length formula for each composition mode.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate horizontal-composition northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicOperation_northwestHorizontalCertificateLedgerRectangles_length
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (first.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicHorizontalComp_northwestCertificateLedgerRectangles_length
    left
    right
    probe

/-- Motive-root aggregate vertical-composition northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicOperation_northwestVerticalCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        third.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicVerticalComp_northwestCertificateLedgerRectangles_length
    morphism
    left
    right

/-- Motive-root aggregate mixed-composition northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicOperation_northwestMixedCertificateLedgerRectangles_length
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    hFirst.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount =
      (hFirst.certificateLedger.importedRectangles ++
        vThird.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicMixedComp_northwestCertificateLedgerRectangles_length
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root aggregate horizontal-identity northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicOperation_northwestIdentityHorizontalCertificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentity_northwestHorizontalCertificateLedgerRectangles_length
    generator
    probe

/-- Motive-root aggregate vertical-identity northwest rectangle count-as-length. -/
theorem TraceAnalyticMotive.publicOperation_northwestIdentityVerticalCertificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  TraceAnalyticMotive.publicIdentity_northwestVerticalCertificateLedgerRectangles_length
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary

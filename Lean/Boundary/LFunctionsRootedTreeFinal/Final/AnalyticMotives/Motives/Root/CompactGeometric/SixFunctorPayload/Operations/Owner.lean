import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Horizontal.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Identity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Mixed.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorPayload.Operations.Vertical.Owner

/-!
# Motive-root compact-geometric six-functor operation payloads

This file collects motive-root operation payload facades for the compact
pullback-pushforward square.  The aggregate surface exposes the northwest
rectangle-count formula for each composition mode.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root aggregate horizontal-composition northwest rectangle count. -/
theorem TraceAnalyticMotive.publicOperation_northwestHorizontalImportedRectangleCount
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (left ≫ right)
        probe =
      first.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicHorizontalComp_northwestImportedRectangleCount
    left
    right
    probe

/-- Motive-root aggregate vertical-composition northwest rectangle count. -/
theorem TraceAnalyticMotive.publicOperation_northwestVerticalImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (left ≫ right) =
      source.certificateLedger.importedRectangleCount +
        third.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicVerticalComp_northwestImportedRectangleCount
    morphism
    left
    right

/-- Motive-root aggregate mixed-composition northwest rectangle count. -/
theorem TraceAnalyticMotive.publicOperation_northwestMixedImportedRectangleCount
    {hFirst hSecond hThird : TraceAnalyticGeometricGenerator}
    (hLeft : hFirst ⟶ hSecond)
    (hRight : hSecond ⟶ hThird)
    {vFirst vSecond vThird : TraceAnalyticGeometricGenerator}
    (vLeft : vFirst ⟶ vSecond)
    (vRight : vSecond ⟶ vThird) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (hLeft ≫ hRight)
        (vLeft ≫ vRight) =
      hFirst.certificateLedger.importedRectangleCount +
        vThird.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicMixedComp_northwestImportedRectangleCount
    hLeft
    hRight
    vLeft
    vRight

/-- Motive-root aggregate horizontal-identity northwest rectangle count. -/
theorem TraceAnalyticMotive.publicOperation_northwestIdentityHorizontalImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentity_northwestHorizontalImportedRectangleCount
    generator
    probe

/-- Motive-root aggregate vertical-identity northwest rectangle count. -/
theorem TraceAnalyticMotive.publicOperation_northwestIdentityVerticalImportedRectangleCount
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.publicIdentity_northwestVerticalImportedRectangleCount
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary

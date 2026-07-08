import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Owner

/-!
# Ledger rectangle lists for identity list-level payload operations

This file records certificate-ledger rectangle-list formulas when either the
horizontal morphism or the vertical probe in the compact pullback-pushforward
square is an identity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity horizontal northwest rectangle list is counted by the generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_rectangles_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal northeast rectangle list is counted by the generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_rectangles_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southwest rectangle list is counted by the generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_rectangles_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southeast rectangle list is counted by the generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_rectangles_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity vertical northwest rectangle list is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical northeast rectangle list is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southwest rectangle list is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southwest_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southeast rectangle list is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southeast_rectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
    morphism
    (𝟙 probe)

end AnalyticMotives
end LFunctions
end Boundary

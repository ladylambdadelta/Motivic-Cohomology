import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Owner

/-!
# Ledger counts for identity pullback-pushforward payload operations

This file records certificate-ledger count formulas when either the horizontal
morphism or the vertical probe in the compact pullback-pushforward square is an
identity.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity horizontal northwest count is counted by the generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_count_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal northeast count is counted by the generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_count_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southwest count is counted by the generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_count_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity horizontal southeast count is counted by the generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_count_eq_certificateLedgers
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        (𝟙 generator)
        probe =
      generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
    (𝟙 generator)
    probe

/-- Identity vertical northwest count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical northeast count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southwest count is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southwest_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        (𝟙 probe) =
      source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

/-- Identity vertical southeast count is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southeast_count_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        (𝟙 probe) =
      target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount :=
  TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
    morphism
    (𝟙 probe)

end AnalyticMotives
end LFunctions
end Boundary

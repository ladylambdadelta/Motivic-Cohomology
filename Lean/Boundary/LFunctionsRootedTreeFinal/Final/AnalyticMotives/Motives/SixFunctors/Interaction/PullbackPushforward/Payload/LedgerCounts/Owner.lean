import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Payload.LedgerCounts.Owner

/-!
# Ledger counts for the compact pullback-pushforward square

This file records that each corner payload count in the concrete
pullback-pushforward square is counted by the certificate ledgers of the two
generators that meet at that corner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest corner count is counted by source and probe-target certificate ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_target_certificateLedger
      probe)

/-- Northeast corner count is counted by target and probe-target certificate ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorSourceImportedRectangleCount_eq_target_certificateLedger
      probe)

/-- Southwest corner count is counted by source and probe-source certificate ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount
        morphism
        probe =
      source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorSourceImportedRectangleCount_eq_source_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_source_certificateLedger
      probe)

/-- Southeast corner count is counted by target and probe-source certificate ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount
        morphism
        probe =
      target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount :=
  congrArg₂
    Nat.add
    (TraceSixFunctorPushforward.compactGeneratorTargetImportedRectangleCount_eq_target_certificateLedger
      morphism)
    (TraceSixFunctorPullback.compactGeneratorTargetImportedRectangleCount_eq_source_certificateLedger
      probe)

end AnalyticMotives
end LFunctions
end Boundary

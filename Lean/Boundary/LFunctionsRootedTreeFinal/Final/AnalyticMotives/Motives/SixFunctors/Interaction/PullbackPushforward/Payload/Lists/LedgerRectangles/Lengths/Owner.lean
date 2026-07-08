import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Lists.LedgerRectangles.Owner

/-!
# Lengths of ledger rectangle lists for pullback-pushforward payloads

This file connects the certificate-ledger rectangle-list formulas for the four
corners of the compact pullback-pushforward square to the corresponding
certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest ledger rectangle-list length is counted by source and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        morphism
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Northeast ledger rectangle-list length is counted by target and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.northeastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        morphism
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Southwest ledger rectangle-list length is counted by source and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southwestCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    source.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        morphism
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Southeast ledger rectangle-list length is counted by target and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.southeastCertificateLedgerImportedRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    target.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        morphism
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
          morphism
          probe)))

end AnalyticMotives
end LFunctions
end Boundary

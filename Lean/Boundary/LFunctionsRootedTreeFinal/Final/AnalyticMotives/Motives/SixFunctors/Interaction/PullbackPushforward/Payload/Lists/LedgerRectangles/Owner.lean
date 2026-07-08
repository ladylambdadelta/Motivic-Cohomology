import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Owner

/-!
# Ledger rectangle lists for pullback-pushforward square payloads

This file records that each imported-rectangle list carried by a corner of the
compact pullback-pushforward square is the concatenation of the corresponding
certificate-ledger rectangle lists.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Northwest rectangle list is the source ledger list followed by the probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.northwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  congrArg₂
    List.append
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      source)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      probeTarget)

/-- Northeast rectangle list is the target ledger list followed by the probe-target ledger list. -/
theorem TraceSixFunctorPullbackPushforward.northeastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.northeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles :=
  congrArg₂
    List.append
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      target)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      probeTarget)

/-- Southwest rectangle list is the source ledger list followed by the probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.southwestImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southwestImportedRectangles
        morphism
        probe =
      source.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  congrArg₂
    List.append
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      source)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      probeSource)

/-- Southeast rectangle list is the target ledger list followed by the probe-source ledger list. -/
theorem TraceSixFunctorPullbackPushforward.southeastImportedRectangles_eq_certificateLedgers
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullbackPushforward.southeastImportedRectangles
        morphism
        probe =
      target.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles :=
  congrArg₂
    List.append
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      target)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger
      probeSource)

end AnalyticMotives
end LFunctions
end Boundary

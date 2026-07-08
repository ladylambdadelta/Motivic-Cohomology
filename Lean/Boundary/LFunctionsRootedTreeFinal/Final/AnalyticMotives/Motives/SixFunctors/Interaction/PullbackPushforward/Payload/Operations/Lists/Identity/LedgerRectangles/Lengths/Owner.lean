import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Identity.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Payload.Operations.Lists.Identity.LedgerRectangles.Owner

/-!
# Lengths of identity operation ledger rectangle lists

This file connects identity-operation certificate-ledger rectangle-list formulas
to identity-operation certificate-ledger count formulas.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Identity horizontal northwest ledger rectangle-list length is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_count_eq_certificateLedgers
        generator
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        (𝟙 generator)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityHorizontal_northwest_rectangles_eq_certificateLedgers
          generator
          probe)))

/-- Identity horizontal northeast ledger rectangle-list length is counted by generator and probe-target ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeTarget.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeTarget.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_count_eq_certificateLedgers
        generator
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        (𝟙 generator)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityHorizontal_northeast_rectangles_eq_certificateLedgers
          generator
          probe)))

/-- Identity horizontal southwest ledger rectangle-list length is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_count_eq_certificateLedgers
        generator
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        (𝟙 generator)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityHorizontal_southwest_rectangles_eq_certificateLedgers
          generator
          probe)))

/-- Identity horizontal southeast ledger rectangle-list length is counted by generator and probe-source ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_certificateLedgerRectangles_length
    (generator : TraceAnalyticGeometricGenerator)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    generator.certificateLedger.importedRectangleCount +
        probeSource.certificateLedger.importedRectangleCount =
      (generator.certificateLedger.importedRectangles ++
        probeSource.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_count_eq_certificateLedgers
        generator
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        (𝟙 generator)
        probe)
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityHorizontal_southeast_rectangles_eq_certificateLedgers
          generator
          probe)))

/-- Identity vertical northwest ledger rectangle-list length is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northwest_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityVertical_northwest_count_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northwestImportedRectangleCount_eq_length
        morphism
        (𝟙 probe))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityVertical_northwest_rectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Identity vertical northeast ledger rectangle-list length is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_northeast_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityVertical_northeast_count_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.northeastImportedRectangleCount_eq_length
        morphism
        (𝟙 probe))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityVertical_northeast_rectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Identity vertical southwest ledger rectangle-list length is counted by source and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southwest_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    source.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (source.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityVertical_southwest_count_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southwestImportedRectangleCount_eq_length
        morphism
        (𝟙 probe))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityVertical_southwest_rectangles_eq_certificateLedgers
          morphism
          probe)))

/-- Identity vertical southeast ledger rectangle-list length is counted by target and probe ledgers. -/
theorem TraceSixFunctorPullbackPushforward.identityVertical_southeast_certificateLedgerRectangles_length
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    (probe : TraceAnalyticGeometricGenerator) :
    target.certificateLedger.importedRectangleCount +
        probe.certificateLedger.importedRectangleCount =
      (target.certificateLedger.importedRectangles ++
        probe.certificateLedger.importedRectangles).length :=
  Eq.trans
    (Eq.sym
      (TraceSixFunctorPullbackPushforward.identityVertical_southeast_count_eq_certificateLedgers
        morphism
        probe))
    (Eq.trans
      (TraceSixFunctorPullbackPushforward.southeastImportedRectangleCount_eq_length
        morphism
        (𝟙 probe))
      (congrArg
        List.length
        (TraceSixFunctorPullbackPushforward.identityVertical_southeast_rectangles_eq_certificateLedgers
          morphism
          probe)))

end AnalyticMotives
end LFunctions
end Boundary

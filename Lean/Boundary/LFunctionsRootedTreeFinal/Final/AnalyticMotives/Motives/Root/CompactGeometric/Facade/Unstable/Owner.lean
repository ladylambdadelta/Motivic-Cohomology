import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Facade.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Compact.Payload.Owner

/-!
# Motive-root compact-geometric unstable facade

This file exposes compact-generator unstable motive and identity payload wrappers
under the `TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact geometric analytic generators determine unstable analytic motives. -/
theorem TraceAnalyticMotive.compactGenerator_unstableMotive_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive.underlying =
      generator.traceObject :=
  TraceAnalyticGeometricGenerator.unstableMotive_underlying
    generator

/-- Compact-generator unstable identity is represented by the identity localization word. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  TraceAnalyticGeometricGenerator.unstableIdentity_eq_ofWord
    generator

/-- Compact-generator unstable imported rectangles are extracted from its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq_certificateLedger
    generator

/-- Compact-generator unstable imported count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_certificateLedger
    generator

/-- Compact-generator unstable imported count is its unstable rectangle-list length. -/
theorem TraceAnalyticMotive.compactGenerator_unstableImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.unstableImportedRectangles.length :=
  TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_length
    generator

/-- Compact-generator unstable certificate ledger is its compact certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableCertificateLedger_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableCertificateLedger =
      generator.certificateLedger :=
  TraceAnalyticGeometricGenerator.unstableCertificateLedger_eq_certificateLedger
    generator

/-- Compact-generator unstable bookkeeping count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.unstableTraceBookkeepingCount_eq_certificateLedger
    generator

/-- Compact-generator unstable rewrite-step count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.unstableRewriteStepCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity source rectangles come from its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangles_eq_certificateLedger
    generator

/-- Compact-generator unstable identity target rectangles come from its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_targetImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangles_eq_certificateLedger
    generator

/-- Compact-generator unstable identity source imported count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangleCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity target imported count is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_targetImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangleCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity source bookkeeping is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_sourceTraceBookkeepingCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity target bookkeeping is counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_targetTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_targetTraceBookkeepingCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity source rewrite steps are counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_sourceRewriteStepCount_eq_certificateLedger
    generator

/-- Compact-generator unstable identity target rewrite steps are counted by its certificate ledger. -/
theorem TraceAnalyticMotive.compactGenerator_unstableIdentity_targetRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticGeometricGenerator.unstableIdentity_targetRewriteStepCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary

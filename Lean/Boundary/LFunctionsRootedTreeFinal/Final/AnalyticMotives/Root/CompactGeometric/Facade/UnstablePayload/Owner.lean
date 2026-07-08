import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Localized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Facade.Evaluation.Owner

/-!
# Top-root compact-geometric unstable payload facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes compact generators in the unstable envelope. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableMotive_underlying
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableMotive.underlying =
      generator.traceObject :=
  TraceAnalyticMotive.compactGenerator_unstableMotive_underlying
    generator

/-- The analytic-motives root exposes compact-generator unstable identity words. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableIdentity_eq_ofWord
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity =
      TraceLocalizationWordClass.ofWord
        (TraceLocalizationWord.identity generator.traceObject) :=
  TraceAnalyticMotive.compactGenerator_unstableIdentity_eq_ofWord
    generator

/-- The analytic-motives root exposes compact unstable imported rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_unstableImportedRectangles_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable imported-rectangle counts. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_unstableImportedRectangleCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable count-as-length. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.unstableImportedRectangles.length :=
  TraceAnalyticMotive.compactGenerator_unstableImportedRectangleCount_eq_length
    generator

/-- The analytic-motives root exposes compact unstable certificate ledgers. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableCertificateLedger_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableCertificateLedger =
      generator.certificateLedger :=
  TraceAnalyticMotive.compactGenerator_unstableCertificateLedger_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable bookkeeping counts. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  TraceAnalyticMotive.compactGenerator_unstableTraceBookkeepingCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable rewrite-step counts. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  TraceAnalyticMotive.compactGenerator_unstableRewriteStepCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable identity source rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableIdentity_sourceImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceImportedRectangles_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable identity target rectangles. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableIdentity_targetImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  TraceAnalyticMotive.compactGenerator_unstableIdentity_targetImportedRectangles_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable identity source imported counts. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableIdentity_sourceImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_unstableIdentity_sourceImportedRectangleCount_eq_certificateLedger
    generator

/-- The analytic-motives root exposes compact unstable identity target imported counts. -/
theorem AnalyticMotivesRoot.compactGenerator_unstableIdentity_targetImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.compactGenerator_unstableIdentity_targetImportedRectangleCount_eq_certificateLedger
    generator

end AnalyticMotives
end LFunctions
end Boundary

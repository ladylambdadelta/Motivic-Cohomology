import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Compact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Compact.Payload.TraceCalculus.Owner

/-!
# Compact-generator payload in the unstable envelope

This file records that the unstable object attached to a compact generator
carries exactly the analytic payload of the generator's certified trace object.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Imported rectangles of a compact generator viewed in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  generator.unstableMotive.importedRectangles

/-- Imported-rectangle count of a compact generator viewed in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.unstableMotive.importedRectangleCount

/-- Certificate ledger of a compact generator viewed in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableCertificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    ResidueChannelCertificateLedger :=
  generator.unstableMotive.certificateLedger

/-- Trace-bookkeeping payload of a compact generator viewed in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableTraceBookkeepingCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.unstableMotive.traceBookkeepingCount

/-- Rewrite-step payload of a compact generator viewed in the unstable envelope. -/
def TraceAnalyticGeometricGenerator.unstableRewriteStepCount
    (generator : TraceAnalyticGeometricGenerator) :
    Nat :=
  generator.unstableMotive.rewriteStepCount

/-- The unstable imported rectangles are the compact generator's imported rectangles. -/
theorem TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangles =
      generator.importedRectangles :=
  TraceUnstableAnalyticMotive.ofTraceObject_importedRectangles
    generator.traceObject

/-- The unstable imported count is the compact generator's imported count. -/
theorem TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.importedRectangleCount :=
  TraceUnstableAnalyticMotive.ofTraceObject_importedRectangleCount
    generator.traceObject

/-- The unstable certificate ledger is the compact generator's certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableCertificateLedger_eq
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableCertificateLedger =
      generator.certificateLedger :=
  TraceUnstableAnalyticMotive.ofTraceObject_certificateLedger
    generator.traceObject

/-- The unstable bookkeeping count is the compact generator's bookkeeping count. -/
theorem TraceAnalyticGeometricGenerator.unstableTraceBookkeepingCount_eq
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableTraceBookkeepingCount =
      generator.traceBookkeepingCount :=
  TraceUnstableAnalyticMotive.ofTraceObject_traceBookkeepingCount
    generator.traceObject

/-- The unstable rewrite-step count is the compact generator's rewrite-step count. -/
theorem TraceAnalyticGeometricGenerator.unstableRewriteStepCount_eq
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableRewriteStepCount =
      generator.rewriteStepCount :=
  TraceUnstableAnalyticMotive.ofTraceObject_rewriteStepCount
    generator.traceObject

/-- The unstable imported count is counted by the unstable imported rectangle list. -/
theorem TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_length
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.unstableImportedRectangles.length :=
  TraceUnstableAnalyticMotive.importedRectangleCount_eq_length
    generator.unstableMotive

/-- The compact generator's unstable imported count is counted by its certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq generator)
    (TraceAnalyticGeometricGenerator.importedRectangleCount_eq_certificateLedger generator)

/-- The compact generator's unstable imported rectangles are extracted from its certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq generator)
    (TraceAnalyticGeometricGenerator.importedRectangles_eq_certificateLedger generator)

/-- The compact generator's unstable ledger is its compact certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableCertificateLedger_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableCertificateLedger =
      generator.certificateLedger :=
  TraceAnalyticGeometricGenerator.unstableCertificateLedger_eq generator

/-- The compact generator's unstable bookkeeping count is counted by its certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableTraceBookkeepingCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableTraceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableTraceBookkeepingCount_eq generator)
    (TraceAnalyticGeometricGenerator.traceBookkeepingCount_eq_certificateLedger generator)

/-- The compact generator's unstable rewrite-step count is counted by its certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableRewriteStepCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableRewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableRewriteStepCount_eq generator)
    (TraceAnalyticGeometricGenerator.rewriteStepCount_eq_certificateLedger generator)

/-- Source endpoint rectangles of the unstable identity are the generator's unstable rectangles. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangles =
      generator.unstableImportedRectangles :=
  TraceUnstableAnalyticMotiveHom.id_sourceImportedRectangles
    generator.unstableMotive

/-- Target endpoint rectangles of the unstable identity are the generator's unstable rectangles. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangles
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangles =
      generator.unstableImportedRectangles :=
  TraceUnstableAnalyticMotiveHom.id_targetImportedRectangles
    generator.unstableMotive

/-- Source endpoint count of the unstable identity is the generator's unstable count. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangleCount =
      generator.unstableImportedRectangleCount :=
  TraceLocalizedWordHom.id_sourceImportedRectangleCount
    generator.unstableMotive

/-- Target endpoint count of the unstable identity is the generator's unstable count. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangleCount
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangleCount =
      generator.unstableImportedRectangleCount :=
  TraceLocalizedWordHom.id_targetImportedRectangleCount
    generator.unstableMotive

/-- Source endpoint rectangles of the unstable identity come from the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangles generator)
    (TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq_certificateLedger generator)

/-- Target endpoint rectangles of the unstable identity come from the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangles_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangles =
      generator.certificateLedger.importedRectangles :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangles generator)
    (TraceAnalyticGeometricGenerator.unstableImportedRectangles_eq_certificateLedger generator)

/-- Source endpoint count of the unstable identity is counted by the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.sourceImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_sourceImportedRectangleCount generator)
    (TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_certificateLedger generator)

/-- Target endpoint count of the unstable identity is counted by the certificate ledger. -/
theorem TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangleCount_eq_certificateLedger
    (generator : TraceAnalyticGeometricGenerator) :
    generator.unstableIdentity.targetImportedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  Eq.trans
    (TraceAnalyticGeometricGenerator.unstableIdentity_targetImportedRectangleCount generator)
    (TraceAnalyticGeometricGenerator.unstableImportedRectangleCount_eq_certificateLedger generator)

end AnalyticMotives
end LFunctions
end Boundary

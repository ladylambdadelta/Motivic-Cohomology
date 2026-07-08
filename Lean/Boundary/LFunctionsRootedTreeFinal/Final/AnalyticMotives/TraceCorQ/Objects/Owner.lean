import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Objects.Owner

/-!
# Q-linear trace-category objects

This file owns the objects of the pre-motivic Q-linear trace category.

The current objects are certified residue-channel trace presentations.  This
keeps the lane on the higher-computadic trace calculus rather than a separate
geometric-object category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Objects of the raw Q-linear trace category. -/
abbrev TraceCorQObject :=
  TraceTransportObject

/-- Extend a trace-correspondence object by additional analytic certificates. -/
def TraceCorQObject.withAdditionalCertificates
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    TraceCorQObject :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates
    object
    certificates

/-- The source trace expression of a Q-linear trace-correspondence object. -/
def TraceCorQObject.source
    (object : TraceCorQObject) :
    QTraceExpression :=
  CertifiedResidueChannelPresentation.source object

/-- The residue ledger of a Q-linear trace-correspondence object. -/
def TraceCorQObject.ledger
    (object : TraceCorQObject) :
    ResidueLedger :=
  CertifiedResidueChannelPresentation.ledger object

/-- The channel expressions of a Q-linear trace-correspondence object. -/
def TraceCorQObject.channels
    (object : TraceCorQObject) :
    ResidueChannelExpressionList :=
  CertifiedResidueChannelPresentation.channels object

/-- The trace schedule of a Q-linear trace-correspondence object. -/
def TraceCorQObject.schedule
    (object : TraceCorQObject) :
    TraceSchedule :=
  CertifiedResidueChannelPresentation.schedule object

/-- The analytic certificate ledger of a Q-linear trace-correspondence object. -/
def TraceCorQObject.certificateLedger
    (object : TraceCorQObject) :
    ResidueChannelCertificateLedger :=
  CertifiedResidueChannelPresentation.certificateLedger object

/-- The imported finite-rectangle payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.importedRectangleCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.importedRectangleCount object

/-- The imported finite explicit-formula rectangles carried by a trace-correspondence object. -/
def TraceCorQObject.importedRectangles
    (object : TraceCorQObject) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  CertifiedResidueChannelPresentation.importedRectangles object

/-- The internal trace-bookkeeping payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.traceBookkeepingCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.traceBookkeepingCount object

/-- The explicit rewrite-step payload carried by a Q-linear trace-correspondence object. -/
def TraceCorQObject.rewriteStepCount
    (object : TraceCorQObject) :
    Nat :=
  CertifiedResidueChannelPresentation.rewriteStepCount object

/-- Object imported payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.importedRectangleCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.certificateLedger.importedRectangleCount :=
  rfl

/-- Object imported rectangles are extracted from its analytic certificate ledger. -/
theorem TraceCorQObject.importedRectangles_eq_certificateLedger_rectangles
    (object : TraceCorQObject) :
    object.importedRectangles =
      object.certificateLedger.importedRectangles :=
  rfl

/-- Object imported-rectangle count is the length of the extracted rectangle list. -/
theorem TraceCorQObject.importedRectangleCount_eq_length_importedRectangles
    (object : TraceCorQObject) :
    object.importedRectangleCount =
      object.importedRectangles.length :=
  CertifiedResidueChannelPresentation.importedRectangleCount_eq_length_importedRectangles
    object

/-- Object bookkeeping payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.traceBookkeepingCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.traceBookkeepingCount =
      object.certificateLedger.traceBookkeepingCount :=
  rfl

/-- Object rewrite-step payload is counted by its analytic certificate ledger. -/
theorem TraceCorQObject.rewriteStepCount_eq_certificateLedger_count
    (object : TraceCorQObject) :
    object.rewriteStepCount =
      object.certificateLedger.rewriteStepCount :=
  rfl

/-- Extending object certificates preserves the source expression. -/
theorem TraceCorQObject.withAdditionalCertificates_source
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).source =
      object.source :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_source
    object
    certificates

/-- Extending object certificates preserves the residue ledger. -/
theorem TraceCorQObject.withAdditionalCertificates_ledger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).ledger =
      object.ledger :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_ledger
    object
    certificates

/-- Extending object certificates preserves the channel expressions. -/
theorem TraceCorQObject.withAdditionalCertificates_channels
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).channels =
      object.channels :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_channels
    object
    certificates

/-- Extending object certificates preserves the trace schedule. -/
theorem TraceCorQObject.withAdditionalCertificates_schedule
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).schedule =
      object.schedule :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_schedule
    object
    certificates

/-- Extending object certificates appends to the object certificate ledger. -/
theorem TraceCorQObject.withAdditionalCertificates_certificateLedger
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).certificateLedger =
      ResidueChannelCertificateLedger.append
        object.certificateLedger
        certificates :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_certificateLedger
    object
    certificates

/-- Extending object certificates appends imported finite explicit-formula rectangles. -/
theorem TraceCorQObject.withAdditionalCertificates_importedRectangles
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangles =
      object.importedRectangles ++
        certificates.importedRectangles :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangles
    object
    certificates

/-- Extending object certificates adds imported finite-rectangle payload. -/
theorem TraceCorQObject.withAdditionalCertificates_importedRectangleCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).importedRectangleCount =
      object.importedRectangleCount +
        certificates.importedRectangleCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_importedRectangleCount
    object
    certificates

/-- Extending object certificates adds trace-bookkeeping payload. -/
theorem TraceCorQObject.withAdditionalCertificates_traceBookkeepingCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).traceBookkeepingCount =
      object.traceBookkeepingCount +
        certificates.traceBookkeepingCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_traceBookkeepingCount
    object
    certificates

/-- Extending object certificates adds rewrite-step payload. -/
theorem TraceCorQObject.withAdditionalCertificates_rewriteStepCount
    (object : TraceCorQObject)
    (certificates : ResidueChannelCertificateLedger) :
    (object.withAdditionalCertificates certificates).rewriteStepCount =
      object.rewriteStepCount +
        certificates.rewriteStepCount :=
  CertifiedResidueChannelPresentation.withAdditionalCertificates_rewriteStepCount
    object
    certificates

end AnalyticMotives
end LFunctions
end Boundary

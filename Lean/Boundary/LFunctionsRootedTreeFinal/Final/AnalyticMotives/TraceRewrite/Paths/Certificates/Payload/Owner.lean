import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Paths.Certificates.Owner

/-!
# Payload facts for named rewrite-path certificate ledgers

This file records imported-rectangle and bookkeeping payload invariants for
the certificate ledgers attached to one-step rewrite paths.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A one-step Stokes certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.stokesCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step residue certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.residueCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step channel certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.channelCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step refinement certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.refinementCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step schedule certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.scheduleCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step weight-drop certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.weightDropCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step Fubini certificate ledger carries no imported finite rectangles. -/
theorem TraceRewritePath.fubiniCertificateLedger_importedRectangleCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).importedRectangleCount =
      0 + 0 :=
  rfl

/-- A one-step Stokes certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.stokesCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step residue certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.residueCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step channel certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.channelCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step refinement certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.refinementCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step schedule certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.scheduleCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step weight-drop certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.weightDropCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step Fubini certificate ledger exposes no imported finite rectangles. -/
theorem TraceRewritePath.fubiniCertificateLedger_importedRectangles
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).importedRectangles =
      [] ++ [] :=
  rfl

/-- A one-step Stokes certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.stokesCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.stokesCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.stokesCertificateLedger source target)

/-- A one-step residue certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.residueCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.residueCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.residueCertificateLedger source target)

/-- A one-step channel certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.channelCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.channelCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.channelCertificateLedger source target)

/-- A one-step refinement certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.refinementCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.refinementCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.refinementCertificateLedger source target)

/-- A one-step schedule certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.scheduleCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.scheduleCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.scheduleCertificateLedger source target)

/-- A one-step weight-drop certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.weightDropCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.weightDropCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.weightDropCertificateLedger source target)

/-- A one-step Fubini certificate ledger count is the length of its rectangle list. -/
theorem TraceRewritePath.fubiniCertificateLedger_importedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).importedRectangleCount =
      (TraceRewritePath.fubiniCertificateLedger
        source
        target).importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    (TraceRewritePath.fubiniCertificateLedger source target)

/-- A one-step Stokes certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.stokesCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step residue certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.residueCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step channel certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.channelCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step refinement certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.refinementCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step schedule certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.scheduleCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step weight-drop certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.weightDropCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

/-- A one-step Fubini certificate ledger has one rewrite-path bookkeeping atom. -/
theorem TraceRewritePath.fubiniCertificateLedger_traceBookkeepingCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).traceBookkeepingCount =
      1 + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

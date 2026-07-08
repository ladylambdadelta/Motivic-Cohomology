import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner

/-!
# Certificate ledgers for named rewrite paths

This file connects the concrete one-step analytic rewrite paths with the
certificate-ledger accounting used by trace transports and Q-linear trace
correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The certificate ledger attached to a one-step Stokes rewrite path. -/
def TraceRewritePath.stokesCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.stokes source target)

/-- The certificate ledger attached to a one-step residue rewrite path. -/
def TraceRewritePath.residueCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.residue source target)

/-- The certificate ledger attached to a one-step channel rewrite path. -/
def TraceRewritePath.channelCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.channel source target)

/-- The certificate ledger attached to a one-step refinement rewrite path. -/
def TraceRewritePath.refinementCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.refinement source target)

/-- The certificate ledger attached to a one-step schedule rewrite path. -/
def TraceRewritePath.scheduleCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.schedule source target)

/-- The certificate ledger attached to a one-step weight-drop rewrite path. -/
def TraceRewritePath.weightDropCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.weightDrop source target)

/-- The certificate ledger attached to a one-step Fubini rewrite path. -/
def TraceRewritePath.fubiniCertificateLedger
    (source target : QTraceExpression) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofRewritePath
    (TraceRewritePath.fubini source target)

/-- A one-step Stokes path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.stokesCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.stokesCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step residue path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.residueCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.residueCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step channel path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.channelCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.channelCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step refinement path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.refinementCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.refinementCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step schedule path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.scheduleCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.scheduleCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step weight-drop path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.weightDropCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.weightDropCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

/-- A one-step Fubini path certificate ledger counts one rewrite step. -/
theorem TraceRewritePath.fubiniCertificateLedger_rewriteStepCount
    (source target : QTraceExpression) :
    (TraceRewritePath.fubiniCertificateLedger
      source
      target).rewriteStepCount =
      1 + 0 :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

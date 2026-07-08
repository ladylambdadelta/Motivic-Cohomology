import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Basic.Owner

/-!
# Additive certificate payloads for relation witnesses

This file owns the analytic certificate and payload facts for additive
compatibility of concrete quotient relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Additive compatibility appends witness certificate ledgers. -/
theorem TraceCorQRelationWitness.addCongr_certificateLedger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  Eq.trans
    (congrArg
      TraceCorQRelationLedger.certificateLedger
      (TraceCorQRelationWitness.addCongr_ledger
        leftWitness
        rightWitness))
    (TraceCorQRelationLedger.append_certificateLedger
      leftWitness.ledger
      rightWitness.ledger)

/-- Additive compatibility adds witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.addCongr_importedRectangleCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQRelationWitness.addCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Additive compatibility concatenates witness imported rectangles. -/
theorem TraceCorQRelationWitness.addCongr_importedRectangles
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQRelationWitness.addCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_importedRectangles
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Additive compatibility adds witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.addCongr_traceBookkeepingCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQRelationWitness.addCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Additive compatibility adds witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.addCongr_rewriteStepCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.addCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQRelationWitness.addCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Basic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Certificates.Add.Owner

/-!
# Compatibility certificate ledgers for relation witnesses

The basic child owner records certificate payloads for relation witnesses and
the basic witness constructors.  This file owns scalar and composition
compatibility payload laws, and re-exports the additive compatibility child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scalar compatibility preserves witness certificate ledgers. -/
theorem TraceCorQRelationWitness.smulCongr_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).certificateLedger =
      witness.certificateLedger :=
  rfl

/-- Scalar compatibility preserves witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.smulCongr_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangleCount =
      witness.importedRectangleCount :=
  rfl

/-- Scalar compatibility preserves witness imported finite explicit-formula rectangles. -/
theorem TraceCorQRelationWitness.smulCongr_importedRectangles
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).importedRectangles =
      witness.importedRectangles :=
  rfl

/-- Scalar compatibility preserves witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.smulCongr_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  rfl

/-- Scalar compatibility preserves witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.smulCongr_rewriteStepCount
    {left right : TraceCorQQuotientCandidate}
    (coefficient : Rat)
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.smulCongr
      coefficient
      witness).rewriteStepCount =
      witness.rewriteStepCount :=
  rfl

/-- Composition compatibility appends witness certificate ledgers. -/
theorem TraceCorQRelationWitness.compCongr_certificateLedger
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        leftWitness.certificateLedger
        rightWitness.certificateLedger :=
  Eq.trans
    (congrArg
      TraceCorQRelationLedger.certificateLedger
      (TraceCorQRelationWitness.compCongr_ledger
        leftWitness
        rightWitness))
    (TraceCorQRelationLedger.append_certificateLedger
      leftWitness.ledger
      rightWitness.ledger)

/-- Composition compatibility adds witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.compCongr_importedRectangleCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangleCount =
      leftWitness.importedRectangleCount +
        rightWitness.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQRelationWitness.compCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Composition compatibility concatenates witness imported rectangles. -/
theorem TraceCorQRelationWitness.compCongr_importedRectangles
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangles =
      leftWitness.importedRectangles ++
        rightWitness.importedRectangles :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangles
      (TraceCorQRelationWitness.compCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_importedRectangles
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Composition compatibility adds witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.compCongr_traceBookkeepingCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      leftWitness.traceBookkeepingCount +
        rightWitness.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQRelationWitness.compCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

/-- Composition compatibility adds witness explicit rewrite-step payload. -/
theorem TraceCorQRelationWitness.compCongr_rewriteStepCount
    {left₁ left₂ right₁ right₂ : TraceCorQQuotientCandidate}
    (leftWitness : TraceCorQRelationWitness left₁ left₂)
    (rightWitness : TraceCorQRelationWitness right₁ right₂) :
    (TraceCorQRelationWitness.compCongr
      leftWitness
      rightWitness).rewriteStepCount =
      leftWitness.rewriteStepCount +
        rightWitness.rewriteStepCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.rewriteStepCount
      (TraceCorQRelationWitness.compCongr_certificateLedger
        leftWitness
        rightWitness))
    (ResidueChannelCertificateLedger.append_rewriteStepCount
      leftWitness.certificateLedger
      rightWitness.certificateLedger)

end AnalyticMotives
end LFunctions
end Boundary

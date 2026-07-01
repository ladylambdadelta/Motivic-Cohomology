import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.RelationWitness.Owner

/-!
# Certificate ledgers for relation witnesses

This file records the analytic certificates carried by concrete quotient
relation witnesses.  A witness is a finite relation-closure derivation together
with its relation ledger, so its analytic certificate ledger is exactly the
certificate ledger of that relation ledger.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic certificate ledger carried by a concrete relation witness. -/
def TraceCorQRelationWitness.certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    ResidueChannelCertificateLedger :=
  witness.ledger.certificateLedger

/-- The imported finite-rectangle payload carried by a concrete relation witness. -/
def TraceCorQRelationWitness.importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.certificateLedger.importedRectangleCount

/-- The internal trace-bookkeeping payload carried by a concrete relation witness. -/
def TraceCorQRelationWitness.traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    Nat :=
  witness.certificateLedger.traceBookkeepingCount

/-- A witness built from a ledger carries that ledger's certificates. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- A witness built from a ledger carries that ledger's imported payload. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- A witness built from a ledger carries that ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.ofLedgerDerivation_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (ledger : TraceCorQRelationLedger)
    (derivation : TraceCorQRelationClosure ledger left right) :
    (TraceCorQRelationWitness.ofLedgerDerivation
      ledger
      derivation).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Reflexive witnesses carry the empty certificate ledger. -/
theorem TraceCorQRelationWitness.refl_certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).certificateLedger =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.empty_certificateLedger

/-- Reflexive witnesses carry no imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.refl_importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).importedRectangleCount =
      0 :=
  TraceCorQRelationLedger.empty_importedRectangleCount

/-- Reflexive witnesses carry no internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.refl_traceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    (TraceCorQRelationWitness.refl candidate).traceBookkeepingCount =
      0 :=
  TraceCorQRelationLedger.empty_traceBookkeepingCount

/-- Symmetry preserves witness certificate ledgers. -/
theorem TraceCorQRelationWitness.symm_certificateLedger
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).certificateLedger =
      witness.certificateLedger :=
  rfl

/-- Symmetry preserves witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.symm_importedRectangleCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).importedRectangleCount =
      witness.importedRectangleCount :=
  rfl

/-- Symmetry preserves witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.symm_traceBookkeepingCount
    {left right : TraceCorQQuotientCandidate}
    (witness : TraceCorQRelationWitness left right) :
    (TraceCorQRelationWitness.symm witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  rfl

/-- Transitivity appends witness certificate ledgers. -/
theorem TraceCorQRelationWitness.trans_certificateLedger
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).certificateLedger =
      ResidueChannelCertificateLedger.append
        first.certificateLedger
        second.certificateLedger :=
  Eq.trans
    (congrArg
      TraceCorQRelationLedger.certificateLedger
      (TraceCorQRelationWitness.trans_ledger first second))
    (TraceCorQRelationLedger.append_certificateLedger
      first.ledger
      second.ledger)

/-- Transitivity adds witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.trans_importedRectangleCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).importedRectangleCount =
      first.importedRectangleCount +
        second.importedRectangleCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.importedRectangleCount
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_importedRectangleCount
      first.certificateLedger
      second.certificateLedger)

/-- Transitivity adds witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.trans_traceBookkeepingCount
    {left middle right : TraceCorQQuotientCandidate}
    (first : TraceCorQRelationWitness left middle)
    (second : TraceCorQRelationWitness middle right) :
    (TraceCorQRelationWitness.trans first second).traceBookkeepingCount =
      first.traceBookkeepingCount +
        second.traceBookkeepingCount :=
  Eq.trans
    (congrArg
      ResidueChannelCertificateLedger.traceBookkeepingCount
      (TraceCorQRelationWitness.trans_certificateLedger first second))
    (ResidueChannelCertificateLedger.append_traceBookkeepingCount
      first.certificateLedger
      second.certificateLedger)

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

/-- Same-formal-sum witnesses carry the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.sameFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.sameFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Same-formal-sum witnesses carry the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.sameFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_eq : left.formalSum = right.formalSum) :
    (TraceCorQRelationWitness.sameFormalSum
      ledger
      formalSum_eq).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.permFormalSum_certificateLedger
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.permFormalSum_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Permuted-formal-sum witnesses carry the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.permFormalSum_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    {left right : TraceCorQQuotientCandidate}
    (formalSum_perm : List.Perm left.formalSum right.formalSum) :
    (TraceCorQRelationWitness.permFormalSum
      ledger
      formalSum_perm).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_certificateLedger
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      prefix
      suffix
      coefficient
      generator).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      prefix
      suffix
      coefficient
      generator).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Adjacent opposite coefficient cancellation carries the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.cancelAdjacentOpposite_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.cancelAdjacentOpposite
      ledger
      prefix
      suffix
      coefficient
      generator).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's certificates. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_certificateLedger
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      prefix
      suffix
      leftCoefficient
      rightCoefficient
      generator).certificateLedger =
      ledger.certificateLedger :=
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's imported payload. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_importedRectangleCount
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      prefix
      suffix
      leftCoefficient
      rightCoefficient
      generator).importedRectangleCount =
      ledger.importedRectangleCount :=
  rfl

/-- Adjacent same-generator combination carries the supplied ledger's bookkeeping payload. -/
theorem TraceCorQRelationWitness.combineAdjacentSame_traceBookkeepingCount
    (ledger : TraceCorQRelationLedger)
    (prefix suffix : TraceCorQFormalSum)
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    (TraceCorQRelationWitness.combineAdjacentSame
      ledger
      prefix
      suffix
      leftCoefficient
      rightCoefficient
      generator).traceBookkeepingCount =
      ledger.traceBookkeepingCount :=
  rfl

/-- Endpoint transport preserves witness certificate ledgers. -/
theorem TraceCorQRelationWitness.transportEndpoints_certificateLedger
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).certificateLedger =
      witness.certificateLedger :=
  rfl

/-- Endpoint transport preserves witness imported finite-rectangle payload. -/
theorem TraceCorQRelationWitness.transportEndpoints_importedRectangleCount
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).importedRectangleCount =
      witness.importedRectangleCount :=
  rfl

/-- Endpoint transport preserves witness internal trace-bookkeeping payload. -/
theorem TraceCorQRelationWitness.transportEndpoints_traceBookkeepingCount
    {sourceLeft sourceRight targetLeft targetRight :
      TraceCorQQuotientCandidate}
    (left_eq : sourceLeft = targetLeft)
    (right_eq : sourceRight = targetRight)
    (witness : TraceCorQRelationWitness sourceLeft sourceRight) :
    (TraceCorQRelationWitness.transportEndpoints
      left_eq
      right_eq
      witness).traceBookkeepingCount =
      witness.traceBookkeepingCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

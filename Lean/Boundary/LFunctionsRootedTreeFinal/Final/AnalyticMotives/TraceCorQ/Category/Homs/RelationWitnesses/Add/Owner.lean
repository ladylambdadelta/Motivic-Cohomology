import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner

/-!
# Additive compatibility for typed hom relation witnesses

This file lifts additive compatibility from proof-valued typed hom relations to
data-bearing typed hom relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Witness from representative addition to ambient candidate addition. -/
def TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceCorQRelationWitness
      (TraceCorQHomRepresentative.add left right).rawCandidate
      (TraceCorQQuotientCandidate.add
        left.rawCandidate
        right.rawCandidate) :=
  TraceCorQRelationWitness.sameFormalSum
    (TraceCorQRelationLedger.append
      left.rawCandidate.ledger
      right.rawCandidate.ledger)
    (TraceCorQHomRepresentative.add_rawCandidate_formalSum
      left
      right)

/-- Witness from ambient candidate addition back to representative addition. -/
def TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.add
        left.rawCandidate
        right.rawCandidate)
      (TraceCorQHomRepresentative.add left right).rawCandidate :=
  TraceCorQRelationWitness.symm
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right)

/-- Additive compatibility for data-bearing typed hom relation witnesses. -/
def TraceCorQHomRelationWitness.addCongr
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    TraceCorQHomRelationWitness
      (TraceCorQHomRepresentative.add left₁ right₁)
      (TraceCorQHomRepresentative.add left₂ right₂) :=
  TraceCorQRelationWitness.trans
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left₁
      right₁)
    (TraceCorQRelationWitness.trans
      (TraceCorQRelationWitness.addCongr leftWitness rightWitness)
      (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
        left₂
        right₂))

/-- Representative-to-candidate addition carries the appended representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQRelationLedger.append_certificateLedger
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Representative-to-candidate addition carries appended representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQRelationLedger.append_importedRectangleCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Representative-to-candidate addition carries appended representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQRelationLedger.append_traceBookkeepingCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative addition carries the appended representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQRelationLedger.append_certificateLedger
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative addition carries appended representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQRelationLedger.append_importedRectangleCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative addition carries appended representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQRelationLedger.append_traceBookkeepingCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Additive compatibility records endpoint certificates around the summed witness certificates. -/
theorem TraceCorQHomRelationWitness.addCongr_certificateLedger
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left₁.rawCandidate.ledger.certificateLedger
          right₁.rawCandidate.ledger.certificateLedger)
        (ResidueChannelCertificateLedger.append
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger)) :=
  Eq.trans
    (TraceCorQRelationWitness.trans_certificateLedger
      (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
        left₁
        right₁)
      (TraceCorQRelationWitness.trans
        (TraceCorQRelationWitness.addCongr leftWitness rightWitness)
          (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
            left₂
            right₂)))
    (congrArg₂
      ResidueChannelCertificateLedger.append
      (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_certificateLedger
        left₁
        right₁)
      (Eq.trans
        (TraceCorQRelationWitness.trans_certificateLedger
          (TraceCorQRelationWitness.addCongr leftWitness rightWitness)
          (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
            left₂
            right₂))
        (congrArg₂
          ResidueChannelCertificateLedger.append
          (TraceCorQRelationWitness.addCongr_certificateLedger
            leftWitness
            rightWitness)
          (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_certificateLedger
            left₂
            right₂))))

/-- Additive compatibility records endpoint and witness imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.addCongr_importedRectangleCount
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness).importedRectangleCount =
      (left₁.rawCandidate.ledger.importedRectangleCount +
        right₁.rawCandidate.ledger.importedRectangleCount) +
        ((leftWitness.importedRectangleCount +
          rightWitness.importedRectangleCount) +
          (left₂.rawCandidate.ledger.importedRectangleCount +
            right₂.rawCandidate.ledger.importedRectangleCount)) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangleCount
        (TraceCorQHomRelationWitness.addCongr_certificateLedger
          leftWitness
          rightWitness))
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        (ResidueChannelCertificateLedger.append
          left₁.rawCandidate.ledger.certificateLedger
          right₁.rawCandidate.ledger.certificateLedger)
        (ResidueChannelCertificateLedger.append
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_importedRectangleCount
        left₁.rawCandidate.ledger.certificateLedger
        right₁.rawCandidate.ledger.certificateLedger)
      (Eq.trans
        (ResidueChannelCertificateLedger.append_importedRectangleCount
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))
        (congrArg₂
          Nat.add
          (ResidueChannelCertificateLedger.append_importedRectangleCount
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append_importedRectangleCount
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))))

/-- Additive compatibility records endpoint and witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.addCongr_traceBookkeepingCount
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness).traceBookkeepingCount =
      (left₁.rawCandidate.ledger.traceBookkeepingCount +
        right₁.rawCandidate.ledger.traceBookkeepingCount) +
        ((leftWitness.traceBookkeepingCount +
          rightWitness.traceBookkeepingCount) +
          (left₂.rawCandidate.ledger.traceBookkeepingCount +
            right₂.rawCandidate.ledger.traceBookkeepingCount)) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.traceBookkeepingCount
        (TraceCorQHomRelationWitness.addCongr_certificateLedger
          leftWitness
          rightWitness))
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        (ResidueChannelCertificateLedger.append
          left₁.rawCandidate.ledger.certificateLedger
          right₁.rawCandidate.ledger.certificateLedger)
        (ResidueChannelCertificateLedger.append
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))))
    (congrArg₂
      Nat.add
      (ResidueChannelCertificateLedger.append_traceBookkeepingCount
        left₁.rawCandidate.ledger.certificateLedger
        right₁.rawCandidate.ledger.certificateLedger)
      (Eq.trans
        (ResidueChannelCertificateLedger.append_traceBookkeepingCount
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))
        (congrArg₂
          Nat.add
          (ResidueChannelCertificateLedger.append_traceBookkeepingCount
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append_traceBookkeepingCount
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))))

end AnalyticMotives
end LFunctions
end Boundary

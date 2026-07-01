import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.Representatives.Owner

/-!
# Composition compatibility for typed hom relation witnesses

This file lifts composition compatibility from proof-valued typed hom relations
to data-bearing typed hom relation witnesses.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Witness from representative composition to ambient candidate composition. -/
def TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQRelationWitness
      (TraceCorQHomRepresentative.comp left right).rawCandidate
      (TraceCorQQuotientCandidate.comp
        left.rawCandidate
        right.rawCandidate) :=
  TraceCorQRelationWitness.sameFormalSum
    (TraceCorQRelationLedger.append
      left.rawCandidate.ledger
      right.rawCandidate.ledger)
    (TraceCorQHomRepresentative.comp_rawCandidate_formalSum
      left
      right)

/-- Witness from ambient candidate composition back to representative composition. -/
def TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    TraceCorQRelationWitness
      (TraceCorQQuotientCandidate.comp
        left.rawCandidate
        right.rawCandidate)
      (TraceCorQHomRepresentative.comp left right).rawCandidate :=
  TraceCorQRelationWitness.symm
    (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
      left
      right)

/-- Composition compatibility for data-bearing typed hom relation witnesses. -/
def TraceCorQHomRelationWitness.compCongr
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    TraceCorQHomRelationWitness
      (TraceCorQHomRepresentative.comp left₁ right₁)
      (TraceCorQHomRepresentative.comp left₂ right₂) :=
  TraceCorQRelationWitness.trans
    (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
      left₁
      right₁)
    (TraceCorQRelationWitness.trans
      (TraceCorQRelationWitness.compCongr leftWitness rightWitness)
      (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
        left₂
        right₂))

/-- Representative-to-candidate composition carries appended representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.compRepresentative_to_candidateComp_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQRelationLedger.append_certificateLedger
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Representative-to-candidate composition carries appended representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.compRepresentative_to_candidateComp_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQRelationLedger.append_importedRectangleCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Representative-to-candidate composition carries appended representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.compRepresentative_to_candidateComp_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQRelationLedger.append_traceBookkeepingCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative composition carries appended representative ledger certificates. -/
theorem TraceCorQHomRelationWitness.candidateComp_to_compRepresentative_certificateLedger
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQRelationLedger.append_certificateLedger
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative composition carries appended representative ledger imported payload. -/
theorem TraceCorQHomRelationWitness.candidateComp_to_compRepresentative_importedRectangleCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQRelationLedger.append_importedRectangleCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Candidate-to-representative composition carries appended representative ledger bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.candidateComp_to_compRepresentative_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    (left : TraceCorQHomRepresentative source middle)
    (right : TraceCorQHomRepresentative middle target) :
    (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQRelationLedger.append_traceBookkeepingCount
    left.rawCandidate.ledger
    right.rawCandidate.ledger

/-- Composition compatibility records endpoint certificates around composed witness certificates. -/
theorem TraceCorQHomRelationWitness.compCongr_certificateLedger
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.compCongr
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
      (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp
        left₁
        right₁)
      (TraceCorQRelationWitness.trans
        (TraceCorQRelationWitness.compCongr leftWitness rightWitness)
        (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
          left₂
          right₂)))
    (congrArg₂
      ResidueChannelCertificateLedger.append
      (TraceCorQHomRelationWitness.compRepresentative_to_candidateComp_certificateLedger
        left₁
        right₁)
      (Eq.trans
        (TraceCorQRelationWitness.trans_certificateLedger
          (TraceCorQRelationWitness.compCongr leftWitness rightWitness)
          (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative
            left₂
            right₂))
        (congrArg₂
          ResidueChannelCertificateLedger.append
          (TraceCorQRelationWitness.compCongr_certificateLedger
            leftWitness
            rightWitness)
          (TraceCorQHomRelationWitness.candidateComp_to_compRepresentative_certificateLedger
            left₂
            right₂))))

/-- Composition compatibility records endpoint and witness imported finite-rectangle payload. -/
theorem TraceCorQHomRelationWitness.compCongr_importedRectangleCount
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.compCongr
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
        (TraceCorQHomRelationWitness.compCongr_certificateLedger
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

/-- Composition compatibility records endpoint and witness internal trace-bookkeeping payload. -/
theorem TraceCorQHomRelationWitness.compCongr_traceBookkeepingCount
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.compCongr
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
        (TraceCorQHomRelationWitness.compCongr_certificateLedger
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

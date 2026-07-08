import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Composition.RelationWitnesses.Basic.Owner

/-!
# Composition compatibility for typed hom relation witnesses

This file records the composed endpoint and witness payload for data-bearing
typed hom relation-witness composition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- Composition compatibility records endpoint and witness imported rectangles. -/
theorem TraceCorQHomRelationWitness.compCongr_importedRectangles
    {source middle target : TraceCorQObject}
    {left₁ left₂ : TraceCorQHomRepresentative source middle}
    {right₁ right₂ : TraceCorQHomRepresentative middle target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.compCongr
      leftWitness
      rightWitness).importedRectangles =
      (left₁.rawCandidate.ledger.importedRectangles ++
        right₁.rawCandidate.ledger.importedRectangles) ++
        ((leftWitness.importedRectangles ++
          rightWitness.importedRectangles) ++
          (left₂.rawCandidate.ledger.importedRectangles ++
            right₂.rawCandidate.ledger.importedRectangles)) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.importedRectangles
        (TraceCorQHomRelationWitness.compCongr_certificateLedger
          leftWitness
          rightWitness))
      (ResidueChannelCertificateLedger.append_importedRectangles
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
      List.append
      (ResidueChannelCertificateLedger.append_importedRectangles
        left₁.rawCandidate.ledger.certificateLedger
        right₁.rawCandidate.ledger.certificateLedger)
      (Eq.trans
        (ResidueChannelCertificateLedger.append_importedRectangles
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))
        (congrArg₂
          List.append
          (ResidueChannelCertificateLedger.append_importedRectangles
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append_importedRectangles
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

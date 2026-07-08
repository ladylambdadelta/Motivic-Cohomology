import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Add.Conversions.Owner

/-!
# Additive compatibility for typed hom relation witnesses

This file lifts additive compatibility from proof-valued typed hom relations to
data-bearing typed hom relation witnesses. Conversion witnesses between typed
representative addition and ambient candidate addition are owned by the
`Conversions` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

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

/-- Additive compatibility records endpoint and witness imported rectangles. -/
theorem TraceCorQHomRelationWitness.addCongr_importedRectangles
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
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
        (TraceCorQHomRelationWitness.addCongr_certificateLedger
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

/-- Additive compatibility records endpoint and witness explicit rewrite-step payload. -/
theorem TraceCorQHomRelationWitness.addCongr_rewriteStepCount
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftWitness : TraceCorQHomRelationWitness left₁ left₂)
    (rightWitness : TraceCorQHomRelationWitness right₁ right₂) :
    (TraceCorQHomRelationWitness.addCongr
      leftWitness
      rightWitness).rewriteStepCount =
      (left₁.rawCandidate.ledger.rewriteStepCount +
        right₁.rawCandidate.ledger.rewriteStepCount) +
        ((leftWitness.rewriteStepCount +
          rightWitness.rewriteStepCount) +
          (left₂.rawCandidate.ledger.rewriteStepCount +
            right₂.rawCandidate.ledger.rewriteStepCount)) :=
  Eq.trans
    (Eq.trans
      (congrArg
        ResidueChannelCertificateLedger.rewriteStepCount
        (TraceCorQHomRelationWitness.addCongr_certificateLedger
          leftWitness
          rightWitness))
      (ResidueChannelCertificateLedger.append_rewriteStepCount
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
      (ResidueChannelCertificateLedger.append_rewriteStepCount
        left₁.rawCandidate.ledger.certificateLedger
        right₁.rawCandidate.ledger.certificateLedger)
      (Eq.trans
        (ResidueChannelCertificateLedger.append_rewriteStepCount
          (ResidueChannelCertificateLedger.append
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))
        (congrArg₂
          Nat.add
          (ResidueChannelCertificateLedger.append_rewriteStepCount
            leftWitness.certificateLedger
            rightWitness.certificateLedger)
          (ResidueChannelCertificateLedger.append_rewriteStepCount
            left₂.rawCandidate.ledger.certificateLedger
            right₂.rawCandidate.ledger.certificateLedger))))

end AnalyticMotives
end LFunctions
end Boundary

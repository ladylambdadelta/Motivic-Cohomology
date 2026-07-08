import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Add.Owner

/-!
# Public additive relation-witness payload facts

This file exposes payload formulas for additive compatibility witnesses between
typed trace-correspondence hom representatives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes representative-to-candidate add witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addRepresentative_to_candidateAdd_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_certificateLedger
    left
    right

/-- The top root exposes representative-to-candidate add witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addRepresentative_to_candidateAdd_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangleCount
    left
    right

/-- The top root exposes representative-to-candidate add witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addRepresentative_to_candidateAdd_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        right.rawCandidate.ledger.importedRectangles :=
  TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangles
    left
    right

/-- The top root exposes representative-to-candidate add witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addRepresentative_to_candidateAdd_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_traceBookkeepingCount
    left
    right

/-- The top root exposes candidate-to-representative add witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateAdd_to_addRepresentative_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).certificateLedger =
      ResidueChannelCertificateLedger.append
        left.rawCandidate.ledger.certificateLedger
        right.rawCandidate.ledger.certificateLedger :=
  TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_certificateLedger
    left
    right

/-- The top root exposes candidate-to-representative add witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateAdd_to_addRepresentative_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangleCount =
      left.rawCandidate.ledger.importedRectangleCount +
        right.rawCandidate.ledger.importedRectangleCount :=
  TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangleCount
    left
    right

/-- The top root exposes candidate-to-representative add witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateAdd_to_addRepresentative_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        right.rawCandidate.ledger.importedRectangles :=
  TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangles
    left
    right

/-- The top root exposes candidate-to-representative add witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_candidateAdd_to_addRepresentative_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).traceBookkeepingCount =
      left.rawCandidate.ledger.traceBookkeepingCount +
        right.rawCandidate.ledger.traceBookkeepingCount :=
  TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_traceBookkeepingCount
    left
    right

/-- The top root exposes additive congruence witness certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_certificateLedger
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
  TraceCorQHomRelationWitness.addCongr_certificateLedger
    leftWitness
    rightWitness

/-- The top root exposes additive congruence witness imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_importedRectangleCount
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
  TraceCorQHomRelationWitness.addCongr_importedRectangleCount
    leftWitness
    rightWitness

/-- The top root exposes additive congruence witness imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_importedRectangles
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
  TraceCorQHomRelationWitness.addCongr_importedRectangles
    leftWitness
    rightWitness

/-- The top root exposes additive congruence witness bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_traceBookkeepingCount
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
  TraceCorQHomRelationWitness.addCongr_traceBookkeepingCount
    leftWitness
    rightWitness

/-- The top root exposes additive congruence witness rewrite-step counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRelationWitness_addCongr_rewriteStepCount
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
  TraceCorQHomRelationWitness.addCongr_rewriteStepCount
    leftWitness
    rightWitness

end AnalyticMotives
end LFunctions
end Boundary

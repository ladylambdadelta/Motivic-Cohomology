import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.RelationWitnesses.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner

/-!
# Additive conversion witnesses for typed hom representatives

This file owns the relation witnesses converting between typed representative
addition and ambient quotient-candidate addition, together with their payload
facts.
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

/-- Representative-to-candidate addition carries appended representative ledger rectangles. -/
theorem TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.addRepresentative_to_candidateAdd
      left
      right).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        right.rawCandidate.ledger.importedRectangles :=
  TraceCorQRelationLedger.append_importedRectangles
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

/-- Candidate-to-representative addition carries appended representative ledger rectangles. -/
theorem TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRelationWitness.candidateAdd_to_addRepresentative
      left
      right).importedRectangles =
      left.rawCandidate.ledger.importedRectangles ++
        right.rawCandidate.ledger.importedRectangles :=
  TraceCorQRelationLedger.append_importedRectangles
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

end AnalyticMotives
end LFunctions
end Boundary

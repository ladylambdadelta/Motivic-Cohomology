import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Add.Owner

/-!
# Public addition of typed trace homs

This file exposes representative addition, typed hom addition, and ambient
compatibility for fixed-endpoint typed trace-correspondence homs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes representative-addition raw formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).rawCandidate.formalSum =
      TraceCorQFormalSum.add
        left.rawCandidate.formalSum
        right.rawCandidate.formalSum :=
  TraceCorQHomRepresentative.add_rawCandidate_formalSum
    left
    right

/-- The top root exposes representative-addition raw ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_rawCandidate_ledger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).rawCandidate.ledger =
      TraceCorQRelationLedger.append
        left.rawCandidate.ledger
        right.rawCandidate.ledger :=
  TraceCorQHomRepresentative.add_rawCandidate_ledger
    left
    right

/-- The top root exposes representative-addition certificate ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_certificateLedger
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).certificateLedger =
      ResidueChannelCertificateLedger.append
        (ResidueChannelCertificateLedger.append
          left.formalSum.certificateLedger
          right.formalSum.certificateLedger)
        (ResidueChannelCertificateLedger.append
          left.ledger.certificateLedger
          right.ledger.certificateLedger) :=
  TraceCorQHomRepresentative.add_certificateLedger
    left
    right

/-- The top root exposes representative-addition imported counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_importedRectangleCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).importedRectangleCount =
      (left.formalSum.importedRectangleCount +
        right.formalSum.importedRectangleCount) +
        (left.ledger.importedRectangleCount +
          right.ledger.importedRectangleCount) :=
  TraceCorQHomRepresentative.add_importedRectangleCount
    left
    right

/-- The top root exposes representative-addition imported rectangles. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_importedRectangles
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).importedRectangles =
      (left.formalSum.importedRectangles ++
        right.formalSum.importedRectangles) ++
        (left.ledger.importedRectangles ++
          right.ledger.importedRectangles) :=
  TraceCorQHomRepresentative.add_importedRectangles
    left
    right

/-- The top root exposes representative-addition bookkeeping counts. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_add_traceBookkeepingCount
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.add left right).traceBookkeepingCount =
      (left.formalSum.traceBookkeepingCount +
        right.formalSum.traceBookkeepingCount) +
        (left.ledger.traceBookkeepingCount +
          right.ledger.traceBookkeepingCount) :=
  TraceCorQHomRepresentative.add_traceBookkeepingCount
    left
    right

/-- The top root exposes addition congruence for typed hom relations. -/
def AnalyticMotivesRoot.traceCorQHomRelationAddCongr
    {source target : TraceCorQObject}
    {left₁ left₂ right₁ right₂ : TraceCorQHomRepresentative source target}
    (leftRelation : TraceCorQHomRelation left₁ left₂)
    (rightRelation : TraceCorQHomRelation right₁ right₂) :
    TraceCorQHomRelation
      (TraceCorQHomRepresentative.add left₁ right₁)
      (TraceCorQHomRepresentative.add left₂ right₂) :=
  TraceCorQHomRelation.addCongr
    leftRelation
    rightRelation

/-- The top root exposes typed hom addition on representatives. -/
theorem AnalyticMotivesRoot.traceCorQHom_add_ofRepresentative
    {source target : TraceCorQObject}
    (left right : TraceCorQHomRepresentative source target) :
    TraceCorQHom.add
      (TraceCorQHom.ofRepresentative left)
      (TraceCorQHom.ofRepresentative right) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.add left right) :=
  TraceCorQHom.add_ofRepresentative
    left
    right

/-- The top root exposes ambient compatibility for typed hom addition. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_add
    {source target : TraceCorQObject}
    (left right : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.add left right) =
      TraceCorQQuotient.add
        (TraceCorQHom.ambient left)
        (TraceCorQHom.ambient right) :=
  TraceCorQHom.ambient_add
    left
    right

/-- The top root exposes cons decomposition of typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHom_ofFormalSum_cons
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target)
    (tail : TraceCorQHomFormalSum source target) :
    TraceCorQHom.ofFormalSum (term :: tail) =
      TraceCorQHom.add
        (TraceCorQHom.singleton
          source
          target
          term.coefficient
          term.generator
          (TraceCorQHomTerm.generator_source term)
          (TraceCorQHomTerm.generator_target term))
        (TraceCorQHom.ofFormalSum tail) :=
  TraceCorQHom.ofFormalSum_cons
    term
    tail

end AnalyticMotives
end LFunctions
end Boundary

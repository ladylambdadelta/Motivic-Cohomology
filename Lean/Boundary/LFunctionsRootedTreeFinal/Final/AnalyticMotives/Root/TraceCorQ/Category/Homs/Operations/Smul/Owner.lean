import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Owner

/-!
# Public scalar multiplication of typed trace homs

This file exposes scalar multiplication of typed terms, formal sums,
representatives, and hom classes.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes raw scalar multiplication of typed hom terms. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_smul_raw
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).raw =
      (coefficient * term.raw.1, term.raw.2) :=
  TraceCorQHomTerm.smul_raw
    coefficient
    term

/-- The top root exposes preservation of imported counts by typed term scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_smul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).importedRectangleCount =
      term.importedRectangleCount :=
  TraceCorQHomTerm.smul_importedRectangleCount
    coefficient
    term

/-- The top root exposes preservation of imported rectangles by typed term scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_smul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).importedRectangles =
      term.importedRectangles :=
  TraceCorQHomTerm.smul_importedRectangles
    coefficient
    term

/-- The top root exposes preservation of bookkeeping counts by typed term scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomTerm_smul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).traceBookkeepingCount =
      term.traceBookkeepingCount :=
  TraceCorQHomTerm.smul_traceBookkeepingCount
    coefficient
    term

/-- The top root exposes raw scalar multiplication of typed formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomFormalSum_smul_raw
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (formalSum : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.smul coefficient formalSum).raw =
      TraceCorQFormalSum.smul coefficient formalSum.raw :=
  TraceCorQHomFormalSum.smul_raw
    coefficient
    formalSum

/-- The top root exposes scaled representative raw formal sums. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate.formalSum =
      TraceCorQFormalSum.smul
        coefficient
        representative.rawCandidate.formalSum :=
  TraceCorQHomRepresentative.smul_rawCandidate_formalSum
    coefficient
    representative

/-- The top root exposes scaled representative raw ledgers. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_rawCandidate_ledger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate.ledger =
      representative.rawCandidate.ledger :=
  TraceCorQHomRepresentative.smul_rawCandidate_ledger
    coefficient
    representative

/-- The top root exposes preservation of certificate ledgers by representative scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).certificateLedger =
      representative.certificateLedger :=
  TraceCorQHomRepresentative.smul_certificateLedger
    coefficient
    representative

/-- The top root exposes preservation of imported counts by representative scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).importedRectangleCount =
      representative.importedRectangleCount :=
  TraceCorQHomRepresentative.smul_importedRectangleCount
    coefficient
    representative

/-- The top root exposes preservation of imported rectangles by representative scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).importedRectangles =
      representative.importedRectangles :=
  TraceCorQHomRepresentative.smul_importedRectangles
    coefficient
    representative

/-- The top root exposes preservation of bookkeeping counts by representative scaling. -/
theorem AnalyticMotivesRoot.traceCorQHomRepresentative_smul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).traceBookkeepingCount =
      representative.traceBookkeepingCount :=
  TraceCorQHomRepresentative.smul_traceBookkeepingCount
    coefficient
    representative

/-- The top root exposes relation from representative scaling to ambient candidate scaling. -/
def AnalyticMotivesRoot.traceCorQHomRelationSmulRepresentativeToCandidateSmul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientRelation
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate) :=
  TraceCorQHomRelation.smulRepresentative_to_candidateSmul
    coefficient
    representative

/-- The top root exposes relation from ambient candidate scaling to representative scaling. -/
def AnalyticMotivesRoot.traceCorQHomRelationCandidateSmulToSmulRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientRelation
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate)
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate :=
  TraceCorQHomRelation.candidateSmul_to_smulRepresentative
    coefficient
    representative

/-- The top root exposes scalar congruence for typed hom relations. -/
def AnalyticMotivesRoot.traceCorQHomRelationSmulCongr
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHomRelation
      (TraceCorQHomRepresentative.smul coefficient left)
      (TraceCorQHomRepresentative.smul coefficient right) :=
  TraceCorQHomRelation.smulCongr
    coefficient
    relation

/-- The top root exposes typed scalar multiplication on representatives. -/
theorem AnalyticMotivesRoot.traceCorQHom_smul_ofRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.ofRepresentative representative) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.smul coefficient representative) :=
  TraceCorQHom.smul_ofRepresentative
    coefficient
    representative

/-- The top root exposes ambient compatibility for typed scalar multiplication. -/
theorem AnalyticMotivesRoot.traceCorQHom_ambient_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.smul coefficient hom) =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQHom.ambient hom) :=
  TraceCorQHom.ambient_smul
    coefficient
    hom

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Owner

/-!
# Scalar multiplication of typed trace-correspondence hom classes

This file owns rational scalar multiplication inside each typed hom quotient.
The construction scales coefficients of typed terms, maps that over typed
formal sums, preserves the relation ledger on representatives, and descends
through the ambient quotient scalar-congruence relation.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scale the rational coefficient of a typed hom term. -/
def TraceCorQHomTerm.smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    TraceCorQHomTerm source target :=
  TraceCorQHomTerm.ofGenerator
    source
    target
    (coefficient * term.coefficient)
    term.generator
    (TraceCorQHomTerm.generator_source term)
    (TraceCorQHomTerm.generator_target term)

/-- The raw term of a scaled typed term is the scaled raw term. -/
theorem TraceCorQHomTerm.smul_raw
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).raw =
      (coefficient * term.raw.1, term.raw.2) :=
  rfl

/-- Scaling a typed hom term preserves imported finite-rectangle payload. -/
theorem TraceCorQHomTerm.smul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).importedRectangleCount =
      term.importedRectangleCount :=
  rfl

/-- Scaling a typed hom term preserves imported finite explicit-formula rectangles. -/
theorem TraceCorQHomTerm.smul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).importedRectangles =
      term.importedRectangles :=
  rfl

/-- Scaling a typed hom term preserves internal trace-bookkeeping payload. -/
theorem TraceCorQHomTerm.smul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (term : TraceCorQHomTerm source target) :
    (TraceCorQHomTerm.smul coefficient term).traceBookkeepingCount =
      term.traceBookkeepingCount :=
  rfl

/-- Scale a typed hom formal sum termwise. -/
def TraceCorQHomFormalSum.smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHomFormalSum source target :=
  formalSum.map (fun term => TraceCorQHomTerm.smul coefficient term)

/-- Raw forgetful map sends typed scalar multiplication to raw scalar multiplication. -/
theorem TraceCorQHomFormalSum.smul_raw
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (formalSum : TraceCorQHomFormalSum source target) :
    (TraceCorQHomFormalSum.smul coefficient formalSum).raw =
      TraceCorQFormalSum.smul coefficient formalSum.raw :=
  match formalSum with
  | [] => rfl
  | term :: tail =>
      congrArg
        (fun tailRaw =>
          (coefficient * term.raw.1, term.raw.2) :: tailRaw)
        (TraceCorQHomFormalSum.smul_raw coefficient tail)

/-- Scale a typed hom representative, preserving its relation ledger. -/
def TraceCorQHomRepresentative.smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomRepresentative source target :=
  TraceCorQHomRepresentative.ofFormalSumLedger
    (TraceCorQHomFormalSum.smul coefficient representative.formalSum)
    representative.ledger

/-- The raw candidate of a scaled representative has scaled formal sum. -/
theorem TraceCorQHomRepresentative.smul_rawCandidate_formalSum
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate.formalSum =
      TraceCorQFormalSum.smul
        coefficient
        representative.rawCandidate.formalSum :=
  TraceCorQHomFormalSum.smul_raw
    coefficient
    representative.formalSum

/-- The raw candidate of a scaled representative has the original ledger. -/
theorem TraceCorQHomRepresentative.smul_rawCandidate_ledger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate.ledger =
      representative.rawCandidate.ledger :=
  rfl

/-- Representative scalar multiplication preserves analytic certificate ledgers. -/
theorem TraceCorQHomRepresentative.smul_certificateLedger
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).certificateLedger =
      representative.certificateLedger :=
  Eq.trans
    (TraceCorQHomRepresentative.ofFormalSumLedger_certificateLedger
      (TraceCorQHomFormalSum.smul coefficient representative.formalSum)
      representative.ledger)
    (congrArg
      (fun formalLedger =>
        ResidueChannelCertificateLedger.append
          formalLedger
          representative.ledger.certificateLedger)
      (Eq.trans
        (congrArg
          TraceCorQFormalSum.certificateLedger
          (TraceCorQHomFormalSum.smul_raw
            coefficient
            representative.formalSum))
        (TraceCorQFormalSum.smul_certificateLedger
          coefficient
          representative.formalSum.raw)))

/-- Representative scalar multiplication preserves imported finite-rectangle payload. -/
theorem TraceCorQHomRepresentative.smul_importedRectangleCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).importedRectangleCount =
      representative.importedRectangleCount :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangleCount
    (TraceCorQHomRepresentative.smul_certificateLedger
      coefficient
      representative)

/-- Representative scalar multiplication preserves imported finite explicit-formula rectangles. -/
theorem TraceCorQHomRepresentative.smul_importedRectangles
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).importedRectangles =
      representative.importedRectangles :=
  congrArg
    ResidueChannelCertificateLedger.importedRectangles
    (TraceCorQHomRepresentative.smul_certificateLedger
      coefficient
      representative)

/-- Representative scalar multiplication preserves internal trace-bookkeeping payload. -/
theorem TraceCorQHomRepresentative.smul_traceBookkeepingCount
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    (TraceCorQHomRepresentative.smul coefficient representative).traceBookkeepingCount =
      representative.traceBookkeepingCount :=
  congrArg
    ResidueChannelCertificateLedger.traceBookkeepingCount
    (TraceCorQHomRepresentative.smul_certificateLedger
      coefficient
      representative)

/-- A scaled representative is related to ambient scaling of its raw candidate. -/
def TraceCorQHomRelation.smulRepresentative_to_candidateSmul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientRelation
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate) :=
  TraceCorQQuotientRelation.sameFormalSum
    representative.rawCandidate.ledger
    (Eq.trans
      (TraceCorQHomRepresentative.smul_rawCandidate_formalSum
        coefficient
        representative)
      (Eq.symm
        (TraceCorQQuotientCandidate.smul_formalSum
          coefficient
          representative.rawCandidate)))

/-- Ambient candidate scaling is related back to the scaled representative. -/
def TraceCorQHomRelation.candidateSmul_to_smulRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientRelation
      (TraceCorQQuotientCandidate.smul
        coefficient
        representative.rawCandidate)
      (TraceCorQHomRepresentative.smul coefficient representative).rawCandidate :=
  TraceCorQQuotientRelation.symm
    (TraceCorQHomRelation.smulRepresentative_to_candidateSmul
      coefficient
      representative)

/-- Representative scalar multiplication is compatible with the typed hom relation. -/
def TraceCorQHomRelation.smulCongr
    {source target : TraceCorQObject}
    {left right : TraceCorQHomRepresentative source target}
    (coefficient : Rat)
    (relation : TraceCorQHomRelation left right) :
    TraceCorQHomRelation
      (TraceCorQHomRepresentative.smul coefficient left)
      (TraceCorQHomRepresentative.smul coefficient right) :=
  TraceCorQQuotientRelation.trans
    (TraceCorQHomRelation.smulRepresentative_to_candidateSmul
      coefficient
      left)
    (TraceCorQQuotientRelation.trans
      (TraceCorQQuotientRelation.smulCongr coefficient relation)
      (TraceCorQHomRelation.candidateSmul_to_smulRepresentative
        coefficient
        right))

/-- Scalar multiplication of typed hom classes. -/
def TraceCorQHom.smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom source target :=
  Quotient.liftOn
    hom
    (fun representative =>
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.smul coefficient representative))
    (fun left right relation =>
      TraceCorQHom.sound
        (TraceCorQHomRelation.smulCongr coefficient relation))

/-- Typed hom scalar multiplication agrees with representative scaling. -/
theorem TraceCorQHom.smul_ofRepresentative
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.ofRepresentative representative) =
      TraceCorQHom.ofRepresentative
        (TraceCorQHomRepresentative.smul coefficient representative) :=
  rfl

/-- The ambient map sends typed scalar multiplication to ambient quotient scaling. -/
theorem TraceCorQHom.ambient_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.ambient
      (TraceCorQHom.smul coefficient hom) =
      TraceCorQQuotient.smul
        coefficient
        (TraceCorQHom.ambient hom) :=
  Quotient.inductionOn
    hom
    (fun representative =>
      Eq.trans
        (TraceCorQHom.ambient_ofRepresentative
          (TraceCorQHomRepresentative.smul coefficient representative))
        (Eq.trans
          (TraceCorQQuotient.sound
            (TraceCorQHomRelation.smulRepresentative_to_candidateSmul
              coefficient
              representative))
          (Eq.symm
            (TraceCorQQuotient.smul_ofCandidate
              coefficient
              representative.rawCandidate))))

end AnalyticMotives
end LFunctions
end Boundary

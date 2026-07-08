import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.FormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientCandidate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Ambient.Owner

/-!
# Representative carriers for analytic effective realization

This file exposes the concrete representative-level morphism data of the
trace-correspondence category: typed formal sums, relation ledgers, raw quotient
candidates, ambient quotient classes, and analytic certificate payloads.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual typed hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeCarrier
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomRepresentative source target :=
  representative

/-- The typed formal sum carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeFormalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQHomFormalSum source target :=
  representative.formalSum

/-- The relation ledger carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQRelationLedger :=
  representative.ledger

/-- The raw quotient candidate carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeRawCandidate
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotientCandidate :=
  representative.rawCandidate

/-- The ambient quotient class carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeAmbientClass
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceCorQQuotient :=
  representative.ambientClass

/-- The analytic certificate ledger carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeCertificateLedger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    ResidueChannelCertificateLedger :=
  representative.certificateLedger

/-- The imported finite-rectangle count carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeImportedRectangleCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.importedRectangleCount

/-- The imported finite rectangles carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeImportedRectangles
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  representative.importedRectangles

/-- The trace-bookkeeping count carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeTraceBookkeepingCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.traceBookkeepingCount

/-- The rewrite-step count carried by a trace hom representative. -/
def TraceAnalyticEffectiveRealization.traceHomRepresentativeRewriteStepCount
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    Nat :=
  representative.rewriteStepCount

/-- The representative carrier is definitionally the supplied representative. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeCarrier_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeCarrier representative =
      representative :=
  rfl

/-- The representative formal-sum carrier is definitionally its formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeFormalSum_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeFormalSum representative =
      representative.formalSum :=
  rfl

/-- The representative ledger carrier is definitionally its relation ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeLedger_eq
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeLedger representative =
      representative.ledger :=
  rfl

/-- The representative raw candidate is built from its formal sum and relation ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeRawCandidate_formalSum
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceAnalyticEffectiveRealization.traceHomRepresentativeRawCandidate
      representative).formalSum =
      representative.formalSum.raw :=
  TraceCorQHomRepresentative.rawCandidate_formalSum
    representative

/-- The representative raw candidate carries its relation ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeRawCandidate_ledger
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    (TraceAnalyticEffectiveRealization.traceHomRepresentativeRawCandidate
      representative).ledger =
      representative.ledger :=
  TraceCorQHomRepresentative.rawCandidate_ledger
    representative

/-- The representative certificate ledger is formal-sum certificates plus relation certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeCertificateLedger_eq_append
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeCertificateLedger representative =
      ResidueChannelCertificateLedger.append
        representative.formalSum.certificateLedger
        representative.ledger.certificateLedger :=
  TraceCorQHomRepresentative.certificateLedger_eq
    representative

/-- The representative imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (representative : TraceCorQHomRepresentative source target) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeImportedRectangleCount representative =
      (TraceAnalyticEffectiveRealization.traceHomRepresentativeImportedRectangles
        representative).length :=
  TraceCorQHomRepresentative.importedRectangleCount_eq_length_importedRectangles
    representative

/-- The zero representative carrier has the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRepresentativeZero_certificateLedger
    (source target : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomRepresentativeCertificateLedger
      (TraceCorQHomRepresentative.ofFormalSumLedger
        (TraceCorQHomFormalSum.zero source target)
        TraceCorQRelationLedger.empty) =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomRepresentative.zero_certificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary

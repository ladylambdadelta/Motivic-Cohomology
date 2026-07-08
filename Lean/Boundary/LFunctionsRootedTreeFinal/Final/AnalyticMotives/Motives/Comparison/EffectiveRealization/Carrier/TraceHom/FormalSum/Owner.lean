import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Term.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Payload.Owner

/-!
# Formal-sum carriers for analytic effective realization

This file exposes the concrete typed formal-sum data carried by a trace
correspondence hom.  These are the morphism-side analytic inputs for the
effective-realization comparison.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual typed formal sum as its carrier. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumCarrier
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQHomFormalSum source target :=
  formalSum

/-- The raw untyped formal sum carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumRaw
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceCorQFormalSum :=
  formalSum.raw

/-- The analytic certificate ledger carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumCertificateLedger
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    ResidueChannelCertificateLedger :=
  formalSum.certificateLedger

/-- The imported finite-rectangle count carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumImportedRectangleCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.importedRectangleCount

/-- The imported finite rectangles carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumImportedRectangles
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  formalSum.importedRectangles

/-- The trace-bookkeeping count carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumTraceBookkeepingCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.traceBookkeepingCount

/-- The rewrite-step count carried by a typed trace hom formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomFormalSumRewriteStepCount
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    Nat :=
  formalSum.rewriteStepCount

/-- The formal-sum carrier is definitionally the supplied formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomFormalSumCarrier_eq
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceAnalyticEffectiveRealization.traceHomFormalSumCarrier formalSum =
      formalSum :=
  rfl

/-- The formal-sum raw carrier is definitionally the underlying raw formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomFormalSumRaw_eq
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceAnalyticEffectiveRealization.traceHomFormalSumRaw formalSum =
      formalSum.raw :=
  rfl

/-- The formal-sum certificate carrier is definitionally the existing ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomFormalSumCertificateLedger_eq
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceAnalyticEffectiveRealization.traceHomFormalSumCertificateLedger formalSum =
      formalSum.certificateLedger :=
  rfl

/-- The formal-sum imported count is the length of the imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomFormalSumImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (formalSum : TraceCorQHomFormalSum source target) :
    TraceAnalyticEffectiveRealization.traceHomFormalSumImportedRectangleCount formalSum =
      (TraceAnalyticEffectiveRealization.traceHomFormalSumImportedRectangles formalSum).length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    formalSum.certificateLedger

/-- The zero formal-sum carrier has the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomFormalSumZero_certificateLedger
    (source target : TraceCorQObject) :
    TraceAnalyticEffectiveRealization.traceHomFormalSumCertificateLedger
      (TraceCorQHomFormalSum.zero source target) =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQHomFormalSum.zero_certificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary

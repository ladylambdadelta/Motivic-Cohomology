import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RawSupport.Term.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Basic.Owner

/-!
# Raw support formal-sum carriers for analytic effective realization

This file exposes the raw finite Q-linear formal sums used as supports of
trace-correspondence relation generators.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual raw trace-correspondence formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCarrier
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum :=
  formalSum

/-- The certificate ledger carried by a raw support formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCertificateLedger
    (formalSum : TraceCorQFormalSum) :
    ResidueChannelCertificateLedger :=
  formalSum.certificateLedger

/-- The imported finite-rectangle count carried by a raw support formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumImportedRectangleCount
    (formalSum : TraceCorQFormalSum) :
    Nat :=
  formalSum.importedRectangleCount

/-- The imported finite rectangles carried by a raw support formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumImportedRectangles
    (formalSum : TraceCorQFormalSum) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  formalSum.importedRectangles

/-- The trace-bookkeeping count carried by a raw support formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumTraceBookkeepingCount
    (formalSum : TraceCorQFormalSum) :
    Nat :=
  formalSum.traceBookkeepingCount

/-- The rewrite-step count carried by a raw support formal sum. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumRewriteStepCount
    (formalSum : TraceCorQFormalSum) :
    Nat :=
  formalSum.rewriteStepCount

/-- The raw support formal-sum carrier is definitionally the supplied formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCarrier_eq
    (formalSum : TraceCorQFormalSum) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCarrier formalSum =
      formalSum :=
  rfl

/-- The zero raw support formal sum carries the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumZero_certificateLedger :
    TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCertificateLedger
      TraceCorQFormalSum.zero =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQFormalSum.zero_certificateLedger

/-- A singleton raw support formal sum carries the generator certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumSingleton_certificateLedger
    (coefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCertificateLedger
      (TraceCorQFormalSum.singleton coefficient generator) =
      ResidueChannelCertificateLedger.append
        generator.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQFormalSum.singleton_certificateLedger
    coefficient
    generator

/-- A cons raw support formal sum carries head certificates followed by tail certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCons_certificateLedger
    (term : TraceCorQTerm)
    (tail : TraceCorQFormalSum) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumCertificateLedger
      (term :: tail) =
      ResidueChannelCertificateLedger.append
        term.certificateLedger
        tail.certificateLedger :=
  TraceCorQFormalSum.cons_certificateLedger
    term
    tail

/-- A raw support formal sum's imported count is the length of its rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumImportedRectangleCount_eq_length
    (formalSum : TraceCorQFormalSum) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumImportedRectangleCount formalSum =
      (TraceAnalyticEffectiveRealization.traceHomRawSupportFormalSumImportedRectangles
        formalSum).length :=
  TraceCorQFormalSum.importedRectangleCount_eq_length_importedRectangles
    formalSum

end AnalyticMotives
end LFunctions
end Boundary

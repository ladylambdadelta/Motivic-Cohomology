import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Generator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Terms.Owner

/-!
# Raw support term carriers for analytic effective realization

This file exposes one raw weighted trace-correspondence term used inside
relation-generator supports.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual raw weighted trace-correspondence term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermCarrier
    (term : TraceCorQTerm) :
    TraceCorQTerm :=
  term

/-- The rational coefficient carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermCoefficient
    (term : TraceCorQTerm) :
    Rat :=
  term.1

/-- The trace-correspondence generator carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermGenerator
    (term : TraceCorQTerm) :
    TraceCorQGenerator :=
  term.2

/-- The certificate ledger carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermCertificateLedger
    (term : TraceCorQTerm) :
    ResidueChannelCertificateLedger :=
  term.certificateLedger

/-- The imported finite-rectangle count carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangleCount
    (term : TraceCorQTerm) :
    Nat :=
  term.importedRectangleCount

/-- The imported finite rectangles carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangles
    (term : TraceCorQTerm) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  term.importedRectangles

/-- The trace-bookkeeping count carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermTraceBookkeepingCount
    (term : TraceCorQTerm) :
    Nat :=
  term.traceBookkeepingCount

/-- The rewrite-step count carried by a raw support term. -/
def TraceAnalyticEffectiveRealization.traceHomRawSupportTermRewriteStepCount
    (term : TraceCorQTerm) :
    Nat :=
  term.rewriteStepCount

/-- The raw support term carrier is definitionally the supplied term. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportTermCarrier_eq
    (term : TraceCorQTerm) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportTermCarrier term =
      term :=
  rfl

/-- A raw support term carries the certificate ledger of its generator. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportTermCertificateLedger_eq_generator
    (term : TraceCorQTerm) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportTermCertificateLedger term =
      (TraceAnalyticEffectiveRealization.traceHomRawSupportTermGenerator
        term).certificateLedger :=
  TraceCorQTerm.certificateLedger_eq_generator
    term

/-- A raw support term imports the rectangles of its generator. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangles_eq_generator
    (term : TraceCorQTerm) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangles term =
      (TraceAnalyticEffectiveRealization.traceHomRawSupportTermGenerator
        term).importedRectangles :=
  TraceCorQTerm.importedRectangles_eq_generator
    term

/-- A raw support term's imported count is the length of its rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangleCount_eq_length
    (term : TraceCorQTerm) :
    TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangleCount term =
      (TraceAnalyticEffectiveRealization.traceHomRawSupportTermImportedRectangles
        term).length :=
  TraceCorQTerm.importedRectangleCount_eq_length_importedRectangles
    term

end AnalyticMotives
end LFunctions
end Boundary

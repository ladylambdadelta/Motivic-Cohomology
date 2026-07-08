import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.Generator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Terms.Owner

/-!
# Term carriers for analytic effective realization

This file exposes one weighted, typed trace-correspondence term.  A term is a
rational coefficient together with a concrete certified trace transport whose
source and target are the declared typed endpoints.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermCarrier
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceCorQHomTerm source target :=
  term

/-- The raw weighted term carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermRaw
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceCorQTerm :=
  term.raw

/-- The rational coefficient carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermCoefficient
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Rat :=
  term.coefficient

/-- The trace-correspondence generator carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermGenerator
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceCorQGenerator :=
  term.generator

/-- The analytic certificate ledger carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermCertificateLedger
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    ResidueChannelCertificateLedger :=
  term.certificateLedger

/-- The imported finite-rectangle count carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermImportedRectangleCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.importedRectangleCount

/-- The imported finite rectangles carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermImportedRectangles
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  term.importedRectangles

/-- The trace-bookkeeping count carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermTraceBookkeepingCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.traceBookkeepingCount

/-- The rewrite-step count carried by a typed trace hom term. -/
def TraceAnalyticEffectiveRealization.traceHomTermRewriteStepCount
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    Nat :=
  term.rewriteStepCount

/-- The typed term carrier is definitionally the supplied term. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermCarrier_eq
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceAnalyticEffectiveRealization.traceHomTermCarrier term =
      term :=
  rfl

/-- The typed term raw carrier is definitionally the underlying weighted generator. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermRaw_eq
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceAnalyticEffectiveRealization.traceHomTermRaw term =
      term.raw :=
  rfl

/-- The typed term coefficient carrier is definitionally its rational coefficient. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermCoefficient_eq
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceAnalyticEffectiveRealization.traceHomTermCoefficient term =
      term.coefficient :=
  rfl

/-- The typed term generator has the declared source endpoint. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermGenerator_source
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    (TraceAnalyticEffectiveRealization.traceHomTermGenerator term).source =
      source :=
  TraceCorQHomTerm.generator_source
    term

/-- The typed term generator has the declared target endpoint. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermGenerator_target
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    (TraceAnalyticEffectiveRealization.traceHomTermGenerator term).target =
      target :=
  TraceCorQHomTerm.generator_target
    term

/-- The typed term certificate ledger is the certificate ledger of its generator. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermCertificateLedger_eq_generator
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceAnalyticEffectiveRealization.traceHomTermCertificateLedger term =
      (TraceAnalyticEffectiveRealization.traceHomTermGenerator term).certificateLedger :=
  rfl

/-- The typed term imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomTermImportedRectangleCount_eq_length
    {source target : TraceCorQObject}
    (term : TraceCorQHomTerm source target) :
    TraceAnalyticEffectiveRealization.traceHomTermImportedRectangleCount term =
      (TraceAnalyticEffectiveRealization.traceHomTermImportedRectangles term).length :=
  TraceCorQHomTerm.importedRectangleCount_eq_length_importedRectangles
    term

end AnalyticMotives
end LFunctions
end Boundary

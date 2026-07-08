import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Owner

/-!
# Generator carriers for analytic effective realization

This file exposes the concrete transport data carried by a trace-correspondence
generator.  A generator is not an abstract correspondence interface here; it is
the existing certified `TraceTransport`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorCarrier
    (generator : TraceCorQGenerator) :
    TraceCorQGenerator :=
  generator

/-- The source trace object of a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorSource
    (generator : TraceCorQGenerator) :
    TraceCorQObject :=
  generator.source

/-- The target trace object of a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorTarget
    (generator : TraceCorQGenerator) :
    TraceCorQObject :=
  generator.target

/-- The rewrite path carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorPath
    (generator : TraceCorQGenerator) :
    TraceRewritePath :=
  generator.path

/-- The path certificate ledger carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorPathCertificateLedger
    (generator : TraceCorQGenerator) :
    ResidueChannelCertificateLedger :=
  generator.pathCertificateLedger

/-- The total analytic certificate ledger carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorCertificateLedger
    (generator : TraceCorQGenerator) :
    ResidueChannelCertificateLedger :=
  generator.certificateLedger

/-- The imported finite-rectangle count carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorImportedRectangleCount
    (generator : TraceCorQGenerator) :
    Nat :=
  generator.importedRectangleCount

/-- The imported finite rectangles carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorImportedRectangles
    (generator : TraceCorQGenerator) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  generator.importedRectangles

/-- The trace-bookkeeping count carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorTraceBookkeepingCount
    (generator : TraceCorQGenerator) :
    Nat :=
  generator.traceBookkeepingCount

/-- The rewrite-step count carried by a trace-correspondence generator. -/
def TraceAnalyticEffectiveRealization.traceHomGeneratorRewriteStepCount
    (generator : TraceCorQGenerator) :
    Nat :=
  generator.rewriteStepCount

/-- The generator carrier is definitionally the supplied generator. -/
theorem TraceAnalyticEffectiveRealization.traceHomGeneratorCarrier_eq
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomGeneratorCarrier generator =
      generator :=
  rfl

/-- The generator source carrier is definitionally the generator source. -/
theorem TraceAnalyticEffectiveRealization.traceHomGeneratorSource_eq
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomGeneratorSource generator =
      generator.source :=
  rfl

/-- The generator target carrier is definitionally the generator target. -/
theorem TraceAnalyticEffectiveRealization.traceHomGeneratorTarget_eq
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomGeneratorTarget generator =
      generator.target :=
  rfl

/-- The generator certificate ledger splits into source, target, and path ledgers. -/
theorem TraceAnalyticEffectiveRealization.traceHomGeneratorCertificateLedger_eq_source_target_path
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomGeneratorCertificateLedger generator =
      ResidueChannelCertificateLedger.append
        generator.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          generator.target.certificateLedger
          generator.pathCertificateLedger) :=
  TraceCorQGenerator.certificateLedger_eq_source_target_path
    generator

/-- The generator imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomGeneratorImportedRectangleCount_eq_length
    (generator : TraceCorQGenerator) :
    TraceAnalyticEffectiveRealization.traceHomGeneratorImportedRectangleCount generator =
      (TraceAnalyticEffectiveRealization.traceHomGeneratorImportedRectangles
        generator).length :=
  TraceCorQGenerator.importedRectangleCount_eq_length_importedRectangles
    generator

end AnalyticMotives
end LFunctions
end Boundary

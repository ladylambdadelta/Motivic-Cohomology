import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Objects.Owner

/-!
# Q-linear trace-correspondence generators

This file owns the morphism generators for trace correspondences over `Q`.

Generators are certified trace transports between residue-channel
presentations.  The analytic content is carried by the rewrite trace and its
certificates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A generator for Q-linear trace correspondences is a raw trace transport. -/
abbrev TraceCorQGenerator :=
  TraceTransport

/-- The analytic certificate ledger carried by a trace-correspondence generator. -/
def TraceCorQGenerator.certificateLedger
    (generator : TraceCorQGenerator) :
    ResidueChannelCertificateLedger :=
  TraceTransport.certificateLedger generator

/-- The imported finite-rectangle analytic payload carried by a trace-correspondence generator. -/
def TraceCorQGenerator.importedRectangleCount
    (generator : TraceCorQGenerator) :
    Nat :=
  TraceTransport.importedRectangleCount generator

/-- The imported finite explicit-formula rectangles carried by a trace-correspondence generator. -/
def TraceCorQGenerator.importedRectangles
    (generator : TraceCorQGenerator) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  TraceTransport.importedRectangles generator

/-- The internal trace-bookkeeping payload carried by a trace-correspondence generator. -/
def TraceCorQGenerator.traceBookkeepingCount
    (generator : TraceCorQGenerator) :
    Nat :=
  TraceTransport.traceBookkeepingCount generator

/-- The explicit rewrite-step payload carried by a trace-correspondence generator. -/
def TraceCorQGenerator.rewriteStepCount
    (generator : TraceCorQGenerator) :
    Nat :=
  TraceTransport.rewriteStepCount generator

/-- Generator imported payload is the imported payload of its certificate ledger. -/
theorem TraceCorQGenerator.importedRectangleCount_eq_certificateLedger_count
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  rfl

/-- Generator imported rectangles are extracted from its analytic certificate ledger. -/
theorem TraceCorQGenerator.importedRectangles_eq_certificateLedger_rectangles
    (generator : TraceCorQGenerator) :
    generator.importedRectangles =
      generator.certificateLedger.importedRectangles :=
  rfl

/-- Generator imported-rectangle count is the length of its extracted rectangle list. -/
theorem TraceCorQGenerator.importedRectangleCount_eq_length_importedRectangles
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.importedRectangles.length :=
  TraceTransport.importedRectangleCount_eq_length_importedRectangles
    generator

/-- Generator bookkeeping payload is the bookkeeping payload of its certificate ledger. -/
theorem TraceCorQGenerator.traceBookkeepingCount_eq_certificateLedger_count
    (generator : TraceCorQGenerator) :
    generator.traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  rfl

/-- Generator rewrite-step payload is the rewrite-step payload of its certificate ledger. -/
theorem TraceCorQGenerator.rewriteStepCount_eq_certificateLedger_count
    (generator : TraceCorQGenerator) :
    generator.rewriteStepCount =
      generator.certificateLedger.rewriteStepCount :=
  rfl

/-- Generator certificate ledger is source certificates, target certificates, then path certificates. -/
theorem TraceCorQGenerator.certificateLedger_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.certificateLedger =
      ResidueChannelCertificateLedger.append
        generator.source.certificateLedger
        (ResidueChannelCertificateLedger.append
          generator.target.certificateLedger
          generator.pathCertificateLedger) :=
  TraceTransport.certificateLedger_eq_source_target_path generator

/-- Generator imported payload splits into source, target, and path payload. -/
theorem TraceCorQGenerator.importedRectangleCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.source.importedRectangleCount +
        (generator.target.importedRectangleCount +
          generator.pathCertificateLedger.importedRectangleCount) :=
  TraceTransport.importedRectangleCount_eq_source_target_path generator

/-- Generator imported rectangles split into source, target, and path payload. -/
theorem TraceCorQGenerator.importedRectangles_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.importedRectangles =
      generator.source.importedRectangles ++
        (generator.target.importedRectangles ++
          generator.pathCertificateLedger.importedRectangles) :=
  TraceTransport.importedRectangles_eq_source_target_path generator

/-- Generator bookkeeping payload splits into source, target, and path payload. -/
theorem TraceCorQGenerator.traceBookkeepingCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.traceBookkeepingCount =
      generator.source.traceBookkeepingCount +
        (generator.target.traceBookkeepingCount +
          generator.pathCertificateLedger.traceBookkeepingCount) :=
  TraceTransport.traceBookkeepingCount_eq_source_target_path generator

/-- Generator rewrite-step payload splits into source, target, and path payload. -/
theorem TraceCorQGenerator.rewriteStepCount_eq_source_target_path
    (generator : TraceCorQGenerator) :
    generator.rewriteStepCount =
      generator.source.rewriteStepCount +
        (generator.target.rewriteStepCount +
          generator.pathCertificateLedger.rewriteStepCount) :=
  TraceTransport.rewriteStepCount_eq_source_target_path generator

end AnalyticMotives
end LFunctions
end Boundary

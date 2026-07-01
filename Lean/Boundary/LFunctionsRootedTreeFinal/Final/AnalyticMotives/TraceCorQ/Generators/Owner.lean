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

/-- The internal trace-bookkeeping payload carried by a trace-correspondence generator. -/
def TraceCorQGenerator.traceBookkeepingCount
    (generator : TraceCorQGenerator) :
    Nat :=
  TraceTransport.traceBookkeepingCount generator

/-- Generator imported payload is the imported payload of its certificate ledger. -/
theorem TraceCorQGenerator.importedRectangleCount_eq_certificateLedger_count
    (generator : TraceCorQGenerator) :
    generator.importedRectangleCount =
      generator.certificateLedger.importedRectangleCount :=
  rfl

/-- Generator bookkeeping payload is the bookkeeping payload of its certificate ledger. -/
theorem TraceCorQGenerator.traceBookkeepingCount_eq_certificateLedger_count
    (generator : TraceCorQGenerator) :
    generator.traceBookkeepingCount =
      generator.certificateLedger.traceBookkeepingCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Relations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceRewrite.Coherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner

/-!
# Relations for Q-linear trace correspondences

This file owns the relations imposed on generated trace correspondences.

The relations should come from analytic rewrite relations and higher
coherences: Stokes cancellation, residue-channel compatibility, refinement
invariance, schedule exchange, weight drop, and Fubini coherence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A generator for a relation on Q-linear trace correspondences.

It consists of the higher coherence cell that justifies the relation and the
formal Q-linear trace-correspondence support on which that coherence acts.
-/
abbrev TraceCorQRelationGenerator :=
  TraceCoherenceCell × TraceCorQFormalSum

/-- The higher coherence cell supporting a trace-correspondence relation. -/
def TraceCorQRelationGenerator.cell
    (relation : TraceCorQRelationGenerator) :
    TraceCoherenceCell :=
  relation.1

/-- The formal Q-linear support of a trace-correspondence relation. -/
def TraceCorQRelationGenerator.support
    (relation : TraceCorQRelationGenerator) :
    TraceCorQFormalSum :=
  relation.2

/-- Build a relation generator from a coherence cell and its formal support. -/
def TraceCorQRelationGenerator.ofCellSupport
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    TraceCorQRelationGenerator :=
  (cell, support)

/-- The analytic certificate ledger attached to a relation generator. -/
def TraceCorQRelationGenerator.certificateLedger
    (relation : TraceCorQRelationGenerator) :
    ResidueChannelCertificateLedger :=
  ResidueChannelCertificateLedger.ofCoherenceCell relation.cell

/-- The imported finite-rectangle payload attached to a relation generator. -/
def TraceCorQRelationGenerator.importedRectangleCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.certificateLedger.importedRectangleCount

/-- The internal trace-bookkeeping payload attached to a relation generator. -/
def TraceCorQRelationGenerator.traceBookkeepingCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload attached to a relation generator. -/
def TraceCorQRelationGenerator.rewriteStepCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.certificateLedger.rewriteStepCount

/-- A relation built from a cell and support is certified by that cell. -/
theorem TraceCorQRelationGenerator.ofCellSupport_certificateLedger
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).certificateLedger =
      ResidueChannelCertificateLedger.ofCoherenceCell cell :=
  rfl

/-- A relation built from a cell carries no imported finite-rectangle payload. -/
theorem TraceCorQRelationGenerator.ofCellSupport_importedRectangleCount
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofCoherenceCell cell).importedRectangleCount :=
  rfl

/-- A relation built from a cell carries the bookkeeping payload of that cell certificate. -/
theorem TraceCorQRelationGenerator.ofCellSupport_traceBookkeepingCount
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).traceBookkeepingCount =
      (ResidueChannelCertificateLedger.ofCoherenceCell cell).traceBookkeepingCount :=
  rfl

/-- A relation built from a cell carries the rewrite-step payload of that cell certificate. -/
theorem TraceCorQRelationGenerator.ofCellSupport_rewriteStepCount
    (cell : TraceCoherenceCell) (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).rewriteStepCount =
      (ResidueChannelCertificateLedger.ofCoherenceCell cell).rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

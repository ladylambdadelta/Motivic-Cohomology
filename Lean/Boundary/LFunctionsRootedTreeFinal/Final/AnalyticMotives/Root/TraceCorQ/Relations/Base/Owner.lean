import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner

/-!
# Top-root trace-correspondence relation generators

This file exposes the base relation-generator bookkeeping for Q-linear trace
correspondences under the top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes the certificate ledger of a relation built from a cell and support. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_ofCellSupport_certificateLedger
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).certificateLedger =
      ResidueChannelCertificateLedger.ofCertifiedCoherenceCell cell :=
  TraceCorQRelationGenerator.ofCellSupport_certificateLedger
    cell
    support

/-- The top root exposes imported-rectangle counts for relations built from cells. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_ofCellSupport_importedRectangleCount
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).importedRectangleCount =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).importedRectangleCount :=
  TraceCorQRelationGenerator.ofCellSupport_importedRectangleCount
    cell
    support

/-- The top root exposes imported-rectangle lists for relations built from cells. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_ofCellSupport_importedRectangles
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).importedRectangles =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).importedRectangles :=
  TraceCorQRelationGenerator.ofCellSupport_importedRectangles
    cell
    support

/-- The top root exposes relation-generator imported-rectangle count as list length. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_importedRectangleCount_eq_length
    (relation : TraceCorQRelationGenerator) :
    relation.importedRectangleCount =
      relation.importedRectangles.length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    relation

/-- The top root exposes trace-bookkeeping counts for relations built from cells. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_ofCellSupport_traceBookkeepingCount
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).traceBookkeepingCount =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).traceBookkeepingCount :=
  TraceCorQRelationGenerator.ofCellSupport_traceBookkeepingCount
    cell
    support

/-- The top root exposes rewrite-step counts for relations built from cells. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_ofCellSupport_rewriteStepCount
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    (TraceCorQRelationGenerator.ofCellSupport
      cell
      support).rewriteStepCount =
      (ResidueChannelCertificateLedger.ofCertifiedCoherenceCell
        cell).rewriteStepCount :=
  TraceCorQRelationGenerator.ofCellSupport_rewriteStepCount
    cell
    support

/-- The top root exposes the path-cell certificate shape of a relation generator. -/
theorem AnalyticMotivesRoot.traceCorQRelationGenerator_certificateLedger_eq_paths_cell
    (relation : TraceCorQRelationGenerator) :
    relation.certificateLedger =
      ResidueChannelCertificateAtom.rewritePath relation.cell.source ::
        ResidueChannelCertificateAtom.rewritePath relation.cell.target ::
          ResidueChannelCertificateAtom.coherenceCell relation.cell ::
            ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.certificateLedger_eq_paths_cell
    relation

end AnalyticMotives
end LFunctions
end Boundary

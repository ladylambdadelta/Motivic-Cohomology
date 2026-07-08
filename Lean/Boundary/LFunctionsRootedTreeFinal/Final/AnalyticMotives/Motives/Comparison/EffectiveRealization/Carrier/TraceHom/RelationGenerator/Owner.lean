import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.CoherenceCell.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RawSupport.FormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Relations.Owner

/-!
# Relation-generator carriers for analytic effective realization

This file exposes one concrete trace-correspondence relation generator: a
higher coherence cell together with the formal Q-linear support on which that
coherence acts.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCarrier
    (relation : TraceCorQRelationGenerator) :
    TraceCorQRelationGenerator :=
  relation

/-- The coherence cell carried by a trace-correspondence relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCell
    (relation : TraceCorQRelationGenerator) :
    TraceCoherenceCell :=
  relation.cell

/-- The formal Q-linear support carried by a trace-correspondence relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorSupport
    (relation : TraceCorQRelationGenerator) :
    TraceCorQFormalSum :=
  relation.support

/-- The certificate ledger carried by a trace-correspondence relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCertificateLedger
    (relation : TraceCorQRelationGenerator) :
    ResidueChannelCertificateLedger :=
  relation.certificateLedger

/-- The imported finite-rectangle count carried by a relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorImportedRectangleCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.importedRectangleCount

/-- The imported finite rectangles carried by a relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorImportedRectangles
    (relation : TraceCorQRelationGenerator) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  relation.importedRectangles

/-- The trace-bookkeeping count carried by a relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorTraceBookkeepingCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.traceBookkeepingCount

/-- The rewrite-step count carried by a relation generator. -/
def TraceAnalyticEffectiveRealization.traceHomRelationGeneratorRewriteStepCount
    (relation : TraceCorQRelationGenerator) :
    Nat :=
  relation.rewriteStepCount

/-- The relation-generator carrier is definitionally the supplied relation. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCarrier_eq
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCarrier relation =
      relation :=
  rfl

/-- The relation-generator cell carrier is definitionally its coherence cell. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCell_eq
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCell relation =
      relation.cell :=
  rfl

/-- The relation-generator support carrier is definitionally its formal support. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorSupport_eq
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorSupport relation =
      relation.support :=
  rfl

/-- A relation built from a cell and support is certified by that cell. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorOfCellSupport_certificateLedger
    (cell : TraceCoherenceCell)
    (support : TraceCorQFormalSum) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCertificateLedger
      (TraceCorQRelationGenerator.ofCellSupport cell support) =
      ResidueChannelCertificateLedger.ofCertifiedCoherenceCell cell :=
  TraceCorQRelationGenerator.ofCellSupport_certificateLedger
    cell
    support

/-- A relation generator's imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorImportedRectangleCount_eq_length
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorImportedRectangleCount relation =
      (TraceAnalyticEffectiveRealization.traceHomRelationGeneratorImportedRectangles
        relation).length :=
  TraceCorQRelationGenerator.importedRectangleCount_eq_length_importedRectangles
    relation

/-- A relation generator certifies source path, target path, and coherence cell. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCertificateLedger_eq_paths_cell
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationGeneratorCertificateLedger relation =
      ResidueChannelCertificateAtom.rewritePath relation.cell.source ::
        ResidueChannelCertificateAtom.rewritePath relation.cell.target ::
          ResidueChannelCertificateAtom.coherenceCell relation.cell ::
            ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationGenerator.certificateLedger_eq_paths_cell
    relation

end AnalyticMotives
end LFunctions
end Boundary

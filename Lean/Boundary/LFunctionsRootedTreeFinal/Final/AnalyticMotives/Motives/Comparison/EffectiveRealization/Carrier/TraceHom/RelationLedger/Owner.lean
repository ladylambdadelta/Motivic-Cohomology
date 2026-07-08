import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationGenerator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.RelationLedgers.Owner

/-!
# Relation-ledger carriers for analytic effective realization

This file exposes the concrete finite relation ledger used by trace hom
representatives and relation witnesses.  The ledger is the certificate-bearing
source of quotient relations for later descent to effective motives.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerCarrier
    (ledger : TraceCorQRelationLedger) :
    TraceCorQRelationLedger :=
  ledger

/-- The certificate ledger carried by a trace-correspondence relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerCertificateLedger
    (ledger : TraceCorQRelationLedger) :
    ResidueChannelCertificateLedger :=
  ledger.certificateLedger

/-- The imported finite-rectangle count carried by a relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerImportedRectangleCount
    (ledger : TraceCorQRelationLedger) :
    Nat :=
  ledger.importedRectangleCount

/-- The imported finite rectangles carried by a relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerImportedRectangles
    (ledger : TraceCorQRelationLedger) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  ledger.importedRectangles

/-- The trace-bookkeeping count carried by a relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerTraceBookkeepingCount
    (ledger : TraceCorQRelationLedger) :
    Nat :=
  ledger.traceBookkeepingCount

/-- The rewrite-step count carried by a relation ledger. -/
def TraceAnalyticEffectiveRealization.traceHomRelationLedgerRewriteStepCount
    (ledger : TraceCorQRelationLedger) :
    Nat :=
  ledger.rewriteStepCount

/-- The relation-ledger carrier is definitionally the supplied ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationLedgerCarrier_eq
    (ledger : TraceCorQRelationLedger) :
    TraceAnalyticEffectiveRealization.traceHomRelationLedgerCarrier ledger =
      ledger :=
  rfl

/-- The empty relation ledger carries the empty certificate ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationLedgerEmpty_certificateLedger :
    TraceAnalyticEffectiveRealization.traceHomRelationLedgerCertificateLedger
      TraceCorQRelationLedger.empty =
      ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.empty_certificateLedger

/-- A singleton relation ledger carries its relation certificates followed by the empty tail. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationLedgerSingleton_certificateLedger
    (relation : TraceCorQRelationGenerator) :
    TraceAnalyticEffectiveRealization.traceHomRelationLedgerCertificateLedger
      (TraceCorQRelationLedger.singleton relation) =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ResidueChannelCertificateLedger.empty :=
  TraceCorQRelationLedger.singleton_certificateLedger
    relation

/-- A cons relation ledger carries head certificates followed by tail certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationLedgerCons_certificateLedger
    (relation : TraceCorQRelationGenerator)
    (ledger : TraceCorQRelationLedger) :
    TraceAnalyticEffectiveRealization.traceHomRelationLedgerCertificateLedger
      (relation :: ledger) =
      ResidueChannelCertificateLedger.append
        relation.certificateLedger
        ledger.certificateLedger :=
  TraceCorQRelationLedger.cons_certificateLedger
    relation
    ledger

/-- The imported count carried by a relation ledger is the length of its rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomRelationLedgerImportedRectangleCount_eq_length
    (ledger : TraceCorQRelationLedger) :
    TraceAnalyticEffectiveRealization.traceHomRelationLedgerImportedRectangleCount ledger =
      (TraceAnalyticEffectiveRealization.traceHomRelationLedgerImportedRectangles
        ledger).length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    ledger.certificateLedger

end AnalyticMotives
end LFunctions
end Boundary

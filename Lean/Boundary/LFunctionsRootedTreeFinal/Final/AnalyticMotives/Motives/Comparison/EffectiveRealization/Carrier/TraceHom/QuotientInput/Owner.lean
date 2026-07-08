import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RawSupport.FormalSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.RelationLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Core.Owner

/-!
# Quotient-input carriers for analytic effective realization

This file exposes the concrete pre-quotient input: a raw formal sum together
with the relation ledger used to certify quotient identifications.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The comparison boundary keeps the actual trace-correspondence quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputCarrier
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientInput :=
  input

/-- The raw formal sum carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputFormalSum
    (input : TraceCorQQuotientInput) :
    TraceCorQFormalSum :=
  input.formalSum

/-- The relation ledger carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputLedger
    (input : TraceCorQQuotientInput) :
    TraceCorQRelationLedger :=
  input.ledger

/-- The certificate ledger carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputCertificateLedger
    (input : TraceCorQQuotientInput) :
    ResidueChannelCertificateLedger :=
  input.certificateLedger

/-- The imported finite-rectangle count carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputImportedRectangleCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.importedRectangleCount

/-- The imported finite rectangles carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputImportedRectangles
    (input : TraceCorQQuotientInput) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  input.importedRectangles

/-- The trace-bookkeeping count carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputTraceBookkeepingCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.traceBookkeepingCount

/-- The rewrite-step count carried by a quotient input. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientInputRewriteStepCount
    (input : TraceCorQQuotientInput) :
    Nat :=
  input.rewriteStepCount

/-- The quotient-input carrier is definitionally the supplied input. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientInputCarrier_eq
    (input : TraceCorQQuotientInput) :
    TraceAnalyticEffectiveRealization.traceHomQuotientInputCarrier input =
      input :=
  rfl

/-- The quotient-input formal-sum carrier is definitionally its formal sum. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientInputFormalSum_eq
    (input : TraceCorQQuotientInput) :
    TraceAnalyticEffectiveRealization.traceHomQuotientInputFormalSum input =
      input.formalSum :=
  rfl

/-- The quotient-input ledger carrier is definitionally its relation ledger. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientInputLedger_eq
    (input : TraceCorQQuotientInput) :
    TraceAnalyticEffectiveRealization.traceHomQuotientInputLedger input =
      input.ledger :=
  rfl

/-- The quotient-input certificate ledger appends formal-sum and relation-ledger certificates. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientInputCertificateLedger_eq_append
    (input : TraceCorQQuotientInput) :
    TraceAnalyticEffectiveRealization.traceHomQuotientInputCertificateLedger input =
      ResidueChannelCertificateLedger.append
        input.formalSum.certificateLedger
        input.ledger.certificateLedger :=
  rfl

/-- A quotient input's imported count is the length of its imported rectangle list. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientInputImportedRectangleCount_eq_length
    (input : TraceCorQQuotientInput) :
    TraceAnalyticEffectiveRealization.traceHomQuotientInputImportedRectangleCount input =
      (TraceAnalyticEffectiveRealization.traceHomQuotientInputImportedRectangles
        input).length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    input.certificateLedger

end AnalyticMotives
end LFunctions
end Boundary

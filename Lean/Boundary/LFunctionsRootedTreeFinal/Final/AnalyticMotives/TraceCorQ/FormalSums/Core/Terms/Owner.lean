import Mathlib.Data.List.Perm.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Generators.Composition.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner

/-!
# Weighted trace-correspondence terms

This file owns rationally weighted trace-correspondence terms and their
certificate-payload projections.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A rationally weighted trace-correspondence generator. -/
abbrev TraceCorQTerm :=
  Rat × TraceCorQGenerator

/-- The analytic certificate ledger carried by a weighted trace-correspondence term. -/
def TraceCorQTerm.certificateLedger
    (term : TraceCorQTerm) :
    ResidueChannelCertificateLedger :=
  term.2.certificateLedger

/-- The imported finite-rectangle analytic payload carried by a weighted term. -/
def TraceCorQTerm.importedRectangleCount
    (term : TraceCorQTerm) :
    Nat :=
  term.certificateLedger.importedRectangleCount

/-- The imported finite explicit-formula rectangles carried by a weighted term. -/
def TraceCorQTerm.importedRectangles
    (term : TraceCorQTerm) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  term.certificateLedger.importedRectangles

/-- The internal trace-bookkeeping payload carried by a weighted term. -/
def TraceCorQTerm.traceBookkeepingCount
    (term : TraceCorQTerm) :
    Nat :=
  term.certificateLedger.traceBookkeepingCount

/-- The explicit rewrite-step payload carried by a weighted term. -/
def TraceCorQTerm.rewriteStepCount
    (term : TraceCorQTerm) :
    Nat :=
  term.certificateLedger.rewriteStepCount

/-- A weighted term carries the certificate ledger of its generator. -/
theorem TraceCorQTerm.certificateLedger_eq_generator
    (term : TraceCorQTerm) :
    term.certificateLedger =
      term.2.certificateLedger :=
  rfl

/-- A weighted term imports the payload of its generator. -/
theorem TraceCorQTerm.importedRectangleCount_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.2.importedRectangleCount :=
  rfl

/-- A weighted term exposes the imported rectangles of its generator. -/
theorem TraceCorQTerm.importedRectangles_eq_generator
    (term : TraceCorQTerm) :
    term.importedRectangles =
      term.2.importedRectangles :=
  rfl

/-- A weighted term's imported-rectangle count is the length of its extracted rectangles. -/
theorem TraceCorQTerm.importedRectangleCount_eq_length_importedRectangles
    (term : TraceCorQTerm) :
    term.importedRectangleCount =
      term.importedRectangles.length :=
  ResidueChannelCertificateLedger.importedRectangleCount_eq_length_importedRectangles
    term.certificateLedger

/-- A weighted term keeps the bookkeeping payload of its generator. -/
theorem TraceCorQTerm.traceBookkeepingCount_eq_generator
    (term : TraceCorQTerm) :
    term.traceBookkeepingCount =
      term.2.traceBookkeepingCount :=
  rfl

/-- A weighted term keeps the rewrite-step payload of its generator. -/
theorem TraceCorQTerm.rewriteStepCount_eq_generator
    (term : TraceCorQTerm) :
    term.rewriteStepCount =
      term.2.rewriteStepCount :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Preparation.Core.Owner

/-!
# Core quotient candidates for Q-linear trace correspondences

This file owns the raw candidate type, its projections, and the primitive
empty, additive, scalar, and composition constructors.  The theorem layer lives
in the parent candidate owner.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A raw representative candidate for the trace-correspondence quotient. -/
abbrev TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput

/-- The quotient input represented by a candidate. -/
def TraceCorQQuotientCandidate.input
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientInput :=
  candidate

/-- Build a quotient candidate from a quotient input. -/
def TraceCorQQuotientCandidate.ofInput
    (input : TraceCorQQuotientInput) :
    TraceCorQQuotientCandidate :=
  input

/-- The formal sum represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.formalSum
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQFormalSum :=
  candidate.input.formalSum

/-- The relation ledger represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.ledger
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQRelationLedger :=
  candidate.input.ledger

/-- The analytic certificate ledger represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.certificateLedger
    (candidate : TraceCorQQuotientCandidate) :
    ResidueChannelCertificateLedger :=
  candidate.input.certificateLedger

/-- The imported finite-rectangle payload represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.importedRectangleCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.input.importedRectangleCount

/-- The imported finite explicit-formula rectangles represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.importedRectangles
    (candidate : TraceCorQQuotientCandidate) :
    List ZetaAdmissibleFunction.ExplicitFormulaRectangle :=
  candidate.input.importedRectangles

/-- The internal trace-bookkeeping payload represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.traceBookkeepingCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.input.traceBookkeepingCount

/-- The explicit rewrite-step payload represented by a quotient candidate. -/
def TraceCorQQuotientCandidate.rewriteStepCount
    (candidate : TraceCorQQuotientCandidate) :
    Nat :=
  candidate.input.rewriteStepCount

/-- The empty quotient candidate. -/
def TraceCorQQuotientCandidate.empty :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.empty

/-- Add quotient candidates by adding their quotient inputs. -/
def TraceCorQQuotientCandidate.add
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.add left.input right.input

/-- Scale a quotient candidate by scaling its quotient input. -/
def TraceCorQQuotientCandidate.smul
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.smul coefficient candidate.input

/-- Compose quotient candidates by composing their quotient inputs. -/
def TraceCorQQuotientCandidate.comp
    (left right : TraceCorQQuotientCandidate) :
    TraceCorQQuotientCandidate :=
  TraceCorQQuotientInput.comp left.input right.input

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.EffectiveRealization.Carrier.TraceHom.QuotientClass.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Owner

/-!
# Quotient-operation carriers for analytic effective realization

This file exposes the descended operations on raw trace-correspondence quotient
classes that the typed hom layer uses as its ambient quotient.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The zero ambient trace-correspondence quotient class. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientZero :
    TraceCorQQuotient :=
  TraceCorQQuotient.zero

/-- Addition of ambient trace-correspondence quotient classes. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientAdd
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient :=
  TraceCorQQuotient.add left right

/-- Rational scalar multiplication of ambient trace-correspondence quotient classes. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientSmul
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient :=
  TraceCorQQuotient.smul coefficient candidateClass

/-- Composition of ambient trace-correspondence quotient classes. -/
def TraceAnalyticEffectiveRealization.traceHomQuotientComp
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient :=
  TraceCorQQuotient.comp left right

/-- The zero quotient class is the class of the empty candidate. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientZero_eq_ofCandidate_empty :
    TraceAnalyticEffectiveRealization.traceHomQuotientZero =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        TraceCorQQuotientCandidate.empty :=
  TraceCorQQuotientOperations.zero_eq_ofCandidate_empty

/-- Addition of quotient classes is represented by candidate addition. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientAdd_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientAdd
        (TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate left)
        (TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate right) =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        (TraceCorQQuotientCandidate.add left right) :=
  TraceCorQQuotientOperations.add_ofCandidate
    left
    right

/-- Scalar multiplication of quotient classes is represented by candidate scalar multiplication. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientSmul_ofCandidate
    (coefficient : Rat)
    (candidate : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientSmul
        coefficient
        (TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
          candidate) =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        (TraceCorQQuotientCandidate.smul coefficient candidate) :=
  TraceCorQQuotientOperations.smul_ofCandidate
    coefficient
    candidate

/-- Composition of quotient classes is represented by candidate composition. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientComp_ofCandidate
    (left right : TraceCorQQuotientCandidate) :
    TraceAnalyticEffectiveRealization.traceHomQuotientComp
        (TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate left)
        (TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate right) =
      TraceAnalyticEffectiveRealization.traceHomQuotientClassOfCandidate
        (TraceCorQQuotientCandidate.comp left right) :=
  TraceCorQQuotientOperations.comp_ofCandidate
    left
    right

/-- Addition of quotient classes is associative. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientAdd_assoc
    (left middle right : TraceCorQQuotient) :
    TraceAnalyticEffectiveRealization.traceHomQuotientAdd
        (TraceAnalyticEffectiveRealization.traceHomQuotientAdd left middle)
        right =
      TraceAnalyticEffectiveRealization.traceHomQuotientAdd
        left
        (TraceAnalyticEffectiveRealization.traceHomQuotientAdd middle right) :=
  TraceCorQQuotientOperations.add_assoc
    left
    middle
    right

/-- Composition of quotient classes is associative. -/
theorem TraceAnalyticEffectiveRealization.traceHomQuotientComp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceAnalyticEffectiveRealization.traceHomQuotientComp
        (TraceAnalyticEffectiveRealization.traceHomQuotientComp left middle)
        right =
      TraceAnalyticEffectiveRealization.traceHomQuotientComp
        left
        (TraceAnalyticEffectiveRealization.traceHomQuotientComp middle right) :=
  TraceCorQQuotientOperations.comp_assoc
    left
    middle
    right

end AnalyticMotives
end LFunctions
end Boundary

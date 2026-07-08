import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Scalars.Owner

/-!
# Top-root formal-sum scalar laws

This file exposes scalar laws for finite `Q`-linear formal sums through the
top-level `AnalyticMotivesRoot` namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes scalar multiplication of the zero formal sum. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_smul_zero
    (coefficient : Rat) :
    TraceCorQFormalSum.smul coefficient TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQ.formalSum_smul_zero
    coefficient

/-- The top root exposes scalar distributivity over formal-sum addition. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_smul_add
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      coefficient
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.smul coefficient left)
        (TraceCorQFormalSum.smul coefficient right) :=
  TraceCorQ.formalSum_smul_add
    coefficient
    left
    right

/-- The top root exposes the unit scalar law for formal sums. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_one_smul
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul 1 formalSum =
      formalSum :=
  TraceCorQ.formalSum_one_smul
    formalSum

/-- The top root exposes scalar-associativity for formal sums. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.smul rightCoefficient formalSum) =
      TraceCorQFormalSum.smul
        (leftCoefficient * rightCoefficient)
        formalSum :=
  TraceCorQ.formalSum_smul_smul
    leftCoefficient
    rightCoefficient
    formalSum

/-- The top root exposes scalar multiplication of singleton formal sums. -/
theorem AnalyticMotivesRoot.traceCorQFormalSum_smul_singleton
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.singleton rightCoefficient generator) =
      TraceCorQFormalSum.singleton
        (leftCoefficient * rightCoefficient)
        generator :=
  TraceCorQ.formalSum_smul_singleton
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary

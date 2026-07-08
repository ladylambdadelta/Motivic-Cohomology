import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Composition.Basic.Scalar.Owner

/-!
# Public formal-sum scalar laws

This file exposes the concrete scalar laws for finite `Q`-linear formal sums
under the `TraceCorQ` aggregate namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The trace-correspondence root exposes scalar multiplication of the zero formal sum. -/
theorem TraceCorQ.formalSum_smul_zero
    (coefficient : Rat) :
    TraceCorQFormalSum.smul coefficient TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  TraceCorQFormalSum.smul_zero
    coefficient

/-- The trace-correspondence root exposes scalar distributivity over formal-sum addition. -/
theorem TraceCorQ.formalSum_smul_add
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      coefficient
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.smul coefficient left)
        (TraceCorQFormalSum.smul coefficient right) :=
  TraceCorQFormalSum.smul_add
    coefficient
    left
    right

/-- The trace-correspondence root exposes the unit scalar law for formal sums. -/
theorem TraceCorQ.formalSum_one_smul
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul 1 formalSum =
      formalSum :=
  TraceCorQFormalSum.one_smul
    formalSum

/-- The trace-correspondence root exposes scalar-associativity for formal sums. -/
theorem TraceCorQ.formalSum_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.smul rightCoefficient formalSum) =
      TraceCorQFormalSum.smul
        (leftCoefficient * rightCoefficient)
        formalSum :=
  TraceCorQFormalSum.smul_smul
    leftCoefficient
    rightCoefficient
    formalSum

/-- The trace-correspondence root exposes scalar multiplication of singleton formal sums. -/
theorem TraceCorQ.formalSum_smul_singleton
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.singleton rightCoefficient generator) =
      TraceCorQFormalSum.singleton
        (leftCoefficient * rightCoefficient)
        generator :=
  TraceCorQFormalSum.smul_singleton
    leftCoefficient
    rightCoefficient
    generator

end AnalyticMotives
end LFunctions
end Boundary

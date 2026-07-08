import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.FormalSums.Core.Owner

/-!
# Scalar laws for Q-linear trace-correspondence formal sums

This file owns the scalar-action laws for raw formal sums, before using the
finite bilinear composition expansion.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Scalar multiplication of the zero formal sum is zero. -/
theorem TraceCorQFormalSum.smul_zero
    (coefficient : Rat) :
    TraceCorQFormalSum.smul coefficient TraceCorQFormalSum.zero =
      TraceCorQFormalSum.zero :=
  rfl

/-- Scalar multiplication distributes over formal-sum addition. -/
theorem TraceCorQFormalSum.smul_add
    (coefficient : Rat)
    (left right : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      coefficient
      (TraceCorQFormalSum.add left right) =
      TraceCorQFormalSum.add
        (TraceCorQFormalSum.smul coefficient left)
        (TraceCorQFormalSum.smul coefficient right) :=
  show
      List.map
        (fun term => (coefficient * term.1, term.2))
        (left ++ right) =
        List.map
          (fun term => (coefficient * term.1, term.2))
          left ++
          List.map
            (fun term => (coefficient * term.1, term.2))
            right from
    List.map_append
      (fun term => (coefficient * term.1, term.2))
      left
      right

/-- Scaling a formal sum by one leaves it unchanged. -/
theorem TraceCorQFormalSum.one_smul
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul 1 formalSum =
      formalSum :=
  match formalSum with
  | [] => rfl
  | (coefficient, generator) :: tail =>
      Eq.trans
        (congrArg
          (fun scaledCoefficient =>
            (scaledCoefficient, generator) ::
              TraceCorQFormalSum.smul 1 tail)
          (one_mul coefficient))
        (congrArg
          (fun scaledTail => (coefficient, generator) :: scaledTail)
          (TraceCorQFormalSum.one_smul tail))

/-- Successive scalar multiplications compose by multiplying scalars. -/
theorem TraceCorQFormalSum.smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (formalSum : TraceCorQFormalSum) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.smul rightCoefficient formalSum) =
      TraceCorQFormalSum.smul
        (leftCoefficient * rightCoefficient)
        formalSum :=
  match formalSum with
  | [] => rfl
  | (coefficient, generator) :: tail =>
      Eq.trans
        (congrArg
          (fun scaledCoefficient =>
            (scaledCoefficient, generator) ::
              TraceCorQFormalSum.smul
                leftCoefficient
                (TraceCorQFormalSum.smul rightCoefficient tail))
          (Eq.symm
            (mul_assoc
              leftCoefficient
              rightCoefficient
              coefficient)))
        (congrArg
          (fun scaledTail =>
            ((leftCoefficient * rightCoefficient) * coefficient,
              generator) :: scaledTail)
          (TraceCorQFormalSum.smul_smul
            leftCoefficient
            rightCoefficient
            tail))

/-- Scalar multiplication of a singleton scales its coefficient. -/
theorem TraceCorQFormalSum.smul_singleton
    (leftCoefficient rightCoefficient : Rat)
    (generator : TraceCorQGenerator) :
    TraceCorQFormalSum.smul
      leftCoefficient
      (TraceCorQFormalSum.singleton rightCoefficient generator) =
      TraceCorQFormalSum.singleton
        (leftCoefficient * rightCoefficient)
        generator :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

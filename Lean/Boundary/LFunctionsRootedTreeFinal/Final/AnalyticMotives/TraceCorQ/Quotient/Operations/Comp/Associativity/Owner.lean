import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.SingletonLeft.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.FormalSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Comp.Associativity.Full.Owner

/-!
# Associativity for quotient trace-correspondence composition

This aggregate owns quotient composition associativity from singleton
generators through formal sums and fourfold normalization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Composition-associativity aggregate: singleton-singleton-formal-sum associativity. -/
theorem TraceCorQQuotient.comp_associativity_singleton_singleton_ofFormalSum
    (firstCoefficient secondCoefficient : Rat)
    (first second : TraceCorQGenerator)
    (right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.singleton secondCoefficient second))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.singleton secondCoefficient second)
          (TraceCorQQuotient.ofFormalSum right)) :=
  TraceCorQQuotient.comp_assoc_singleton_singleton_ofFormalSum
    firstCoefficient
    secondCoefficient
    first
    second
    right

/-- Composition-associativity aggregate: singleton-formal-sum-formal-sum associativity. -/
theorem TraceCorQQuotient.comp_associativity_singleton_ofFormalSum_ofFormalSum
    (firstCoefficient : Rat)
    (first : TraceCorQGenerator)
    (middle right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.ofFormalSum middle))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.singleton firstCoefficient first)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.ofFormalSum middle)
          (TraceCorQQuotient.ofFormalSum right)) :=
  TraceCorQQuotient.comp_assoc_singleton_ofFormalSum_ofFormalSum
    firstCoefficient
    first
    middle
    right

/-- Composition-associativity aggregate: formal-sum representative associativity. -/
theorem TraceCorQQuotient.comp_associativity_ofFormalSum
    (left middle right : TraceCorQFormalSum) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.ofFormalSum left)
        (TraceCorQQuotient.ofFormalSum middle))
      (TraceCorQQuotient.ofFormalSum right) =
      TraceCorQQuotient.comp
        (TraceCorQQuotient.ofFormalSum left)
        (TraceCorQQuotient.comp
          (TraceCorQQuotient.ofFormalSum middle)
          (TraceCorQQuotient.ofFormalSum right)) :=
  TraceCorQQuotient.comp_assoc_ofFormalSum
    left
    middle
    right

/-- Composition-associativity aggregate: quotient composition is associative. -/
theorem TraceCorQQuotient.comp_associativity_comp_assoc
    (left middle right : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp left middle)
      right =
      TraceCorQQuotient.comp
        left
        (TraceCorQQuotient.comp middle right) :=
  TraceCorQQuotient.comp_assoc
    left
    middle
    right

/-- Composition-associativity aggregate: fully left-associated fourfold composites normalize. -/
theorem TraceCorQQuotient.comp_associativity_four_left
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.comp first second)
        third)
      fourth =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  TraceCorQQuotient.comp_assoc_four_left
    first
    second
    third
    fourth

/-- Composition-associativity aggregate: binary-split fourfold composites normalize. -/
theorem TraceCorQQuotient.comp_associativity_four_binary
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      (TraceCorQQuotient.comp first second)
      (TraceCorQQuotient.comp third fourth) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  TraceCorQQuotient.comp_assoc_four_binary
    first
    second
    third
    fourth

/-- Composition-associativity aggregate: right-tail-left-associated fourfold composites normalize. -/
theorem TraceCorQQuotient.comp_associativity_four_middle_right
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.comp
      first
      (TraceCorQQuotient.comp
        (TraceCorQQuotient.comp second third)
        fourth) =
      TraceCorQQuotient.comp
        first
        (TraceCorQQuotient.comp
          second
          (TraceCorQQuotient.comp third fourth)) :=
  TraceCorQQuotient.comp_assoc_four_middle_right
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary

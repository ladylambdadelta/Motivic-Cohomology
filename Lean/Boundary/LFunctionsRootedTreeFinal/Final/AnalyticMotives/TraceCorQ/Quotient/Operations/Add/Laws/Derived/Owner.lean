import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Add.Laws.Full.Owner

/-!
# Derived additive laws for quotient trace correspondences

This aggregate owns additive laws downstream from the base quotient additive
unit, associativity, and commutativity theorems.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived additive-law aggregate: zero is a left additive identity. -/
theorem TraceCorQQuotient.add_lawsDerived_zero_add
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      TraceCorQQuotient.zero
      candidateClass =
      candidateClass :=
  TraceCorQQuotient.zero_add candidateClass

/-- Derived additive-law aggregate: zero is a right additive identity. -/
theorem TraceCorQQuotient.add_lawsDerived_add_zero
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.add
      candidateClass
      TraceCorQQuotient.zero =
      candidateClass :=
  TraceCorQQuotient.add_zero candidateClass

/-- Derived additive-law aggregate: quotient addition is associative. -/
theorem TraceCorQQuotient.add_lawsDerived_add_assoc
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      third =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third) :=
  TraceCorQQuotient.add_assoc first second third

/-- Derived additive-law aggregate: quotient addition is commutative. -/
theorem TraceCorQQuotient.add_lawsDerived_add_comm
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.add left right =
      TraceCorQQuotient.add right left :=
  TraceCorQQuotient.add_comm left right

/-- Derived additive-law aggregate: binary four-summand sums normalize to the right. -/
theorem TraceCorQQuotient.add_lawsDerived_add_assoc_four_binary
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      (TraceCorQQuotient.add third fourth) =
      TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add
          second
          (TraceCorQQuotient.add third fourth)) :=
  TraceCorQQuotient.add_assoc_four_binary
    first
    second
    third
    fourth

/-- Derived additive-law aggregate: four-summand middle swapping is available. -/
theorem TraceCorQQuotient.add_lawsDerived_add_add_add_comm
    (first second third fourth : TraceCorQQuotient) :
    TraceCorQQuotient.add
      (TraceCorQQuotient.add first second)
      (TraceCorQQuotient.add third fourth) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.add first third)
        (TraceCorQQuotient.add second fourth) :=
  TraceCorQQuotient.add_add_add_comm
    first
    second
    third
    fourth

end AnalyticMotives
end LFunctions
end Boundary

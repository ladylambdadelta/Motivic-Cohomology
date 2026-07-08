import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.ZeroCoefficient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.CoefficientAdditivity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.NegCoefficient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Quotient.Operations.Smul.Laws.SubCoefficient.Owner

/-!
# Derived scalar laws for quotient trace correspondences

This aggregate owns scalar laws downstream from the base quotient scalar
actions, binary distribution theorem, zero-coefficient normalization, and
scalar-coefficient additivity, negation, and subtraction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived scalar-law aggregate: scaling zero gives zero. -/
theorem TraceCorQQuotient.smul_lawsDerived_smul_zero
    (coefficient : Rat) :
    TraceCorQQuotient.smul
      coefficient
      TraceCorQQuotient.zero =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.smul_zero coefficient

/-- Derived scalar-law aggregate: scalar multiplication distributes over addition. -/
theorem TraceCorQQuotient.smul_lawsDerived_smul_add
    (coefficient : Rat)
    (left right : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add left right) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient left)
        (TraceCorQQuotient.smul coefficient right) :=
  TraceCorQQuotient.smul_add coefficient left right

/-- Derived scalar-law aggregate: one is the identity scalar. -/
theorem TraceCorQQuotient.smul_lawsDerived_one_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 1 candidateClass =
      candidateClass :=
  TraceCorQQuotient.one_smul candidateClass

/-- Derived scalar-law aggregate: scalar composition multiplies coefficients. -/
theorem TraceCorQQuotient.smul_lawsDerived_smul_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      leftCoefficient
      (TraceCorQQuotient.smul rightCoefficient candidateClass) =
      TraceCorQQuotient.smul
        (leftCoefficient * rightCoefficient)
        candidateClass :=
  TraceCorQQuotient.smul_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- Derived scalar-law aggregate: scaling by zero gives the zero quotient class. -/
theorem TraceCorQQuotient.smul_lawsDerived_zero_smul
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul 0 candidateClass =
      TraceCorQQuotient.zero :=
  TraceCorQQuotient.zero_smul candidateClass

/-- Derived scalar-law aggregate: scalar multiplication is additive in the coefficient. -/
theorem TraceCorQQuotient.smul_lawsDerived_add_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (leftCoefficient + rightCoefficient)
      candidateClass =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul leftCoefficient candidateClass)
        (TraceCorQQuotient.smul rightCoefficient candidateClass) :=
  TraceCorQQuotient.add_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- Derived scalar-law aggregate: negative scalar coefficients negate scaled classes. -/
theorem TraceCorQQuotient.smul_lawsDerived_neg_smul
    (coefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (-coefficient)
      candidateClass =
      TraceCorQQuotient.neg
        (TraceCorQQuotient.smul coefficient candidateClass) :=
  TraceCorQQuotient.neg_smul coefficient candidateClass

/-- Derived scalar-law aggregate: scalar multiplication is subtractive in the coefficient. -/
theorem TraceCorQQuotient.smul_lawsDerived_sub_smul
    (leftCoefficient rightCoefficient : Rat)
    (candidateClass : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      (leftCoefficient - rightCoefficient)
      candidateClass =
      TraceCorQQuotient.sub
        (TraceCorQQuotient.smul leftCoefficient candidateClass)
        (TraceCorQQuotient.smul rightCoefficient candidateClass) :=
  TraceCorQQuotient.sub_smul
    leftCoefficient
    rightCoefficient
    candidateClass

/-- Derived scalar-law aggregate: scalar multiplication distributes over left-associated triples. -/
theorem TraceCorQQuotient.smul_lawsDerived_smul_add_three_left
    (coefficient : Rat)
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        (TraceCorQQuotient.add first second)
        third) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.smul coefficient third)) :=
  TraceCorQQuotient.smul_add_three_left
    coefficient
    first
    second
    third

/-- Derived scalar-law aggregate: scalar multiplication distributes over right-associated triples. -/
theorem TraceCorQQuotient.smul_lawsDerived_smul_add_three_right
    (coefficient : Rat)
    (first second third : TraceCorQQuotient) :
    TraceCorQQuotient.smul
      coefficient
      (TraceCorQQuotient.add
        first
        (TraceCorQQuotient.add second third)) =
      TraceCorQQuotient.add
        (TraceCorQQuotient.smul coefficient first)
        (TraceCorQQuotient.add
          (TraceCorQQuotient.smul coefficient second)
          (TraceCorQQuotient.smul coefficient third)) :=
  TraceCorQQuotient.smul_add_three_right
    coefficient
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary

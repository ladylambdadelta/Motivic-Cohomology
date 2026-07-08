import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.Distribution.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.ZeroCoefficient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.CoefficientAdditivity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.NegCoefficient.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceCorQ.Category.Homs.Smul.Laws.SubCoefficient.Owner

/-!
# Derived scalar laws for typed trace-correspondence homs

This aggregate owns scalar laws downstream from the base typed scalar action
and binary distribution theorem, including zero-coefficient normalization and
scalar-coefficient additivity, negation, and subtraction.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Derived typed-hom scalar aggregate: scaling zero gives zero. -/
theorem TraceCorQHom.smul_lawsDerived_smul_zero
    (source target : TraceCorQObject)
    (coefficient : Rat) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.zero source target) =
      TraceCorQHom.zero source target :=
  TraceCorQHom.smul_zero
    source
    target
    coefficient

/-- Derived typed-hom scalar aggregate: zero scalar gives zero. -/
theorem TraceCorQHom.smul_lawsDerived_zero_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul 0 hom =
      TraceCorQHom.zero source target :=
  TraceCorQHom.zero_smul
    hom

/-- Derived typed-hom scalar aggregate: scalar multiplication distributes over addition. -/
theorem TraceCorQHom.smul_lawsDerived_smul_add
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (left right : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add left right) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient left)
        (TraceCorQHom.smul coefficient right) :=
  TraceCorQHom.smul_add
    coefficient
    left
    right

/-- Derived typed-hom scalar aggregate: one is the identity scalar. -/
theorem TraceCorQHom.smul_lawsDerived_one_smul
    {source target : TraceCorQObject}
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul 1 hom =
      hom :=
  TraceCorQHom.one_smul
    hom

/-- Derived typed-hom scalar aggregate: successive scalars multiply. -/
theorem TraceCorQHom.smul_lawsDerived_smul_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      leftCoefficient
      (TraceCorQHom.smul rightCoefficient hom) =
      TraceCorQHom.smul
        (leftCoefficient * rightCoefficient)
        hom :=
  TraceCorQHom.smul_smul
    leftCoefficient
    rightCoefficient
    hom

/-- Derived typed-hom scalar aggregate: scalar multiplication commutes with negation. -/
theorem TraceCorQHom.smul_lawsDerived_smul_neg
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul coefficient (TraceCorQHom.neg hom) =
      TraceCorQHom.neg (TraceCorQHom.smul coefficient hom) :=
  TraceCorQHom.smul_neg
    coefficient
    hom

/-- Derived typed-hom scalar aggregate: scalar multiplication is additive in the coefficient. -/
theorem TraceCorQHom.smul_lawsDerived_add_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (leftCoefficient + rightCoefficient)
      hom =
      TraceCorQHom.add
        (TraceCorQHom.smul leftCoefficient hom)
        (TraceCorQHom.smul rightCoefficient hom) :=
  TraceCorQHom.add_smul
    leftCoefficient
    rightCoefficient
    hom

/-- Derived typed-hom scalar aggregate: negating the scalar negates the scaled hom. -/
theorem TraceCorQHom.smul_lawsDerived_neg_smul
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (-coefficient)
      hom =
      TraceCorQHom.neg
        (TraceCorQHom.smul coefficient hom) :=
  TraceCorQHom.neg_smul
    coefficient
    hom

/-- Derived typed-hom scalar aggregate: scalar multiplication is subtractive in the coefficient. -/
theorem TraceCorQHom.smul_lawsDerived_sub_smul
    {source target : TraceCorQObject}
    (leftCoefficient rightCoefficient : Rat)
    (hom : TraceCorQHom source target) :
    TraceCorQHom.smul
      (leftCoefficient - rightCoefficient)
      hom =
      TraceCorQHom.sub
        (TraceCorQHom.smul leftCoefficient hom)
        (TraceCorQHom.smul rightCoefficient hom) :=
  TraceCorQHom.sub_smul
    leftCoefficient
    rightCoefficient
    hom

/-- Derived typed-hom scalar aggregate: distribute over left-associated triples. -/
theorem TraceCorQHom.smul_lawsDerived_smul_add_three_left
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        (TraceCorQHom.add first second)
        third) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.smul coefficient third)) :=
  TraceCorQHom.smul_add_three_left
    coefficient
    first
    second
    third

/-- Derived typed-hom scalar aggregate: distribute over right-associated triples. -/
theorem TraceCorQHom.smul_lawsDerived_smul_add_three_right
    {source target : TraceCorQObject}
    (coefficient : Rat)
    (first second third : TraceCorQHom source target) :
    TraceCorQHom.smul
      coefficient
      (TraceCorQHom.add
        first
        (TraceCorQHom.add second third)) =
      TraceCorQHom.add
        (TraceCorQHom.smul coefficient first)
        (TraceCorQHom.add
          (TraceCorQHom.smul coefficient second)
          (TraceCorQHom.smul coefficient third)) :=
  TraceCorQHom.smul_add_three_right
    coefficient
    first
    second
    third

end AnalyticMotives
end LFunctions
end Boundary

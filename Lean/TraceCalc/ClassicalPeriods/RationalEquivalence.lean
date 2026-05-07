import TraceCalc.ClassicalPeriods.AlgebraicCycles

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure RationalFunctionDivisor (X : SchemeOverQ) where
  support : ClosedIntegralSubscheme X
  divisor : AlgebraicCycle X
  comes_from_rational_function : Prop

inductive RationalEquivalence (X : SchemeOverQ) : AlgebraicCycle X → AlgebraicCycle X → Prop
  | refl (a : AlgebraicCycle X) : RationalEquivalence X a a
  | symm {a b : AlgebraicCycle X} : RationalEquivalence X a b → RationalEquivalence X b a
  | trans {a b c : AlgebraicCycle X} :
      RationalEquivalence X a b → RationalEquivalence X b c → RationalEquivalence X a c
  | add_left {a b c : AlgebraicCycle X} :
      RationalEquivalence X a b → RationalEquivalence X (a + c) (b + c)
  | principal (D : RationalFunctionDivisor X) :
      D.comes_from_rational_function → RationalEquivalence X D.divisor 0

namespace RationalEquivalence

variable {X : SchemeOverQ}

theorem add_right {a b c : AlgebraicCycle X}
    (h : RationalEquivalence X a b) : RationalEquivalence X (c + a) (c + b) := by
  rw [add_comm c a, add_comm c b]
  exact add_left h

theorem add {a b c d : AlgebraicCycle X}
    (h₁ : RationalEquivalence X a b) (h₂ : RationalEquivalence X c d) :
    RationalEquivalence X (a + c) (b + d) := by
  exact trans (add_left h₁) (add_right h₂)

end RationalEquivalence

abbrev ChowGroup (X : SchemeOverQ) := Quot (RationalEquivalence X)

def cycleClass {X : SchemeOverQ} (a : AlgebraicCycle X) : ChowGroup X :=
  Quot.mk (RationalEquivalence X) a

end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc

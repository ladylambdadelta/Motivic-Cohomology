import TraceCalc.ClassicalPeriods.AGPredicates

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

abbrev CycleGenerator (X : SchemeOverQ) := ClosedIntegralSubscheme X

abbrev AlgebraicCycle (X : SchemeOverQ) := CycleGenerator X →₀ ℤ

namespace AlgebraicCycle

variable {X : SchemeOverQ}

def ofGenerator (Z : CycleGenerator X) : AlgebraicCycle X :=
  Finsupp.single Z 1

def zero (X : SchemeOverQ) : AlgebraicCycle X :=
  0

def add (a b : AlgebraicCycle X) : AlgebraicCycle X :=
  a + b

def neg (a : AlgebraicCycle X) : AlgebraicCycle X :=
  -a

def smul (n : ℤ) (a : AlgebraicCycle X) : AlgebraicCycle X :=
  n • a

@[simp]
theorem add_assoc (a b c : AlgebraicCycle X) : add (add a b) c = add a (add b c) := by
  exact AddSemigroup.add_assoc a b c

@[simp]
theorem zero_add (a : AlgebraicCycle X) : add (zero X) a = a := by
  simp [add, zero]

@[simp]
theorem add_zero (a : AlgebraicCycle X) : add a (zero X) = a := by
  simp [add, zero]

@[simp]
theorem add_comm (a b : AlgebraicCycle X) : add a b = add b a := by
  exact AddCommMagma.add_comm a b

end AlgebraicCycle
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc

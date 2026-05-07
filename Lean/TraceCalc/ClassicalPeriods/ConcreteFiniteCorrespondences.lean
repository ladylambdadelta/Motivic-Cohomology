import TraceCalc.ClassicalPeriods.CycleOperationLaws

noncomputable section

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

namespace SchemeOverQ

structure FiniteCorrespondenceGenerator (X Y : SchemeOverQ) where
  support : ClosedIntegralSubscheme (prod X Y)
  finiteOverSource : support.IsFiniteOver

structure FiniteCorrespondenceTerm (X Y : SchemeOverQ) where
  generator : FiniteCorrespondenceGenerator X Y
  multiplicity : ℤ

structure FiniteCorrespondenceCycle (X Y : SchemeOverQ) where
  terms : List (FiniteCorrespondenceTerm X Y)

namespace FiniteCorrespondenceCycle

def zero (X Y : SchemeOverQ) : FiniteCorrespondenceCycle X Y where
  terms := []

def ofGenerator {X Y : SchemeOverQ} (Z : FiniteCorrespondenceGenerator X Y) :
    FiniteCorrespondenceCycle X Y where
  terms := [{ generator := Z, multiplicity := 1 }]

def add {X Y : SchemeOverQ} (a b : FiniteCorrespondenceCycle X Y) :
    FiniteCorrespondenceCycle X Y where
  terms := a.terms ++ b.terms

@[simp]
theorem add_assoc {X Y : SchemeOverQ} (a b c : FiniteCorrespondenceCycle X Y) :
    add (add a b) c = add a (add b c) := by
  cases a
  cases b
  cases c
  simp [add, List.append_assoc]

@[simp]
theorem zero_add {X Y : SchemeOverQ} (a : FiniteCorrespondenceCycle X Y) :
    add (zero X Y) a = a := by
  cases a
  simp [add, zero]

@[simp]
theorem add_zero {X Y : SchemeOverQ} (a : FiniteCorrespondenceCycle X Y) :
    add a (zero X Y) = a := by
  cases a
  simp [add, zero]

end FiniteCorrespondenceCycle

structure ConcreteFiniteCorrespondence (X Y : SchemeOverQ) where
  cycle : FiniteCorrespondenceCycle X Y

namespace ConcreteFiniteCorrespondence

def zero (X Y : SchemeOverQ) : ConcreteFiniteCorrespondence X Y where
  cycle := FiniteCorrespondenceCycle.zero X Y

def add {X Y : SchemeOverQ} (a b : ConcreteFiniteCorrespondence X Y) :
    ConcreteFiniteCorrespondence X Y where
  cycle := FiniteCorrespondenceCycle.add a.cycle b.cycle

@[ext]
theorem ext {X Y : SchemeOverQ} {a b : ConcreteFiniteCorrespondence X Y}
    (h : a.cycle = b.cycle) : a = b := by
  cases a
  cases b
  simp only at h
  subst h
  rfl

end ConcreteFiniteCorrespondence
end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc

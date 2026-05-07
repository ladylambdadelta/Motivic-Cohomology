import TraceCalc.ClassicalPeriods.AlgebraicCycleCategory

universe u v w x y z

namespace TraceCalc
namespace ClassicalPeriods
namespace Package3B0Cycles

open AlgebraicCycleCategory
open AlgebraicCycleLaws

/-- Left identity for composition of algebraic cycles (witness equivalence). -/
theorem left_identity_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : Cycle X Y) :
    CycleEquiv (compose (identity X) α) α :=
  left_identity α

/-- Right identity for composition of algebraic cycles (witness equivalence). -/
theorem right_identity_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {X Y : GeometricPeriodObject ctx}
    (α : Cycle X Y) :
    CycleEquiv (compose α (identity Y)) α :=
  right_identity α

/-- Associativity for composition of algebraic cycles (witness equivalence). -/
theorem associativity_cycles
    {ctx : ClassicalComparisonContext.{u, v}}
    {W X Y Z : GeometricPeriodObject ctx}
    (α : Cycle W X)
    (β : Cycle X Y)
    (γ : Cycle Y Z) :
    CycleEquiv (compose (compose α β) γ) (compose α (compose β γ)) :=
  associativity α β γ

end Package3B0Cycles

end ClassicalPeriods
end TraceCalc

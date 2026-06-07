import Boundary.Cycles.Support

/-!
# Cycle groups

This file packages finite formal sums of cycle-support atoms.

The intended mathematical model is the free abelian group on integral closed
subschemes, following the standard cycle formalism in Fulton,
*Intersection Theory*, §1.3.
-/

universe u

namespace Boundary
namespace Cycles

noncomputable section

/-- The integral cycle group on a scheme: finite formal integer sums of support atoms. -/
abbrev CycleGroup (X : Scheme.{u}) : Type (u + 1) :=
  CycleSupportAtom X →₀ ℤ

/-- The rational cycle group on a scheme. -/
abbrev CycleGroupQ (X : Scheme.{u}) : Type (u + 1) :=
  CycleSupportAtom X →₀ ℚ

namespace CycleGroup

variable {X : Scheme.{u}}

/-- Zero cycle. -/
abbrev zero : CycleGroup X :=
  0

/-- Add two cycles. -/
abbrev add (c d : CycleGroup X) : CycleGroup X :=
  c + d

/-- The singleton cycle supported on one atom. -/
abbrev singleton (Z : CycleSupportAtom X) (n : ℤ) : CycleGroup X :=
  Finsupp.single Z n

end CycleGroup

namespace CycleGroupQ

variable {X : Scheme.{u}}

/-- Zero rational cycle. -/
abbrev zero : CycleGroupQ X :=
  0

/-- Add two rational cycles. -/
abbrev add (c d : CycleGroupQ X) : CycleGroupQ X :=
  c + d

/-- The singleton rational cycle supported on one atom. -/
abbrev singleton (Z : CycleSupportAtom X) (q : ℚ) : CycleGroupQ X :=
  Finsupp.single Z q

end CycleGroupQ

end Cycles
end Boundary

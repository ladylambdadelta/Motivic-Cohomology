import Boundary.Cycles.Support
import Geometry.Cycles.Basic

/-!
# Finite sums of cycle supports

This file packages finite sums of cycle-support atoms as actual algebraic cycles.
The construction is deliberately small: it is the finite-support layer that sits
between the support atom API and later rational-equivalence infrastructure.

This is the standard free-abelian-group layer on integral closed subschemes;
cf. Fulton, *Intersection Theory*, §1.3.
-/

universe u

open AlgebraicGeometry

namespace Boundary
namespace Cycles

noncomputable section

/-- Convert a finite cycle support into an algebraic cycle by summing the
corresponding integral closed subschemes with coefficient `1`. -/
def CycleSupport.toAlgCycle {X : Scheme.{u}} (S : CycleSupport X) : AlgCycle X :=
  S.sum fun Z => AlgCycle.ofSubscheme Z

@[simp] theorem CycleSupport.toAlgCycle_empty {X : Scheme.{u}} :
    (CycleSupport.empty : CycleSupport X).toAlgCycle = 0 := by
  rfl

@[simp] theorem CycleSupport.toAlgCycle_singleton {X : Scheme.{u}}
    (Z : CycleSupportAtom X) :
    (CycleSupport.singleton Z).toAlgCycle = AlgCycle.ofSubscheme Z := by
  unfold CycleSupport.toAlgCycle CycleSupport.singleton
  rw [Finset.sum_singleton]
  rfl

/-- Adding a new support atom to a finite support adds the corresponding
algebraic cycle summand. -/
theorem CycleSupport.toAlgCycle_insert {X : Scheme.{u}}
    {Z : CycleSupportAtom X} {S : CycleSupport X} (h : Z ∉ S) :
    (insert Z S).toAlgCycle = AlgCycle.ofSubscheme Z + S.toAlgCycle := by
  unfold CycleSupport.toAlgCycle
  rw [Finset.sum_insert h]
  rfl

end

end Cycles
end Boundary

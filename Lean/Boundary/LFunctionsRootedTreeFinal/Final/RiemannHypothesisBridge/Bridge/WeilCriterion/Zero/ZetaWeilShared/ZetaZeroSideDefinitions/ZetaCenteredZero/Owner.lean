import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Owner

/-!
# Boundary centered zeta zeros

This file isolates the actual zero locus of the centered completed zeta
function on the critical line and records the symmetry that is already proved
for the centered normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A centered zeta zero is a complex number annihilating the centered completed
zeta function. -/
def CenteredZetaZero : Type := {s : ℂ // centeredCompletedRiemannZeta s = 0}

namespace CenteredZetaZero

/-- The underlying complex coordinate of a centered zeta zero. -/
def coordinate (z : CenteredZetaZero) : ℂ := z.1

instance : Coe CenteredZetaZero ℂ := ⟨coordinate⟩

@[ext]
theorem ext {z w : CenteredZetaZero} (h : (z : ℂ) = w) : z = w := by
  cases z
  cases w
  cases h
  rfl

/-- Reflection sends a centered zero to a centered zero. -/
def reflect (z : CenteredZetaZero) : CenteredZetaZero :=
  ⟨-z, by
    exact (centeredCompletedRiemannZeta_neg z).trans z.2⟩

/-- The reflection of a centered zero has coordinate `-z`. -/
theorem reflect_coordinate (z : CenteredZetaZero) :
    (reflect z : ℂ) = -z := rfl

/-- Reflection is an involution on centered zeta zeros. -/
theorem reflect_reflect (z : CenteredZetaZero) : reflect (reflect z) = z := by
  ext
  exact neg_neg (z : ℂ)

/-- The centered zero locus is stable under negation. -/
theorem neg_mem_iff (z : ℂ) :
    centeredCompletedRiemannZeta z = 0 ↔ centeredCompletedRiemannZeta (-z) = 0 := by
  constructor
  · intro hz
    calc
      centeredCompletedRiemannZeta (-z) = centeredCompletedRiemannZeta z := by
        exact centeredCompletedRiemannZeta_neg z
      _ = 0 := hz
  · intro hz
    calc
      centeredCompletedRiemannZeta z = centeredCompletedRiemannZeta (-z) := by
        exact (centeredCompletedRiemannZeta_neg z).symm
      _ = 0 := hz

end CenteredZetaZero

end
end LFunctions
end Boundary

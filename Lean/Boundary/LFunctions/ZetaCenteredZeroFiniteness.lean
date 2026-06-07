import Boundary.LFunctions.ZetaCenteredZeroOrbit

/-!
# Boundary centered zeta zero finiteness

This file exports the finite reflection-orbit fact for centered zeta zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The reflection orbit of a centered zeta zero is finite. -/
theorem orbit_finite' (z : CenteredZetaZero) : ({x : ℂ | x ∈ orbit z}.Finite) := by
  exact orbit_finite z

/-- The centered zero orbit is finite as a set. -/
theorem orbit_finite (z : CenteredZetaZero) : ({x : ℂ | x ∈ orbit z}.Finite) := by
  classical
  exact Set.Finite.ofFinset (orbit z) (by
    intro x
    constructor
    · intro hx
      exact hx
    · intro hx
      exact hx)

end CenteredZetaZero

end
end LFunctions
end Boundary

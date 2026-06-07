import Boundary.LFunctions.ZetaZeroOrbitIsolation

/-!
# Boundary centered zeta zero local finiteness

This file exports the finite orbit fact for the centered zero locus.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The centered zero orbit is finite inside the centered zero set. -/
theorem centeredZetaZeros_locallyFinite (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z}.Finite := by
  exact orbit_finite z

/-- The centered zero set is locally finite on each reflection orbit. -/
theorem centeredZetaZeros_localFiniteness (z : CenteredZetaZero) :
    {x : ℂ | x ∈ orbit z}.Finite := by
  exact centeredZetaZeros_locallyFinite z

end CenteredZetaZero

end
end LFunctions
end Boundary

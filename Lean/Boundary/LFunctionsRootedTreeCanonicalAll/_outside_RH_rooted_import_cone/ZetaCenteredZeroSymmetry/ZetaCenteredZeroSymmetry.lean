import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.ZetaCenteredZeroFiniteness.ZetaCenteredZeroFiniteness

/-!
# Boundary centered zeta zero symmetry

This file exports the reflection symmetry of centered zeta zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- Reflection preserves the centered zero locus. -/
theorem reflect_mem (z : CenteredZetaZero) : (reflect z : ℂ) ∈ orbit z := by
  change (-z : ℂ) ∈ orbit z
  exact mem_orbit_right z

end CenteredZetaZero

end
end LFunctions
end Boundary

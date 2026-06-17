import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroOrbit.ZetaCenteredZeroOrbit

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

end CenteredZetaZero

end
end LFunctions
end Boundary

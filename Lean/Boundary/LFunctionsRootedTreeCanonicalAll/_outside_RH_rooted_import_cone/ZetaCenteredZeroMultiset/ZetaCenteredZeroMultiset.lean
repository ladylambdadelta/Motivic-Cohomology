import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroOrbit.ZetaCenteredZeroOrbit

/-!
# Boundary centered zeta zero multiset

This file packages the finite reflection orbit of a centered zeta zero as a
multiset.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace CenteredZetaZero

/-- The reflection orbit of a centered zeta zero as a multiset. -/
def orbitMultiset (z : CenteredZetaZero) : Multiset ℂ := {(z : ℂ), (-z : ℂ)}

theorem mem_orbitMultiset_left (z : CenteredZetaZero) : (z : ℂ) ∈ orbitMultiset z := by
  exact Multiset.mem_cons_self (z : ℂ) ({(-z : ℂ)} : Multiset ℂ)

theorem mem_orbitMultiset_right (z : CenteredZetaZero) : (-z : ℂ) ∈ orbitMultiset z := by
  have hmem_singleton : (-z : ℂ) ∈ ({(-z : ℂ)} : Multiset ℂ) :=
    Multiset.mem_singleton_self (-z : ℂ)
  exact Multiset.mem_cons_of_mem hmem_singleton

/-- The orbit multiset is stable under reflection. -/
theorem orbitMultiset_neg (z : CenteredZetaZero) :
    orbitMultiset z = {(-z : ℂ), (z : ℂ)} := by
  exact Multiset.cons_swap (z : ℂ) (-z : ℂ) 0

/-- The orbit multiset is the reflection pair. -/
theorem orbitMultiset_eq (z : CenteredZetaZero) :
    orbitMultiset z = {(z : ℂ), (-z : ℂ)} := by
  rfl

end CenteredZetaZero

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeCanonicalAll._outside_RH_rooted_import_cone.CohomologicalEulerFactor.TraceExpansion.TraceExpansionCore.TraceExpansionCore

open scoped BigOperators PowerSeries

/-
This file groups the finite geometric inverse identity layer.
-/

namespace Boundary
namespace TraceExpansion

theorem one_add_mul_finiteGeomInverse_geometric_identity
    {K : Type*} [Field K] (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g N =
      1 - (-g) ^ (N + 1) := by
  exact one_add_mul_finiteGeomInverse_geometric_identity_core (K := K) (g := g) (N := N)

theorem one_add_mul_finiteGeomInverse_zero
    {K : Type*} [Field K] (g : K⟦X⟧) :
    (1 + g) * finiteGeomInverse (K := K) g 0 = 1 - (-g) ^ 1 := by
  exact one_add_mul_finiteGeomInverse_zero_core (K := K) g

theorem one_add_mul_finiteGeomInverse_succ
    {K : Type*} [Field K] (g : K⟦X⟧) (N : ℕ) :
    (1 + g) * finiteGeomInverse (K := K) g (N + 1) =
      1 - (-g) ^ (N + 2) := by
  exact one_add_mul_finiteGeomInverse_succ_core (K := K) g N

theorem finiteGeomInverse_zero
    {K : Type*} [Field K] (g : K⟦X⟧) :
    finiteGeomInverse (K := K) g 0 = 1 := by
  exact finiteGeomInverse_zero_core (K := K) g

theorem finiteGeomInverse_succ
    {K : Type*} [Field K] (g : K⟦X⟧) (N : ℕ) :
    finiteGeomInverse (K := K) g (N + 1) =
      finiteGeomInverse (K := K) g N + (-g) ^ (N + 1) := by
  exact finiteGeomInverse_succ_core (K := K) g N

theorem coeff_mul_pow_succ_eq_zero_from_X_factor
    {K : Type*} [Field K] {g q h : K⟦X⟧} {N d : ℕ}
    (hgx : g = PowerSeries.X * h) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  exact coeff_mul_pow_succ_eq_zero_from_X_factor_core (K := K) (g := g) (q := q) (h := h)
    (N := N) (d := d) hgx hd

theorem coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero
    {K : Type*} [Field K] {g q : K⟦X⟧} {N d : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * g ^ (N + 1)) = 0 := by
  exact coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero_core (K := K) (g := g) (q := q)
    (N := N) (d := d) hg hd

end TraceExpansion
end Boundary

import Boundary.LFunctions.TraceExpansionCore

open scoped BigOperators PowerSeries

/-
This file groups the coefficient extraction and vanishing lemmas.
-/

namespace Boundary
namespace TraceExpansion

theorem coeff_mul_finiteGeomInverse_nonzero_constant_term
    {K : Type*} [Field K] {g : K⟦X⟧} (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_const (K := K) (g := g) hg

theorem coeff_mul_finiteGeomInverse_nonzero_constant_term_proof
    {K : Type*} [Field K] {g : K⟦X⟧} (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_const (K := K) (g := g) hg

end TraceExpansion
end Boundary

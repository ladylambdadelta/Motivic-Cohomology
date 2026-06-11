import Boundary.LFunctions.TraceExpansionCore

open scoped BigOperators PowerSeries

/-
This file groups the coefficient transport layer for the finite inverse.
-/

namespace Boundary
namespace TraceExpansion

theorem coeff_mul_finiteGeomInverse_geometric_inverse_nonzero_constant_term
    {K : Type*} [Field K] {g : K⟦X⟧} (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_const_core (K := K) (g := g) hg

theorem coeff_mul_finiteGeomInverse_geometric_inverse_left_step
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N * (1 + g) =
      q * (1 - (-g) ^ (N + 1)) := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_left_core (K := K) (g := g) (q := q)
    (N := N) hg

theorem coeff_mul_finiteGeomInverse_geometric_inverse_mul_inv
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ}
    (hconst : PowerSeries.constantCoeff K (1 + g) ≠ 0) :
    q * finiteGeomInverse (K := K) g N =
      (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_mul_core
    (K := K) (g := g) (q := q) (N := N) hconst

theorem coeff_mul_finiteGeomInverse_geometric_inverse_mul_left
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ}
    (hleft : q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1))) :
    (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ =
      q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_cancel_hleft_core
    (K := K) (g := g) (q := q) (N := N) hleft

theorem coeff_mul_finiteGeomInverse_geometric_inverse_commute
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ} :
    q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  exact coeff_mul_finiteGeomInverse_eq_coeff_inv_swap_core
    (K := K) (g := g) (q := q) (N := N)

theorem coeff_mul_finiteGeomInverse_geometric_inverse_transport_proof
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  have hconst :
      PowerSeries.constantCoeff K (1 + g) ≠ 0 := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_nonzero_constant_term
      (K := K) (g := g) hg
  have hleft :
      q * finiteGeomInverse (K := K) g N * (1 + g) =
        q * (1 - (-g) ^ (N + 1)) := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_left_step
      (K := K) (g := g) (q := q) (N := N) hg
  have hcancel1 :
      q * finiteGeomInverse (K := K) g N =
        (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_mul_inv
      (K := K) (g := g) (q := q) (N := N) hconst
  have hcancel2 :
      (q * finiteGeomInverse (K := K) g N * (1 + g)) * (1 + g)⁻¹ =
        q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_mul_left
      (K := K) (g := g) (q := q) (N := N) hleft
  have hswap :
      q * (1 - (-g) ^ (N + 1)) * (1 + g)⁻¹ =
        q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_commute
      (K := K) (g := g) (q := q) (N := N)
  exact hcancel1.trans (hcancel2.trans hswap)

theorem coeff_mul_finiteGeomInverse_geometric_inverse_transport
    {K : Type*} [Field K] {g q : K⟦X⟧} {N : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) :
    q * finiteGeomInverse (K := K) g N =
      q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
  exact coeff_mul_finiteGeomInverse_geometric_inverse_transport_proof
    (K := K) (g := g) (q := q) (N := N) hg

theorem coeff_mul_right_sub_coeff_eq_map_sub
    {K : Type*} [Field K] {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) -
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) := by
  exact coeff_mul_right_sub_coeff_eq_map_sub_core (K := K) (g := g) (q := q) (N := N)
    (d := d) hzero

theorem coeff_mul_right_sub_coeff_eq_of_hzero
    {K : Type*} [Field K] {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq_of_hzero_core (K := K) (g := g) (q := q)
    (N := N) (d := d) hzero

theorem coeff_mul_right_sub_coeff_eq_zero_sub
    {K : Type*} [Field K] {g q : K⟦X⟧} {N d : ℕ}
    (hzero : PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0) :
    PowerSeries.coeff K d
        (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  exact coeff_mul_right_sub_coeff_eq_zero_sub_core (K := K) (g := g) (q := q)
    (N := N) (d := d) hzero

theorem constantCoeff_neg_eq_zero_of_constantCoeff_eq_zero
    {K : Type*} [Field K] {g : K⟦X⟧}
    (hg : PowerSeries.constantCoeff K g = 0) :
    PowerSeries.constantCoeff K (-g) = 0 := by
  have hneg :
      PowerSeries.constantCoeff K (-g) =
        -PowerSeries.constantCoeff K g := by
    exact map_neg (PowerSeries.constantCoeff K) g
  have hzeroArg : -PowerSeries.constantCoeff K g = -0 := by
    exact congrArg Neg.neg hg
  have hzero : (-0 : K) = 0 := by
    exact neg_zero
  exact hneg.trans (hzeroArg.trans hzero)

theorem coeff_mul_finiteGeomInverse_eq_coeff_mul_inv
    {K : Type*} [Field K] {g q : K⟦X⟧} {N d : ℕ}
    (hg : PowerSeries.constantCoeff K g = 0) (hd : d < N + 1) :
    PowerSeries.coeff K d (q * finiteGeomInverse (K := K) g N) =
      PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
  have htransport :
      q * finiteGeomInverse (K := K) g N =
        q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1)) := by
    exact coeff_mul_finiteGeomInverse_geometric_inverse_transport
      (K := K) (g := g) (q := q) (N := N) hg
  have hzero :
      PowerSeries.coeff K d (q * (1 + g)⁻¹ * (-g) ^ (N + 1)) = 0 := by
    exact coeff_mul_pow_succ_eq_zero_of_constantCoeff_eq_zero_core
      (K := K) (g := -g) (q := q * (1 + g)⁻¹) (N := N) (d := d)
      (constantCoeff_neg_eq_zero_of_constantCoeff_eq_zero (K := K) (g := g) hg) hd
  have hcoeffTransport :
      PowerSeries.coeff K d (q * finiteGeomInverse (K := K) g N) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) := by
    exact congrArg (PowerSeries.coeff K d) htransport
  have hcoeffCancel :
      PowerSeries.coeff K d (q * (1 + g)⁻¹ * (1 - (-g) ^ (N + 1))) =
        PowerSeries.coeff K d (q * (1 + g)⁻¹) := by
    exact coeff_mul_right_sub_coeff_eq_zero_sub
      (K := K) (g := g) (q := q) (N := N) (d := d) hzero
  exact hcoeffTransport.trans hcoeffCancel

end TraceExpansion
end Boundary

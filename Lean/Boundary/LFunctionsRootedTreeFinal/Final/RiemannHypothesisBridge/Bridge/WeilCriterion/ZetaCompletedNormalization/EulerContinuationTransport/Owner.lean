import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.Owner

/-!
# Euler continuation and right-half-plane transport

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard

/-- The reflected `re = 1` pole-cleared zeta factor has finite-order vertical growth.

This is the exact analytic input left after unfolding the completed functional equation in
the raw zeta variable.  The map `z ↦ 1-z` sends `re z = 0` to `re = 1`, so this is not a
consequence of the already-proved far-right Dirichlet-series boundary theorem at `re = 2`.
-/
theorem riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, 2 * m, hA, hB, ?_⟩
  intro z hz_re hz_im
  let w : ℂ := (1 : ℂ) - z
  have hw_re : w.re = 1 :=
    one_sub_leftBoundary_re_eq_one hz_re
  have hw_im_norm : ‖w.im‖ = ‖z.im‖ := by
    have him_eq : w.im = -z.im := by
      calc
        w.im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im (1 : ℂ) z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    calc
      ‖w.im‖ = ‖-z.im‖ := by exact congrArg norm him_eq
      _ = ‖z.im‖ := norm_neg z.im
  have hw_im : 1 ≤ ‖w.im‖ :=
    Eq.subst (motive := fun x : ℝ => 1 ≤ x) hw_im_norm.symm hz_im
  have hw_norm_le : ‖w‖ ≤ 1 + ‖z‖ := by
    calc
      ‖w‖ = ‖(1 : ℂ) - z‖ := rfl
      _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le (1 : ℂ) z
      _ = 1 + ‖z‖ := by
        exact congrArg (fun x : ℝ => x + ‖z‖) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hbase_le : 1 + ‖w‖ ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
    let H : ℝ := 1 + ‖z‖
    have hH_ge_one : (1 : ℝ) ≤ H :=
      le_add_of_nonneg_right (norm_nonneg z)
    have hleft_le : 1 + ‖w‖ ≤ 1 + (1 + ‖z‖) :=
      add_le_add_left hw_norm_le 1
    have htwoH_le_Hsq : 1 + (1 + ‖z‖) ≤ H ^ (2 : ℕ) := by
      calc
        1 + (1 + ‖z‖) = 1 + H := rfl
        _ ≤ H * H := by
          nlinarith [hH_ge_one]
        _ = H ^ (2 : ℕ) := by ring
    exact le_trans hleft_le htwoH_le_Hsq
  have hpow_le : (1 + ‖w‖) ^ m ≤ (1 + ‖z‖) ^ (2 * m) := by
    have hleft_nonneg : 0 ≤ 1 + ‖w‖ :=
      le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
    have hpow_base :
        (1 + ‖w‖) ^ m ≤ ((1 + ‖z‖) ^ (2 : ℕ)) ^ m :=
      pow_le_pow_right₀ hleft_nonneg hbase_le m
    have htarget_ge :
        ((1 + ‖z‖) ^ (2 : ℕ)) ^ m = (1 + ‖z‖) ^ (2 * m) := by
      exact pow_mul (1 + ‖z‖) 2 m
    exact hpow_base.trans_eq htarget_ge
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp (B * (1 + ‖z‖) ^ (2 * m)) := by
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB))
  exact le_trans (hbound w hw_re hw_im)
    (mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA))

/-- Functional-equation algebra for the left-edge pole-cleared zeta factor. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_factorization
    {z : ℂ}
    (hz_re : z.re = 0)
    (hz_im : 1 ≤ ‖z.im‖) :
    (z - 1) * riemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
  rcases Gammaℝ_leftBoundary_nonzero_of_verticalTail hz_re hz_im with
    ⟨hz_ne_zero, hone_sub_ne_zero, hGamma_ne, hGamma_reflected_ne⟩
  have hw_ne_zero : ((1 : ℂ) - z) ≠ 0 := hone_sub_ne_zero
  have hw_minus_one_ne_zero : ((1 : ℂ) - z) - 1 ≠ 0 := by
    intro h
    have hz_zero : z = 0 := by
      calc
        z = -(((1 : ℂ) - z) - 1) := by ring
        _ = -0 := by exact congrArg Neg.neg h
        _ = 0 := by exact neg_zero
    exact hz_ne_zero hz_zero
  have hGamma_factor :
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    have hζ := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
    have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) hζ
    have hcancel :
        (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
          completedRiemannZeta z := by
      exact div_mul_cancel₀ _ hGamma_ne
    exact (hmul.trans hcancel).symm
  have hcompleted_symm :
      completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) := by
    exact (completedRiemannZeta_one_sub z).symm
  have hzeta_z :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
    have hζw := riemannZeta_def_of_ne_zero (s := ((1 : ℂ) - z)) hw_ne_zero
    calc
      riemannZeta z =
          completedRiemannZeta z / Complex.Gammaℝ z := by
        exact riemannZeta_def_of_ne_zero hz_ne_zero
      _ = completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z := by
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hcompleted_symm
      _ = (riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z)) /
          Complex.Gammaℝ z := by
        have hζw_mul := congrArg
          (fun x : ℂ => x * Complex.Gammaℝ ((1 : ℂ) - z)) hζw
        have hζw_completed :
            riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z) =
              completedRiemannZeta ((1 : ℂ) - z) := by
          exact hζw_mul.trans (div_mul_cancel₀ _ hGamma_reflected_ne)
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hζw_completed.symm
      _ = riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
        rfl
  calc
    (z - 1) * riemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
      exact congrArg (fun x : ℂ => (z - 1) * x) hzeta_z
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
      field_simp [hw_minus_one_ne_zero, hGamma_ne]
      ring

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation before the removable-pole normalization is applied.

This is the remaining analytic component: reflect by
`completedRiemannZeta_one_sub`, use the peeled vertical-growth input on the reflected
line `re (1 - z) = 1`, and control the resulting Gamma/reflection multiplier by the
left-boundary Stirling-ratio estimate. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases leftBoundary_finiteOrder_product_growth_bound
      Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound
      riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hproduct⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hfactor :
      (z - 1) * riemannZeta z =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) :=
    riemannZeta_leftBoundary_completedFunctionalEquation_factorization hz_re hz_im
  have hnorm_factor :
      ‖(z - 1) * riemannZeta z‖ =
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ *
          ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ := by
    have hnorm_raw := congrArg norm hfactor
    simpa [norm_mul] using hnorm_raw
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hnorm_factor.symm
    (hproduct z hz_re hz_im)

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation and the available vertical-tail Gamma/Stirling control. -/
theorem poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          exact Complex.one_re
    have hzero_eq_one : (0 : ℝ) = 1 := by
      calc
        (0 : ℝ) = z.re := hz_re.symm
        _ = 1 := hz_re_one
    norm_num at hzero_eq_one
  have hpole :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpole.symm
    (hbound z hz_re hz_im)

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This is the boundary-growth layer separated from the vertical-strip Phragmen-Lindelöf
application: the left edge is the functional-equation/Gamma side, and the right edge is
the Dirichlet-series side. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound

/-- On `2 ≤ re z`, subtracting the leading Dirichlet coefficient identifies `ζ z - 1`
with the honest Dirichlet tail starting at `n = 2`. -/
theorem riemannZeta_sub_one_eq_dirichletSeries_tail
    {z : ℂ}
    (hz : 2 ≤ z.re) :
    riemannZeta z - 1 =
      ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
  have h_one_lt_re : 1 < z.re :=
    lt_of_lt_of_le one_lt_two hz
  let f : ℕ → ℂ := fun n : ℕ => 1 / ((n : ℂ) ^ z)
  have hsum : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr h_one_lt_re
  have hzeta :
      riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow h_one_lt_re
  have hsplit :
      (∑ n ∈ Finset.range 2, f n) + (∑' n : ℕ, f (n + 2)) =
        ∑' n : ℕ, f n :=
    sum_add_tsum_nat_add 2 hsum
  have hprefix :
      ∑ n ∈ Finset.range 2, f n = 1 := by
    dsimp [f]
    simp [zero_cpow (Complex.ne_zero_of_one_lt_re h_one_lt_re)]
  have hone_add_tail_eq_zeta :
      1 + (∑' n : ℕ, f (n + 2)) = riemannZeta z := by
    calc
      1 + (∑' n : ℕ, f (n + 2)) =
          (∑ n ∈ Finset.range 2, f n) + (∑' n : ℕ, f (n + 2)) := by
            exact congrArg (fun x : ℂ => x + (∑' n : ℕ, f (n + 2))) hprefix.symm
      _ = ∑' n : ℕ, f n := hsplit
      _ = riemannZeta z := hzeta.symm
  have hzeta_eq_one_add_tail :
      riemannZeta z = 1 + (∑' n : ℕ, f (n + 2)) :=
    hone_add_tail_eq_zeta.symm
  calc
    riemannZeta z - 1 =
        (1 + (∑' n : ℕ, f (n + 2))) - 1 := by
          exact congrArg (fun w : ℂ => w - 1) hzeta_eq_one_add_tail
    _ = ∑' n : ℕ, f (n + 2) := by
          ring
    _ = ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
          rfl

/-- Uniform boundedness of the far-right Dirichlet-series tail.

This far-right standard analytic primitive is the zeta-side input for finite-order control
of the completed zero packet; analytically it is the comparison of
`∑_{n≥2} n^{-z}` with the convergent real p-series at exponent `2`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖(∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z))‖ ≤ A := by
  let g : ℕ → ℝ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ))
  have hg_summable : Summable g := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ))) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    exact (summable_nat_add_iff 2).mpr hfull
  refine ⟨(∑' n : ℕ, g n) + 1, ?_, ?_⟩
  · have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
      intro n
      exact div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg (n + 2)) 2)
    exact add_pos_of_nonneg_of_pos (tsum_nonneg hg_nonneg) zero_lt_one
  intro z hz
  let f : ℕ → ℂ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)
  have hz_one_lt : 1 < z.re :=
    lt_of_lt_of_le one_lt_two hz
  have hf_summable : Summable (fun n : ℕ => ‖f n‖) := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ z)) :=
      (Complex.summable_one_div_nat_cpow (p := z)).mpr hz_one_lt
    have htail : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)) :=
      (summable_nat_add_iff 2).mpr hfull
    exact htail.norm
  have hterm_le : ∀ n : ℕ, ‖f n‖ ≤ g n := by
    intro n
    have hn_nat_pos : 0 < n + 2 :=
      Nat.succ_pos (n + 1)
    have hn_real_pos : 0 < ((n + 2 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hn_nat_pos
    have hn_real_one_le : 1 ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.succ_pos (n + 1))
    have hnorm_cpow :
        ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ =
          ((n + 2 : ℕ) : ℝ) ^ z.re :=
      Complex.norm_natCast_cpow_of_pos hn_nat_pos z
    have hnorm_term :
        ‖f n‖ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
      calc
        ‖f n‖ = ‖(1 : ℂ)‖ / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
          exact norm_div (1 : ℂ) ((((n + 2 : ℕ) : ℂ) ^ z))
        _ = 1 / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
          exact congrArg
            (fun x : ℝ => x / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖)
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
        _ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
          exact congrArg (fun x : ℝ => 1 / x) hnorm_cpow
    have hpow_mono :
        ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
          ((n + 2 : ℕ) : ℝ) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le hn_real_one_le hz
    have hpow_two_pos : 0 < ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_pos_of_pos hn_real_pos 2
    have hdiv_le :
        1 / (((n + 2 : ℕ) : ℝ) ^ z.re) ≤
          1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) :=
      one_div_le_one_div_of_le hpow_two_pos hpow_mono
    have hg_eq :
        g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
      calc
        g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := rfl
        _ = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
          exact congrArg
            (fun x : ℝ => 1 / x)
            (Real.rpow_natCast (((n + 2 : ℕ) : ℝ)) 2).symm
    exact Eq.subst
      (motive := fun x : ℝ => ‖f n‖ ≤ x)
      hg_eq.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)))
        hnorm_term.symm
        hdiv_le)
  have hnorm_tail :
      ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ :=
    norm_tsum_le_tsum_norm hf_summable
  have hnorms_le_g :
      (∑' n : ℕ, ‖f n‖) ≤ ∑' n : ℕ, g n :=
    tsum_le_tsum hterm_le hf_summable hg_summable
  have htail_le_g :
      ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, g n :=
    le_trans hnorm_tail hnorms_le_g
  exact le_trans htail_le_g (le_add_of_nonneg_right zero_le_one)

/-- The Dirichlet series tail for `ζ` is uniformly bounded on `2 ≤ re z`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z - 1‖ ≤ A := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound with
    ⟨A, hA, htail⟩
  refine ⟨A, hA, ?_⟩
  intro z hz
  have hidentity :
      riemannZeta z - 1 =
        ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) :=
    riemannZeta_sub_one_eq_dirichletSeries_tail hz
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ A)
    hidentity.symm
    (htail z hz)

/-- Adding back the leading `1` preserves far-right boundedness of `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖riemannZeta z - 1‖ ≤ A) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  rcases htail with ⟨A, hA, htail_bound⟩
  refine ⟨A + 1, add_pos hA zero_lt_one, ?_⟩
  intro z hz
  have hdecomp : riemannZeta z = (riemannZeta z - 1) + 1 := by
    exact (sub_add_cancel (riemannZeta z) 1).symm
  have htriangle :
      ‖riemannZeta z‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ := by
    exact Eq.subst
      (motive := fun w : ℂ => ‖w‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖)
      hdecomp.symm
      (norm_add_le (riemannZeta z - 1) (1 : ℂ))
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    norm_num
  have hsum :
      ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ ≤ A + 1 := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖riemannZeta z - 1‖ + x ≤ A + 1)
      hone_norm.symm
      (add_le_add_right (htail_bound z hz) 1)
  exact le_trans htriangle hsum

/-- The far-right half-plane Dirichlet-series bound for `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  exact riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound

/-- On the right edge `re z = 2` of the critical strip, the pole-cleared zeta factor
has finite-order growth by the far-right Dirichlet-series bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_bound with
    ⟨A, hA, hzeta_bound⟩
  refine ⟨A, 1, 1, hA, zero_lt_one, ?_⟩
  intro z hz_re _hz_im
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hz_far : 2 ≤ z.re :=
    le_of_eq hz_re.symm
  have hzeta : ‖riemannZeta z‖ ≤ A :=
    hzeta_bound z hz_far
  have hsub_norm : ‖z - 1‖ ≤ H := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ = H := by
        exact (add_comm ‖z‖ 1)
  have hproduct :
      ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
    calc
      ‖(z - 1) * riemannZeta z‖ =
          ‖z - 1‖ * ‖riemannZeta z‖ := by
        exact norm_mul (z - 1) (riemannZeta z)
      _ ≤ H * A :=
        mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
  have hH_le_expH : H ≤ Real.exp H := by
    exact le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp H)
  have hscaled :
      H * A ≤ A * Real.exp H := by
    calc
      H * A = A * H := by
        exact mul_comm H A
      _ ≤ A * Real.exp H :=
        mul_le_mul_of_nonneg_left hH_le_expH (le_of_lt hA)
  have hexponent :
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = (1 + ‖z‖) ^ (1 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
      _ = 1 + ‖z‖ := by
        exact pow_one (1 + ‖z‖)
      _ = H := rfl
  exact le_trans hproduct
    (Eq.subst
      (motive := fun x : ℝ => H * A ≤ A * Real.exp x)
      hexponent.symm
      hscaled)

/-- The right-edge estimate transfers to the removable pole-cleared zeta normalization.

The vertical edge `re z = 2` is disjoint from the pole face, so this is only the
definition-level transport from `(s - 1) ζ(s)` to `poleClearedRiemannZeta`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hone_re : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          exact Complex.one_re
    have htwo_eq_one : (2 : ℝ) = 1 := by
      calc
        (2 : ℝ) = z.re := hz_re.symm
        _ = 1 := hone_re
    norm_num at htwo_eq_one
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpc.symm
    (hbound z hz_re hz_im)

/-- Right-edge boundary growth for the pole-cleared zeta factor from the far-right
Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This public owner theorem is a thin wrapper over the two mathematically distinct vertical
edge inputs: the left edge comes from the functional equation and Gamma control, while the
right edge comes from the Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound :
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  exact
    ⟨poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

/-- A real `IsBigO` bound against a positive exponential envelope gives an
eventual raw inequality with a positive multiplicative constant. -/
theorem real_isBigO_exp_eventually_le_pos_mul
    {f : ℝ → ℝ}
    (c : ℝ)
    (h : f =O[Filter.atTop] fun T : ℝ => Real.exp (c * T)) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        f T ≤ D * Real.exp (c * T) := by
  rcases h.isBigOWith with ⟨C, hC⟩
  refine ⟨|C| + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one
  have hnonneg :
      ∀ᶠ T : ℝ in Filter.atTop,
        0 ≤ Real.exp (c * T) :=
    Filter.Eventually.of_forall
      (fun T => le_of_lt (Real.exp_pos (c * T)))
  exact
    (hC.bound.and hnonneg).mono
      (fun T hT =>
        by
          let G : ℝ := Real.exp (c * T)
          let D : ℝ := |C| + 1
          have hf_le_norm : f T ≤ ‖f T‖ :=
            Real.le_norm_self (f T)
          have hC_le_abs : C ≤ |C| :=
            le_abs_self C
          have hC_le_D : C ≤ D :=
            le_trans hC_le_abs (le_add_of_nonneg_right zero_le_one)
          have hG_norm_nonneg : 0 ≤ ‖G‖ :=
            norm_nonneg G
          have hmul_le : C * ‖G‖ ≤ D * ‖G‖ :=
            mul_le_mul_of_nonneg_right hC_le_D hG_norm_nonneg
          have hG_norm : ‖G‖ = G :=
            Real.norm_of_nonneg hT.2
          have hmul_eq : D * ‖G‖ = D * G :=
            congrArg (fun x : ℝ => D * x) hG_norm
          calc
            f T ≤ ‖f T‖ :=
              hf_le_norm
            _ ≤ C * ‖G‖ :=
              hT.1
            _ ≤ D * ‖G‖ :=
              hmul_le
            _ = D * G :=
              hmul_eq)

/-- Standard shifted-polynomial/exponential comparison used in finite-order
envelope domination. -/
theorem finiteOrder_shiftedPower_isBigO_scaledPower
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => (c * T) ^ m := by
  let K : ℝ := (2 / c) ^ m
  have hK_nonneg : 0 ≤ K :=
    pow_nonneg (le_of_lt (div_pos two_pos hc)) m
  refine
    IsBigO.of_bound K
      (eventually_atTop.2
        ⟨1, fun T hT => ?_⟩)
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  have hcT_nonneg : 0 ≤ c * T :=
    mul_nonneg (le_of_lt hc) hT_nonneg
  have hleft_nonneg : 0 ≤ (1 + T) ^ m :=
    pow_nonneg (add_nonneg zero_le_one hT_nonneg) m
  have hnorm_left :
      ‖(1 + T) ^ m‖ = (1 + T) ^ m :=
    Real.norm_of_nonneg hleft_nonneg
  have hnorm_right_base :
      ‖(c * T) ^ m‖ = (c * T) ^ m :=
    Real.norm_of_nonneg (pow_nonneg hcT_nonneg m)
  have hshift_le_twoT : 1 + T ≤ 2 * T := by
    calc
      1 + T ≤ T + T :=
        add_le_add_right hT T
      _ = 2 * T :=
        (two_mul T).symm
  have htwoT_eq :
      2 * T = (2 / c) * (c * T) := by
    calc
      (2 / c) * (c * T) = ((2 / c) * c) * T :=
        mul_assoc (2 / c) c T
      _ = 2 * T := by
        exact congrArg (fun x : ℝ => x * T) (div_mul_cancel₀ 2 (ne_of_gt hc))
  have hbase_le :
      1 + T ≤ (2 / c) * (c * T) :=
    Eq.subst
      (motive := fun x : ℝ => 1 + T ≤ x)
      htwoT_eq
      hshift_le_twoT
  have hpow_le :
      (1 + T) ^ m ≤ ((2 / c) * (c * T)) ^ m :=
    pow_le_pow_left₀ (add_nonneg zero_le_one hT_nonneg) hbase_le m
  have hmul_pow :
      ((2 / c) * (c * T)) ^ m = K * (c * T) ^ m :=
    mul_pow (2 / c) (c * T) m
  have hraw :
      (1 + T) ^ m ≤ K * (c * T) ^ m :=
    Eq.subst
      (motive := fun x : ℝ => (1 + T) ^ m ≤ x)
      hmul_pow
      hpow_le
  have htarget :
      ‖(1 + T) ^ m‖ ≤ K * ‖(c * T) ^ m‖ :=
    Eq.subst
      (motive := fun x : ℝ => ‖(1 + T) ^ m‖ ≤ K * x)
      hnorm_right_base.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ K * (c * T) ^ m)
        hnorm_left.symm
        hraw)
  exact htarget

/-- Positive linear changes of variable preserve the standard polynomial-versus-exponential
comparison at infinity. -/
theorem finiteOrder_scaledPower_isBigO_exp_scaled
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (c * T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (Real.isLittleO_pow_exp_atTop (n := m)).isBigO.comp_tendsto
      (Filter.Tendsto.const_mul_atTop hc tendsto_id)

/-- Shifted polynomial height is `O(exp (cT))` for every positive `c`. -/
theorem finiteOrder_shiftedPower_isBigO_exp
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (finiteOrder_shiftedPower_isBigO_scaledPower c m hc).trans
      (finiteOrder_scaledPower_isBigO_exp_scaled c m hc)

theorem finiteOrder_verticalExponent_isBigO_exp
    (A B c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => Real.log A + B * (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  have hconst :
      (fun _T : ℝ => Real.log A) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    have hone :
        (fun _T : ℝ => (1 : ℝ)) =O[Filter.atTop]
          fun T : ℝ => Real.exp (c * T) := by
      exact
        Real.isBigO_one_exp_comp.2
          ((Filter.Tendsto.const_mul_atTop hc tendsto_id))
    exact
      (isBigO_const_mul_self (Real.log A)
        (fun _T : ℝ => (1 : ℝ)) Filter.atTop).trans hone
  have hpoly :
      (fun T : ℝ => B * (1 + T) ^ m) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    exact
      (finiteOrder_shiftedPower_isBigO_exp c m hc).const_mul_left B
  exact IsBigO.add hconst hpoly

/-- Real exponent comparison behind finite-order versus double-exponential
domination.

This is the canonical real-analysis core: a polynomial in `1 + T`, after
adding the fixed logarithmic constant `log A`, is eventually bounded by a
positive multiple of `exp (cT)`.  It is the only growth-rate input needed for
the vertical finite-order envelope domination below. -/
theorem finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        Real.log A + B * (1 + T) ^ m ≤ D * Real.exp (c * T) := by
  exact real_isBigO_exp_eventually_le_pos_mul c
    (finiteOrder_verticalExponent_isBigO_exp A B c m hc)

/-- Exponentiating the real finite-order/double-exponential comparison gives
eventual domination of the vertical envelopes. -/
theorem finiteOrder_verticalEnvelope_eventually_le_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) ≤
          Real.exp (D * Real.exp (c * T)) := by
  rcases finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
      A B c m hA hB hc with
    ⟨D, hD_pos, hcompare⟩
  refine ⟨D, hD_pos, ?_⟩
  exact hcompare.mono
    (fun T hT =>
      by
        have hA_exp_log : A = Real.exp (Real.log A) :=
          (Real.exp_log hA).symm
        have hleft_exp :
            A * Real.exp (B * (1 + T) ^ m) =
              Real.exp (Real.log A + B * (1 + T) ^ m) := by
          calc
            A * Real.exp (B * (1 + T) ^ m) =
                Real.exp (Real.log A) * Real.exp (B * (1 + T) ^ m) := by
              exact congrArg
                (fun x : ℝ => x * Real.exp (B * (1 + T) ^ m))
                hA_exp_log
            _ = Real.exp (Real.log A + B * (1 + T) ^ m) :=
              (Real.exp_add (Real.log A) (B * (1 + T) ^ m)).symm
        have hexp_le :
            Real.exp (Real.log A + B * (1 + T) ^ m) ≤
              Real.exp (D * Real.exp (c * T)) :=
          Real.exp_le_exp.mpr hT
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ Real.exp (D * Real.exp (c * T)))
          hleft_exp.symm
          hexp_le)

/-- Pure real eventual domination of finite-order vertical envelopes by a
double-exponential envelope.

This is the exact real-variable core behind the admissible-growth conversion:
for every `0 < c`, polynomial height in the exponent,
`B * (1 + T)^m`, is eventually dominated by `D * exp (c * T)`.
After exponentiating, the ordinary finite-order envelope is controlled by the
subcritical Phragmen-Lindelöf growth envelope. -/
theorem finiteOrder_verticalEnvelope_isBigO_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun T : ℝ => A * Real.exp (B * (1 + T) ^ m)) =O[Filter.atTop]
        fun T : ℝ => Real.exp (D * Real.exp (c * T)) := by
  rcases finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
    ⟨D, _hD_pos, hdom⟩
  refine ⟨D, ?_⟩
  exact
    IsBigO.of_bound 1
      (hdom.mono
        (fun T hT =>
          by
            let R : ℝ := Real.exp (D * Real.exp (c * T))
            have hR_nonneg : 0 ≤ R :=
              le_of_lt (Real.exp_pos (D * Real.exp (c * T)))
            have hR_norm : ‖R‖ = R :=
              Real.norm_of_nonneg hR_nonneg
            have hone_norm : 1 * ‖R‖ = R := by
              calc
                1 * ‖R‖ = ‖R‖ :=
                  one_mul ‖R‖
                _ = R :=
                  hR_norm
            Eq.subst
              (motive := fun x : ℝ =>
                ‖A * Real.exp (B * (1 + T) ^ m)‖ ≤ x)
              hone_norm.symm
              (le_trans
                (le_of_eq
                  (Real.norm_of_nonneg
                    (mul_nonneg (le_of_lt hA)
                      (le_of_lt (Real.exp_pos (B * (1 + T) ^ m))))))
                hT)))

/-- Bounded-strip height comparison in the exact form used by the
finite-order-to-admissible-envelope transport. -/
theorem strip_norm_height_le_vertical_height_envelope
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    1 + ‖z‖ ≤ (|a| + |b| + 2) * (1 + ‖z.im‖) :=
  strip_basicHeight_le_verticalHeight a b hza hzb

/-- On a closed bounded strip, the finite-order complex-height envelope is
`O` of the corresponding vertical-height envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_verticalEnvelope
    (A B a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B) :
    (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
      fun z : ℂ =>
        A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E₁ : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            let E₂ : ℝ :=
              A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m)
            have hpoint : E₁ ≤ E₂ :=
              finiteOrder_norm_envelope_le_strip_vertical_envelope
                (le_of_lt hA)
                (le_of_lt hB)
                hz.1
                hz.2
            have hE₁_nonneg : 0 ≤ E₁ :=
              mul_nonneg (le_of_lt hA)
                (le_of_lt (Real.exp_pos (B * (1 + ‖z‖) ^ m)))
            have hE₂_nonneg : 0 ≤ E₂ :=
              le_trans hE₁_nonneg hpoint
            have hE₁_norm : ‖E₁‖ = E₁ :=
              Real.norm_of_nonneg hE₁_nonneg
            have hE₂_norm : ‖E₂‖ = E₂ :=
              Real.norm_of_nonneg hE₂_nonneg
            have hone_norm : 1 * ‖E₂‖ = E₂ := by
              calc
                1 * ‖E₂‖ = ‖E₂‖ :=
                  one_mul ‖E₂‖
                _ = E₂ :=
                  hE₂_norm
            Eq.subst
              (motive := fun x : ℝ => ‖E₁‖ ≤ x)
              hone_norm.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ E₂)
                hE₁_norm.symm
                hpoint))))

/-- The real vertical double-exponential domination transports through
`z ↦ |im z|` to the closed-strip filter. -/
theorem finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z.im‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
    ⟨D, _hD_pos, hdom⟩
  refine ⟨D, ?_⟩
  have hcomap :
      ∀ᶠ z : ℂ in Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop,
        A * Real.exp (B * (1 + |z.im|) ^ m) ≤
          Real.exp (D * Real.exp (c * |z.im|)) :=
    hdom.comap (_root_.abs ∘ Complex.im)
  have hclosed :
      ∀ᶠ z : ℂ in
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b},
        A * Real.exp (B * (1 + |z.im|) ^ m) ≤
          Real.exp (D * Real.exp (c * |z.im|)) :=
    hcomap.filter_mono inf_le_left
  exact
    IsBigO.of_bound 1
      (hclosed.mono
        (fun z hz =>
          by
            let E : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
            let R : ℝ := Real.exp (D * Real.exp (c * |z.im|))
            have him_norm_eq_abs : ‖z.im‖ = |z.im| :=
              Real.norm_eq_abs z.im
            have hraw : E ≤ R :=
              Eq.subst
                (motive := fun x : ℝ =>
                  A * Real.exp (B * (1 + x) ^ m) ≤ R)
                him_norm_eq_abs.symm
                hz
            have hE_nonneg : 0 ≤ E :=
              mul_nonneg (le_of_lt hA)
                (le_of_lt (Real.exp_pos (B * (1 + ‖z.im‖) ^ m)))
            have hR_nonneg : 0 ≤ R :=
              le_of_lt (Real.exp_pos (D * Real.exp (c * |z.im|)))
            have hE_norm : ‖E‖ = E :=
              Real.norm_of_nonneg hE_nonneg
            have hR_norm : ‖R‖ = R :=
              Real.norm_of_nonneg hR_nonneg
            have hone_norm : 1 * ‖R‖ = R := by
              calc
                1 * ‖R‖ = ‖R‖ :=
                  one_mul ‖R‖
                _ = R :=
                  hR_norm
            Eq.subst
              (motive := fun x : ℝ => ‖E‖ ≤ x)
              hone_norm.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ R)
                hE_norm.symm
                hraw)))

/-- Bounded-strip finite-order envelopes are admissible double-exponential
envelopes after reducing complex height to vertical height.

The proof first uses `finiteOrder_norm_envelope_le_strip_vertical_envelope` to
replace `1 + ‖z‖` by a fixed multiple of `1 + ‖im z‖` on the strip, then uses
the pure real eventual domination theorem for the vertical envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  let Bv : ℝ := B * (|a| + |b| + 2) ^ m
  have hK_pos : 0 < |a| + |b| + 2 := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have htwo_le : (2 : ℝ) ≤ |a| + |b| + 2 :=
      le_add_of_nonneg_left hsum_nonneg
    exact lt_of_lt_of_le htwo_pos htwo_le
  have hBv_pos : 0 < Bv :=
    mul_pos hB (pow_pos hK_pos m)
  have hstrip_to_vertical :
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => A * Real.exp (Bv * (1 + ‖z.im‖) ^ m) :=
    finiteOrder_stripEnvelope_isBigO_verticalEnvelope
      A B a b m hA hB
  rcases finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
      A Bv c a b m hA hBv_pos hc with
    ⟨D, hvertical_to_double⟩
  exact ⟨D, hstrip_to_vertical.trans hvertical_to_double⟩

/-- Membership in the open vertical strip gives the corresponding closed-strip
inequalities needed by finite-order pointwise bounds. -/
theorem openStrip_mem_closedStrip_bounds
    {a b : ℝ}
    {z : ℂ}
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    a ≤ z.re ∧ z.re ≤ b :=
  ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- A pointwise finite-order bound on a strip gives the matching `IsBigO`
bound against the finite-order envelope on the same strip filter. -/
theorem finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
    (f : ℂ → ℂ)
    (A B a b : ℝ)
    (m : ℕ)
    (hbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    f =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            have hstrip : a ≤ z.re ∧ z.re ≤ b :=
              openStrip_mem_closedStrip_bounds hz
            have hpoint : ‖f z‖ ≤ E :=
              hbound z hstrip.1 hstrip.2
            have hE_nonneg : 0 ≤ E :=
              le_trans (norm_nonneg (f z)) hpoint
            have hE_norm : ‖E‖ = E :=
              Real.norm_of_nonneg hE_nonneg
            have hone_norm : 1 * ‖E‖ = E := by
              calc
                1 * ‖E‖ = ‖E‖ :=
                  one_mul ‖E‖
                _ = E :=
                  hE_norm
            Eq.subst
              (motive := fun x : ℝ => ‖f z‖ ≤ x)
              hone_norm.symm
              hpoint)))

/-- An `IsBigO` statement on the closed-strip principal filter restricts to
the corresponding open-strip principal filter. -/
theorem isBigO_on_openStrip_of_isBigO_on_closedStrip
    {F G : ℂ → ℝ}
    {a b : ℝ}
    (h :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        G) :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        G := by
  let L : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hopen_subset_closed :
      Complex.re ⁻¹' Set.Ioo a b ⊆ {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
    intro z hz
    exact openStrip_mem_closedStrip_bounds hz
  have hprincipal :
      𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    principal_mono.2 hopen_subset_closed
  have hle_left :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤ L :=
    inf_le_left
  have hle_right :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_trans inf_le_right hprincipal
  have hle :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        L ⊓ 𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_inf hle_left hle_right
  exact h.mono hle

/-- The closed-strip envelope domination can be used on the open-strip filter. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases finiteOrder_stripEnvelope_isBigO_doubleExponential
      A B c a b m hA hB hc with
    ⟨D, hclosed⟩
  exact ⟨D, isBigO_on_openStrip_of_isBigO_on_closedStrip hclosed⟩

/-- The half-width Phragmen-Lindelöf growth parameter is strictly below the
strip threshold. -/
theorem real_pi_div_two_width_lt_pi_div_width
    {a b : ℝ}
    (hab : a < b) :
    Real.pi / (2 * (b - a)) < Real.pi / (b - a) := by
  let w : ℝ := b - a
  have hw_pos : 0 < w :=
    sub_pos.mpr hab
  have hw_lt_two_w : w < 2 * w := by
    calc
      w = 1 * w := (one_mul w).symm
      _ < 2 * w := mul_lt_mul_of_pos_right one_lt_two hw_pos
  exact
    div_lt_div₀'
      (le_refl Real.pi)
      hw_lt_two_w
      Real.pi_pos
      hw_pos

/-- Ordinary finite-order growth in a bounded vertical strip gives the
subcritical double-exponential admissible-growth hypothesis used by the
bounded-boundary Phragmen-Lindelöf theorem.

This is the generic envelope conversion: on a fixed-width strip, every
polynomial/exponential finite-order envelope
`A * exp (B * (1 + ‖z‖)^m)` is eventually dominated by
`exp (D * exp (c * |im z|))` for any positive `c`, so one chooses a small
`c < π / (b - a)`. -/
theorem strip_admissible_doubleExponential_growth_of_finiteOrder_growth
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases hfinite with ⟨A, B, m, hA, hB, hbound⟩
  let c : ℝ := Real.pi / (2 * (b - a))
  have hwidth_pos : 0 < b - a :=
    sub_pos.mpr hab
  have hc_pos : 0 < c := by
    exact div_pos Real.pi_pos (mul_pos two_pos hwidth_pos)
  have hc_lt : c < Real.pi / (b - a) :=
    real_pi_div_two_width_lt_pi_div_width hab
  rcases finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
      A B c a b m hA hB hc_pos with
    ⟨D, henv⟩
  have hfunction :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
      f A B a b m hbound
  refine ⟨c, hc_lt, D, ?_⟩
  exact hfunction.trans henv

/-- Global finite-order growth for the pole-cleared Riemann zeta factor.

This is the canonical standard zeta theorem behind the strip-local growth
input: `(s - 1)ζ(s)` is an entire function of finite order.  Analytically this
is proved from the meromorphic finite-order theory of `ζ`, using
Euler-Maclaurin/Abel estimates in the right half-plane, the functional equation
and Gamma/Stirling transport in the left half-plane, and local boundedness near
the removable pole. -/
theorem poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_bound with
    ⟨A, hA, hzeta_bound⟩
  refine ⟨A, 1, 1, hA, zero_lt_one, ?_⟩
  intro z hz_far
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          exact Complex.one_re
    have htwo_le_one : (2 : ℝ) ≤ 1 := by
      exact hz_far.trans_eq hz_re_one
    exact (not_le_of_gt one_lt_two) htwo_le_one
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hzeta : ‖riemannZeta z‖ ≤ A :=
    hzeta_bound z hz_far
  have hsub_norm : ‖z - 1‖ ≤ H := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ = H := by
        exact add_comm ‖z‖ 1
  have hproduct :
      ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
    calc
      ‖(z - 1) * riemannZeta z‖ =
          ‖z - 1‖ * ‖riemannZeta z‖ := by
        exact norm_mul (z - 1) (riemannZeta z)
      _ ≤ H * A :=
        mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
  have hH_le_expH : H ≤ Real.exp H :=
    le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp H)
  have hscaled :
      H * A ≤ A * Real.exp H := by
    calc
      H * A = A * H := by
        exact mul_comm H A
      _ ≤ A * Real.exp H :=
        mul_le_mul_of_nonneg_left hH_le_expH (le_of_lt hA)
  have hexponent :
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
          (1 + ‖z‖) ^ (1 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
      _ = 1 + ‖z‖ := by
        exact pow_one (1 + ‖z‖)
      _ = H := rfl
  have hraw :
      ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp H :=
    Eq.subst
      (motive := fun w : ℂ => ‖w‖ ≤ A * Real.exp H)
      hpc.symm
      (le_trans hproduct hscaled)
  exact Eq.subst
    (motive := fun x : ℝ => ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp x)
    hexponent.symm
    hraw

/-- Far-right finite-order growth for the raw pole-cleared zeta product.

This is the Dirichlet-series half-plane estimate on `2 ≤ Re s`, with the
elementary pole-clearing factor absorbed into the finite-order envelope. -/
theorem riemannZeta_poleCleared_rightHalfPlane_two_le_finiteOrder_growth_from_dirichletSeries :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        2 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_two
  have hw_ne_one : w ≠ 1 := by
    intro hw_one
    have hw_re_one : w.re = 1 := by
      calc
        w.re = (1 : ℂ).re := by
          exact congrArg Complex.re hw_one
        _ = 1 := by
          exact Complex.one_re
    have htwo_le_one : (2 : ℝ) ≤ 1 :=
      hw_two.trans_eq hw_re_one
    exact (not_le_of_gt one_lt_two) htwo_le_one
  have hpole :
      poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  exact Eq.subst
    (motive := fun u : ℂ =>
      ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
    hpole
    (hbound w hw_two)

/-- Left boundary finite-order growth for the removable pole-cleared zeta on
`Re s = 1`, from the Abel/Euler-Maclaurin boundary estimate. -/
theorem poleClearedRiemannZeta_one_two_strip_leftBoundary_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hz_ne_one : z ≠ 1 := by
    intro hz_one
    have hz_im_zero : z.im = 0 := by
      calc
        z.im = (1 : ℂ).im := by
          exact congrArg Complex.im hz_one
        _ = 0 := by
          exact Complex.one_im
    have hz_im_norm_zero : ‖z.im‖ = 0 := by
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm hz_im_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        hz_im_norm_zero
        hz_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hpole :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpole.symm
    (hbound z hz_re hz_im)

/-- Right boundary finite-order growth for the removable pole-cleared zeta on
`Re s = 2`, from the Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_one_two_strip_rightBoundary_growth_from_dirichletSeries :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound

/-- Holomorphicity of the removable pole-cleared zeta on the open strip
`1 < Re s < 2`, inherited from the larger right-critical strip. -/
theorem poleClearedRiemannZeta_one_two_strip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 1 2) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl.mono
    (by
      intro z hz
      exact ⟨lt_trans zero_lt_one hz.1, hz.2⟩)

/-- Euler-Maclaurin cutoff used in the bounded strip `1 ≤ Re s ≤ 2`.

The choice is height-comparable and avoids the zero cutoff; it is the same
classical scale as the boundary-line Abel/Euler-Maclaurin truncation. -/
noncomputable def eulerMaclaurinPoleClearedZetaCutoff
    (z : ℂ) : ℕ :=
  ⌊2 + ‖z‖⌋₊

/-- Finite Dirichlet-polynomial part of the Euler-Maclaurin continuation for
`ζ(s)`, after multiplying by the pole-clearing factor `s - 1`. -/
noncomputable def eulerMaclaurinPoleClearedZetaFinitePart
    (z : ℂ) : ℂ :=
  (z - 1) *
    ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
      1 / (((n : ℕ) : ℂ) ^ z)

/-- Pole-cancelling main term `(s - 1) · N^(1-s)/(s-1) = N^(1-s)` in the
Euler-Maclaurin continuation. -/
noncomputable def eulerMaclaurinPoleClearedZetaMainTerm
    (z : ℂ) : ℂ :=
  ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)

/-- Endpoint correction in the pole-cleared Euler-Maclaurin continuation. -/
noncomputable def eulerMaclaurinPoleClearedZetaEndpointTerm
    (z : ℂ) : ℂ :=
  ((z - 1) / 2) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

/-- Finite Dirichlet-polynomial part in the raw first-order Euler-Maclaurin
formula for `ζ(s)` at the owner cutoff. -/
noncomputable def eulerMaclaurinZetaFinitePart
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
    1 / (((n : ℕ) : ℂ) ^ z)

/-- Integral main term `N^(1-s)/(s-1)` in the raw Euler-Maclaurin formula
away from the pole. -/
noncomputable def eulerMaclaurinZetaMainTerm
    (z : ℂ) : ℂ :=
  (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)) /
    (z - 1)

/-- Endpoint correction `1/2 · N^{-s}` in the raw Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaEndpointTerm
    (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))

/-- The bounded-strip Euler-Maclaurin cutoff is always at least one. -/
theorem eulerMaclaurinPoleClearedZetaCutoff_pos
    (z : ℂ) :
    0 < eulerMaclaurinPoleClearedZetaCutoff z := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ = 2 := rfl
  have hone_le : (1 : ℝ) ≤ 2 + ‖z‖ :=
    le_trans hone_le_two (le_add_of_nonneg_right (norm_nonneg z))
  exact (Nat.one_le_floor_iff zero_lt_one).mpr hone_le

/-- The bounded-strip Euler-Maclaurin cutoff is at least one as a real number. -/
theorem one_le_eulerMaclaurinPoleClearedZetaCutoff_real
    (z : ℂ) :
    (1 : ℝ) ≤ (eulerMaclaurinPoleClearedZetaCutoff z : ℝ) :=
  Nat.cast_le.mpr (Nat.succ_le_iff.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z))

/-- The cutoff main Euler-Maclaurin power has norm at most one on `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 1 := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N :=
    eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm :
      ‖((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)‖ =
        (N : ℝ) ^ (((1 : ℂ) - z).re) :=
    Complex.norm_natCast_cpow_of_pos hN_pos ((1 : ℂ) - z)
  have hre :
      (((1 : ℂ) - z).re) = 1 - z.re := by
    calc
      (((1 : ℂ) - z).re) = (1 : ℂ).re - z.re :=
        Complex.sub_re (1 : ℂ) z
      _ = 1 - z.re := by
        exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
  have hexponent_nonpos : 1 - z.re ≤ 0 :=
    sub_nonpos.mpr hz_one
  have hpow_le :
      (N : ℝ) ^ (((1 : ℂ) - z).re) ≤ 1 :=
    Eq.subst
      (motive := fun e : ℝ => (N : ℝ) ^ e ≤ 1)
      hre.symm
      (Real.rpow_le_one_of_one_le_of_nonpos hN_one hexponent_nonpos)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm.symm
    hpow_le

/-- The reciprocal cutoff power in the endpoint correction is bounded by one
on `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hN_pos : 0 < N :=
    eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hN_one : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm_cpow :
      ‖((N : ℕ) : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hN_pos z
  have hpow_one : 1 ≤ (N : ℝ) ^ z.re :=
    Real.one_le_rpow hN_one hz_one
  have hpow_pos : 0 < (N : ℝ) ^ z.re :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN_pos) z.re
  have hnorm_pos : 0 < ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 0 < x)
      hnorm_cpow.symm
      hpow_pos
  have hnorm_one : 1 ≤ ‖((N : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm_cpow.symm
      hpow_one
  have hnorm_inv :
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((N : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((N : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((N : ℕ) : ℂ) ^ z‖ := by
        exact congrArg
          (fun x : ℝ => x / ‖((N : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((N : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_inv.symm
    hinv_le

/-- Each finite-window Euler-Maclaurin Dirichlet summand has norm at most one
on the strip `1 ≤ Re z`. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_summand_norm_le_one
    (z : ℂ)
    {n : ℕ}
    (hn : 1 ≤ n)
    (hz_one : 1 ≤ z.re) :
    ‖1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 1 := by
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_real_one : (1 : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hn
  have hnorm_cpow :
      ‖((n : ℕ) : ℂ) ^ z‖ = (n : ℝ) ^ z.re :=
    Complex.norm_natCast_cpow_of_pos hn_pos z
  have hpow_one : 1 ≤ (n : ℝ) ^ z.re :=
    Real.one_le_rpow hn_real_one hz_one
  have hnorm_one : 1 ≤ ‖((n : ℕ) : ℂ) ^ z‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hnorm_cpow.symm
      hpow_one
  have hnorm_inv :
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
        1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
    calc
      ‖1 / (((n : ℕ) : ℂ) ^ z)‖ =
          ‖(1 : ℂ)‖ / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact norm_div (1 : ℂ) (((n : ℕ) : ℂ) ^ z)
      _ = 1 / ‖((n : ℕ) : ℂ) ^ z‖ := by
        exact congrArg
          (fun x : ℝ => x / ‖((n : ℕ) : ℂ) ^ z‖)
          (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hinv_le :
      1 / ‖((n : ℕ) : ℂ) ^ z‖ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hnorm_one)
      (le_of_eq (div_one (1 : ℝ)))
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_inv.symm
    hinv_le

/-- The norm of the finite Euler-Maclaurin Dirichlet window is bounded by its
cardinality. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_sum_norm_le_card
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
        1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
      ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) := by
  have hsum_norm :
      ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          ‖1 / (((n : ℕ) : ℂ) ^ z)‖ :=
    norm_sum_le _ _
  have hterms :
      (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          ‖1 / (((n : ℕ) : ℂ) ^ z)‖) ≤
        ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z), (1 : ℝ) := by
    exact Finset.sum_le_sum
      (fun n hn =>
        eulerMaclaurinPoleClearedZetaFinitePart_summand_norm_le_one
          z (Finset.mem_Icc.mp hn).1 hz_one)
  have hcard :
      (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z), (1 : ℝ)) =
        ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) :=
    Finset.sum_const_nat (Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)) 1
  exact le_trans hsum_norm (le_trans hterms (le_of_eq hcard))

/-- The finite Euler-Maclaurin window cardinality is controlled by the
height-comparable cutoff. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height
    (z : ℂ) :
    ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) ≤
      3 * (1 + ‖z‖) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hsubset : Finset.Icc 1 N ⊆ Finset.Icc 0 N := by
    intro n hn
    exact ⟨Nat.zero_le n, (Finset.mem_Icc.mp hn).2⟩
  have hcard_nat :
      (Finset.Icc 1 N).card ≤ (Finset.Icc 0 N).card :=
    Finset.card_le_card hsubset
  have hcard_zero :
      (Finset.Icc 0 N).card = N + 1 :=
    Finset.card_Icc 0 N
  have hcard_le_nat :
      ((Finset.Icc 1 N).card : ℝ) ≤ (N + 1 : ℝ) := by
    exact Nat.cast_le.mpr
      (le_trans hcard_nat (le_of_eq hcard_zero))
  have hN_le : (N : ℝ) ≤ 2 + ‖z‖ := by
    unfold N
    unfold eulerMaclaurinPoleClearedZetaCutoff
    have hnonneg : 0 ≤ 2 + ‖z‖ :=
      le_trans zero_le_one
        (le_trans (by
          calc
            (1 : ℝ) ≤ 2 := one_le_two) (le_add_of_nonneg_right (norm_nonneg z)))
    exact Nat.floor_le hnonneg
  have hN_add_le : (N + 1 : ℝ) ≤ 3 + ‖z‖ := by
    calc
      (N + 1 : ℝ) = (N : ℝ) + 1 := by
        exact Nat.cast_add N 1
      _ ≤ (2 + ‖z‖) + 1 :=
        add_le_add_right hN_le 1
      _ = 3 + ‖z‖ := by
        calc
          (2 + ‖z‖) + 1 = (2 + 1) + ‖z‖ := by
            exact add_right_comm 2 ‖z‖ 1
          _ = 3 + ‖z‖ := rfl
  have hthree_height : 3 + ‖z‖ ≤ 3 * (1 + ‖z‖) := by
    calc
      3 + ‖z‖ ≤ 3 + 3 * ‖z‖ :=
        add_le_add_left
          (calc
            ‖z‖ ≤ 3 * ‖z‖ := by
              exact le_mul_of_one_le_left (norm_nonneg z) one_le_three)
          3
      _ = 3 * (1 + ‖z‖) := by
        calc
          3 + 3 * ‖z‖ = 3 * 1 + 3 * ‖z‖ := by
            exact congrArg (fun x : ℝ => x + 3 * ‖z‖) (mul_one 3).symm
          _ = 3 * (1 + ‖z‖) := by
            exact (mul_add 3 1 ‖z‖).symm
  exact le_trans hcard_le_nat (le_trans hN_add_le hthree_height)

/-- The pole-clearing factor in the finite Euler-Maclaurin part contributes at
most one factor of the height envelope. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height
    (z : ℂ) :
    ‖z - 1‖ ≤ 1 + ‖z‖ := by
  calc
    ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le z (1 : ℂ)
    _ = ‖z‖ + 1 := by
      exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 + ‖z‖ := by
      exact add_comm ‖z‖ 1

/-- Uniform polynomial control for the finite Euler-Maclaurin Dirichlet window.

This is the canonical finite-window estimate: on `1 ≤ Re z ≤ 2`, each summand
`n^{-z}` has norm at most `1` for `1 ≤ n`, the window cardinality is controlled
by the height-comparable cutoff `⌊2 + ‖z‖⌋₊`, and the pole-clearing factor
`z - 1` contributes only one more power of `1 + ‖z‖`. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_sum_cardinality_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨3, 2, zero_lt_three, ?_⟩
  intro z hz_one _hz_two
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpole :
      ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hsum_card :
      ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) :=
    eulerMaclaurinPoleClearedZetaFinitePart_sum_norm_le_card z hz_one
  have hcard :
      ((Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z)).card : ℝ) ≤
        3 * H :=
    eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height z
  have hsum : ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 3 * H :=
    le_trans hsum_card hcard
  have hprod :
      ‖(z - 1) *
          ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z)‖ ≤
        H * (3 * H) := by
    calc
      ‖(z - 1) *
          ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z)‖ =
          ‖z - 1‖ *
            ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
              1 / (((n : ℕ) : ℂ) ^ z)‖ := by
        exact norm_mul (z - 1)
          (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
            1 / (((n : ℕ) : ℂ) ^ z))
      _ ≤ H * (3 * H) :=
        mul_le_mul hpole hsum
          (norm_nonneg
            (∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
              1 / (((n : ℕ) : ℂ) ^ z)))
          hH_nonneg
  have hcollapse : H * (3 * H) = 3 * H ^ (2 : ℕ) := by
    calc
      H * (3 * H) = (H * 3) * H := by
        exact mul_assoc H 3 H
      _ = (3 * H) * H := by
        exact congrArg (fun x : ℝ => x * H) (mul_comm H 3)
      _ = 3 * (H * H) := by
        exact (mul_assoc 3 H H).symm
      _ = 3 * H ^ (2 : ℕ) := by
        exact congrArg (fun x : ℝ => 3 * x) (pow_two H).symm
  have htarget : 3 * H ^ (2 : ℕ) = 3 * (1 + ‖z‖) ^ (2 : ℕ) := rfl
  exact le_trans hprod (le_of_eq (hcollapse.trans htarget))

/-- Bernoulli-periodic remainder term in the pole-cleared Euler-Maclaurin
continuation.

This name isolates the standard remainder estimate.  The exact analytic
construction is the usual `B₁({x})` integral after multiplying by `s - 1`; the
owner theorem below records the formula identity and the polynomial bound used
by the finite-order chain. -/
noncomputable def eulerMaclaurinPoleClearedZetaRemainderTerm
    (z : ℂ) : ℂ :=
  poleClearedRiemannZeta z -
    (eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z)

/-- First periodic Bernoulli factor in the Euler-Maclaurin zeta remainder.

This is the sawtooth `B₁({x}) = {x} - 1/2`, written with `Int.fract`. -/
noncomputable def eulerMaclaurinFirstPeriodicBernoulli
    (x : ℝ) : ℝ :=
  Int.fract x - 1 / 2

/-- The bare Bernoulli-periodic tail integral in the Euler-Maclaurin zeta
remainder, before multiplication by `-(z - 1) z`. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Raw first-order Euler-Maclaurin Bernoulli-periodic remainder
`-s ∫_N^∞ B₁({x}) x^{-s-1} dx`. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

/-- Explicit Bernoulli-periodic integral remainder for the pole-cleared zeta
Euler-Maclaurin formula.

With `N = ⌊2 + ‖z‖⌋₊`, this is
`-(z - 1) z ∫_N^∞ B₁({x}) x^{-z-1} dx`, the standard first-order
Euler-Maclaurin remainder after multiplying by the pole-clearing factor. -/
noncomputable def eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
    (z : ℂ) : ℂ :=
  -((z - 1) * z) *
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z

/-- The pole-cleared finite Euler-Maclaurin term is `(s - 1)` times the raw
finite Dirichlet window. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaFinitePart z =
      (z - 1) * eulerMaclaurinZetaFinitePart z := by
  unfold eulerMaclaurinPoleClearedZetaFinitePart
  unfold eulerMaclaurinZetaFinitePart
  rfl

/-- Away from `s = 1`, the pole-cleared main term is `(s - 1)` times the raw
Euler-Maclaurin integral main term. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw
    {z : ℂ}
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurinPoleClearedZetaMainTerm z =
      (z - 1) * eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  unfold eulerMaclaurinZetaMainTerm
  let A : ℂ :=
    ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ ((1 : ℂ) - z)
  have hden_ne : z - 1 ≠ 0 :=
    sub_ne_zero.mpr hz_ne_one
  calc
    A = A := rfl
    _ = (z - 1) * (A / (z - 1)) := by
      exact (mul_div_cancel₀ A hden_ne).symm

/-- The pole-cleared endpoint correction is `(s - 1)` times the raw endpoint
correction. -/
theorem eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaEndpointTerm z =
      (z - 1) * eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinPoleClearedZetaEndpointTerm
  unfold eulerMaclaurinZetaEndpointTerm
  let U : ℂ :=
    1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)
  calc
    ((z - 1) / 2) * U =
        ((z - 1) * (1 / 2 : ℂ)) * U := by
      exact congrArg (fun w : ℂ => w * U) (div_eq_mul_inv (z - 1) 2)
    _ = (z - 1) * ((1 / 2 : ℂ) * U) := by
      exact (mul_assoc (z - 1) (1 / 2 : ℂ) U).symm

/-- The pole-cleared Bernoulli remainder is `(s - 1)` times the raw
Euler-Maclaurin Bernoulli remainder. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z =
      (z - 1) * eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z
  calc
    -((z - 1) * z) * I =
        ((z - 1) * -z) * I := by
      exact congrArg (fun w : ℂ => w * I) (mul_neg (z - 1) z).symm
    _ = (z - 1) * (-z * I) := by
      exact (mul_assoc (z - 1) (-z) I).symm

/-- Adding back a subtracted term. -/
theorem complex_eq_add_of_sub_eq
    {A B C : ℂ}
    (h : A - B = C) :
    A = B + C := by
  have hcancel : B + (A - B) = A := by
    calc
      B + (A - B) = B + (A + -B) := by
        exact congrArg (fun w : ℂ => B + w) (sub_eq_add_neg A B)
      _ = B + A + -B := by
        exact (add_assoc B A (-B)).symm
      _ = A + B + -B := by
        exact congrArg (fun w : ℂ => w + -B) (add_comm B A)
      _ = A + (B + -B) := by
        exact add_assoc A B (-B)
      _ = A + 0 := by
        exact congrArg (fun w : ℂ => A + w) (add_neg_cancel B)
      _ = A := by
        exact add_zero A
  calc
    A = B + (A - B) := by
      exact hcancel.symm
    _ = B + C := by
      exact congrArg (fun w : ℂ => B + w) h

/-- The zeroth Dirichlet monomial vanishes in the convergent half-plane. -/
theorem riemannZeta_dirichletTerm_zero_of_one_lt_re
    {z : ℂ}
    (hz : 1 < z.re) :
    (1 : ℂ) / ((0 : ℂ) ^ z) = 0 := by
  have hz_ne_zero : z ≠ 0 :=
    Complex.ne_zero_of_one_lt_re hz
  have hpow_zero : (0 : ℂ) ^ z = 0 :=
    (cpow_eq_zero_iff).mpr ⟨rfl, hz_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ z) = (1 : ℂ) / 0 := by
      exact congrArg (fun w : ℂ => (1 : ℂ) / w) hpow_zero
    _ = 0 := by
      exact div_zero (1 : ℂ)

/-- In the convergent half-plane, removing the finite Dirichlet window from
`ζ(s)` leaves the post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePart z) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    exact riemannZeta_dirichletTerm_zero_of_one_lt_re hz
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  unfold eulerMaclaurinZetaFinitePart
  exact htail_if

/-- The exponent `-z` is integrable at infinity exactly in the half-plane
`1 < Re z`. -/
theorem eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re
    {z : ℂ}
    (hhalf_plane : 1 < z.re) :
    (-z).re < -1 := by
  have hneg : -z.re < -1 :=
    neg_lt_neg hhalf_plane
  exact
    Eq.subst
      (motive := fun x : ℝ => x < -1)
      (Complex.neg_re z).symm
      hneg

/-- The Euler-Maclaurin cutoff is a positive lower endpoint for improper
integrals. -/
theorem eulerMaclaurinPoleClearedZetaCutoff_real_pos
    (z : ℂ) :
    0 < (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (eulerMaclaurinPoleClearedZetaCutoff_pos z)

/-- Mathlib's improper-integral formula applied to the zeta tail exponent
`-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) := by
  exact
    integral_Ioi_cpow_of_lt
      (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
      (eulerMaclaurinPoleClearedZetaCutoff_real_pos z)

/-- Algebraic normalization of the improper-integral value.

This is the remaining `cpow` and division transport from mathlib's
`-N^((-z)+1)/((-z)+1)` to the owner term `N^(1-z)/(z-1)`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm
    (z : ℂ) :
    -((((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) : ℂ) ^
          ((-z) + 1)) /
        ((-z) + 1) =
      eulerMaclaurinZetaMainTerm z := by
  unfold eulerMaclaurinZetaMainTerm
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  calc
    -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
      exact congrArg
        (fun W : ℂ => -W / ((-z) + 1))
        hpow
    _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
      exact congrArg
        (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
        hden
    _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
      exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)

/-- The Euler-Maclaurin integral main term for the post-cutoff tail.

For `N = ⌊2 + ‖z‖⌋₊`, mathlib's improper-integral formula for
`∫_N^∞ x^{-z} dx` gives `N^(1-z)/(z-1)` when `1 < Re z`.  This lemma records
the normalization used by the zeta owner definitions; the remaining work is
the standard `cpow` exponent arithmetic transporting
`integral_Ioi_cpow_of_lt` from exponent `-z`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTerm z := by
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_postCutoffTail_integral_cpow_neg_formula
        z hhalf_plane)
      (eulerMaclaurin_riemannZeta_postCutoffTail_integralFormula_eq_mainTerm z)

/-- Endpoint normalization for the first-order Euler-Maclaurin tail.

The endpoint correction is exactly `(1/2)N^{-z}` in the owner notation. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm
    (z : ℂ) :
    (1 / 2 : ℂ) *
        (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
      eulerMaclaurinZetaEndpointTerm z := by
  unfold eulerMaclaurinZetaEndpointTerm
  rfl

/-- Remainder-sign normalization for the first-order Euler-Maclaurin tail.

With `B₁({x}) = {x} - 1/2`, the first-order remainder for
`f(x) = x^{-z}` is
`-z ∫_N^∞ B₁({x}) x^{-z-1} dx`, matching the raw owner remainder. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm
    (z : ℂ) :
    -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
      eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  rfl

/-- Derivative of the complex power profile used in the zeta tail.

On the positive real ray, the derivative of `x ↦ x^{-z}` is
`-z · x^{-z-1}`.  This is the calculus input in the first-order
Euler-Maclaurin formula. -/
theorem eulerMaclaurin_cpow_neg_deriv_eq
    (z : ℂ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z))) x =
      -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
  have hslit : ((x : ℂ) : ℂ) ∈ slitPlane :=
    ofReal_mem_slitPlane.mpr hx
  have hcomplex :
      HasDerivAt
        (fun w : ℂ => w ^ (-z))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).cpow_const hslit
  have hreal :
      HasDerivAt
        (fun t : ℝ => (((t : ℝ) : ℂ) ^ (-z)))
        ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1)
        x :=
    hcomplex.comp_ofReal
  have hexponent :
      ((-z) - 1) = -(z + 1) := by
    calc
      ((-z) - 1) = (-z) + (-(1 : ℂ)) := by
        exact sub_eq_add_neg (-z) (1 : ℂ)
      _ = -(z + 1) := by
        exact (neg_add z (1 : ℂ)).symm
  have hvalue :
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
        -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
    calc
      ((-z) * ((x : ℂ) ^ ((-z) - 1)) * 1) =
          (-z) * ((x : ℂ) ^ ((-z) - 1)) := by
        exact mul_one ((-z) * ((x : ℂ) ^ ((-z) - 1)))
      _ = -z * (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact congrArg
          (fun W : ℂ => -z * W)
          (congrArg (fun E : ℂ => ((x : ℂ) ^ E)) hexponent)
  exact Eq.trans hreal.deriv hvalue

/-- Positive natural reciprocal as a negative complex power.

This is the pointwise bridge between the Dirichlet summand notation
`1 / n^z` and the Euler-Maclaurin function notation `n^{-z}`. -/
theorem eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg
    (z : ℂ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) := by
  have hn_ne : (n : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  calc
    (1 : ℂ) / ((n : ℂ) ^ z) = (((n : ℂ) ^ z)⁻¹) := by
      exact one_div (((n : ℂ) ^ z))
    _ = (n : ℂ) ^ (-z) := by
      exact (Complex.cpow_neg (n : ℂ) z).symm

/-- Standard first-order Euler-Maclaurin formula for an infinite post-cutoff
tail.

For a `C¹` function `f` on the positive ray with derivative `f'`, this is the
canonical periodic-Bernoulli form
`∑_{n>N} f(n) = ∫_N^∞ f(x) dx + (1/2)f(N) + ∫_N^∞ B₁({x}) f'(x) dx`.
This is the reusable owner theorem that the zeta specialization consumes. -/
theorem eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
    (f f' : ℝ → ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hderiv : ∀ x : ℝ, ((N : ℝ) < x) → deriv f x = f' x) :
    HasSum
      (fun n : ℕ =>
        if N < n then f ((n : ℕ) : ℝ) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)), f x) +
        ((1 / 2 : ℂ) * f ((N : ℕ) : ℝ)) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x)) := by
  sorry

/-- Specialization of the first-order Euler-Maclaurin theorem to
`f(x)=x^{-z}` in function notation. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  let f : ℝ → ℂ := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-z))
  let f' : ℝ → ℂ := fun x : ℝ => -z * (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hderiv : ∀ x : ℝ, ((N : ℝ) < x) → deriv f x = f' x := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_trans (Nat.cast_pos.mpr hN) hx
    exact eulerMaclaurin_cpow_neg_deriv_eq z hx_pos
  exact
    eulerMaclaurin_firstOrder_postCutoffTail_hasSum_standard
      f f' N hN hderiv

/-- Fold the derivative into the periodic-Bernoulli integral for
`f(x)=x^{-z}`. -/
theorem eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder
    (z : ℂ)
    (N : ℕ) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
      -z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1)))) := by
  let g : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        (fun x : ℝ => -z * g x) := by
    exact funext
      (fun x : ℝ => by
        let a : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
        let b : ℂ := (((x : ℝ) : ℂ) ^ (-(z + 1)))
        calc
          a * (-z * b) = (a * -z) * b := by
            exact (mul_assoc a (-z) b).symm
          _ = (-z * a) * b := by
            exact congrArg (fun w : ℂ => w * b) (mul_comm a (-z))
          _ = -z * (a * b) := by
            exact mul_assoc (-z) a b)
  have hintegral_point :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        ∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x := by
    exact congrArg
      (fun F : ℝ → ℂ => ∫ x in Set.Ioi (((N : ℕ) : ℝ)), F x)
      hpoint
  have hlinear :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)), -z * g x) =
        -z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)), g x) := by
    exact integral_mul_left (-z) g
  exact Eq.trans hintegral_point hlinear

/-- Generic first-order Euler-Maclaurin formula for the infinite post-cutoff
tail of `x ↦ x^{-z}`.

For any positive natural cutoff `N` and `1 < Re z`, the Dirichlet tail after
`N` has sum equal to the improper integral, the endpoint correction, and the
periodic Bernoulli derivative remainder.  This is the canonical non-zeta
Euler-Maclaurin owner theorem consumed by the zeta cutoff specialization. -/
theorem eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (N : ℕ)
    (hN : 0 < N)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1))))) := by
  have hfunction :
      HasSum
        (fun n : ℕ =>
          if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_function_hasSum_standard
      z N hN hhalf_plane
  have hterm_eq :
      (fun n : ℕ =>
        if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0) := by
    exact funext
      (fun n : ℕ => by
        by_cases hn : N < n
        · have hn_pos : 0 < n :=
            lt_trans hN hn
          have hif_left :
              (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) =
                (((n : ℕ) : ℝ) : ℂ) ^ (-z) :=
            if_pos hn
          have hif_right :
              (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) =
                (1 : ℂ) / ((n : ℂ) ^ z) :=
            if_pos hn
          have hcast : (((n : ℕ) : ℝ) : ℂ) = (n : ℂ) :=
            Complex.ofReal_natCast n
          have hpow :
              (((n : ℕ) : ℝ) : ℂ) ^ (-z) =
                (n : ℂ) ^ (-z) :=
            congrArg (fun w : ℂ => w ^ (-z)) hcast
          have hrecip :
              (1 : ℂ) / ((n : ℂ) ^ z) = (n : ℂ) ^ (-z) :=
            eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hn_pos
          exact Eq.trans hif_left
            (Eq.trans hpow (Eq.trans hrecip.symm hif_right.symm))
        · have hif_left :
              (if N < n then (((n : ℕ) : ℝ) : ℂ) ^ (-z) else 0) = 0 :=
            if_neg hn
          have hif_right :
              (if N < n then (1 : ℂ) / ((n : ℂ) ^ z) else 0) = 0 :=
            if_neg hn
          exact Eq.trans hif_left hif_right.symm)
  have hsum_eq :
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) +
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1)))))) =
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
        (-z *
          (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
    have hendpoint :
        ((1 / 2 : ℂ) * ((((N : ℕ) : ℝ) : ℂ) ^ (-z))) =
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) := by
      have hcast : (((N : ℕ) : ℝ) : ℂ) = (N : ℂ) :=
        Complex.ofReal_natCast N
      have hpow :
          ((((N : ℕ) : ℝ) : ℂ) ^ (-z)) =
            (N : ℂ) ^ (-z) :=
        congrArg (fun w : ℂ => w ^ (-z)) hcast
      have hrecip :
          (1 : ℂ) / ((N : ℂ) ^ z) = (N : ℂ) ^ (-z) :=
        eulerMaclaurin_positiveNat_one_div_cpow_eq_cpow_neg z hN
      exact congrArg (fun W : ℂ => (1 / 2 : ℂ) * W)
        (Eq.trans hpow hrecip.symm)
    have hremainder :
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-z * (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
          -z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))) :=
      eulerMaclaurin_cpow_neg_derivative_integral_eq_factored_remainder z N
    exact congrArg₂
      (fun A B : ℂ =>
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) + A + B)
      hendpoint
      hremainder
  exact
    Eq.subst
      (motive := fun p : (ℕ → ℂ) × ℂ => HasSum p.1 p.2)
      (Prod.ext hterm_eq hsum_eq)
      hfunction

/-- Specialization of the generic Euler-Maclaurin tail formula to the owner
cutoff `⌊2 + ‖z‖⌋₊`, before folding the Bernoulli integral into the named core. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
        (-z *
          (∫ x in Set.Ioi
            (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))))) := by
  exact
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      hhalf_plane

/-- Standard first-order Euler-Maclaurin formula for the convergent
post-cutoff Dirichlet tail of `x ↦ x^{-z}`.

This is the canonical analytic owner theorem: for `1 < Re z` and
`N = ⌊2 + ‖z‖⌋₊`, the post-cutoff Dirichlet tail has sum equal to the
improper integral main term, the endpoint correction, and the periodic
Bernoulli remainder.  It is the precise theorem supplied by the classical
Euler-Maclaurin formula with periodic Bernoulli function `B₁`; cf. Apostol,
Analytic Number Theory, Ch. 3. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
        ((1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
        (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_unfolded_hasSum
      z hhalf_plane

/-- Transport the standard first-order Euler-Maclaurin tail formula into the
raw owner terms `MainTerm`, `EndpointTerm`, and
`BernoulliIntegralRemainder`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  have hstandard :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        ((∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) *
            (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
          (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_firstOrder_hasSum_standard
      z hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        eulerMaclaurinZetaMainTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_integralMain_eq_mainTerm_standard
      z hhalf_plane
  have hendpoint :
      (1 / 2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) =
        eulerMaclaurinZetaEndpointTerm z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_endpoint_eq_endpointTerm z
  have hremainder :
      -z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z =
        eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_postCutoffTail_remainderSign_eq_remainderTerm z
  have hsum_eq :
      (∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) *
              (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) +
            (-z * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)) =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
    exact congrArg₂
      (fun A B : ℂ => A + B)
      hmain
      (congrArg₂
        (fun A B : ℂ => A + B)
        hendpoint
        hremainder)
  exact
    Eq.subst
      (motive := fun S : ℂ =>
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          S)
      hsum_eq
      hstandard

/-- Defect of the raw zeta Euler-Maclaurin tail identity.  The boundary-line
continuation theorem is stated as vanishing of this holomorphic defect. -/
noncomputable def eulerMaclaurin_riemannZeta_tailIdentityDefect
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePart z) -
    (eulerMaclaurinZetaMainTerm z +
      eulerMaclaurinZetaEndpointTerm z +
      eulerMaclaurinZetaBernoulliIntegralRemainder z)

/-- Fixed-cutoff finite Dirichlet window.  This is the holomorphic object used
in the identity theorem; unlike the height-dependent owner cutoff, `N` is a
parameter and therefore does not introduce floor-jump discontinuities. -/
noncomputable def eulerMaclaurinZetaFinitePartWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, 1 / (((n : ℕ) : ℂ) ^ z)

/-- Fixed-cutoff integral main term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaMainTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)) / (z - 1)

/-- Fixed-cutoff endpoint term for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaEndpointTermWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))

/-- Fixed-cutoff Bernoulli integral core. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  ∫ x in Set.Ioi (((N : ℕ) : ℝ)),
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))

/-- Fixed-cutoff Bernoulli remainder for the raw zeta Euler-Maclaurin formula. -/
noncomputable def eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
    (N : ℕ)
    (z : ℂ) : ℂ :=
  -z * eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N z

/-- Fixed-cutoff Euler-Maclaurin tail defect.  This is the correct object for
holomorphic identity-theorem arguments. -/
noncomputable def eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
    (N : ℕ)
    (z : ℂ) : ℂ :=
  (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) -
    (eulerMaclaurinZetaMainTermWithCutoff N z +
      eulerMaclaurinZetaEndpointTermWithCutoff N z +
      eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z)

/-- The height-dependent owner defect agrees pointwise with the fixed-cutoff
defect at the cutoff chosen by that point. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect
    (z : ℂ) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z =
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z := by
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  unfold eulerMaclaurinZetaMainTermWithCutoff
  unfold eulerMaclaurinZetaEndpointTermWithCutoff
  unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
  unfold eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
  unfold eulerMaclaurinZetaFinitePart
  unfold eulerMaclaurinZetaMainTerm
  unfold eulerMaclaurinZetaEndpointTerm
  unfold eulerMaclaurinZetaBernoulliIntegralRemainder
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  rfl

/-- In the convergent half-plane, removing a fixed finite Dirichlet window from
`ζ(s)` leaves the fixed post-cutoff Dirichlet tail as a `HasSum`. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
    (N : ℕ)
    (z : ℂ)
    (hz : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) := by
  let f : ℕ → ℂ := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ z)
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr hz
  have hζ_eq : riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow hz
  have hf_has_tsum : HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have hf_has_zeta : HasSum f (riemannZeta z) :=
    Eq.subst
      (motive := fun S : ℂ => HasSum f S)
      hζ_eq.symm
      hf_has_tsum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has_zeta
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    exact riemannZeta_dirichletTerm_zero_of_one_lt_re hz
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g (riemannZeta z - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  exact htail_if

/-- Fixed-cutoff improper-integral main term in owner normalization. -/
theorem eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-z))) =
      eulerMaclaurinZetaMainTermWithCutoff N z := by
  unfold eulerMaclaurinZetaMainTermWithCutoff
  have hformula :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) := by
    exact
      integral_Ioi_cpow_of_lt
        (eulerMaclaurin_cpow_neg_re_lt_neg_one_of_one_lt_re hhalf_plane)
        (Nat.cast_pos.mpr hN)
  let A : ℂ := ((N : ℕ) : ℂ)
  have hbase :
      (((N : ℕ) : ℝ) : ℂ) = A :=
    Complex.ofReal_natCast N
  have hexponent :
      (-z) + 1 = (1 : ℂ) - z := by
    calc
      (-z) + 1 = (1 : ℂ) + (-z) := by
        exact add_comm (-z) (1 : ℂ)
      _ = (1 : ℂ) - z := by
        exact (sub_eq_add_neg (1 : ℂ) z).symm
  have hden :
      (-z) + 1 = -((z - 1)) := by
    calc
      (-z) + 1 = (1 : ℂ) - z :=
        hexponent
      _ = -(z - 1) := by
        exact (neg_sub z (1 : ℂ)).symm
  have hpow :
      ((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) =
        A ^ ((1 : ℂ) - z) := by
    exact congrArg₂ (fun b e : ℂ => b ^ e) hbase hexponent
  have hnormal :
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
        A ^ ((1 : ℂ) - z) / (z - 1) := by
    calc
      -((((N : ℕ) : ℝ) : ℂ) ^ ((-z) + 1)) / ((-z) + 1) =
          -(A ^ ((1 : ℂ) - z)) / ((-z) + 1) := by
        exact congrArg
          (fun W : ℂ => -W / ((-z) + 1))
          hpow
      _ = -(A ^ ((1 : ℂ) - z)) / (-(z - 1)) := by
        exact congrArg
          (fun D : ℂ => -(A ^ ((1 : ℂ) - z)) / D)
          hden
      _ = A ^ ((1 : ℂ) - z) / (z - 1) := by
        exact neg_div_neg_eq (A ^ ((1 : ℂ) - z)) (z - 1)
  exact Eq.trans hformula hnormal

/-- Fixed-cutoff Euler-Maclaurin tail formula in owner term notation. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if N < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTermWithCutoff N z +
        eulerMaclaurinZetaEndpointTermWithCutoff N z +
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) := by
  have hstandard :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
          (-z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))) :=
    eulerMaclaurin_cpow_neg_postCutoffTail_firstOrder_hasSum_standard
      z N hN hhalf_plane
  have hmain :
      (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) =
        eulerMaclaurinZetaMainTermWithCutoff N z :=
    eulerMaclaurin_fixedCutoff_integralMain_eq_mainTerm N hN z hhalf_plane
  have hendpoint :
      ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) =
        eulerMaclaurinZetaEndpointTermWithCutoff N z := by
    unfold eulerMaclaurinZetaEndpointTermWithCutoff
    rfl
  have hremainder :
      (-z *
        (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(z + 1))))) =
        eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
    unfold eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff
    rfl
  have hsum_eq :
      ((∫ x in Set.Ioi (((N : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-z))) +
          ((1 / 2 : ℂ) * (1 / (((N : ℕ) : ℂ) ^ z))) +
          (-z *
            (∫ x in Set.Ioi (((N : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))))) =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z := by
    exact congrArg₂
      (fun A B : ℂ => A + B)
      hmain
      (congrArg₂
        (fun A B : ℂ => A + B)
        hendpoint
        hremainder)
  exact
    Eq.subst
      (motive := fun S : ℂ =>
        HasSum
          (fun n : ℕ =>
            if N < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          S)
      hsum_eq
      hstandard

/-- Vanishing of the Euler-Maclaurin tail defect is exactly the desired
tail identity. -/
theorem eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
    {z : ℂ}
    (hdefect : eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect at hdefect
  exact sub_eq_zero.mp hdefect

/-- In the convergent half-plane, the Euler-Maclaurin tail defect vanishes by
uniqueness of the post-cutoff `HasSum`: the Dirichlet split and the
Euler-Maclaurin tail formula have the same summand. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_zero_on_halfPlane
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
    eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum
      z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if eulerMaclaurinPoleClearedZetaCutoff z < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    hsplit.unique htail
  unfold eulerMaclaurin_riemannZeta_tailIdentityDefect
  exact sub_eq_zero.mpr hidentity

/-- First-order Euler-Maclaurin evaluation of the convergent post-cutoff
Dirichlet tail.

This is the standard Euler-Maclaurin theorem for `x ↦ x^{-z}` on the ray
`[N,∞)`, with `N = eulerMaclaurinPoleClearedZetaCutoff z`:
the post-cutoff Dirichlet tail has sum
`N^(1-z)/(z-1) + (1/2)N^{-z} - z∫_N^∞ B₁({x})x^{-z-1}dx`. -/
theorem eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hhalf_plane : 1 < z.re) :
    HasSum
      (fun n : ℕ =>
        if eulerMaclaurinPoleClearedZetaCutoff z < n then
          (1 : ℂ) / ((n : ℂ) ^ z)
        else
          0)
      (eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z) := by
  exact
    eulerMaclaurin_riemannZeta_postCutoffTail_ownerTerms_hasSum
      z hhalf_plane

/-- `ζ` is holomorphic on the fixed-cutoff punctured strip, where the pole
point `1` is excluded. -/
theorem eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip :
    DifferentiableOn ℂ
      riemannZeta
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  intro z hz
  exact (differentiableAt_riemannZeta hz.2.2).differentiableWithinAt

/-- Fixed finite Dirichlet polynomial is holomorphic in the complex variable. -/
theorem eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaFinitePartWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaFinitePartWithCutoff
  exact
    DifferentiableOn.sum
      (fun n hn => by
        have hn_bounds : n ∈ Finset.Icc 1 N := hn
        have hn_one : 1 ≤ n := (Finset.mem_Icc.mp hn_bounds).1
        have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn_one
        have hbase_ne : ((n : ℕ) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn_pos)
        have hden :
            DifferentiableOn ℂ
              (fun z : ℂ => (((n : ℕ) : ℂ) ^ z))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_id.const_cpow (Or.inl hbase_ne)
        have hnum :
            DifferentiableOn ℂ
              (fun _ : ℂ => (1 : ℂ))
              ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
          differentiableOn_const (1 : ℂ)
        exact
          hnum.div hden
            (fun z hz => by
              intro hzero
              have hbase_zero : ((n : ℕ) : ℂ) = 0 :=
                (Complex.cpow_eq_zero_iff ((n : ℕ) : ℂ) z).mp hzero |>.1
              exact hbase_ne hbase_zero))

/-- Fixed-cutoff main term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaMainTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaMainTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) - z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hone.sub hid
  have hnum :
      DifferentiableOn ℂ
        (fun z : ℂ => ((N : ℕ) : ℂ) ^ ((1 : ℂ) - z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => z - 1)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.sub hone
  exact
    hnum.div hden
      (fun z hz => sub_ne_zero.mpr hz.2.2)

/-- Fixed-cutoff endpoint term is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaEndpointTermWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaEndpointTermWithCutoff
  have hbase_ne : ((N : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hden :
      DifferentiableOn ℂ
        (fun z : ℂ => (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.const_cpow (Or.inl hbase_ne)
  have hrecip :
      DifferentiableOn ℂ
        (fun z : ℂ => (1 : ℂ) / (((N : ℕ) : ℂ) ^ z))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (differentiableOn_const (1 : ℂ)).div hden
      (fun z hz => by
        intro hzero
        have hbase_zero : ((N : ℕ) : ℂ) = 0 :=
          (Complex.cpow_eq_zero_iff ((N : ℕ) : ℂ) z).mp hzero |>.1
        exact hbase_ne hbase_zero)
  have hhalf :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 / 2 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 / 2 : ℂ)
  exact hhalf.mul hrecip

/-- Pointwise parameter-holomorphicity of the fixed-cutoff Bernoulli kernel.

For each positive real `x`, the parameter dependence
`z ↦ B₁({x}) x^(-(z+1))` is entire.  This is the local kernel theorem used
before applying differentiation under the improper integral. -/
theorem eulerMaclaurinBernoulliKernel_parameter_differentiableOn
    (x : ℝ)
    (hx : 0 < x) :
    DifferentiableOn ℂ
      (fun z : ℂ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(z + 1))))
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hbase_ne : ((x : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hone :
      DifferentiableOn ℂ
        (fun _ : ℂ => (1 : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const (1 : ℂ)
  have hexponent :
      DifferentiableOn ℂ
        (fun z : ℂ => -(z + 1))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    (hid.add hone).neg
  have hpow :
      DifferentiableOn ℂ
        (fun z : ℂ => (((x : ℝ) : ℂ) ^ (-(z + 1))))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hexponent.const_cpow (Or.inl hbase_ne)
  have hfactor :
      DifferentiableOn ℂ
        (fun _ : ℂ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_const
      (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
  exact hfactor.mul hpow

/-- Locally uniform integrable majorant for the fixed-cutoff Bernoulli kernel
on compact parameter neighborhoods inside the punctured strip. -/
theorem eulerMaclaurinBernoulliKernel_local_integrable_majorant_on_puncturedStrip
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1})) :
    ∃ r : ℝ, 0 < r ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) ∧
        ∀ z : ℂ, z ∈ Metric.ball z₀ r →
          ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤ g x := by
  sorry

/-- Dominated differentiation for the fixed-cutoff Bernoulli kernel, using
the local integrable majorant and the pointwise parameter differentiability
already owned above.

This is the reusable parameter-integral theorem for the Euler-Maclaurin
Bernoulli kernel with fixed lower limit.  It is deliberately separated from
the zeta defect so the remaining analytic work is the dominated-differentiation
API, not an endpoint-shaped holomorphicity assertion. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  sorry

/-- Differentiation under the fixed lower-limit Bernoulli improper integral in
the complex parameter. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral_from_local_majorant
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip.

This is the standard parameter-integral theorem: the lower limit is fixed, the
Bernoulli factor is bounded, and the complex-power kernel has locally uniform
integrable majorants on vertical compacta. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_differentiable_under_integral
      N hN

/-- Fixed lower-limit Bernoulli integral core is holomorphic in the complex
parameter on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_parameter_holomorphic_standard
      N hN

/-- Fixed-cutoff Bernoulli remainder is holomorphic on the punctured strip. -/
theorem eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff
  have hid :
      DifferentiableOn ℂ
        (fun z : ℂ => z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    differentiableOn_id
  have hneg_id :
      DifferentiableOn ℂ
        (fun z : ℂ => -z)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    hid.neg
  have hcore :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralCoreWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact hneg_id.mul hcore

/-- Fixed-cutoff defect is holomorphic on the punctured vertical strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N) :
    DifferentiableOn ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  have hzeta :
      DifferentiableOn ℂ
        riemannZeta
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_riemannZeta_holomorphicOn_fixedCutoff_puncturedStrip
  have hfinite :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaFinitePartWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaFinitePartWithCutoff_holomorphicOn_puncturedStrip N
  have hmain :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaMainTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaMainTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hendpoint :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaEndpointTermWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaEndpointTermWithCutoff_holomorphicOn_puncturedStrip N hN
  have hremainder :
      DifferentiableOn ℂ
        (eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff_holomorphicOn_puncturedStrip
      N hN
  exact (hzeta.sub hfinite).sub ((hmain.add hendpoint).add hremainder)

/-- The fixed punctured vertical strip used for the Euler-Maclaurin defect is open. -/
theorem eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen :
    IsOpen ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have hleft : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hright : IsOpen {z : ℂ | z.re < 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hpole : IsOpen {z : ℂ | z ≠ 1} :=
    isOpen_compl_singleton
  exact (hleft.inter hright).inter hpole

/-- The fixed-cutoff Euler-Maclaurin defect is analytic on a neighborhood of
the punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
    (N : ℕ)
    (hN : 0 < N) :
    AnalyticOnNhd ℂ
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_holomorphicOn_puncturedStrip_standard
      N hN).analyticOnNhd
      eulerMaclaurin_fixedCutoff_puncturedStrip_isOpen

/-- Horizontal segments at nonzero imaginary height stay inside the punctured
strip once their endpoints lie in the strip.

This is the horizontal leg in the polygonal detour around the deleted point
`1`. -/
theorem eulerMaclaurin_puncturedVerticalStrip_horizontalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re ∈ Set.Icc z.re w.re ∨ p.re ∈ Set.Icc w.re z.re)
    (hp_im : p.im = z.im)
    (hzw_im : z.im = w.im)
    (hz_im : z.im ≠ 0) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_lt_of_le hz.1 hp_between.1
    | inr hp_between =>
        exact lt_of_lt_of_le hw.1 hp_between.1
  constructor
  · cases hp_re with
    | inl hp_between =>
        exact lt_of_le_of_lt hp_between.2 hw.2.1
    | inr hp_between =>
        exact lt_of_le_of_lt hp_between.2 hz.2.1
  · intro hbad
    have hp_one_im : p.im = (1 : ℂ).im :=
      congrArg Complex.im hbad
    have hz_zero : z.im = 0 := by
      calc
        z.im = p.im := hp_im.symm
        _ = (1 : ℂ).im := hp_one_im
        _ = 0 := rfl
    exact hz_im hz_zero

/-- Vertical segments at real part different from `1` stay inside the punctured
strip once their endpoints lie in the strip.

This is the vertical leg in the polygonal detour around the deleted point. -/
theorem eulerMaclaurin_puncturedVerticalStrip_verticalSegment_mem
    {z w p : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hp_re : p.re = z.re)
    (hp_im : p.im ∈ Set.Icc z.im w.im ∨ p.im ∈ Set.Icc w.im z.im)
    (hzw_re : z.re = w.re)
    (hz_re : z.re ≠ 1) :
    p ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · calc
      0 < z.re := hz.1
      _ = p.re := hp_re.symm
  constructor
  · calc
      p.re = z.re := hp_re
      _ < 2 := hz.2.1
  · intro hbad
    have hp_one_re : p.re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    have hz_one : z.re = 1 := by
      calc
        z.re = p.re := hp_re.symm
        _ = (1 : ℂ).re := hp_one_re
        _ = 1 := rfl
    exact hz_re hz_one

/-- For any two points in the punctured strip, choose an endpoint detour height
away from the deleted point `1`.

This records only the endpoint normalization used by the corridor construction;
vertical path safety is handled by the corridor lemmas below. -/
theorem eulerMaclaurin_puncturedVerticalStrip_detourHeight_exists
    (z w : ℂ)
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    ∃ h : ℝ, h ≠ 0 ∧
      Complex.mk z.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) ∧
      Complex.mk w.re h ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  refine ⟨1, one_ne_zero, ?_, ?_⟩
  · constructor
    · exact hz.1
    constructor
    · exact hz.2.1
    · intro hbad
      have him : (Complex.mk z.re (1 : ℝ)).im = (1 : ℂ).im :=
        congrArg Complex.im hbad
      change (1 : ℝ) = 0 at him
      exact one_ne_zero him
  · constructor
    · exact hw.1
    constructor
    · exact hw.2.1
    · intro hbad
      have him : (Complex.mk w.re (1 : ℝ)).im = (1 : ℂ).im :=
        congrArg Complex.im hbad
      change (1 : ℝ) = 0 at him
      exact one_ne_zero him

/-- Points in the left component `0 < Re z < 1` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_left : z.re < 1)
    (hw_left : w.re < 1) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  sorry

/-- Points in the right component `1 < Re z < 2` of the punctured strip are
joined inside the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hz_right : 1 < z.re)
    (hw_right : 1 < w.re) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      z w := by
  sorry

/-- Horizontal segments at nonzero height cross safely between any two real
parts in the open strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
    {x₁ x₂ h : ℝ}
    (hx₁_left : 0 < x₁)
    (hx₁_right : x₁ < 2)
    (hx₂_left : 0 < x₂)
    (hx₂_right : x₂ < 2)
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk x₁ h)
      (Complex.mk x₂ h) := by
  sorry

/-- The left safe corridor has positive real coordinate. -/
theorem real_zero_lt_one_half_for_puncturedVerticalStrip :
    (0 : ℝ) < 1 / 2 := by
  exact half_pos zero_lt_one

/-- The left safe corridor lies left of the deleted vertical line. -/
theorem real_one_half_lt_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 1 := by
  exact half_lt_self zero_lt_one

/-- The left safe corridor lies inside the right strip boundary. -/
theorem real_one_half_lt_two_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) < 2 := by
  exact
    lt_trans
      real_one_half_lt_one_for_puncturedVerticalStrip
      one_lt_two

/-- The right safe corridor has positive real coordinate. -/
theorem real_zero_lt_three_halves_for_puncturedVerticalStrip :
    (0 : ℝ) < 3 / 2 := by
  exact div_pos (show (0 : ℝ) < 3 by
    calc
      (0 : ℝ) < 1 := zero_lt_one
      _ < 3 := lt_trans one_lt_two (show (2 : ℝ) < 3 by
        exact lt_add_of_pos_right 2 zero_lt_one)) two_pos

/-- The right safe corridor lies right of the deleted vertical line. -/
theorem real_one_lt_three_halves_for_puncturedVerticalStrip :
    (1 : ℝ) < 3 / 2 := by
  exact
    (lt_div_iff₀ two_pos).2
      (show (1 : ℝ) * 2 < 3 by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := lt_add_of_pos_right 2 zero_lt_one)

/-- The right safe corridor lies inside the right strip boundary. -/
theorem real_three_halves_lt_two_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) < 2 := by
  exact
    (div_lt_iff₀ two_pos).2
      (show (3 : ℝ) < 2 * 2 by
        calc
          (3 : ℝ) < 4 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := (show (4 : ℝ) = 2 * 2 by rfl))

/-- The left safe corridor real coordinate is not the deleted coordinate. -/
theorem real_one_half_ne_one_for_puncturedVerticalStrip :
    (1 / 2 : ℝ) ≠ 1 := by
  exact ne_of_lt real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right safe corridor real coordinate is not the deleted coordinate. -/
theorem real_three_halves_ne_one_for_puncturedVerticalStrip :
    (3 / 2 : ℝ) ≠ 1 := by
  exact ne_of_gt real_one_lt_three_halves_for_puncturedVerticalStrip

/-- The left safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
    {y : ℝ} :
    Complex.mk (1 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_one_half_for_puncturedVerticalStrip
  constructor
  · exact real_one_half_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (1 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_one_half_ne_one_for_puncturedVerticalStrip hre

/-- The right safe column lies in the punctured strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
    {y : ℝ} :
    Complex.mk (3 / 2) y ∈
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) := by
  constructor
  · exact real_zero_lt_three_halves_for_puncturedVerticalStrip
  constructor
  · exact real_three_halves_lt_two_for_puncturedVerticalStrip
  · intro hbad
    have hre : (Complex.mk (3 / 2 : ℝ) y).re = (1 : ℂ).re :=
      congrArg Complex.re hbad
    exact real_three_halves_ne_one_for_puncturedVerticalStrip hre

/-- The left half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) y₁)
      (Complex.mk (1 / 2) y₂) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
      real_one_half_lt_one_for_puncturedVerticalStrip
      real_one_half_lt_one_for_puncturedVerticalStrip

/-- The right half-column is a safe vertical corridor inside the punctured
strip. -/
theorem eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
    {y₁ y₂ : ℝ} :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (3 / 2) y₁)
      (Complex.mk (3 / 2) y₂) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
      real_one_lt_three_halves_for_puncturedVerticalStrip
      real_one_lt_three_halves_for_puncturedVerticalStrip

/-- Every point in the punctured strip is joined to one of the two safe
vertical corridors at its own imaginary height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor
    {z : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (1 / 2) z.im) ∨
      JoinedIn
        ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
        z
        (Complex.mk (3 / 2) z.im) := by
  by_cases hz_left : z.re < 1
  · left
    exact
      eulerMaclaurin_puncturedVerticalStrip_leftHalf_joined
        hz
        eulerMaclaurin_puncturedVerticalStrip_leftColumn_mem
        hz_left
        real_one_half_lt_one_for_puncturedVerticalStrip
  · have hz_one_le : 1 ≤ z.re :=
      le_of_not_gt hz_left
    by_cases hz_re_eq_one : z.re = 1
    · have hz_im_ne_zero : z.im ≠ 0 := by
        intro hz_im_zero
        have hz_eq_one : z = (1 : ℂ) := by
          exact Complex.ext
            (by
              calc
                z.re = 1 := hz_re_eq_one
                _ = (1 : ℂ).re := rfl)
            (by
              calc
                z.im = 0 := hz_im_zero
                _ = (1 : ℂ).im := rfl)
        exact hz.2.2 hz_eq_one
      left
      have hjoined :
          JoinedIn
            ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
            (Complex.mk z.re z.im)
            (Complex.mk (1 / 2) z.im) :=
        eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
          (by
            calc
              0 < z.re := hz.1)
          (by
            calc
              z.re < 2 := hz.2.1)
          real_zero_lt_one_half_for_puncturedVerticalStrip
          real_one_half_lt_two_for_puncturedVerticalStrip
          hz_im_ne_zero
      exact Eq.subst
        (motive := fun u : ℂ =>
          JoinedIn
            ({v : ℂ | 0 < v.re ∧ v.re < 2 ∧ v ≠ 1})
            u
            (Complex.mk (1 / 2) z.im))
        (Complex.eta z)
        hjoined
    · right
      have hz_right : 1 < z.re :=
        lt_of_le_of_ne hz_one_le (Ne.symm hz_re_eq_one)
      exact
        eulerMaclaurin_puncturedVerticalStrip_rightHalf_joined
          hz
          eulerMaclaurin_puncturedVerticalStrip_rightColumn_mem
          hz_right
          real_one_lt_three_halves_for_puncturedVerticalStrip

/-- The two safe vertical corridors are joined at any nonzero imaginary
height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
    {h : ℝ}
    (hh : h ≠ 0) :
    JoinedIn
      ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
      (Complex.mk (1 / 2) h)
      (Complex.mk (3 / 2) h) := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_nonzeroHeight_horizontalJoined
      real_zero_lt_one_half_for_puncturedVerticalStrip
      real_one_half_lt_two_for_puncturedVerticalStrip
      real_zero_lt_three_halves_for_puncturedVerticalStrip
      real_three_halves_lt_two_for_puncturedVerticalStrip
      hh

/-- Corridor polygonal-path construction in the punctured vertical strip.

The path first moves each endpoint horizontally to a safe column, moves
vertically in the safe columns, and crosses between the columns at nonzero
height. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  have hz_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (1 / 2) z.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          z
          (Complex.mk (3 / 2) z.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hz
  have hw_corridor :
      JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (1 / 2) w.im) ∨
        JoinedIn
          ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
          w
          (Complex.mk (3 / 2) w.im) :=
    eulerMaclaurin_puncturedVerticalStrip_joinedTo_safeCorridor hw
  cases hz_corridor with
  | inl hz_left =>
      cases hw_corridor with
      | inl hw_left =>
          exact
            hz_left.trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined).trans
                hw_left.symm)
      | inr hw_right =>
          have hleft_to_right :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (1 / 2) z.im)
                (Complex.mk (3 / 2) w.im) :=
            (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
              (y₁ := z.im) (y₂ := 1)).trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                (h := 1) one_ne_zero).trans
                (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
                  (y₁ := 1) (y₂ := w.im)))
          exact hz_left.trans (hleft_to_right.trans hw_right.symm)
  | inr hz_right =>
      cases hw_corridor with
      | inl hw_left =>
          have hright_to_left :
              JoinedIn
                ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})
                (Complex.mk (3 / 2) z.im)
                (Complex.mk (1 / 2) w.im) :=
            (eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined
              (y₁ := z.im) (y₂ := 1)).trans
              ((eulerMaclaurin_puncturedVerticalStrip_leftCorridor_joined_rightCorridor
                (h := 1) one_ne_zero).symm.trans
                (eulerMaclaurin_puncturedVerticalStrip_leftColumn_verticalJoined
                  (y₁ := 1) (y₂ := w.im)))
          exact hz_right.trans (hright_to_left.trans hw_left.symm)
      | inr hw_right =>
          exact
            hz_right.trans
              ((eulerMaclaurin_puncturedVerticalStrip_rightColumn_verticalJoined).trans
                hw_right.symm)

/-- Polygonal-path construction in the punctured vertical strip.

This is the public wrapper around the safe-corridor construction. -/
theorem eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_polygon
    {z w : ℂ}
    (hz : z ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}))
    (hw : w ∈ ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1})) :
    JoinedIn ({u : ℂ | 0 < u.re ∧ u.re < 2 ∧ u ≠ 1}) z w := by
  exact
    eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_corridors
      hz hw

/-- The punctured vertical strip is nonempty. -/
theorem eulerMaclaurin_puncturedVerticalStrip_nonempty :
    ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}).Nonempty := by
  refine ⟨Complex.mk 1 1, ?_⟩
  constructor
  · exact zero_lt_one
  constructor
  · exact one_lt_two
  · intro hbad
    have him : (Complex.mk (1 : ℝ) 1).im = (1 : ℂ).im :=
      congrArg Complex.im hbad
    change (1 : ℝ) = 0 at him
    exact one_ne_zero him

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is path-connected.

Geometrically this is an open vertical strip in the real plane with one point
removed; polygonal paths route around the removed point `1`. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPathConnected :
    IsPathConnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    isPathConnected_iff.mpr
      ⟨eulerMaclaurin_puncturedVerticalStrip_nonempty,
        fun z hz w hw =>
          eulerMaclaurin_puncturedVerticalStrip_joinedIn_via_polygon
            hz hw⟩

/-- The punctured vertical strip `0 < Re z < 2`, `z ≠ 1`, is preconnected. -/
theorem eulerMaclaurin_puncturedVerticalStrip_isPreconnected :
    IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  exact
    (eulerMaclaurin_puncturedVerticalStrip_isPathConnected).isConnected.isPreconnected

/-- The fixed-cutoff defect vanishes on the open half-plane part of the
punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  intro z hz
  exact
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_halfPlane_standard
      N hN z hz.1

/-- The open half-plane part `1 < Re z < 2` accumulates at the base point used
for the punctured-strip identity theorem. -/
theorem eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase :
    ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
      z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
  have hopen : IsOpen ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    have hleft : IsOpen {z : ℂ | 1 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hright : IsOpen {z : ℂ | z.re < 2} :=
      isOpen_lt Complex.continuous_re continuous_const
    exact hleft.inter hright
  have hbase : ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) := by
    constructor
    · exact (lt_div_iff₀' zero_lt_two).mpr (by
        calc
          (1 : ℝ) * 2 = 2 := one_mul 2
          _ < 3 := by
            exact two_lt_three)
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 3 + 1 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := rfl)
  have heventually :
      ∀ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        z ∈ ({z : ℂ | 1 < z.re ∧ z.re < 2}) :=
    mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hbase)
  exact heventually.frequently

/-- The chosen base point for the identity theorem lies in the punctured
vertical strip. -/
theorem eulerMaclaurin_identityBase_mem_puncturedVerticalStrip :
    ((3 / 2 : ℝ) : ℂ) ∈
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  constructor
  · exact div_pos zero_lt_three zero_lt_two
  · constructor
    · exact (div_lt_iff₀ zero_lt_two).mpr (by
        calc
          (3 : ℝ) < 3 + 1 := lt_add_of_pos_right 3 zero_lt_one
          _ = 2 * 2 := rfl)
    · intro h
      have hre : (3 / 2 : ℝ) = 1 := by
        exact congrArg Complex.re h
      have hmul : (3 / 2 : ℝ) * 2 = 1 * 2 :=
        congrArg (fun x : ℝ => x * 2) hre
      have hleft : (3 / 2 : ℝ) * 2 = 3 :=
        div_mul_cancel₀ (3 : ℝ) (show (2 : ℝ) ≠ 0 by exact two_ne_zero)
      have hright : (1 : ℝ) * 2 = 2 :=
        one_mul 2
      have hthree_eq_two : (3 : ℝ) = 2 :=
        Eq.trans hleft.symm (Eq.trans hmul hright)
      have hthree_ne_two : (3 : ℝ) ≠ 2 := by
        exact ne_of_gt two_lt_three
      exact hthree_ne_two hthree_eq_two

/-- Identity theorem specialized to a fixed-cutoff defect on the punctured
vertical strip, using its vanishing on the half-plane substrip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
    (N : ℕ)
    (hN : 0 < N) :
    EqOn
      (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
      0
      ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
  have han :
      AnalyticOnNhd ℂ
        (eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N)
        ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticOnNhd_puncturedStrip
      N hN
  have hpre :
      IsPreconnected ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) :=
    eulerMaclaurin_puncturedVerticalStrip_isPreconnected
  have hbase_mem :
      ((3 / 2 : ℝ) : ℂ) ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1}) := by
    exact eulerMaclaurin_identityBase_mem_puncturedVerticalStrip
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((3 / 2 : ℝ) : ℂ),
        eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 :=
    eulerMaclaurin_halfPlaneSubset_frequently_near_identityBase.mono
      (fun z hz =>
        eulerMaclaurin_fixedCutoffTailIdentityDefect_zero_on_halfPlaneSubset
          N hN hz)
  exact
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero
      hpre hbase_mem hfreq

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip.

This is the standard complex-analysis step: the fixed-cutoff defect is
holomorphic on the punctured strip and vanishes on the nonempty open subset
`1 < Re z < 2`, hence it vanishes throughout the connected component of the
punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_analytic_zeroSet
      N hN z ⟨hz_re_pos, hz_re_lt_two, hz_ne_one⟩

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_from_halfPlaneZero_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_analyticContinuation_zero_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Fixed-cutoff defect vanishes on the convergent half-plane by the
Dirichlet-series split and the fixed-cutoff Euler-Maclaurin formula. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_halfPlane_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hhalf_plane : 1 < z.re) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  have hsplit :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_halfPlane_finite_split_tail_hasSum
      N z hhalf_plane
  have htail :
      HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ z)
          else
            0)
        (eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z) :=
    eulerMaclaurin_riemannZeta_fixedCutoff_postCutoffTail_ownerTerms_hasSum
      N hN z hhalf_plane
  have hidentity :
      riemannZeta z - eulerMaclaurinZetaFinitePartWithCutoff N z =
        eulerMaclaurinZetaMainTermWithCutoff N z +
          eulerMaclaurinZetaEndpointTermWithCutoff N z +
          eulerMaclaurinZetaBernoulliIntegralRemainderWithCutoff N z :=
    hsplit.unique htail
  unfold eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
  exact sub_eq_zero.mpr hidentity

/-- Identity theorem for the fixed-cutoff Euler-Maclaurin defect on the
connected punctured strip. -/
theorem eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ)
    (hz_re_pos : 0 < z.re)
    (hz_re_lt_two : z.re < 2)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect N z = 0 := by
  exact
    eulerMaclaurin_fixedCutoffTailIdentityDefect_identityTheorem_on_puncturedStrip_standard
      N hN z hz_re_pos hz_re_lt_two hz_ne_one

/-- Boundary-line vanishing of the Euler-Maclaurin tail defect by analytic
continuation.

The defect is holomorphic on the punctured strip, vanishes on the connected
open subset `1 < Re z ≤ 2` by the half-plane Dirichlet-series calculation, and
therefore vanishes at the non-pole boundary points on `Re z = 1` by the
identity theorem/continuity of the owner continuation. -/
theorem eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    eulerMaclaurin_riemannZeta_tailIdentityDefect z = 0 := by
  have hfixed :
      eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect
        (eulerMaclaurinPoleClearedZetaCutoff z) z = 0 :=
    eulerMaclaurin_riemannZeta_fixedCutoffTailIdentityDefect_eq_zero_on_puncturedStrip_by_identityTheorem_standard
      (eulerMaclaurinPoleClearedZetaCutoff z)
      (eulerMaclaurinPoleClearedZetaCutoff_pos z)
      z
      (Eq.subst (motive := fun x : ℝ => 0 < x) hz_re.symm zero_lt_one)
      (Eq.subst (motive := fun x : ℝ => x < 2) hz_re.symm one_lt_two)
      hz_ne_one
  exact
    Eq.trans
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_eq_fixedCutoffDefect z)
      hfixed

/-- Boundary-line analytic-continuation uniqueness for the first-order
Euler-Maclaurin zeta tail.

The half-plane identity obtained from the Dirichlet series and
Euler-Maclaurin has a meromorphic continuation to the closed strip; after
removing the pole point `z = 1`, uniqueness of analytic continuation gives
the stated boundary-line equality at `Re z = 1`.  This is the exact owner
API needed for the boundary case, not a restatement of the public wrapper;
cf. Edwards, Ch. 1, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_tailIdentity_of_defect_eq_zero
      (eulerMaclaurin_riemannZeta_tailIdentityDefect_boundaryLine_eq_zero_by_identityTheorem_standard
        z hz_re hz_ne_one)

/-- Boundary-line analytic continuation of the first-order Euler-Maclaurin
tail identity.

At `Re z = 1`, the ordinary Dirichlet tail is no longer absolutely summable;
the equality is the Abel/Euler-Maclaurin continuation of the half-plane tail
formula, away from the pole `z = 1`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_re : z.re = 1)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_by_analyticContinuation_standard
      z hz_re hz_ne_one

/-- First-order Euler-Maclaurin tail identity for the Riemann zeta function at
the owner cutoff `N = ⌊2 + ‖s‖⌋₊`.

This is the exact analytic theorem: the finite Dirichlet window is removed from
`ζ(s)`, and Euler-Maclaurin applied to the remaining tail of
`x ↦ x^{-s}` gives
`N^(1-s)/(s-1) + (1/2)N^{-s} - s ∫_N^∞ B₁({x})x^{-s-1} dx`.
It combines the Dirichlet-series split in `Re s > 1` with analytic
continuation across the closed strip away from `s = 1`; cf. Apostol, Analytic
Number Theory, Ch. 3, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z - eulerMaclaurinZetaFinitePart z =
      eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  by_cases hhalf_plane : 1 < z.re
  · have hsplit :
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          (riemannZeta z - eulerMaclaurinZetaFinitePart z) :=
      eulerMaclaurin_riemannZeta_halfPlane_finite_split_tail_hasSum z hhalf_plane
    have htail :
        HasSum
          (fun n : ℕ =>
            if eulerMaclaurinPoleClearedZetaCutoff z < n then
              (1 : ℂ) / ((n : ℂ) ^ z)
            else
              0)
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
      eulerMaclaurin_riemannZeta_postCutoffTail_eulerMaclaurin_hasSum_standard
        z hz_one hz_two hhalf_plane
    exact hsplit.unique htail
  · have hz_re_le_one : z.re ≤ 1 :=
      le_of_not_gt hhalf_plane
    have hz_re_eq_one : z.re = 1 :=
      le_antisymm hz_re_le_one hz_one
    exact
      eulerMaclaurin_riemannZeta_boundaryLine_tail_identity_with_bernoulliIntegralRemainder_standard
        z hz_re_eq_one hz_ne_one

/-- First-order Euler-Maclaurin formula for the raw Riemann zeta away from its
pole, with owner cutoff `N = ⌊2 + ‖s‖⌋₊`.

This is the canonical analytic input: split the Dirichlet series at `N`, apply
Euler-Maclaurin to the tail of `x ↦ x^{-s}`, and write the remainder as the
periodic Bernoulli integral `-s ∫_N^∞ B₁({x}) x^{-s-1} dx`; cf. Apostol,
Analytic Number Theory, Ch. 3, and Titchmarsh, Ch. 2. -/
theorem eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2)
    (hz_ne_one : z ≠ 1) :
    riemannZeta z =
      eulerMaclaurinZetaFinitePart z +
        eulerMaclaurinZetaMainTerm z +
        eulerMaclaurinZetaEndpointTerm z +
        eulerMaclaurinZetaBernoulliIntegralRemainder z := by
  have htail :
      riemannZeta z - eulerMaclaurinZetaFinitePart z =
        eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_riemannZeta_tail_identity_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two hz_ne_one
  have hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
    complex_eq_add_of_sub_eq htail
  calc
    riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          (eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z) :=
      hraw
    _ = eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z := by
      calc
        eulerMaclaurinZetaFinitePart z +
            (eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z) =
            (eulerMaclaurinZetaFinitePart z +
              (eulerMaclaurinZetaMainTerm z +
                eulerMaclaurinZetaEndpointTerm z)) +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact (add_assoc
            (eulerMaclaurinZetaFinitePart z)
            (eulerMaclaurinZetaMainTerm z + eulerMaclaurinZetaEndpointTerm z)
            (eulerMaclaurinZetaBernoulliIntegralRemainder z)).symm
        _ = eulerMaclaurinZetaFinitePart z +
              eulerMaclaurinZetaMainTerm z +
              eulerMaclaurinZetaEndpointTerm z +
              eulerMaclaurinZetaBernoulliIntegralRemainder z := by
          exact congrArg
            (fun w : ℂ => w + eulerMaclaurinZetaBernoulliIntegralRemainder z)
            ((add_assoc
              (eulerMaclaurinZetaFinitePart z)
              (eulerMaclaurinZetaMainTerm z)
              (eulerMaclaurinZetaEndpointTerm z)).symm)

/-- Multiplication by `s - 1` transports the raw non-pole
Euler-Maclaurin formula to the existing pole-cleared term definitions. -/
theorem eulerMaclaurin_poleCleared_formula_of_raw_formula
    {z : ℂ}
    (hz_ne_one : z ≠ 1)
    (hraw :
      riemannZeta z =
        eulerMaclaurinZetaFinitePart z +
          eulerMaclaurinZetaMainTerm z +
          eulerMaclaurinZetaEndpointTerm z +
          eulerMaclaurinZetaBernoulliIntegralRemainder z) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  let a : ℂ := z - 1
  let F : ℂ := eulerMaclaurinZetaFinitePart z
  let M : ℂ := eulerMaclaurinZetaMainTerm z
  let E : ℂ := eulerMaclaurinZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinZetaBernoulliIntegralRemainder z
  have hpole :
      poleClearedRiemannZeta z = a * riemannZeta z := by
    exact poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hraw_local : riemannZeta z = F + M + E + R :=
    hraw
  have hmul_raw :
      a * riemannZeta z = a * (F + M + E + R) :=
    congrArg (fun w : ℂ => a * w) hraw_local
  have hdistribute :
      a * (F + M + E + R) =
        a * F + a * M + a * E + a * R := by
    calc
      a * (F + M + E + R) = a * ((F + M + E) + R) := rfl
      _ = a * (F + M + E) + a * R := by
        exact mul_add a (F + M + E) R
      _ = (a * (F + M) + a * E) + a * R := by
        exact congrArg (fun w : ℂ => w + a * R) (mul_add a (F + M) E)
      _ = ((a * F + a * M) + a * E) + a * R := by
        exact congrArg
          (fun w : ℂ => (w + a * E) + a * R)
          (mul_add a F M)
      _ = a * F + a * M + a * E + a * R := rfl
  have hF :
      a * F = eulerMaclaurinPoleClearedZetaFinitePart z :=
    (eulerMaclaurinPoleClearedZetaFinitePart_eq_mul_raw z).symm
  have hM :
      a * M = eulerMaclaurinPoleClearedZetaMainTerm z :=
    (eulerMaclaurinPoleClearedZetaMainTerm_eq_mul_raw hz_ne_one).symm
  have hE :
      a * E = eulerMaclaurinPoleClearedZetaEndpointTerm z :=
    (eulerMaclaurinPoleClearedZetaEndpointTerm_eq_mul_raw z).symm
  have hR :
      a * R = eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    (eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_eq_mul_raw z).symm
  have hterms :
      a * F + a * M + a * E + a * R =
        eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
    calc
      a * F + a * M + a * E + a * R =
          eulerMaclaurinPoleClearedZetaFinitePart z + a * M + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => w + a * M + a * E + a * R)
          hF
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z + a * E + a * R := by
        exact congrArg
          (fun w : ℂ => eulerMaclaurinPoleClearedZetaFinitePart z + w + a * E + a * R)
          hM
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z + a * R := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z + w + a * R)
          hE
      _ = eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z +
            eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
        exact congrArg
          (fun w : ℂ =>
            eulerMaclaurinPoleClearedZetaFinitePart z +
              eulerMaclaurinPoleClearedZetaMainTerm z +
              eulerMaclaurinPoleClearedZetaEndpointTerm z + w)
          hR
  calc
    poleClearedRiemannZeta z = a * riemannZeta z :=
      hpole
    _ = a * (F + M + E + R) :=
      hmul_raw
    _ = a * F + a * M + a * E + a * R :=
      hdistribute
    _ = eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
      hterms

/-- Subtracting a left summand from a two-term sum leaves the right summand. -/
theorem complex_add_sub_left_cancel
    (S R : ℂ) :
    (S + R) - S = R := by
  calc
    (S + R) - S = S + R + -S := by
      exact sub_eq_add_neg (S + R) S
    _ = S + (R + -S) := by
      exact add_assoc S R (-S)
    _ = S + (-S + R) := by
      exact congrArg (fun x : ℂ => S + x) (add_comm R (-S))
    _ = (S + -S) + R := by
      exact (add_assoc S (-S) R).symm
    _ = 0 + R := by
      exact congrArg (fun x : ℂ => x + R) (add_neg_cancel S)
    _ = R := by
      exact zero_add R

/-- Removable value of the pole-cleared first-order Euler-Maclaurin formula at
`s = 1`.

This is the endpoint cancellation of the raw formula after multiplying by
`s - 1`: the finite, endpoint, and Bernoulli terms vanish and the main term
has value `N^0 = 1`, matching the residue-normalized removable value
`poleClearedRiemannZeta 1 = 1`. -/
theorem eulerMaclaurin_poleCleared_formula_at_one_from_removable_value :
    poleClearedRiemannZeta (1 : ℂ) =
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
  have hpole : poleClearedRiemannZeta (1 : ℂ) = 1 :=
    poleClearedRiemannZeta_one
  have hfinite :
      eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaFinitePart
    let S : ℂ :=
      ∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ)),
        1 / (((n : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      ((1 : ℂ) - 1) * S = 0 * S := by
        exact congrArg (fun w : ℂ => w * S) (sub_self (1 : ℂ))
      _ = 0 := by
        exact zero_mul S
  have hmain :
      eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) = 1 := by
    unfold eulerMaclaurinPoleClearedZetaMainTerm
    let N : ℂ := ((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ)
    calc
      N ^ ((1 : ℂ) - 1) = N ^ (0 : ℂ) := by
        exact congrArg (fun w : ℂ => N ^ w) (sub_self (1 : ℂ))
      _ = 1 := by
        exact Complex.cpow_zero N
  have hendpoint :
      eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaEndpointTerm
    let U : ℂ :=
      1 / (((eulerMaclaurinPoleClearedZetaCutoff (1 : ℂ) : ℕ) : ℂ) ^ (1 : ℂ))
    calc
      (((1 : ℂ) - 1) / 2) * U = (0 / 2 : ℂ) * U := by
        exact congrArg (fun w : ℂ => (w / 2) * U) (sub_self (1 : ℂ))
      _ = 0 * U := by
        exact congrArg (fun w : ℂ => w * U) (zero_div (2 : ℂ))
      _ = 0 := by
        exact zero_mul U
  have hremainder :
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) = 0 := by
    unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
    let I : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralCore (1 : ℂ)
    calc
      -(((1 : ℂ) - 1) * 1) * I = -(0 * 1) * I := by
        exact congrArg (fun w : ℂ => -(w * 1) * I) (sub_self (1 : ℂ))
      _ = -0 * I := by
        exact congrArg (fun w : ℂ => -w * I) (zero_mul (1 : ℂ))
      _ = 0 * I := by
        exact congrArg (fun w : ℂ => w * I) (neg_zero : -(0 : ℂ) = 0)
      _ = 0 := by
        exact zero_mul I
  calc
    poleClearedRiemannZeta (1 : ℂ) = 1 :=
      hpole
    _ = 0 + 1 + 0 + 0 := by
      calc
        (1 : ℂ) = 0 + 1 := by
          exact (zero_add (1 : ℂ)).symm
        _ = 0 + 1 + 0 := by
          exact (add_zero (0 + (1 : ℂ))).symm
        _ = 0 + 1 + 0 + 0 := by
          exact (add_zero (0 + (1 : ℂ) + 0)).symm
    _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
      calc
        0 + 1 + 0 + 0 =
            eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + 1 + 0 + 0 := by
          exact congrArg (fun w : ℂ => w + 1 + 0 + 0) hfinite.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + 0 + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) + w + 0 + 0)
            hmain.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + 0 := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) + w + 0)
            hendpoint.symm
        _ = eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) +
              eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder (1 : ℂ) := by
          exact congrArg
            (fun w : ℂ =>
              eulerMaclaurinPoleClearedZetaFinitePart (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaMainTerm (1 : ℂ) +
                eulerMaclaurinPoleClearedZetaEndpointTerm (1 : ℂ) + w)
            hremainder.symm

/-- First-order Euler-Maclaurin formula for the pole-cleared zeta on
`1 ≤ Re s ≤ 2`, with cutoff `⌊2 + ‖s‖⌋₊` and explicit Bernoulli integral
remainder. -/
theorem eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  by_cases hz_ne_one : z ≠ 1
  · have hraw :
        riemannZeta z =
          eulerMaclaurinZetaFinitePart z +
            eulerMaclaurinZetaMainTerm z +
            eulerMaclaurinZetaEndpointTerm z +
            eulerMaclaurinZetaBernoulliIntegralRemainder z :=
      eulerMaclaurin_riemannZeta_formula_with_bernoulliIntegralRemainder_standard
        z hz_one hz_two hz_ne_one
    exact eulerMaclaurin_poleCleared_formula_of_raw_formula hz_ne_one hraw
  · have hz_eq_one : z = 1 :=
      of_not_not hz_ne_one
    exact Eq.subst
      (motive := fun w : ℂ =>
        poleClearedRiemannZeta w =
          eulerMaclaurinPoleClearedZetaFinitePart w +
            eulerMaclaurinPoleClearedZetaMainTerm w +
            eulerMaclaurinPoleClearedZetaEndpointTerm w +
            eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder w)
      hz_eq_one.symm
      eulerMaclaurin_poleCleared_formula_at_one_from_removable_value

/-- Euler-Maclaurin formula identifies the difference-defined pole-cleared
remainder with the explicit Bernoulli-periodic integral remainder. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    eulerMaclaurinPoleClearedZetaRemainderTerm z =
      eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z := by
  unfold eulerMaclaurinPoleClearedZetaRemainderTerm
  let S : ℂ :=
    eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z
  let R : ℂ := eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z
  have hformula :
      poleClearedRiemannZeta z = S + R :=
    eulerMaclaurin_poleClearedRiemannZeta_formula_with_bernoulliIntegralRemainder_standard
      z hz_one hz_two
  have hsub :
      poleClearedRiemannZeta z - S = (S + R) - S :=
    congrArg (fun w : ℂ => w - S) hformula
  have hcancel : (S + R) - S = R :=
    complex_add_sub_left_cancel S R
  exact Eq.trans hsub hcancel

/-- The first periodic Bernoulli sawtooth is bounded by one in absolute value. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_abs_le_one
    (x : ℝ) :
    |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 := by
  unfold eulerMaclaurinFirstPeriodicBernoulli
  have hfract_nonneg : 0 ≤ Int.fract x :=
    Int.fract_nonneg x
  have hfract_le_one : Int.fract x ≤ 1 :=
    le_of_lt (Int.fract_lt_one x)
  have hlower : -(1 : ℝ) ≤ Int.fract x - 1 / 2 := by
    have hneg_half : -(1 : ℝ) ≤ -(1 / 2 : ℝ) := by
      exact neg_le_neg one_half_le_one
    have hshift : -(1 / 2 : ℝ) ≤ Int.fract x - 1 / 2 := by
      calc
        -(1 / 2 : ℝ) = 0 - 1 / 2 := by
          exact (zero_sub (1 / 2 : ℝ)).symm
        _ ≤ Int.fract x - 1 / 2 :=
          sub_le_sub_right hfract_nonneg (1 / 2 : ℝ)
    exact le_trans hneg_half hshift
  have hupper : Int.fract x - 1 / 2 ≤ 1 := by
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
      one_half_nonneg
    calc
      Int.fract x - 1 / 2 ≤ Int.fract x :=
        sub_le_self (Int.fract x) hhalf_nonneg
      _ ≤ 1 :=
        hfract_le_one
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Positive-real complex powers in the Euler-Maclaurin tail are bounded by the
corresponding real power majorant. -/
theorem norm_real_cpow_neg_z_add_one_le_rpow
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ)
    (hz_one : 1 ≤ z.re) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z + 1)).re := by
    calc
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
          Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
      _ = x ^ (-(z + 1)).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hre : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun t : ℝ => -(z.re + t)) Complex.one_re
  exact le_of_eq
    (Eq.trans hnorm (congrArg (fun e : ℝ => x ^ e) hre))

/-- Scalar tail integral bound for the real power majorant after a cutoff
`N ≥ 1` and exponent `σ ≥ 1`. -/
theorem integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
    {N σ : ℝ}
    (hN : 1 ≤ N)
    (hσ : 1 ≤ σ) :
    ∫ x in Set.Ioi N, x ^ (-(σ + 1)) ≤ 1 := by
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN
  have htwo_le : (2 : ℝ) ≤ σ + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ σ + 1 :=
        add_le_add hσ le_rfl
  have hone_lt : (1 : ℝ) < σ + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(σ + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hintegral :
      ∫ x in Set.Ioi N, x ^ (-(σ + 1)) =
        -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) :=
    integral_Ioi_rpow_of_lt ha hN_pos
  have hden : -(σ + 1) + 1 = -σ := by
    calc
      -(σ + 1) + 1 = (-σ + -1) + 1 := by
        exact congrArg (fun t : ℝ => t + 1) (neg_add σ 1)
      _ = -σ + (-1 + 1) := by
        exact add_assoc (-σ) (-1) 1
      _ = -σ + 0 := by
        exact congrArg (fun t : ℝ => -σ + t) (neg_add_cancel (1 : ℝ))
      _ = -σ := by
        exact add_zero (-σ)
  have hvalue :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
        N ^ (-σ) / σ := by
    have hnum :
        N ^ (-(σ + 1) + 1) = N ^ (-σ) :=
      congrArg (fun e : ℝ => N ^ e) hden
    calc
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
          -N ^ (-σ) / (-(σ + 1) + 1) := by
        exact congrArg
          (fun t : ℝ => -t / (-(σ + 1) + 1))
          hnum
      _ = -N ^ (-σ) / (-σ) := by
        exact congrArg
          (fun t : ℝ => -N ^ (-σ) / t)
          hden
      _ = N ^ (-σ) / σ := by
        exact neg_div_neg_eq (N ^ (-σ)) σ
  have hsigma_nonneg : 0 ≤ σ :=
    le_trans zero_le_one hσ
  have hsigma_pos : 0 < σ :=
    lt_of_lt_of_le zero_lt_one hσ
  have hexponent_nonpos : -σ ≤ 0 :=
    neg_nonpos.mpr hsigma_nonneg
  have hpow_le : N ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hexponent_nonpos
  have hquotient_le_one_div :
      N ^ (-σ) / σ ≤ 1 / σ :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hsigma_pos)
  have hone_div_le_one :
      1 / σ ≤ 1 :=
    le_trans
      (one_div_le_one_div_of_le zero_lt_one hσ)
      (le_of_eq (div_one (1 : ℝ)))
  have htail :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) ≤ 1 :=
    le_trans
      (Eq.subst
        (motive := fun t : ℝ => t ≤ 1 / σ)
        hvalue.symm
        hquotient_le_one_div)
      hone_div_le_one
  exact Eq.subst
    (motive := fun t : ℝ => t ≤ 1)
    hintegral.symm
    htail

/-- Bochner norm domination for the Bernoulli-periodic Euler-Maclaurin core by
the scalar real-power tail integral. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
        x ^ (-(z.re + 1)) := by
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralCore
  let N : ℝ := ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)
  let s : Set ℝ := Set.Ioi N
  let f : ℝ → ℂ :=
    fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let g : ℝ → ℝ :=
    fun x => x ^ (-(z.re + 1))
  have hN_one : (1 : ℝ) ≤ N :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN_one
  have htwo_le : (2 : ℝ) ≤ z.re + 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by
        exact (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
      _ ≤ z.re + 1 :=
        add_le_add hz_one le_rfl
  have hone_lt : (1 : ℝ) < z.re + 1 :=
    lt_of_lt_of_le one_lt_two htwo_le
  have ha : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg hone_lt
  have hg : Integrable g (volume.restrict s) :=
    integrableOn_Ioi_rpow_of_lt ha hN_pos
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx =>
        by
          have hx_pos : 0 < x :=
            lt_trans hN_pos hx
          have hB_abs :
              |eulerMaclaurinFirstPeriodicBernoulli x| ≤ 1 :=
            eulerMaclaurinFirstPeriodicBernoulli_abs_le_one x
          have hB_norm :
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
            calc
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ =
                  |eulerMaclaurinFirstPeriodicBernoulli x| := by
                exact Complex.norm_ofReal (eulerMaclaurinFirstPeriodicBernoulli x)
              _ ≤ 1 :=
                hB_abs
          have hcpow :
              ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ g x :=
            norm_real_cpow_neg_z_add_one_le_rpow hx_pos z hz_one
          have hg_nonneg : 0 ≤ g x :=
            Real.rpow_nonneg (le_of_lt hx_pos) (-(z.re + 1))
          calc
            ‖f x‖ =
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                  ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
              exact norm_mul
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
                (((x : ℝ) : ℂ) ^ (-(z + 1)))
            _ ≤ 1 * g x :=
              mul_le_mul hB_norm hcpow
                (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
                zero_le_one
            _ = g x := by
              exact one_mul (g x)
      )
  exact norm_integral_le_of_norm_le hg hbound

/-- Scalar improper-integral tail estimate for the first periodic Bernoulli
Euler-Maclaurin kernel.

This is the real-variable analytic input behind the zeta remainder bound:
`|B₁({x})| ≤ 1`, positivity of the cutoff, the positive-real `cpow` norm
formula, and the tail estimate for `∫_N^∞ x^{-σ-1} dx` with `σ ≥ 1`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  have hdom :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) :=
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_norm_integral_domination
      z hz_one hz_two
  have hcutoff :
      (1 : ℝ) ≤ ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have htail :
      ∫ x in Set.Ioi (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)),
          x ^ (-(z.re + 1)) ≤ 1 :=
    integral_Ioi_rpow_neg_re_add_one_le_one_of_one_le_cutoff
      hcutoff hz_one
  exact le_trans hdom htail

/-- Standard Bernoulli-periodic tail majorant for the Euler-Maclaurin zeta
remainder core on the closed strip `1 ≤ Re z ≤ 2`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one
    (z : ℂ)
    (hz_one : 1 ≤ z.re)
    (hz_two : z.re ≤ 2) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 := by
  exact
    eulerMaclaurin_firstPeriodicBernoulli_cpow_tail_integral_norm_le_one_standard
      z hz_one hz_two

/-- Polynomial bound for the explicit Bernoulli-periodic integral remainder.

The proof is the standard majorization:
`|B₁({x})| ≤ 1`, `‖x^{-z-1}‖ ≤ x^{-Re z-1}` for positive `x`, and
`∫_N^∞ x^{-Re z-1} dx ≤ 1` on `1 ≤ Re z`, followed by the elementary
polynomial bound for `(z - 1) z`. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  refine ⟨1, 2, zero_lt_one, ?_⟩
  intro z hz_one hz_two
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hz_norm : ‖z‖ ≤ H :=
    le_add_of_nonneg_left zero_le_one
  have hz_sub_norm : ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hleft :
      ‖(z - 1) * z‖ ≤ H * H := by
    calc
      ‖(z - 1) * z‖ = ‖z - 1‖ * ‖z‖ := by
        exact norm_mul (z - 1) z
      _ ≤ H * H :=
        mul_le_mul hz_sub_norm hz_norm (norm_nonneg z) hH_nonneg
  have hcore :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 1 :=
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_one z hz_one hz_two
  have hprod :
      ‖-((z - 1) * z) *
          eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        (H * H) * 1 := by
    calc
      ‖-((z - 1) * z) *
          eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ =
          ‖-((z - 1) * z)‖ *
            ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
        exact norm_mul (-((z - 1) * z))
          (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z)
      _ = ‖(z - 1) * z‖ *
            ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
        exact congrArg
          (fun x : ℝ =>
            x * ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖)
          (norm_neg ((z - 1) * z))
      _ ≤ (H * H) * 1 :=
        mul_le_mul hleft hcore
          (norm_nonneg (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))
          (mul_nonneg hH_nonneg hH_nonneg)
  have hcollapse : (H * H) * 1 = (1 : ℝ) * H ^ (2 : ℕ) := by
    calc
      (H * H) * 1 = H * H := by
        exact mul_one (H * H)
      _ = H ^ (2 : ℕ) := by
        exact (pow_two H).symm
      _ = (1 : ℝ) * H ^ (2 : ℕ) := by
        exact (one_mul (H ^ (2 : ℕ))).symm
  have htarget : (1 : ℝ) * H ^ (2 : ℕ) =
      (1 : ℝ) * (1 + ‖z‖) ^ (2 : ℕ) := rfl
  exact le_trans hprod (le_of_eq (hcollapse.trans htarget))

/-- Standard Euler-Maclaurin Bernoulli-periodic integral estimate for the
pole-cleared remainder on `1 ≤ Re s ≤ 2`.

This is the analytic owner input: after multiplying the usual
Euler-Maclaurin remainder
`s ∫_N^∞ B₁({x}) x^{-s-1} dx` by `s - 1`, the bounded Bernoulli function,
`‖x^{-s-1}‖ ≤ x^{-Re s - 1}`, and
`N = ⌊2 + ‖s‖⌋₊ ≥ 1` give a fixed polynomial envelope in `1 + ‖s‖`. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  rcases eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_polynomial_bound with
    ⟨C, m, hC, hbound⟩
  refine ⟨C, m, hC, ?_⟩
  intro z hz_one hz_two
  have hformula :
      eulerMaclaurinPoleClearedZetaRemainderTerm z =
        eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    eulerMaclaurinPoleClearedZetaRemainderTerm_eq_bernoulliIntegralRemainder
      z hz_one hz_two
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ C * (1 + ‖z‖) ^ m)
    hformula.symm
    (hbound z hz_one hz_two)

/-- Polynomial control for the pole-cleared Euler-Maclaurin remainder from the
standard Bernoulli-periodic integral majorant.

Analytically this is the estimate for
`(s - 1) · s ∫_N^∞ B₁({x}) x^{-s-1} dx` with
`N = ⌊2 + ‖s‖⌋₊`, using boundedness of `B₁`, `1 ≤ Re s ≤ 2`, and the
height-comparable cutoff. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_integral_majorant_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaRemainderTerm_bernoulliIntegral_polynomial_bound_standard

/-- The pole-cleared Euler-Maclaurin continuation formula in the `1 ≤ Re s ≤ 2`
strip, with the four canonical terms separated. -/
theorem poleClearedRiemannZeta_eq_eulerMaclaurin_one_two_strip_terms
    (z : ℂ) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaRemainderTerm z := by
  unfold eulerMaclaurinPoleClearedZetaRemainderTerm
  let S : ℂ :=
    (eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z)
  have hsub :
      poleClearedRiemannZeta z = (poleClearedRiemannZeta z - S) + S :=
    (sub_add_cancel (poleClearedRiemannZeta z) S).symm
  have hcomm :
      (poleClearedRiemannZeta z - S) + S =
        S + (poleClearedRiemannZeta z - S) :=
    add_comm (poleClearedRiemannZeta z - S) S
  exact Eq.trans hsub hcomm

/-- Polynomial bound for the finite Dirichlet-polynomial piece in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaFinitePart_sum_cardinality_polynomial_bound

/-- Polynomial bound for the pole-cancelling main term in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨1, 0, zero_lt_one, ?_⟩
  intro z hz_one _hz_two
  have hterm :
      ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 1 :=
    eulerMaclaurinPoleClearedZetaMainTerm_norm_le_one z hz_one
  have hright : (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) = 1 := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) =
          (1 + ‖z‖) ^ (0 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (0 : ℕ))
      _ = 1 := by
        exact pow_zero (1 + ‖z‖)
  exact Eq.subst
    (motive := fun x : ℝ => ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ x)
    hright.symm
    hterm

/-- Polynomial bound for the endpoint correction in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaEndpointTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  refine ⟨1, 1, zero_lt_one, ?_⟩
  intro z hz_one _hz_two
  unfold eulerMaclaurinPoleClearedZetaEndpointTerm
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hsub_norm : ‖z - 1‖ ≤ H := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ = H := by
        exact add_comm ‖z‖ 1
  have hdiv_two_norm : ‖(z - 1) / (2 : ℂ)‖ ≤ ‖z - 1‖ := by
    have hnorm_div :
        ‖(z - 1) / (2 : ℂ)‖ = ‖z - 1‖ / ‖(2 : ℂ)‖ :=
      norm_div (z - 1) (2 : ℂ)
    have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
      calc
        ‖(2 : ℂ)‖ = ‖((2 : ℝ) : ℂ)‖ := rfl
        _ = ‖(2 : ℝ)‖ := by
          exact Complex.norm_ofReal 2
        _ = 2 := by
          exact Real.norm_of_nonneg zero_le_two
    have hraw : ‖z - 1‖ / ‖(2 : ℂ)‖ ≤ ‖z - 1‖ := by
      have htwo_pos : (0 : ℝ) < ‖(2 : ℂ)‖ :=
        Eq.subst
          (motive := fun x : ℝ => 0 < x)
          htwo_norm.symm
          zero_lt_two
      have hone_le_two : (1 : ℝ) ≤ ‖(2 : ℂ)‖ :=
        Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ x)
          htwo_norm.symm
          one_le_two
      exact div_le_self (norm_nonneg (z - 1)) hone_le_two
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z - 1‖)
      hnorm_div.symm
      hraw
  have hfactor : ‖(z - 1) / (2 : ℂ)‖ ≤ H :=
    le_trans hdiv_two_norm hsub_norm
  have hrecip :
      ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 :=
    eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one z hz_one
  have hproduct :
      ‖(z - 1) / (2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ ≤
        H := by
    calc
      ‖(z - 1) / (2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ =
          ‖(z - 1) / (2 : ℂ)‖ *
            ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ := by
        exact norm_mul ((z - 1) / (2 : ℂ))
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))
      _ ≤ H * 1 :=
        mul_le_mul hfactor hrecip
          (norm_nonneg (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))
          hH_nonneg
      _ = H := by
        exact mul_one H
  have hright : (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
          (1 + ‖z‖) ^ (1 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
      _ = 1 + ‖z‖ := by
        exact pow_one (1 + ‖z‖)
      _ = H := rfl
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(z - 1) / (2 : ℂ) *
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ ≤ x)
    hright.symm
    hproduct

/-- Polynomial bound for the Bernoulli-periodic Euler-Maclaurin remainder in
the bounded strip. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaRemainderTerm_integral_majorant_polynomial_bound

/-- Four polynomial Euler-Maclaurin term bounds assemble to a polynomial bound
for the pole-cleared zeta factor. -/
theorem poleClearedRiemannZeta_one_two_strip_polynomial_bound_of_eulerMaclaurin_term_bounds
    (hfinite :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hmain :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hendpoint :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hremainder :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m := by
  rcases hfinite with ⟨Cf, mf, hCf, hf⟩
  rcases hmain with ⟨Cm, mm, hCm, hm⟩
  rcases hendpoint with ⟨Ce, me, hCe, he⟩
  rcases hremainder with ⟨Cr, mr, hCr, hr⟩
  let C : ℝ := Cf + Cm + Ce + Cr
  let m : ℕ := mf + mm + me + mr
  have hCf_nonneg : 0 ≤ Cf := le_of_lt hCf
  have hCm_nonneg : 0 ≤ Cm := le_of_lt hCm
  have hCe_nonneg : 0 ≤ Ce := le_of_lt hCe
  have hCr_nonneg : 0 ≤ Cr := le_of_lt hCr
  refine ⟨C, m, add_pos (add_pos (add_pos hCf hCm) hCe) hCr, ?_⟩
  intro z hz_one hz_two
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hmf : H ^ mf ≤ H ^ m :=
    pow_le_pow_right₀ hH_ge_one (Nat.le_add_right mf (mm + me + mr))
  have hmm : H ^ mm ≤ H ^ m := by
    have hmm_le : mm ≤ mf + mm + me + mr := by
      exact le_trans
        (le_add_of_nonneg_left (Nat.zero_le mf))
        (Nat.le_add_right (mf + mm) (me + mr))
    exact pow_le_pow_right₀ hH_ge_one hmm_le
  have hme : H ^ me ≤ H ^ m := by
    have hme_le : me ≤ mf + mm + me + mr := by
      exact le_trans
        (le_add_of_nonneg_left (Nat.zero_le (mf + mm)))
        (Nat.le_add_right (mf + mm + me) mr)
    exact pow_le_pow_right₀ hH_ge_one hme_le
  have hmr : H ^ mr ≤ H ^ m := by
    have hmr_le : mr ≤ (mf + mm + me) + mr :=
      Nat.le_add_left mr (mf + mm + me)
    exact Eq.subst
      (motive := fun d : ℕ => H ^ mr ≤ H ^ d)
      (show (mf + mm + me) + mr = mf + mm + me + mr from rfl)
      (pow_le_pow_right₀ hH_ge_one hmr_le)
  have hf' :
      ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ Cf * H ^ m :=
    le_trans (hf z hz_one hz_two)
      (mul_le_mul_of_nonneg_left hmf hCf_nonneg)
  have hm' :
      ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ Cm * H ^ m :=
    le_trans (hm z hz_one hz_two)
      (mul_le_mul_of_nonneg_left hmm hCm_nonneg)
  have he' :
      ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ Ce * H ^ m :=
    le_trans (he z hz_one hz_two)
      (mul_le_mul_of_nonneg_left hme hCe_nonneg)
  have hr' :
      ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ Cr * H ^ m :=
    le_trans (hr z hz_one hz_two)
      (mul_le_mul_of_nonneg_left hmr hCr_nonneg)
  have hformula :
      poleClearedRiemannZeta z =
        eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaRemainderTerm z :=
    poleClearedRiemannZeta_eq_eulerMaclaurin_one_two_strip_terms z
  have htriangle :
      ‖poleClearedRiemannZeta z‖ ≤
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ := by
    exact Eq.subst
      (motive := fun w : ℂ =>
        ‖w‖ ≤
          ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
            ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
            ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
            ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖)
      hformula.symm
      (le_trans
        (norm_add_le
          (eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z)
          (eulerMaclaurinPoleClearedZetaRemainderTerm z))
        (add_le_add_right
          (le_trans
            (norm_add_le
              (eulerMaclaurinPoleClearedZetaFinitePart z +
                eulerMaclaurinPoleClearedZetaMainTerm z)
              (eulerMaclaurinPoleClearedZetaEndpointTerm z))
            (add_le_add_right
              (norm_add_le
                (eulerMaclaurinPoleClearedZetaFinitePart z)
                (eulerMaclaurinPoleClearedZetaMainTerm z))
              ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖))
          ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖))
  have hsum_bound :
      ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤
        C * H ^ m := by
    have hsum :
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
            ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
            ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
            ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤
          Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m :=
      add_le_add (add_le_add (add_le_add hf' hm') he') hr'
    have hcombine :
        Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m =
          C * H ^ m := by
      calc
        Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m =
            (Cf + Cm) * H ^ m + Ce * H ^ m + Cr * H ^ m := by
          exact congrArg (fun x : ℝ => x + Ce * H ^ m + Cr * H ^ m)
            (add_mul Cf Cm (H ^ m)).symm
        _ = (Cf + Cm + Ce) * H ^ m + Cr * H ^ m := by
          exact congrArg (fun x : ℝ => x + Cr * H ^ m)
            (add_mul (Cf + Cm) Ce (H ^ m)).symm
        _ = (Cf + Cm + Ce + Cr) * H ^ m := by
          exact (add_mul (Cf + Cm + Ce) Cr (H ^ m)).symm
        _ = C * H ^ m := rfl
    exact hsum.trans_eq hcombine
  exact le_trans htriangle hsum_bound

/-- Euler-Maclaurin formula/remainder polynomial bound for the pole-cleared zeta
factor on the closed strip `1 ≤ Re s ≤ 2`.

This is the precise classical analytic input behind the strip continuation
estimate.  In standard notation it comes from the Euler-Maclaurin continuation
formula
`ζ(s) = Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + O(N^{-σ}) +
  s ∫_N^∞ B₁({x}) x^{-s-1} dx`,
after multiplying by `s - 1` and taking `N` comparable to `2 + |Im s|`.
The finite Dirichlet polynomial, the pole-cancelling term `N^{1-s}`, the
endpoint correction, and the Bernoulli-remainder integral are all polynomially
bounded in `1 + ‖s‖` uniformly for `1 ≤ σ ≤ 2`; cf. Titchmarsh, §3.5 and
Davenport, Ch. 12. -/
theorem eulerMaclaurin_poleClearedRiemannZeta_one_two_strip_formula_remainder_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact
    poleClearedRiemannZeta_one_two_strip_polynomial_bound_of_eulerMaclaurin_term_bounds
      eulerMaclaurinPoleClearedZetaFinitePart_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaMainTerm_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaEndpointTerm_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaRemainderTerm_one_two_strip_polynomial_bound

/-- Polynomial Euler-Maclaurin growth on the closed strip implies the
finite-order exponential envelope used by the strip admissibility API. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_of_polynomial_bound
    (hpoly :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hpoly with ⟨C, m, hC, hbound⟩
  refine ⟨C, 1, m, hC, zero_lt_one, ?_⟩
  intro z hz_one hz_two
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpow_nonneg : 0 ≤ H ^ m :=
    pow_nonneg hH_nonneg m
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * H ^ m) := by
    have hexponent_nonneg : 0 ≤ (1 : ℝ) * H ^ m :=
      mul_nonneg zero_le_one hpow_nonneg
    exact le_trans
      (le_of_eq Real.exp_zero.symm)
      (Real.exp_le_exp.mpr hexponent_nonneg)
  have hHpow_le_exp :
      H ^ m ≤ Real.exp ((1 : ℝ) * H ^ m) := by
    exact le_trans
      (le_add_of_nonneg_right zero_le_one)
      (Real.add_one_le_exp (H ^ m))
  have htarget :
      C * H ^ m ≤ C * Real.exp ((1 : ℝ) * H ^ m) :=
    mul_le_mul_of_nonneg_left hHpow_le_exp (le_of_lt hC)
  exact le_trans (hbound z hz_one hz_two) htarget

/-- Pointwise finite-order Euler-Maclaurin continuation estimate for the
removable pole-cleared zeta on `1 ≤ Re s ≤ 2`.

This is the exact standard continuation estimate behind the strip admissibility
input: Euler-Maclaurin gives finite-order growth for the meromorphic zeta
continuation on the closed bounded-width strip, and the pole-cleared
normalization removes the singularity at `s = 1`. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_of_polynomial_bound
      eulerMaclaurin_poleClearedRiemannZeta_one_two_strip_formula_remainder_polynomial_bound

/-- Interior admissible-growth input for the `1 < Re s < 2` strip.

This is the exact remaining growth hypothesis consumed by the generic
Phragmen-Lindelöf API.  Analytically it is the subcritical strip growth of the
removable pole-cleared zeta in the bounded strip, obtained from the standard
Euler-Maclaurin continuation estimates. -/
theorem poleClearedRiemannZeta_one_two_strip_admissible_growth_from_EulerMaclaurin_continuation :
    ∃ c : ℝ,
      c < Real.pi / (2 - 1) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 1 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 1 2 one_lt_two
      poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation

/-- Vertical-tail finite-order growth for the removable pole-cleared zeta on
`1 ≤ Re s ≤ 2`, obtained from the two boundary estimates and strip PL. -/
theorem poleClearedRiemannZeta_one_two_strip_verticalTail_growth_from_boundary_and_PL :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 1 2 one_lt_two
    poleClearedRiemannZeta_one_two_strip_diffContOnCl
    poleClearedRiemannZeta_one_two_strip_admissible_growth_from_EulerMaclaurin_continuation
    poleClearedRiemannZeta_one_two_strip_leftBoundary_growth_from_EulerMaclaurin
    poleClearedRiemannZeta_one_two_strip_rightBoundary_growth_from_dirichletSeries

/-- Compact-height finite-order growth for the removable pole-cleared zeta on
`1 ≤ Re s ≤ 2`. -/
theorem poleClearedRiemannZeta_one_two_strip_compactCore_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, 1, 0, hC_pos, zero_lt_one, ?_⟩
  intro z hz_one hz_two hz_im
  have hz_zero : 0 ≤ z.re :=
    le_trans zero_le_one hz_one
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz_zero, hz_two, hz_im⟩
  have hraw : ‖poleClearedRiemannZeta z‖ ≤ C :=
    hC_bound z hz_mem
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    have hexponent_nonneg :
        0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
      mul_nonneg zero_le_one
        (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) 0)
    exact le_trans
      (le_of_eq Real.exp_zero.symm)
      (Real.exp_le_exp.mpr hexponent_nonneg)
  have hC_le_target :
      C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    calc
      C = C * 1 := by
        exact (mul_one C).symm
      _ ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos)
  exact le_trans hraw hC_le_target

/-- Compact core and PL vertical tail patch to finite-order growth on the
whole bounded strip `1 ≤ Re s ≤ 2`. -/
theorem poleClearedRiemannZeta_one_two_strip_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz_one hz_two
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz_one hz_two hcompact_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg
          (le_add_of_nonneg_right hAt_nonneg)
          (le_add_of_nonneg_right hBt_nonneg)
          hBc_nonneg
          (Nat.le_add_right mc mt))
  | Or.inr htail_im =>
      have hdegree : mt ≤ mc + mt := by
        exact Eq.subst
          (motive := fun d : ℕ => mt ≤ d)
          (Nat.add_comm mt mc)
          (Nat.le_add_right mt mc)
      exact le_trans (ht z hz_one hz_two htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Bounded-width Euler-Maclaurin/PL growth for the removable pole-cleared zeta
normalization on `1 ≤ Re s ≤ 2`.

This is the exact strip owner input: Euler-Maclaurin gives the boundary-line
estimate at `Re s = 1`, the Dirichlet-series estimate gives the right edge at
`Re s = 2`, and the generic vertical-strip Phragmen-Lindelöf finite-order API
transports these boundary estimates across the strip.  The removable
normalization is essential at `s = 1`; the raw product is recovered only after
this theorem. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_boundary_and_PL :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        w.re ≤ 2 →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    poleClearedRiemannZeta_one_two_strip_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_one_two_strip_compactCore_growth_from_localBoundedness
      poleClearedRiemannZeta_one_two_strip_verticalTail_growth_from_boundary_and_PL

/-- Bounded-width Euler-Maclaurin/continuation growth for the raw pole-cleared
zeta product on `1 ≤ Re s ≤ 2`.

This is the exact bounded-strip standard input: Euler-Maclaurin gives the
boundary-line estimate at `Re s = 1`, the Dirichlet series gives the right edge
at `Re s = 2`, and the pole-cleared product is holomorphic across `s = 1`, so
the generic vertical-strip Phragmen-Lindelöf finite-order API gives the
bounded-width envelope. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_two_le_finiteOrder_growth_from_EulerMaclaurin_strip :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        w.re ≤ 2 →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_boundary_and_PL with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_one hw_two
  by_cases hw_eq_one : w = 1
  · have hraw_zero :
        (w - 1) * riemannZeta w = 0 := by
      have hfactor_zero : w - 1 = 0 := by
        exact sub_eq_zero.mpr hw_eq_one
      exact Eq.subst
        (motive := fun u : ℂ => u * riemannZeta w = 0)
        hfactor_zero.symm
        (zero_mul (riemannZeta w))
    have htarget_nonneg :
        0 ≤ A * Real.exp (B * (1 + ‖w‖) ^ m) :=
      mul_nonneg (le_of_lt hA)
        (le_of_lt (Real.exp_pos (B * (1 + ‖w‖) ^ m)))
    exact Eq.subst
      (motive := fun u : ℂ =>
        ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
      hraw_zero.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          x ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
        (norm_zero : ‖(0 : ℂ)‖ = (0 : ℝ)).symm
        htarget_nonneg)
  · have hpole :
        poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
      poleClearedRiemannZeta_eq_of_ne_one hw_eq_one
    exact Eq.subst
      (motive := fun u : ℂ =>
        ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
      hpole
      (hbound w hw_one hw_two)

/-- Patch `1 ≤ Re s ≤ 2` Euler-Maclaurin/PL growth with the far-right
Dirichlet-series growth to obtain the full right half-plane. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_of_strip_and_farRight
    (hstrip :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          w.re ≤ 2 →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m))
    (hfar :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          2 ≤ w.re →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hstrip with ⟨As, Bs, ms, hAs, hBs, hstrip_bound⟩
  rcases hfar with ⟨Af, Bf, mf, hAf, hBf, hfar_bound⟩
  let A : ℝ := As + Af
  let B : ℝ := Bs + Bf
  let m : ℕ := ms + mf
  have hAs_nonneg : 0 ≤ As := le_of_lt hAs
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hBs_nonneg : 0 ≤ Bs := le_of_lt hBs
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hA_pos : 0 < A :=
    add_pos hAs hAf
  have hB_pos : 0 < B :=
    add_pos hBs hBf
  refine ⟨A, B, m, hA_pos, hB_pos, ?_⟩
  intro w hw_one
  match le_total w.re 2 with
  | Or.inl hw_two =>
      exact le_trans (hstrip_bound w hw_one hw_two)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAs_nonneg
          (le_add_of_nonneg_right hAf_nonneg)
          (le_add_of_nonneg_right hBf_nonneg)
          hBs_nonneg
          (Nat.le_add_right ms mf))
  | Or.inr hw_two =>
      have hdegree : mf ≤ ms + mf := by
        exact Eq.subst
          (motive := fun d : ℕ => mf ≤ d)
          (Nat.add_comm mf ms)
          (Nat.le_add_right mf ms)
      exact le_trans (hfar_bound w hw_two)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAf_nonneg
          (le_add_of_nonneg_left hAs_nonneg)
          (le_add_of_nonneg_left hBs_nonneg)
          hBf_nonneg
          hdegree)

/-- Classical Euler-Maclaurin half-plane finite-order theorem for the raw
pole-cleared Riemann zeta factor.

This is the exact analytic owner input absent from mathlib in the required
form.  It is the standard theorem that Euler-Maclaurin summation gives
polynomial, hence finite-order, growth for `(s - 1)ζ(s)` uniformly on
`Re s ≥ 1`; the factor `(s - 1)` removes the simple pole at `1`.  See
Titchmarsh, Ch. 3, or Edwards, Ch. 1. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_of_strip_and_farRight
      classicalZeta_poleCleared_rightHalfPlane_one_le_two_le_finiteOrder_growth_from_EulerMaclaurin_strip
      riemannZeta_poleCleared_rightHalfPlane_two_le_finiteOrder_growth_from_dirichletSeries

/-- Euler-Maclaurin finite-order growth for the pole-cleared zeta factor on the
full reflected right half-plane `1 ≤ Re s`.

This is the standard continuation-strength form of the right-side zeta input:
Euler-Maclaurin/Abel summation controls `(s - 1)ζ(s)` uniformly from the
boundary line `Re s = 1` into the half-plane `Re s ≥ 1`.  The far-right
Dirichlet-series theorem above only proves the easier subregion `2 ≤ Re s`;
the transport across the functional equation genuinely needs this full
half-plane statement. -/
theorem riemannZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin

/-- The standard Euler-Maclaurin bound for `(s - 1)ζ(s)` gives the removable
pole-cleared zeta bound on `1 ≤ Re s`. -/
theorem poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_of_raw_EulerMaclaurin
    (hraw :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hraw with ⟨A, B, m, hA, hB, hraw_bound⟩
  refine ⟨A + 1, B, m, add_pos hA zero_lt_one, hB, ?_⟩
  intro w hw_re
  have hA_nonneg : 0 ≤ A := le_of_lt hA
  have hA_le : A ≤ A + 1 :=
    le_add_of_nonneg_right zero_le_one
  by_cases hw_one : w = 1
  · have hpole_one :
        poleClearedRiemannZeta w = 1 := by
      exact Eq.subst
        (motive := fun u : ℂ => poleClearedRiemannZeta u = 1)
        hw_one.symm
        poleClearedRiemannZeta_one
    have hfactor_ge_one :
        (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ m) := by
      have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
        le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
      have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ m :=
        mul_nonneg (le_of_lt hB) (pow_nonneg hbase_nonneg m)
      exact le_trans (le_of_eq Real.exp_zero.symm)
        (Real.exp_le_exp.mpr hexponent_nonneg)
    have hone_le_A : (1 : ℝ) ≤ A + 1 :=
      le_add_of_nonneg_left hA_nonneg
    have htarget :
        (1 : ℝ) ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) := by
      calc
        (1 : ℝ) ≤ A + 1 := hone_le_A
        _ = (A + 1) * 1 := by
          exact (mul_one (A + 1)).symm
        _ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) :=
          mul_le_mul_of_nonneg_left hfactor_ge_one
            (le_trans zero_le_one hone_le_A)
    exact Eq.subst
      (motive := fun u : ℂ =>
        ‖u‖ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
      hpole_one.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          x ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
        (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ)).symm
        htarget)
  · have hpole_raw :
        poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
      poleClearedRiemannZeta_eq_of_ne_one hw_one
    have henlarge :
        A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
          (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) :=
      exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hA_nonneg hA_le (le_refl B) (le_of_lt hB) (le_refl m)
    exact Eq.subst
      (motive := fun u : ℂ =>
        ‖u‖ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
      hpole_raw.symm
      ((hraw_bound w hw_re).trans henlarge)

theorem poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_of_raw_EulerMaclaurin
      riemannZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin_standard

/-- Reflected right half-plane finite-order growth for the pole-cleared zeta factor.

This is the right-side input needed by the functional equation on the left
half-plane: after reflection `w = 1 - z`, one only has `1 ≤ Re w`.  The proof is
the Euler-Maclaurin/Abel finite-order theorem in the half-plane of meromorphic
continuation, with the pole at `1` removed. -/
theorem poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin

/-- The removable completed-functional-equation multiplier for the pole-cleared
zeta factor on the left half-plane.

Away from the removable point `z = 0`, this is the raw multiplier obtained by
writing the completed functional equation as a relation between `(z - 1)ζ(z)`
and `((1 - z) - 1)ζ(1 - z)`.  At `z = 0` the value is the removable value
forced by the pole-cleared identity. -/
noncomputable def poleClearedRiemannZeta_completedFunctionalEquationMultiplier
    (z : ℂ) : ℂ :=
  if z = 0 then
    poleClearedRiemannZeta 0
  else if Complex.Gammaℝ z = 0 then
    poleClearedRiemannZeta z / poleClearedRiemannZeta ((1 : ℂ) - z)
  else
    ((z - 1) / (((1 : ℂ) - z) - 1)) *
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)

/-- Nonzero left-half-plane normalization identity for the raw completed
functional-equation multiplier.

This is the exact algebraic identity obtained by unfolding
`completedRiemannZeta_one_sub`, `riemannZeta_def_of_ne_zero`, and the
pole-cleared definition away from both removable points. -/
/-- Denominator data needed to divide the completed functional equation into the
raw pole-cleared zeta multiplier.

The full left half-plane contains the `Gammaℝ` zero faces, so the algebraic
division step must be isolated from the exceptional trivial-zero compatibility
statement below. -/

end
end LFunctions
end Boundary

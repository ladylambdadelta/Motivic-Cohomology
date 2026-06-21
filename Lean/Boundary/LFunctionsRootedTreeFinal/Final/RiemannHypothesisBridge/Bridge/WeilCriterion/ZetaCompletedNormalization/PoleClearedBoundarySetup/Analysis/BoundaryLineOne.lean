import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Analysis.LeftBoundaryStirlingGrowth

/-!
# Boundary-line Gamma analysis and Abel-Plana assembly

## Helper lemmas for numeric bounds
-/

namespace Boundary
namespace LFunctions

/-- Helper: Large denominator positive. -/
private lemma ten_billion_pos : (0 : ℝ) < 10000000000 := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 9999999999)

/-- Helper: Euler's constant approximation bound. -/
private lemma euler_approx_le_three : (27182818286 : ℕ) ≤ 3 * 10000000000 := by
  exact Nat.le.intro (show 27182818286 + 2817181714 = 3 * 10000000000 by rfl)

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi
theorem boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    {f : ℂ → ℂ}
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact match hpoly with
    | ⟨A, m, hA_pos, hbound⟩ =>
      ⟨A, 1, m, hA_pos, zero_lt_one, fun w hw_re hw_im => by
  let H : ℝ := (1 + ‖w.im‖) ^ m
  have hH_nonneg : 0 ≤ H :=
    pow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im)))
      m
  have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
    have hone_mul : (1 : ℝ) * H = H := by
      exact one_mul H
    exact Eq.subst
      (motive := fun x : ℝ => H ≤ Real.exp x)
      hone_mul.symm
      (by
        have hH_le_H1 : H ≤ H + 1 := by
          exact le_add_of_nonneg_right zero_le_one
        exact le_trans hH_le_H1 (Real.add_one_le_exp H))
  have hscaled :
      A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
    mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
  exact le_trans (hbound w hw_re hw_im) hscaled⟩

/-- On the boundary line `re = 1`, the pole-clearing factor has zero real part. -/
theorem boundaryLine_one_sub_one_re_eq_zero
    {w : ℂ}
    (hw_re : w.re = 1) :
    (w - 1).re = 0 := by
  have hone_re : (1 : ℂ).re = 1 :=
    rfl
  calc
    (w - 1).re = w.re - (1 : ℂ).re := by
      exact Complex.sub_re w 1
    _ = 1 - (1 : ℂ).re := by
      exact congrArg (fun x : ℝ => x - (1 : ℂ).re) hw_re
    _ = 1 - 1 := by
      exact congrArg (fun x : ℝ => 1 - x) hone_re
    _ = 0 := by
      exact sub_self 1

/-- On the boundary line `re = 1`, the pole-clearing factor keeps the original
imaginary coordinate. -/
theorem boundaryLine_one_sub_one_im_eq
    (w : ℂ) :
    (w - 1).im = w.im := by
  have hone_im : (1 : ℂ).im = 0 :=
    rfl
  calc
    (w - 1).im = w.im - (1 : ℂ).im := by
      exact Complex.sub_im w 1
    _ = w.im - 0 := by
      exact congrArg (fun x : ℝ => w.im - x) hone_im
    _ = w.im := by
      exact sub_zero w.im

/-- On the boundary line `re = 1`, the pole-clearing factor has exactly the vertical
height as norm. -/
theorem boundaryLine_one_sub_one_norm_eq_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ = ‖w.im‖ := by
  have hre_zero : (w - 1).re = 0 :=
    boundaryLine_one_sub_one_re_eq_zero hw_re
  have him_eq : (w - 1).im = w.im :=
    boundaryLine_one_sub_one_im_eq w
  have habs_eq_im :
      Complex.abs (w - 1) = |(w - 1).im| :=
    (Complex.abs_im_eq_abs.mpr hre_zero).symm
  have him_abs_eq_norm : |(w - 1).im| = ‖w.im‖ := by
    calc
      |(w - 1).im| = |w.im| := by
        exact congrArg abs him_eq
      _ = ‖w.im‖ := (Real.norm_eq_abs w.im).symm
  calc
    ‖w - 1‖ = Complex.abs (w - 1) := by
      exact Complex.norm_eq_abs (w - 1)
    _ = |(w - 1).im| := habs_eq_im
    _ = ‖w.im‖ := him_abs_eq_norm

/-- On the boundary line `re = 1`, the pole-clearing factor has norm controlled by the
vertical height. -/
theorem boundaryLine_one_sub_one_norm_le_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ ≤ 1 + ‖w.im‖ := by
  have hnorm_eq :
      ‖w - 1‖ = ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_eq_vertical_height hw_re
  exact le_trans (le_of_eq hnorm_eq)
    (le_add_of_nonneg_left zero_le_one)

/-- The complex point with real coordinate `1` and imaginary coordinate `t`. -/
def boundaryLineOnePointRealParam (t : ℝ) : ℂ :=
  ⟨1, t⟩

/-- Real coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_re
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).re = 1 := by
  rfl

/-- Imaginary coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_im
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).im = t := by
  rfl

/-- The vertical height of the canonical point `1 + it` is the absolute value of `t`. -/
theorem boundaryLineOnePointRealParam_vertical_height
    (t : ℝ) :
    ‖(boundaryLineOnePointRealParam t).im‖ = ‖t‖ := by
  rfl

/-- A point on the boundary line `re = 1` is the canonical real-parameter boundary
point attached to its vertical coordinate. -/
theorem boundaryLine_one_eq_realParam_point
    {w : ℂ}
    (hw_re : w.re = 1) :
    w = boundaryLineOnePointRealParam w.im := by
  exact Complex.ext hw_re rfl

/-- The real-parameter zeta value attached to the boundary line `re = 1`. -/
def boundaryLineOneZetaRealParam (t : ℝ) : ℂ :=
  riemannZeta (boundaryLineOnePointRealParam t)

/-- Boundary-line zeta is the real-parameter zeta value at the same vertical
coordinate. -/
theorem riemannZeta_boundaryLine_one_eq_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    riemannZeta w = boundaryLineOneZetaRealParam w.im := by
  exact congrArg riemannZeta (boundaryLine_one_eq_realParam_point hw_re)

/-- Norm form of the boundary-line real-parameter zeta transport. -/
theorem norm_riemannZeta_boundaryLine_one_eq_norm_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖riemannZeta w‖ = ‖boundaryLineOneZetaRealParam w.im‖ := by
  exact congrArg norm (riemannZeta_boundaryLine_one_eq_realParam hw_re)

/-- Harmonic sums are controlled by the logarithm at the natural cutoff `⌊y⌋₊`.

This is the finite-sum side of the Abel/Euler-Maclaurin estimate: after truncating
at a real height `y`, the positive harmonic majorant is at most `1 + log y`. -/
theorem harmonic_truncation_floor_le_one_add_log
    {y : ℝ}
    (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  exact harmonic_floor_le_one_add_log y hy

/-- The cutoff `2 + |t|` is always in the range where the harmonic-log comparison applies. -/
theorem one_le_two_add_norm
    (t : ℝ) :
    (1 : ℝ) ≤ 2 + ‖t‖ := by
  have hnorm : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have htwo_le : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ = 2 := by
        exact one_add_one_eq_two
  exact le_trans htwo_le (le_add_of_nonneg_right hnorm)

/-- Harmonic control at the boundary-line truncation height `2 + |t|`. -/
theorem harmonic_boundaryLine_truncation_le_one_add_log
    (t : ℝ) :
    harmonic ⌊2 + ‖t‖⌋₊ ≤ 1 + Real.log (2 + ‖t‖) := by
  exact harmonic_truncation_floor_le_one_add_log (one_le_two_add_norm t)

/-- Each Dirichlet monomial on the boundary line `re = 1` has norm `1 / n`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ = 1 / (n : ℝ) := by
  have hnorm_pow :
    ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ = (n : ℝ) ^ (1 : ℝ) := by
    calc
      ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ =
          Complex.abs ((n : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Complex.norm_eq_abs ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      _ = (n : ℝ) ^ (boundaryLineOnePointRealParam t).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn)
          (boundaryLineOnePointRealParam t)
      _ = (n : ℝ) ^ (1 : ℝ) := by
        exact congrArg (fun x : ℝ => (n : ℝ) ^ x)
          (boundaryLineOnePointRealParam_re t)
  have hpow_one : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := by
    exact Real.rpow_one (n : ℝ)
  calc
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ =
        ‖(1 : ℂ)‖ / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact norm_div (1 : ℂ) ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = 1 / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact congrArg
            (fun x : ℝ => x / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖)
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 / ((n : ℝ) ^ (1 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 / x) hnorm_pow
    _ = 1 / (n : ℝ) := by
          exact congrArg (fun x : ℝ => 1 / x) hpow_one

/-- The finite Dirichlet truncation on `re = 1` is bounded by the corresponding
positive harmonic majorant. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
    (t : ℝ)
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      harmonic N := by
  have hsum_norm :
      ‖∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
    exact norm_sum_le _ _
  have hterm_sum :
      (∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖) =
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := by
    exact Finset.sum_congr rfl
      (fun n hn_mem => by
        have hn_one_le : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hn_pos : 0 < n :=
          Nat.lt_of_succ_le hn_one_le
        exact boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv t hn_pos)
  have hharmonic :
      (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 / (n : ℝ))) = harmonic N := by
    have hrat :
        (∑ n ∈ Finset.Icc (1 : ℕ) N, ((n : ℚ)⁻¹ : ℚ)) = harmonic N :=
      (harmonic_eq_sum_Icc (n := N)).symm
    have hcast :
        (∑ n ∈ Finset.Icc (1 : ℕ) N, (((n : ℚ)⁻¹ : ℚ) : ℝ)) =
          (harmonic N : ℝ) := by
      exact_mod_cast hrat
    calc
      (∑ n ∈ Finset.Icc (1 : ℕ) N, (1 / (n : ℝ))) =
          ∑ n ∈ Finset.Icc (1 : ℕ) N, (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
        exact Finset.sum_congr rfl
          (fun n hn_mem => by
            have hn_one_le : 1 ≤ n :=
              (Finset.mem_Icc.mp hn_mem).1
            have hn_pos : 0 < n :=
              Nat.lt_of_succ_le hn_one_le
            calc
              (1 / (n : ℝ)) = ((n : ℝ)⁻¹) := by
                exact one_div (n : ℝ)
              _ = (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
                exact (Rat.cast_inv (α := ℝ) (n : ℚ)).symm)
      _ = harmonic N := hcast
  exact le_trans hsum_norm (le_of_eq (hterm_sum.trans hharmonic))

/-- The finite Dirichlet truncation at the Abel/Euler-Maclaurin boundary cutoff is
bounded by `1 + log (2 + |t|)`. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log
    (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      1 + Real.log (2 + ‖t‖) := by
  exact le_trans
    (boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
      t ⌊2 + ‖t‖⌋₊)
    (harmonic_boundaryLine_truncation_le_one_add_log t)

/-- On the logarithmic boundary range used below, `1 ≤ log (2 + |t|)`. -/
theorem one_le_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.log (2 + ‖t‖) := by
  have hthree_le : (3 : ℝ) ≤ 2 + ‖t‖ := by
    calc
      (3 : ℝ) = 2 + 1 := by
        exact two_add_one_eq_three.symm
      _ ≤ 2 + ‖t‖ :=
        add_le_add_left ht 2
  have hexp_one_le_three : Real.exp (1 : ℝ) ≤ 3 := by
    have hexp_le_d9 : Real.exp (1 : ℝ) ≤ 2.7182818286 :=
      le_of_lt Real.exp_one_lt_d9
    have hden_pos : (0 : ℝ) < 10000000000 := by
      exact ten_billion_pos
    have hnum_le :
        (27182818286 : ℝ) ≤ 3 * (10000000000 : ℝ) := by
      have hnat : (27182818286 : ℕ) ≤ 3 * 10000000000 :=
        euler_approx_le_three
      have hcast : (27182818286 : ℝ) ≤ ((3 * 10000000000 : ℕ) : ℝ) :=
        Nat.cast_le.mpr hnat
      have hprod : ((3 * 10000000000 : ℕ) : ℝ) = 3 * (10000000000 : ℝ) := by
        exact Nat.cast_mul 3 10000000000
      exact Eq.subst
        (motive := fun x : ℝ => (27182818286 : ℝ) ≤ x)
        hprod
        hcast
    have hd9_le_three_q :
        @OfScientific.ofScientific ℚ Rat.instOfScientific 27182818286 true 10 ≤ 3 := by
      native_decide
    have hd9_le_three : (2.7182818286 : ℝ) ≤ 3 := by
      change
        ((@OfScientific.ofScientific ℚ Rat.instOfScientific 27182818286 true 10 : ℚ) : ℝ) ≤
          3
      exact_mod_cast hd9_le_three_q
    exact le_trans hexp_le_d9 hd9_le_three
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans hexp_one_le_three hthree_le
  have hpos : (0 : ℝ) < 2 + ‖t‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_two_add_norm t)
  exact (Real.le_log_iff_exp_le hpos).2 hexp_one_le

/-- The Abel/Euler-Maclaurin cutoff `⌊2 + |t|⌋₊` is nonzero. -/
theorem boundaryLineOnePointRealParam_cutoff_pos
    (t : ℝ) :
    0 < ⌊2 + ‖t‖⌋₊ := by
  have hone_le : (1 : ℝ) ≤ 2 + ‖t‖ :=
    one_le_two_add_norm t
  exact (Nat.one_le_floor_iff (2 + ‖t‖)).2 hone_le

/-- The Abel/Euler-Maclaurin cutoff dominates `2`. -/
theorem boundaryLineOnePointRealParam_two_le_cutoff
    (t : ℝ) :
    2 ≤ ⌊2 + ‖t‖⌋₊ := by
  have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
    le_add_of_nonneg_right (norm_nonneg t)
  have hnonneg : (0 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans zero_le_one (one_le_two_add_norm t)
  exact (Nat.le_floor_iff hnonneg).2 htwo_le

/-- Transport the finite Dirichlet truncation from `Icc 1 N` to the successor-indexed
form used by analytic Dirichlet-series tails. -/
theorem boundaryLineOnePointRealParam_dirichlet_truncation_eq_sum_range_add_one
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc (1 : ℕ) N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.range N,
        (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
  induction N with
  | zero =>
      have hleft :
          (∑ n ∈ Finset.Icc (1 : ℕ) 0,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Finset.sum_eq_zero
          (fun n hn => by
            have hn_bounds : 1 ≤ n ∧ n ≤ 0 :=
              Finset.mem_Icc.mp hn
            have hone_le_zero : (1 : ℕ) ≤ 0 :=
              le_trans hn_bounds.1 hn_bounds.2
            exact False.elim
              ((Nat.not_succ_le_zero 0) hone_le_zero))
      have hright :
          (∑ n ∈ Finset.range 0,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Eq.subst
          (motive := fun s : Finset ℕ =>
            (∑ n ∈ s,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0)
          (Finset.range_zero.symm)
          rfl
      exact Eq.trans hleft hright.symm
  | succ N ih =>
      have hleft :
          (∑ n ∈ Finset.Icc (1 : ℕ) (N + 1),
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.Icc (1 : ℕ) N,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_Icc_succ_top (Nat.succ_pos N)
          (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (∑ n ∈ Finset.range (N + 1),
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.range N,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_range_succ
          (fun n : ℕ =>
            (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
          N
      exact Eq.trans hleft (Eq.trans (congrArg
        (fun z : ℂ =>
          z + (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        ih) hright.symm)

/-- The oscillatory coefficient in the boundary-line Dirichlet term is exactly `n^{-it}`
after the real part `1` is peeled off. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpoint :
      boundaryLineOnePointRealParam t = 1 + (t : ℂ) * Complex.I := by
    apply Complex.ext
    · have hre_rhs : (1 + (t : ℂ) * Complex.I).re = 1 := by
        calc
          (1 + (t : ℂ) * Complex.I).re =
              (1 : ℂ).re + ((t : ℂ) * Complex.I).re := by
            exact Complex.add_re (1 : ℂ) ((t : ℂ) * Complex.I)
          _ = 1 + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
            exact congrArg (fun x : ℝ => 1 + x) (Complex.mul_re (t : ℂ) Complex.I)
          _ = 1 := by
            have hre : (t : ℂ).re = t := Complex.ofReal_re t
            have him : (t : ℂ).im = 0 := Complex.ofReal_im t
            calc
              1 + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im)
                  = 1 + (t * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
                    exact congrArg
                      (fun x : ℝ => 1 + (x * Complex.I.re - (t : ℂ).im * Complex.I.im))
                      hre
              _ = 1 + (t * 0 - (t : ℂ).im * Complex.I.im) := by
                    exact congrArg
                      (fun x : ℝ => 1 + (t * x - (t : ℂ).im * Complex.I.im))
                      Complex.I_re
              _ = 1 + (t * 0 - 0 * 1) := by
                    exact congrArg
                      (fun x : ℝ => 1 + (t * 0 - x * Complex.I.im))
                      him
              _ = 1 + (0 - 0 * 1) := by
                    exact congrArg (fun x : ℝ => 1 + (x - 0 * 1)) (mul_zero t)
              _ = 1 + (0 - 0) := by
                    exact congrArg (fun x : ℝ => 1 + (0 - x)) (zero_mul 1)
              _ = 1 + 0 := by
                    exact congrArg (fun x : ℝ => 1 + x) (sub_self 0)
              _ = 1 := add_zero 1
      · calc
          (boundaryLineOnePointRealParam t).re = 1 := boundaryLineOnePointRealParam_re t
          _ = (1 + (t : ℂ) * Complex.I).re := hre_rhs.symm
    · have him_rhs : (1 + (t : ℂ) * Complex.I).im = t := by
        calc
          (1 + (t : ℂ) * Complex.I).im =
              (1 : ℂ).im + ((t : ℂ) * Complex.I).im := by
            exact Complex.add_im (1 : ℂ) ((t : ℂ) * Complex.I)
          _ = 0 + ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re) := by
            exact congrArg (fun x : ℝ => 0 + x) (Complex.mul_im (t : ℂ) Complex.I)
          _ = t := by
            have hre : (t : ℂ).re = t := Complex.ofReal_re t
            have him : (t : ℂ).im = 0 := Complex.ofReal_im t
            calc
              0 + ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re)
                  = 0 + (t * Complex.I.im + (t : ℂ).im * Complex.I.re) := by
                    exact congrArg
                      (fun x : ℝ => 0 + (x * Complex.I.im + (t : ℂ).im * Complex.I.re))
                      hre
              _ = 0 + (t * 1 + (t : ℂ).im * Complex.I.re) := by
                    exact congrArg
                      (fun x : ℝ => 0 + (t * x + (t : ℂ).im * Complex.I.re))
                      Complex.I_im
              _ = 0 + (t * 1 + 0 * 0) := by
                    exact congrArg
                      (fun x : ℝ => 0 + (t * 1 + x * Complex.I.re))
                      him
              _ = 0 + (t + 0 * 0) := by
                    exact congrArg (fun x : ℝ => 0 + (x + 0 * 0)) (mul_one t)
              _ = 0 + (t + 0) := by
                    exact congrArg (fun x : ℝ => 0 + (t + x)) (zero_mul 0)
              _ = 0 + t := by
                    exact congrArg (fun x : ℝ => 0 + x) (add_zero t)
              _ = t := zero_add t
      · calc
          (boundaryLineOnePointRealParam t).im = t := boundaryLineOnePointRealParam_im t
          _ = (1 + (t : ℂ) * Complex.I).im := him_rhs.symm
  have hpow_add :
      (n : ℂ) ^ boundaryLineOnePointRealParam t =
        (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        (n : ℂ) ^ z =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))
      hpoint.symm
      (Complex.cpow_add (1 : ℂ) ((t : ℂ) * Complex.I) hn_complex_ne)
  have hinv_osc :
      ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    calc
      ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
          (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
        exact (Complex.cpow_neg (n : ℂ) ((t : ℂ) * Complex.I)).symm
      _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
        exact congrArg (fun z : ℂ => (n : ℂ) ^ z) (neg_mul (t : ℂ) Complex.I).symm
  calc
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
        ((n : ℂ) ^ boundaryLineOnePointRealParam t)⁻¹ := by
          exact one_div ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = ((n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
          exact congrArg Inv.inv hpow_add
    _ = ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact mul_inv_rev ((n : ℂ) ^ (1 : ℂ)) ((n : ℂ) ^ ((t : ℂ) * Complex.I))
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact congrArg
            (fun z : ℂ => z * ((n : ℂ) ^ (1 : ℂ))⁻¹)
            hinv_osc
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) / (n : ℂ) := by
          calc
            (n : ℂ) ^ (-(t : ℂ) * Complex.I) * ((n : ℂ) ^ (1 : ℂ))⁻¹ =
                (n : ℂ) ^ (-(t : ℂ) * Complex.I) * (n : ℂ)⁻¹ := by
              exact congrArg (fun z : ℂ => (n : ℂ) ^ (-(t : ℂ) * Complex.I) * z⁻¹)
                (Complex.cpow_one (n : ℂ))
            _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) / (n : ℂ) := by
              exact (div_eq_mul_inv ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) (n : ℂ)).symm

/-- The boundary-line Dirichlet monomial with the oscillation written on the right,
matching the Abel-summation convention `f k * c k`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have hright :
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    calc
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) * (n : ℂ)⁻¹ := by
            exact div_eq_mul_inv ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) (n : ℂ)
      _ = ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
            exact mul_comm ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) ((n : ℂ)⁻¹ : ℂ)
  exact Eq.trans
    (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation t hn)
    hright

/-- Finite boundary-line Dirichlet truncations are exactly the Abel-summation
weighted oscillatory sums. -/
theorem boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact Finset.sum_congr rfl
    (fun n hn_mem => by
      have hn_one_le : 1 ≤ n :=
        (Finset.mem_Icc.mp hn_mem).1
      have hn_pos : 0 < n :=
        Nat.lt_of_succ_le hn_one_le
      exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos)

/-- A finite boundary-line tail after the Abel/Euler-Maclaurin cutoff is exactly the
corresponding Abel weighted oscillatory tail. -/
theorem boundaryLineOnePointRealParam_finite_tail_after_cutoff_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (M : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact Finset.sum_congr rfl
    (fun n hn_mem => by
      have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
        (Finset.mem_Ioc.mp hn_mem).1
      have hn_pos : 0 < n :=
        lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
      exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos)

/-- The natural Abel/Euler-Maclaurin cutoff is fixed by taking the natural floor
after coercion to the real line. -/
theorem boundaryLineOnePointRealParam_cutoff_floor_natCast
    (t : ℝ) :
    ⌊((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)⌋₊ = ⌊2 + ‖t‖⌋₊ := by
  exact Nat.floor_natCast ⌊2 + ‖t‖⌋₊

/-- The Abel/Euler-Maclaurin cutoff is the left endpoint immediately below
`2 + |t|`. -/
theorem boundaryLineOnePointRealParam_cutoff_cast_le_height
    (t : ℝ) :
    (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 2 + ‖t‖ := by
  have hnonneg : (0 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans zero_le_one (one_le_two_add_norm t)
  exact Nat.floor_le hnonneg

/-- The real height `2 + |t|` lies strictly before the successor of the cutoff. -/
theorem boundaryLineOnePointRealParam_height_lt_cutoff_add_one
    (t : ℝ) :
    2 + ‖t‖ < (⌊2 + ‖t‖⌋₊ : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (2 + ‖t‖)

/-- The cutoff endpoint contributes at most one through the reciprocal weight. -/
theorem boundaryLineOnePointRealParam_cutoff_inv_le_one
    (t : ℝ) :
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 1 := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff_nat : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_le_cutoff_real : (1 : ℝ) ≤ (⌊2 + ‖t‖⌋₊ : ℝ) := by
    exact_mod_cast hone_le_cutoff_nat
  calc
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) =
        ((⌊2 + ‖t‖⌋₊ : ℝ)⁻¹ : ℝ) := by
          exact one_div (⌊2 + ‖t‖⌋₊ : ℝ)
    _ ≤ 1 := by
          exact inv_le_one_of_one_le₀ hone_le_cutoff_real

/-- Reciprocal weights are monotone decreasing along the positive natural tail. -/
theorem positive_nat_reciprocal_antitone
    {m n : ℕ}
    (hm : 0 < m)
    (hmn : m ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by
    exact Nat.cast_pos.mpr hm
  have hmn_real : (m : ℝ) ≤ (n : ℝ) := by
    exact Nat.cast_le.mpr hmn
  exact one_div_le_one_div_of_le hm_real_pos hmn_real

/-- Past the Abel/Euler-Maclaurin cutoff, all reciprocal weights are bounded by
the reciprocal of the cutoff endpoint. -/
theorem boundaryLineOnePointRealParam_post_cutoff_reciprocal_le_cutoff
    (t : ℝ)
    {n : ℕ}
    (hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_le_n : ⌊2 + ‖t‖⌋₊ ≤ n :=
    Nat.le_of_lt hcutoff_lt_n
  exact positive_nat_reciprocal_antitone hcutoff_pos hcutoff_le_n

-- Logarithmic-phase partial sums for the boundary-line oscillator `n^{-it}`.
-- The phase is `-t log n`; these sums must not be treated as constant-ratio
-- geometric sums.

end
end LFunctions
end Boundary

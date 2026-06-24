import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part10_PublicPartialSums

/-!
# Boundary growth owner part 11

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (_hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
      t ht hfinite
  exact boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    t htail

/-- The exact Abel/Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`. -/
theorem eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    t ht hpartial hfinite

/-- Public Abel/Euler-Maclaurin zeta-tail root.  The proof is now only name
transport from the canonical Euler-Maclaurin tail estimate at the exact cutoff. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    t ht hpartial hfinite

/-- Triangle-inequality split of `ζ(1+it)` into its Abel/Euler-Maclaurin tail
and finite Dirichlet truncation. -/
theorem boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation
    (t : ℝ) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
  let S : ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
      (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
  have hsplit :
      riemannZeta (boundaryLineOnePointRealParam t) =
        (riemannZeta (boundaryLineOnePointRealParam t) - S) + S := by
    exact (sub_add_cancel (riemannZeta (boundaryLineOnePointRealParam t)) S).symm
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ ‖riemannZeta (boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
    hsplit.symm
    (norm_add_le (riemannZeta (boundaryLineOnePointRealParam t) - S) S)

/-- The analytic tail estimate and finite harmonic majorant give the intermediate
explicit-tail boundary estimate. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  have hsplit :
      ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
        ‖riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ :=
    boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation t
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
      t ht hpartial hfinite
  have hfinite :
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        1 + Real.log (2 + ‖t‖) :=
    boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log t
  have htail_plus_finite :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
          (1 + Real.log (2 + ‖t‖)) :=
    add_le_add htail hfinite
  exact le_trans hsplit htail_plus_finite

/-- On the large vertical range, the intermediate `2 + log` bound is absorbed by
`3 * log`. -/
theorem two_add_log_two_add_norm_le_three_mul_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    2 + Real.log (2 + ‖t‖) ≤
      3 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hlog_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_le_twoL : (2 : ℝ) ≤ 2 * L := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * L :=
        mul_le_mul_of_nonneg_left hlog_one zero_le_two
  calc
    2 + Real.log (2 + ‖t‖) = 2 + L := rfl
    _ ≤ 2 * L + L :=
      add_le_add_right htwo_le_twoL L
    _ = 2 * L + 1 * L := by
      exact congrArg (fun x : ℝ => 2 * L + x) (one_mul L).symm
    _ = (2 + 1) * L := by
      exact (add_mul 2 1 L).symm
    _ = 3 * L := by
      exact congrArg (fun x : ℝ => x * L) boundaryGrowth_real_two_add_one_eq_three
    _ = 3 * Real.log (2 + ‖t‖) := rfl

/-- The enlarged logarithmic argument `3 + |t|` is absorbed by twice the
canonical boundary-line logarithm. -/
theorem log_three_add_norm_le_two_mul_log_two_add_norm
    (t : ℝ) :
    Real.log (3 + ‖t‖) ≤
      2 * Real.log (2 + ‖t‖) := by
  let x : ℝ := ‖t‖
  have hx_nonneg : 0 ≤ x :=
    norm_nonneg t
  have hleft_pos : 0 < 3 + x := by
    have hthree_pos : (0 : ℝ) < 3 :=
      three_pos
    exact lt_of_lt_of_le hthree_pos (le_add_of_nonneg_right hx_nonneg)
  have hright_pos : 0 < 2 * (2 + x) := by
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have harg_pos : 0 < 2 + x :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg)
    exact mul_pos htwo_pos harg_pos
  have harg_ne : (2 : ℝ) + x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg))
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have harg_ge_two : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx_nonneg
  have hthree_le :
      3 + x ≤ 2 * (2 + x) := by
    have hx_le_two_x : x ≤ 2 * x := by
      calc
        x = 1 * x := by
          exact (one_mul x).symm
        _ ≤ 2 * x :=
          mul_le_mul_of_nonneg_right one_le_two hx_nonneg
    calc
      3 + x ≤ 4 + 2 * x :=
        add_le_add
          (Nat.cast_le.mpr (show (3 : ℕ) ≤ 4 from Nat.le_succ 3))
          hx_le_two_x
      _ = 2 * 2 + 2 * x := by
        exact congrArg (fun y : ℝ => y + 2 * x)
          boundaryGrowth_real_two_mul_two_eq_four.symm
      _ = 2 * (2 + x) := by
        exact (left_distrib 2 2 x).symm
  have hlog_le :
      Real.log (3 + x) ≤ Real.log (2 * (2 + x)) :=
    Real.log_le_log hleft_pos hthree_le
  have hlog_mul :
      Real.log (2 * (2 + x)) =
        Real.log 2 + Real.log (2 + x) :=
    Real.log_mul htwo_ne harg_ne
  have hlog_two_le :
      Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hsum_le :
      Real.log 2 + Real.log (2 + x) ≤
        Real.log (2 + x) + Real.log (2 + x) :=
    add_le_add_right hlog_two_le (Real.log (2 + x))
  calc
    Real.log (3 + ‖t‖) = Real.log (3 + x) := rfl
    _ ≤ Real.log (2 * (2 + x)) :=
      hlog_le
    _ = Real.log 2 + Real.log (2 + x) :=
      hlog_mul
    _ ≤ Real.log (2 + x) + Real.log (2 + x) :=
      hsum_le
    _ = 2 * Real.log (2 + x) := by
      exact (two_mul (Real.log (2 + x))).symm
    _ = 2 * Real.log (2 + ‖t‖) := rfl

/-- The explicit Abel-tail constant plus finite-truncation logarithmic term is
absorbed by an absolute multiple of the canonical logarithm. -/
theorem boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      39 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hL_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hL_nonneg : 0 ≤ L :=
    le_trans zero_le_one hL_one
  have hfive_le : (5 : ℝ) ≤ 5 * L := by
    calc
      (5 : ℝ) = 5 * 1 := by
        exact (mul_one 5).symm
      _ ≤ 5 * L :=
        mul_le_mul_of_nonneg_left hL_one
          (show (0 : ℝ) ≤ 5 from Nat.cast_nonneg 5)
  have hone_le : (1 : ℝ) ≤ L :=
    hL_one
  have hlog_three :
      Real.log (3 + ‖t‖) ≤ 2 * L := by
    exact log_three_add_norm_le_two_mul_log_two_add_norm t
  have hsixteen_log :
      16 * Real.log (3 + ‖t‖) ≤ 32 * L := by
    calc
      16 * Real.log (3 + ‖t‖) ≤ 16 * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog_three
          (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16)
      _ = (16 * 2) * L := by
        exact (mul_assoc 16 2 L).symm
      _ = 32 * L := by
        exact congrArg (fun x : ℝ => x * L)
          boundaryGrowth_real_sixteen_mul_two_eq_thirty_two
  have htail :
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
        37 * L := by
    calc
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
          5 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 5 * L + 32 * L :=
        add_le_add hfive_le hsixteen_log
      _ = (5 + 32) * L := by
        exact (add_mul 5 32 L).symm
      _ = 37 * L := by
        exact congrArg (fun x : ℝ => x * L)
          boundaryGrowth_real_five_add_thirty_two_eq_thirty_seven
  have hfinite :
      1 + Real.log (2 + ‖t‖) ≤ 2 * L := by
    calc
      1 + Real.log (2 + ‖t‖) = 1 + L := rfl
      _ ≤ L + L :=
        add_le_add_right hone_le L
      _ = 2 * L := by
        exact (two_mul L).symm
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      37 * L + 2 * L :=
        add_le_add htail hfinite
    _ = (37 + 2) * L := by
      exact (add_mul 37 2 L).symm
    _ = 39 * L := by
      exact congrArg (fun x : ℝ => x * L)
        boundaryGrowth_real_thirty_seven_add_two_eq_thirty_nine
    _ = 39 * Real.log (2 + ‖t‖) := rfl

/-- The finite truncation plus the Abel/Euler-Maclaurin tail gives the logarithmic
boundary estimate with the explicit Abel-tail constant still visible. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  exact
    abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
      t ht hpartial hfinite

/-- The exact analytic Abel/Euler-Maclaurin tail estimate on `ζ(1 + it)`.

Intended proof chain:
Dirichlet truncation at `N = ⌊2 + |t|⌋₊`, Abel summation for the oscillatory tail
`∑ n^{-1-it}`, Euler-Maclaurin control of the endpoint remainder, the harmonic
majorant for the finite part, and the standard logarithmic normalization; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact Exists.intro 39
    (And.intro
      (Nat.cast_pos.mpr (show (0 : ℕ) < 39 from Nat.succ_pos 38))
      (fun t ht hpartial hfinite =>
        let hexplicit :
            ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
              boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                (1 + Real.log (2 + ‖t‖)) :=
          abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
            t ht hpartial hfinite
        let habsorb :
            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                (1 + Real.log (2 + ‖t‖)) ≤
              39 * Real.log (2 + ‖t‖) :=
          boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log ht
        le_trans hexplicit habsorb))

/-- Euler-Maclaurin/Abel-truncation boundary estimate for the Riemann zeta function on
`1 + it`.

This is the canonical classical number-theoretic input: truncate the Dirichlet
series at height comparable to `|t|`, control the tail by Euler-Maclaurin or Abel
summation, and derive the standard logarithmic bound; cf. Titchmarsh, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic

/-- The historical owner-root spelling for the boundary-line logarithmic zeta estimate.

The proof is only name transport from the canonical Abel/Euler-Maclaurin theorem on
`ζ(1 + it)`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of raw zeta on `1 + it`.

This is the smallest analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and derive the standard `O(log (2 + |t|))` boundary-line bound; cf. Titchmarsh,
The Theory of the Riemann Zeta-function, §3.5. -/
theorem classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of zeta on the line `1 + it`.

This is only the definitional transport from the raw boundary-line zeta value to the
local real-parameter name. -/
theorem classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖boundaryLineOneZetaRealParam t‖ ≤ A * Real.log (2 + ‖t‖) := by
  exact Exists.elim
    classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun t ht hpartial hfinite =>
            Eq.subst
              (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖t‖))
              (show ‖riemannZeta (boundaryLineOnePointRealParam t)‖ =
                  ‖boundaryLineOneZetaRealParam t‖ from rfl)
              (hA.right t ht hpartial hfinite))))


end LFunctions
end Boundary

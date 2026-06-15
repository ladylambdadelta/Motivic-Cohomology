import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Owner

/-!
# Boundary zeta growth consequences

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.BoundaryEulerAbel.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
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
      t ht
  exact boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    t htail

/-- The exact Abel/Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`. -/
theorem eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate t ht

/-- Public Abel/Euler-Maclaurin zeta-tail root.  The proof is now only name
transport from the canonical Euler-Maclaurin tail estimate at the exact cutoff. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit t ht

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
    (ht : 1 ≤ ‖t‖) :
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
    abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit t ht
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
    _ = (2 + 1) * L := by
      exact (add_mul 2 1 L).symm
    _ = 3 * L := rfl
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
        add_le_add (by exact three_le_four) hx_le_two_x
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
      38 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hL_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hL_nonneg : 0 ≤ L :=
    le_trans zero_le_one hL_one
  have hfour_le : (4 : ℝ) ≤ 4 * L := by
    calc
      (4 : ℝ) = 4 * 1 := by
        exact (mul_one 4).symm
      _ ≤ 4 * L :=
        mul_le_mul_of_nonneg_left hL_one (by exact zero_le_four)
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
      _ = 32 * L := rfl
  have htail :
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
        36 * L := by
    calc
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
          4 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 4 * L + 32 * L :=
        add_le_add hfour_le hsixteen_log
      _ = (4 + 32) * L := by
        exact (add_mul 4 32 L).symm
      _ = 36 * L := rfl
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
      36 * L + 2 * L :=
        add_le_add htail hfinite
    _ = (36 + 2) * L := by
      exact (add_mul 36 2 L).symm
    _ = 38 * L := rfl
    _ = 38 * Real.log (2 + ‖t‖) := rfl

/-- The finite truncation plus the Abel/Euler-Maclaurin tail gives the logarithmic
boundary estimate with the explicit Abel-tail constant still visible. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  exact
    abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
      t ht

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
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  refine ⟨38, ?_, ?_⟩
  · exact Nat.cast_pos.mpr (by decide : (0 : ℕ) < 38)
  · intro t ht
    have hexplicit :
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) :=
      abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
        t ht
    have habsorb :
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) ≤
          38 * Real.log (2 + ‖t‖) :=
      boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log ht
    exact le_trans hexplicit habsorb

/-- Euler-Maclaurin/Abel-truncation boundary estimate for the Riemann zeta function on
`1 + it`.

This is the canonical classical number-theoretic input: truncate the Dirichlet
series at height comparable to `|t|`, control the tail by Euler-Maclaurin or Abel
summation, and obtain the standard logarithmic bound; cf. Titchmarsh, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
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
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of raw zeta on `1 + it`.

This is the smallest analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound; cf. Titchmarsh,
The Theory of the Riemann Zeta-function, §3.5. -/
theorem classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
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
        ‖boundaryLineOneZetaRealParam t‖ ≤ A * Real.log (2 + ‖t‖) := by
  rcases
    classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖t‖))
    (show ‖riemannZeta (boundaryLineOnePointRealParam t)‖ =
        ‖boundaryLineOneZetaRealParam t‖ from rfl)
    (hbound t ht)

/-- A logarithmic zeta estimate on `re = 1` gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  rcases hzeta with ⟨A, hA_pos, hzeta_bound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  have hpole_norm :
      ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_le_vertical_height hw_re
  have hzeta_norm :
      ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
    hzeta_bound w hw_re hw_im
  have hzeta_rhs_nonneg :
      0 ≤ A * Real.log (2 + ‖w.im‖) :=
    le_trans (norm_nonneg (riemannZeta w)) hzeta_norm
  have hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hmul :
      ‖w - 1‖ * ‖riemannZeta w‖ ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
    mul_le_mul hpole_norm hzeta_norm hzeta_rhs_nonneg hheight_nonneg
  have htarget_eq :
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
        A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
    calc
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
          ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
        exact mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))
      _ =
          (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
        exact congrArg
          (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
          (mul_comm (1 + ‖w.im‖) A)
      _ =
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
        exact rfl
  have hnorm_eq :
      ‖(w - 1) * riemannZeta w‖ = ‖w - 1‖ * ‖riemannZeta w‖ :=
    norm_mul (w - 1) (riemannZeta w)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(w - 1) * riemannZeta w‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
      hnorm_eq.symm
      hmul)

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, proved
by Euler-Maclaurin/Abel truncation.

This is the exact analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  rcases
    classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖w.im‖))
    (norm_riemannZeta_boundaryLine_one_eq_norm_realParam hw_re).symm
    (hbound w.im hw_im)

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, in the
standard partial-summation/truncation form. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, obtained from the raw boundary-line zeta estimate and the elementary
pole-clearing factor. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation

/-- The logarithmic boundary-line zeta estimate gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_of_zeta_log
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound hzeta

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.  This is the standard boundary-line zeta estimate in the form needed before
coarsening to a finite polynomial envelope. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation

/-- A log-linear vertical-height boundary estimate gives the coarser polynomial envelope
used by the normalization chain. -/
theorem boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    {f : ℂ → ℂ}
    (hlog :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m := by
  rcases hlog with ⟨A, hA_pos, hbound⟩
  refine ⟨2 * A, 2, ?_, ?_⟩
  · exact mul_pos two_pos hA_pos
  intro w hw_re hw_im
  let H : ℝ := 1 + ‖w.im‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg w.im)
  have hlog_arg_pos : 0 < 2 + ‖w.im‖ := by
    exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) (norm_nonneg w.im)
  have hlog_le_arg :
      Real.log (2 + ‖w.im‖) ≤ 2 + ‖w.im‖ :=
    Real.log_le_self hlog_arg_pos.le
  have harg_eq : 2 + ‖w.im‖ = H + 1 := by
    change 2 + ‖w.im‖ = (1 + ‖w.im‖) + 1
    ring
  have harg_le_twoH : 2 + ‖w.im‖ ≤ 2 * H := by
    have : 2 + ‖w.im‖ = H + 1 := harg_eq
    nlinarith [this]
  have hlog_le_twoH :
      Real.log (2 + ‖w.im‖) ≤ 2 * H :=
    le_trans hlog_le_arg harg_le_twoH
  have hleft_nonneg : 0 ≤ A * H :=
    mul_nonneg (le_of_lt hA_pos) hH_nonneg
  have hmul_log_le :
      A * H * Real.log (2 + ‖w.im‖) ≤ A * H * (2 * H) :=
    mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
  have htarget_eq :
      A * H * (2 * H) = (2 * A) * H ^ (2 : ℕ) := by
    ring
  exact le_trans (hbound w hw_re hw_im)
    (Eq.subst
      (motive := fun x : ℝ =>
        A * H * Real.log (2 + ‖w.im‖) ≤ x)
      htarget_eq
      hmul_log_le)

/-- Standard polynomial vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.

This is the classical boundary-line estimate for the removable meromorphic factor
`(s - 1)ζ(s)`, stated before conversion to the coarser finite-order envelope. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  exact boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, converted from the polynomial boundary-line estimate.

This is the zeta-side finite-order theorem that must come from boundary-line estimates
for the pole-cleared meromorphic zeta function, not from the false far-right `re = 2`
Dirichlet-series route. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard

/-- The standard vertical-height finite-order estimate for `(s - 1)ζ(s)` on `re = 1`
implies the complex-height envelope consumed by the strip-normalization chain. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    (hvertical :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hvertical with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  exact le_trans (hbound w hw_re hw_im)
    (finiteOrder_vertical_envelope_le_complex_envelope
      (le_of_lt hA)
      (le_of_lt hB))

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, in the complex-height envelope used downstream. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard

/-- The removable pole-cleared boundary-line estimate implies the raw
`(s - 1)ζ(s)` boundary-line estimate on the vertical tail.

The vertical-tail hypothesis excludes the removable point `1`, so the raw product and
`poleClearedRiemannZeta` agree there. -/
theorem riemannZeta_boundaryLine_one_raw_growth_bound_of_poleCleared_growth_bound
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hpole with ⟨A, B, m, hA, hB, hpole_bound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  have hw_ne_one : w ≠ 1 := by
    intro hw
    have him_zero : w.im = 0 := by
      calc
        w.im = (1 : ℂ).im := by
          exact congrArg Complex.im hw
        _ = 0 := by
          exact Complex.one_im
    have him_norm_zero : ‖w.im‖ = 0 := by
      calc
        ‖w.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hw_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hpole_eq :
      poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
    hpole_eq
    (hpole_bound w hw_re hw_im)

/-- Pole-cleared zeta has finite-order vertical growth on the boundary line `re = 1`.

This is the smallest zeta-side analytic primitive needed on the reflected left boundary:
reflection sends `re z = 0` to `re (1 - z) = 1`, not to the `re = 2`
Dirichlet-series boundary. -/


end
end LFunctions
end Boundary

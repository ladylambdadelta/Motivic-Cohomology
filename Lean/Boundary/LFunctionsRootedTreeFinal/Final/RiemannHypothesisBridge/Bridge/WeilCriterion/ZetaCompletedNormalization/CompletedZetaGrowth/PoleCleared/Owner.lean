import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FunctionalEquationTransport.Owner

/-!
# Pole-cleared zeta growth

This owner layer contains finite-order estimates for the pole-cleared zeta factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_lt_one_real : (0 : ℝ) < 1 :=
  zero_lt_one

/-- Helper: Algebraic identity for polynomial coefficient. -/
private lemma poly_coeff_identity (P : ℝ) : 3 * P + 3 = 3 * (P + 1) := by
  calc
    3 * P + 3 = 3 * P + 3 * 1 := by
      exact congrArg (fun x : ℝ => 3 * P + x) (mul_one 3).symm
    _ = 3 * (P + 1) := by
      exact (mul_add 3 P 1).symm

/-- Helper: Algebraic regrouping for the completed-zeta pole bound. -/
private lemma pole_bound_coeff_regroup (P : ℝ) :
    (P + 2) + (2 * P + 1) = 3 * P + 3 := by
  calc
    (P + 2) + (2 * P + 1) =
        (P + 2 * P) + (2 + 1) := by
      exact add_add_add_comm P 2 (2 * P) 1
    _ = (P + 2 * P) + 3 := by
      have h : (2 : ℝ) + 1 = 3 := two_add_one_eq_three
      exact congrArg (fun x : ℝ => (P + 2 * P) + x) h
    _ = ((1 : ℝ) * P + 2 * P) + 3 := by
      exact congrArg (fun x : ℝ => (x + 2 * P) + 3) (one_mul P).symm
    _ = ((1 : ℝ) + 2) * P + 3 := by
      exact congrArg (fun x : ℝ => x + 3) (add_mul 1 2 P).symm
    _ = 3 * P + 3 := by
      have h : (1 : ℝ) + 2 = 3 :=
        (add_comm (1 : ℝ) 2).trans two_add_one_eq_three
      exact congrArg (fun x : ℝ => x * P + 3) h

/-- Helper: Arithmetic normalization for the far-right pole face. -/
private lemma one_add_neg_two_eq_neg_one : (1 : ℝ) + (-2) = -1 := by
  calc
    (1 : ℝ) + (-2) = 1 + (-(1 + 1)) := by
      exact congrArg (fun x : ℝ => 1 + (-x)) (one_add_one_eq_two.symm)
    _ = 1 + ((-1) + (-1)) := by
      exact congrArg (fun x : ℝ => 1 + x) (neg_add 1 1)
    _ = (1 + (-1)) + (-1) := by
      exact (add_assoc 1 (-1) (-1)).symm
    _ = 0 + (-1) := by
      exact congrArg (fun x : ℝ => x + (-1)) (add_neg_cancel 1)
    _ = -1 := by
      exact zero_add (-1)

/-- Helper: Integer inequality for sum. -/
private lemma int_sum_ineq (n : ℕ) : (1 : ℤ) - (n : ℤ) - 1 = -(n : ℤ) := by
  calc
    (1 : ℤ) - (n : ℤ) - 1 =
        1 + (-(n : ℤ)) + (-1) := by
      exact congrArg (fun x : ℤ => x + (-1)) (sub_eq_add_neg 1 (n : ℤ))
    _ = 1 + (-1) + (-(n : ℤ)) := by
      exact add_right_comm 1 (-(n : ℤ)) (-1)
    _ = 0 - (n : ℤ) := by
      exact congrArg (fun x : ℤ => x + (-(n : ℤ))) (add_neg_cancel 1)
    _ = -(n : ℤ) := Int.zero_sub (n : ℤ)

/-- Helper: One is at most two. -/
private lemma one_le_two : (1 : ℝ) ≤ 2 :=
  calc
    (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
    _ = 2 := by
      exact one_add_one_eq_two

/-- Global reflected Abel truncation package needed on the left edge `re = 0`. -/
def ReflectedBoundaryAbelPartialMajorant : Prop :=
  ∀ z : ℂ,
    z.re = 0 →
    1 ≤ ‖z.im‖ →
    boundaryLineOneVerticalTruncationHypotheses ((1 : ℂ) - z)

/-- Reflection transports the `re = 1` Abel truncation package to the left edge
`re = 0`. -/
theorem reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
    (hpartial : BoundaryLineOneAbelPartialMajorant) :
    ReflectedBoundaryAbelPartialMajorant := by
  exact
    fun z hz_re hz_im =>
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
          ‖w.im‖ = ‖-z.im‖ := by
            exact congrArg norm him_eq
          _ = ‖z.im‖ := by
            exact norm_neg z.im
      have hw_im : 1 ≤ ‖w.im‖ :=
        Eq.subst (motive := fun x : ℝ => 1 ≤ x) hw_im_norm.symm hz_im
      hpartial w hw_re hw_im

/-- Uniform bounded-boundary vertical-tail input for the right critical strip. -/
def PoleClearedRightCriticalStripBoundedTailBoundary : Prop :=
  ∃ A : ℝ,
    0 < A ∧
    (∀ z : ℂ,
      z.re = 0 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A) ∧
    (∀ z : ℂ,
      z.re = 2 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A)

/-- Uniform bounded-boundary compact-height input for the right critical strip. -/
def PoleClearedRightCriticalStripCompactBoundaryBound : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    (∀ z : ℂ,
      z.re = 0 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C) ∧
    (∀ z : ℂ,
      z.re = 2 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C)

/-- The compact-height boundary input on the right critical strip follows from
the owner compact bound on the closed rectangle `0 ≤ re ≤ 2`, `|im| ≤ 1`. -/
theorem poleClearedRightCriticalStripCompactBoundaryBound_from_compact :
    PoleClearedRightCriticalStripCompactBoundaryBound := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_zero : 0 ≤ z.re :=
              le_of_eq hz_re.symm
            have hz_two : z.re ≤ 2 :=
              le_trans (le_of_eq hz_re) zero_le_two
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_zero : 0 ≤ z.re :=
              le_trans zero_le_two (le_of_eq hz_re.symm)
            have hz_two : z.re ≤ 2 :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            hC_bound z hz_mem⟩

/-- Admissible finite-order growth input on the full right critical strip. -/
def PoleClearedRightCriticalStripAdmissibleGrowth : Prop :=
  ∃ c : ℝ,
    c < Real.pi / (2 - 0) ∧
    ∃ D : ℝ,
      poleClearedRiemannZeta =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))

/-- Ordinary finite-order growth on the reflected half of the right critical
strip.

This is the precise noncircular analytic half-strip theorem for the
right-critical admissible-growth owner: the completed functional equation on
`0 ≤ Re s ≤ 1` transports the Euler-Maclaurin finite-order estimate on
`1 ≤ Re (1 - s) ≤ 2`, with the Gamma/Stirling multiplier bounds. -/
def PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth : Prop :=
  ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
    0 < A ∧
    0 < B ∧
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ 1 →
      ‖poleClearedRiemannZeta z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)

/-- The denominator in the zero-one pole-clearing quotient is `-z`. -/
private lemma poleClearingQuotient_zeroOne_denominator_eq_neg
    (z : ℂ) :
    (((1 : ℂ) - z) - 1) = -z := by
  calc
    (((1 : ℂ) - z) - 1) = ((1 : ℂ) + -z) - 1 := by
      exact congrArg (fun x : ℂ => x - 1) (sub_eq_add_neg (1 : ℂ) z)
    _ = ((1 : ℂ) + -z) + (-1) := by
      exact sub_eq_add_neg ((1 : ℂ) + -z) 1
    _ = ((1 : ℂ) + (-1)) + -z := by
      exact add_right_comm (1 : ℂ) (-z) (-1)
    _ = (0 : ℂ) + -z := by
      exact congrArg (fun x : ℂ => x + -z) (add_neg_cancel (1 : ℂ))
    _ = -z := by
      exact zero_add (-z)

/-- The zero-one quotient denominator has the same norm as `z`. -/
private lemma poleClearingQuotient_zeroOne_denominator_norm_eq
    (z : ℂ) :
    ‖(((1 : ℂ) - z) - 1)‖ = ‖z‖ := by
  have hden : (((1 : ℂ) - z) - 1) = -z :=
    poleClearingQuotient_zeroOne_denominator_eq_neg z
  calc
    ‖(((1 : ℂ) - z) - 1)‖ = ‖-z‖ := by
      exact congrArg norm hden
    _ = ‖z‖ := by
      exact norm_neg z

/-- The numerator of the pole-clearing quotient is bounded by `‖z‖ + 1`. -/
private lemma poleClearingQuotient_zeroOne_numerator_norm_le
    (z : ℂ) :
    ‖z - 1‖ ≤ ‖z‖ + 1 := by
  have htriangle : ‖z - (1 : ℂ)‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
    norm_sub_le z (1 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    exact complex_one_norm_eq_one
  exact Eq.subst
    (motive := fun x : ℝ => ‖z - (1 : ℂ)‖ ≤ ‖z‖ + x)
    hone_norm
    htriangle

/-- On the vertical tail, the pole-clearing quotient is linearly bounded. -/
private lemma poleClearingQuotient_zeroOne_norm_le_linear
    (z : ℂ)
    (hz_im_tail : (1 : ℝ) ≤ ‖z.im‖) :
    ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ ‖z‖ + 1 := by
  have hz_norm_tail : (1 : ℝ) ≤ ‖z‖ :=
    le_trans hz_im_tail (Complex.norm_im_le_norm z)
  have hden_norm :
      ‖(((1 : ℂ) - z) - 1)‖ = ‖z‖ :=
    poleClearingQuotient_zeroOne_denominator_norm_eq z
  have hden_tail : (1 : ℝ) ≤ ‖(((1 : ℂ) - z) - 1)‖ :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hden_norm.symm
      hz_norm_tail
  have hquot_norm :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
        ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ :=
    norm_div (z - 1) (((1 : ℂ) - z) - 1)
  have hquot_le_num :
      ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ ≤ ‖z - 1‖ :=
    div_le_self (norm_nonneg (z - 1)) hden_tail
  calc
    ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
        ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ := hquot_norm
    _ ≤ ‖z - 1‖ := hquot_le_num
    _ ≤ ‖z‖ + 1 := poleClearingQuotient_zeroOne_numerator_norm_le z

/-- The degree-one exponential envelope absorbs the linear quotient bound. -/
private lemma poleClearingQuotient_zeroOne_linear_le_exponential_envelope
    (z : ℂ) :
    ‖z‖ + 1 ≤
      (2 : ℝ) * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
  have hpow_one : (1 + ‖z‖) ^ (1 : ℕ) = 1 + ‖z‖ := by
    exact pow_one (1 + ‖z‖)
  have hone_mul : (1 : ℝ) * (1 + ‖z‖) = 1 + ‖z‖ := by
    exact one_mul (1 + ‖z‖)
  have hexponent :
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = 1 + ‖z‖ := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
          (1 : ℝ) * (1 + ‖z‖) := by
        exact congrArg (fun x : ℝ => (1 : ℝ) * x) hpow_one
      _ = 1 + ‖z‖ := hone_mul
  have hlinear_to_exp :
      ‖z‖ + 1 ≤ Real.exp (1 + ‖z‖) := by
    have hlinear_to_exp_norm : ‖z‖ + 1 ≤ Real.exp ‖z‖ :=
      Real.add_one_le_exp ‖z‖
    have hexp_norm_le_exp_one_add :
        Real.exp ‖z‖ ≤ Real.exp (1 + ‖z‖) :=
      Real.exp_le_exp.mpr
        (le_add_of_nonneg_left zero_le_one)
    have hlinear_to_exp_one_add :
        ‖z‖ + 1 ≤ Real.exp (1 + ‖z‖) :=
      le_trans hlinear_to_exp_norm hexp_norm_le_exp_one_add
    exact hlinear_to_exp_one_add
  have hexp_le_scaled :
      Real.exp (1 + ‖z‖) ≤
        (2 : ℝ) * Real.exp (1 + ‖z‖) := by
    exact le_mul_of_one_le_left
      (le_of_lt (Real.exp_pos (1 + ‖z‖)))
      one_le_two
  have htarget_exp :
      Real.exp (1 + ‖z‖) =
        Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
    exact congrArg Real.exp hexponent.symm
  calc
    ‖z‖ + 1 ≤ Real.exp (1 + ‖z‖) := hlinear_to_exp
    _ ≤ (2 : ℝ) * Real.exp (1 + ‖z‖) := hexp_le_scaled
    _ = (2 : ℝ) * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
      exact congrArg (fun x : ℝ => (2 : ℝ) * x) htarget_exp

/-- Elementary finite-order control of the pole-clearing quotient on the
zero-one vertical band.

This is the algebraic denominator estimate in the raw completed-functional-
equation multiplier.  It is independent of the special-function input: the
tail condition keeps the denominator `((1 : ℂ) - z) - 1 = -z` away from zero,
and the numerator is at most linear in the same height variable. -/
theorem poleClearedRiemannZeta_zero_one_strip_poleClearingQuotient_growth_ownerVerticalBandAlgebra :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    ⟨2, 1, 1, zero_lt_two, zero_lt_one,
      fun z _hz_re_nonneg _hz_re_le_one hz_im_tail =>
        le_trans
          (poleClearingQuotient_zeroOne_norm_le_linear z hz_im_tail)
          (poleClearingQuotient_zeroOne_linear_le_exponential_envelope z)⟩

/-- Gamma/Stirling finite-order control of the reflected Gamma-real ratio on the
zero-one vertical band.

This is the special-function input for the raw completed-functional-equation
multiplier: sectorial/vertical recurrence Stirling bounds for
`Gammaℝ (1 - z) / Gammaℝ z`, uniformly on `0 ≤ Re z ≤ 1` and `|Im z| ≥ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_GammaRatio_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match Gammaℝ_one_sub_zeroOneStrip_verticalTail_stirling_growth_bound hbranch with
  | ⟨An, Bn, mn, hAn_pos, hBn_pos, hn_bound⟩ =>
  match Gammaℝ_rightCriticalStrip_verticalTail_reciprocal_stirling_growth_bound hbranch with
  | ⟨Ad, Bd, md, hAd_pos, hBd_pos, hd_bound⟩ =>
      refine ⟨An * Ad, 2 * (Bn + Bd + 1), mn + md,
        mul_pos hAn_pos hAd_pos,
        mul_pos zero_lt_two (add_pos (add_pos hBn_pos hBd_pos) zero_lt_one),
        ?_⟩
      intro z hz_re_nonneg hz_re_le_one hz_im_tail
      let H : ℝ := 1 + ‖z‖
      have hBn_nonneg : 0 ≤ Bn := le_of_lt hBn_pos
      have hBd_nonneg : 0 ≤ Bd := le_of_lt hBd_pos
      have hAn_nonneg : 0 ≤ An := le_of_lt hAn_pos
      have hAd_nonneg : 0 ≤ Ad := le_of_lt hAd_pos
      have hn_enlarge :
          An * Real.exp (Bn * H ^ mn) ≤
            An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
        exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAn_nonneg
          (le_refl An)
          (by
            calc
              Bn ≤ Bn + Bd := le_add_of_nonneg_right hBd_nonneg
              _ ≤ Bn + Bd + 1 := le_add_of_nonneg_right zero_le_one)
          hBn_nonneg
          (Nat.le_add_right mn md)
      have hmd_le : md ≤ mn + md := by
        exact Eq.subst
          (motive := fun d : ℕ => md ≤ d)
          (Nat.add_comm md mn)
          (Nat.le_add_right md mn)
      have hd_enlarge :
          Ad * Real.exp (Bd * H ^ md) ≤
            Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
        exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAd_nonneg
          (le_refl Ad)
          (by
            calc
              Bd ≤ Bn + Bd := le_add_of_nonneg_left hBn_nonneg
              _ ≤ Bn + Bd + 1 := le_add_of_nonneg_right zero_le_one)
          hBd_nonneg
          hmd_le
      have hn_target :
          ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ ≤
            An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
        (hn_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hn_enlarge
      have hd_target :
          ‖(Complex.Gammaℝ z)⁻¹‖ ≤
            Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
        (hd_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hd_enlarge
      have hnorm :
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ =
            ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ *
              ‖(Complex.Gammaℝ z)⁻¹‖ := by
        calc
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ =
              ‖Complex.Gammaℝ ((1 : ℂ) - z) *
                (Complex.Gammaℝ z)⁻¹‖ :=
            congrArg norm
              (div_eq_mul_inv
                (Complex.Gammaℝ ((1 : ℂ) - z)) (Complex.Gammaℝ z))
          _ = ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ *
              ‖(Complex.Gammaℝ z)⁻¹‖ :=
            norm_mul (Complex.Gammaℝ ((1 : ℂ) - z)) (Complex.Gammaℝ z)⁻¹
      have hproduct :
          ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ *
              ‖(Complex.Gammaℝ z)⁻¹‖ ≤
            (An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) *
              (Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) :=
        mul_le_mul hn_target hd_target
          (norm_nonneg ((Complex.Gammaℝ z)⁻¹))
          (mul_nonneg hAn_nonneg
            (le_of_lt (Real.exp_pos ((Bn + Bd + 1) * H ^ (mn + md)))))
      have hcollapse :
          (An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) *
              (Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) =
            An * Ad * Real.exp ((2 * (Bn + Bd + 1)) * H ^ (mn + md)) :=
        finiteOrderGrowthProductEnvelope_exp_collapse
          An Ad (Bn + Bd + 1) (H ^ (mn + md))
      calc
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ =
            ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ *
              ‖(Complex.Gammaℝ z)⁻¹‖ := hnorm
        _ ≤ (An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) *
              (Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md))) :=
          hproduct
        _ = An * Ad * Real.exp ((2 * (Bn + Bd + 1)) * H ^ (mn + md)) :=
          hcollapse

/-- Product assembly for the raw completed-functional-equation multiplier on the
zero-one vertical band.

This is only finite-order bookkeeping: combine the pole-clearing quotient
envelope with the Gamma-ratio envelope and use multiplicativity of the norm. -/
theorem poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_of_poleClearingQuotient_and_GammaRatio
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hgamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hpole with ⟨Ap, Bp, mp, hAp, hBp, hpole_bound⟩
  rcases hgamma with ⟨Ag, Bg, mg, hAg, hBg, hgamma_bound⟩
  refine ⟨Ap * Ag, 2 * (Bp + Bg + 1), mp + mg,
    mul_pos hAp hAg,
    mul_pos zero_lt_two (add_pos (add_pos hBp hBg) zero_lt_one), ?_⟩
  intro z hz_re_nonneg hz_re_le_one hz_im_tail
  let H : ℝ := 1 + ‖z‖
  have hBp_nonneg : 0 ≤ Bp := le_of_lt hBp
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hAp_nonneg : 0 ≤ Ap := le_of_lt hAp
  have hAg_nonneg : 0 ≤ Ag := le_of_lt hAg
  have hpole_enlarge :
      Ap * Real.exp (Bp * H ^ mp) ≤
        Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAp_nonneg
      (le_refl Ap)
      (by
        calc
          Bp ≤ Bp + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bp + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBp_nonneg
      (Nat.le_add_right mp mg)
  have hmg_le : mg ≤ mp + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mp)
      (Nat.le_add_right mg mp)
  have hgamma_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      hAg_nonneg
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bp + Bg := le_add_of_nonneg_left hBp_nonneg
          _ ≤ Bp + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hpole_target :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
        Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
    (hpole_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hpole_enlarge
  have hgamma_target :
      ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
        Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
    (hgamma_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hgamma_enlarge
  have hnorm :
      ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
    norm_mul ((z - 1) / (((1 : ℂ) - z) - 1))
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  have hproduct :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
        (Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) *
          (Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) :=
    mul_le_mul hpole_target hgamma_target
      (norm_nonneg (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z))
      (mul_nonneg hAp_nonneg
        (le_of_lt (Real.exp_pos ((Bp + Bg + 1) * H ^ (mp + mg)))))
  have hcollapse :
      (Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) *
          (Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) =
        Ap * Ag * Real.exp ((2 * (Bp + Bg + 1)) * H ^ (mp + mg)) :=
    finiteOrderGrowthProductEnvelope_exp_collapse
      Ap Ag (Bp + Bg + 1) (H ^ (mp + mg))
  calc
    ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ := hnorm
    _ ≤ (Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) *
          (Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg))) := hproduct
    _ = Ap * Ag * Real.exp ((2 * (Bp + Bg + 1)) * H ^ (mp + mg)) :=
      hcollapse

/-- Holomorphicity of the removable pole-cleared zeta on the open strip
`0 < Re s < 1`, inherited from the larger right-critical strip. -/
theorem poleClearedRiemannZeta_zero_one_strip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 0 1) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl.mono
    (fun _z hz => ⟨hz.1, lt_trans hz.2 one_lt_two⟩)

/-- Raw Gamma/Stirling multiplier bound on the closed critical band
`0 ≤ Re s ≤ 1`, away from the real-axis removable point.

This is the genuine Gamma/Stirling input for the zero-one reflected-band
transport.  The already available left-half-plane multiplier theorem does not
apply on this band; the proof belongs to the sectorial/vertical recurrence
Stirling package for the ratio
`Gammaℝ (1 - z) / Gammaℝ z`, together with the elementary pole-clearing factor. -/
theorem poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_of_poleClearingQuotient_and_GammaRatio
      poleClearedRiemannZeta_zero_one_strip_poleClearingQuotient_growth_ownerVerticalBandAlgebra
      (poleClearedRiemannZeta_zero_one_strip_GammaRatio_growth_ownerGammaStirling
        hbranch)

/-- Gamma/Stirling owner bound for the completed-functional-equation multiplier
on the reflected closed band `0 ≤ Re s ≤ 1`.

This is only the multiplier part of the noncircular zero-one strip transport:
it estimates the completed-functional-equation factor itself, uniformly on the
vertical tail of the closed reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match
      poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch with
  | ⟨A, B, m, hA_pos, hB_pos, hraw_bound⟩ =>
      exact
        ⟨A, B, m, hA_pos, hB_pos,
          fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
            have hz_ne_zero : z ≠ 0 :=
              fun hz_zero =>
                have hzero_im : z.im = 0 := by
                  calc
                    z.im = (0 : ℂ).im := by
                      exact congrArg Complex.im hz_zero
                    _ = 0 := Complex.zero_im
                have htail_zero : (1 : ℝ) ≤ 0 := by
                  exact Eq.subst
                    (motive := fun x : ℝ => (1 : ℝ) ≤ ‖x‖)
                    hzero_im
                    hz_im_tail
                not_lt_of_ge htail_zero zero_lt_one
            have hz_norm_tail : 1 ≤ ‖z‖ :=
              le_trans hz_im_tail (Complex.norm_im_le_norm z)
            have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
              Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
                hz_re_nonneg hz_norm_tail
            have hmult_eq :
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                  ((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
              unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
              exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)
            exact Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hmult_eq.symm
              (hraw_bound z hz_re_nonneg hz_re_le_one hz_im_tail)⟩

/-- Raw pole-cleared algebra for the completed functional equation, with the
nonzero denominators supplied explicitly rather than inferred from the left
half-plane. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient_of_denominators
    {z : ℂ}
    (hz_ne_one : z ≠ 1)
    (hw_ne_one : ((1 : ℂ) - z) ≠ 1)
    (hw_minus_one_ne_zero : (((1 : ℂ) - z) - 1) ≠ 0)
    (hzeta :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :
    poleClearedRiemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hpz :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hpw :
      poleClearedRiemannZeta ((1 : ℂ) - z) =
        (((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  let a : ℂ := z - 1
  let b : ℂ := ((1 : ℂ) - z) - 1
  let c : ℂ := riemannZeta ((1 : ℂ) - z)
  let d : ℂ := Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
  have halg : ((a / b) * d) * (b * c) = a * (c * d) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_algebra
      hw_minus_one_ne_zero
  have hleft :
      poleClearedRiemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
    calc
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z := hpz
      _ = (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
        exact congrArg (fun x : ℂ => (z - 1) * x) hzeta
      _ = (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
        exact congrArg (fun x : ℂ => (z - 1) * x)
          (mul_div_assoc
            (riemannZeta ((1 : ℂ) - z))
            (Complex.Gammaℝ ((1 : ℂ) - z))
            (Complex.Gammaℝ z))
  calc
    poleClearedRiemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := hleft
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
      exact halg.symm
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
      exact congrArg
        (fun x : ℂ =>
          (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) * x)
        hpw.symm

/-- Quotient form of the completed functional equation on the zero-one vertical
tail.  This is the analytic continuation step needed beyond the imported
left-half-plane transport. -/
theorem riemannZeta_zero_one_strip_completedFunctionalEquation_quotient_ownerStripContinuation
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    riemannZeta z =
      riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
  have hz_ne_zero : z ≠ 0 :=
    fun hz_zero =>
      have hzero_im : z.im = 0 := by
        calc
          z.im = (0 : ℂ).im := by
            exact congrArg Complex.im hz_zero
          _ = 0 := Complex.zero_im
      have htail_zero : (1 : ℝ) ≤ 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ ‖x‖)
          hzero_im
          hz_im_tail
      not_lt_of_ge htail_zero zero_lt_one
  have hw_re_nonneg : 0 ≤ ((1 : ℂ) - z).re := by
    have hw_re_eq : ((1 : ℂ) - z).re = 1 - z.re := by
      calc
        ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
          exact Complex.sub_re (1 : ℂ) z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
    have hzero_le_sub : 0 ≤ 1 - z.re := by
      calc
        0 = 1 - 1 := by
          exact (sub_self 1).symm
        _ ≤ 1 - z.re := by
          exact sub_le_sub_left hz_re_le_one 1
    exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hw_re_eq.symm
      hzero_le_sub
  have hw_im_norm : ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
    have him_eq : ((1 : ℂ) - z).im = -z.im := by
      calc
        ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im (1 : ℂ) z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    calc
      ‖((1 : ℂ) - z).im‖ = ‖-z.im‖ := by
        exact congrArg norm him_eq
      _ = ‖z.im‖ := by
        exact norm_neg z.im
  have hw_im_tail : 1 ≤ ‖((1 : ℂ) - z).im‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      hw_im_norm.symm
      hz_im_tail
  have hGamma_reflected_ne :
      Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      hw_re_nonneg
      (one_le_norm_of_one_le_norm_im hw_im_tail)
  have hcompleted_symm :
      completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) := by
    exact (completedRiemannZeta_one_sub z).symm
  have hw_ne_zero : ((1 : ℂ) - z) ≠ 0 :=
    fun hw_zero =>
      have hzero_im : ((1 : ℂ) - z).im = 0 := by
        calc
          ((1 : ℂ) - z).im = (0 : ℂ).im := by
            exact congrArg Complex.im hw_zero
          _ = 0 := Complex.zero_im
      have htail_zero : (1 : ℝ) ≤ 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ ‖x‖)
          hzero_im
          hw_im_tail
      not_lt_of_ge htail_zero zero_lt_one
  have hζw := riemannZeta_def_of_ne_zero (s := ((1 : ℂ) - z)) hw_ne_zero
  have hGamma_z_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      hz_re_nonneg
      (one_le_norm_of_one_le_norm_im hz_im_tail)
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
      exact Eq.refl _

/-- Interior closed-band continuation of the pole-cleared completed functional
equation identity.

The imported functional-equation multiplier identity currently owns the closed
left half-plane.  The zero-one strip transport additionally needs the same
pointwise identity after analytic continuation across the critical band,
excluding the left edge already handled by the left-half-plane theorem below. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerStripContinuation
    (z : ℂ)
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖)
    (hz_not_left_edge : z.re ≠ 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hz_ne_zero : z ≠ 0 :=
    fun hz_zero =>
      have hzero_re : z.re = 0 := by
        calc
          z.re = (0 : ℂ).re := by
            exact congrArg Complex.re hz_zero
          _ = 0 := Complex.zero_re
      hz_not_left_edge hzero_re
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      hz_re_nonneg
      (one_le_norm_of_one_le_norm_im hz_im_tail)
  have hM_raw :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
        ((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
    unfold poleClearedRiemannZeta_completedFunctionalEquationMultiplier
    exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)
  have hz_ne_one : z ≠ 1 :=
    fun hz_one =>
      have hone_im : z.im = 0 := by
        calc
          z.im = (1 : ℂ).im := by
            exact congrArg Complex.im hz_one
          _ = 0 := Complex.one_im
      have htail_zero : (1 : ℝ) ≤ 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ ‖x‖)
          hone_im
          hz_im_tail
      not_lt_of_ge htail_zero zero_lt_one
  have hw_minus_one_ne_zero : (((1 : ℂ) - z) - 1) ≠ 0 :=
    fun hden =>
      have hw_one : ((1 : ℂ) - z) = 1 :=
        sub_eq_zero.mp hden
      have him_eq : z.im = 0 := by
        have hleft_im : ((1 : ℂ) - z).im = (1 : ℂ).im := by
          exact congrArg Complex.im hw_one
        have hneg_im_zero : -z.im = 0 := by
          calc
            -z.im = 0 - z.im := by
              exact (zero_sub z.im).symm
            _ = (1 : ℂ).im - z.im := by
              exact congrArg (fun x : ℝ => x - z.im) Complex.one_im.symm
            _ = ((1 : ℂ) - z).im := by
              exact (Complex.sub_im (1 : ℂ) z).symm
            _ = (1 : ℂ).im := hleft_im
            _ = 0 := Complex.one_im
        exact neg_eq_zero.mp hneg_im_zero
      have htail_zero : (1 : ℝ) ≤ 0 := by
        exact Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ ‖x‖)
          him_eq
          hz_im_tail
      not_lt_of_ge htail_zero zero_lt_one
  have hw_ne_one : ((1 : ℂ) - z) ≠ 1 :=
    fun hw_one =>
      hw_minus_one_ne_zero (sub_eq_zero.mpr hw_one)
  have hquotient :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z :=
    riemannZeta_zero_one_strip_completedFunctionalEquation_quotient_ownerStripContinuation
      hz_re_nonneg hz_re_le_one hz_im_tail
  have hraw :
      poleClearedRiemannZeta z =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          poleClearedRiemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient_of_denominators
      hz_ne_one hw_ne_one hw_minus_one_ne_zero hquotient
  calc
    poleClearedRiemannZeta z =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          poleClearedRiemannZeta ((1 : ℂ) - z) := hraw
    _ =
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
          poleClearedRiemannZeta ((1 : ℂ) - z) := by
      exact congrArg
        (fun w : ℂ => w * poleClearedRiemannZeta ((1 : ℂ) - z))
        hM_raw.symm

/-- Pointwise completed-functional-equation identity for the pole-cleared factor
on the closed reflected band `0 ≤ Re s ≤ 1`, restricted to the vertical tail.

The left-half-plane identity already exists upstream.  This wrapper uses it on
the left edge and leaves only the genuine interior strip-continuation statement
as owner content. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
    (z : ℂ)
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  match eq_or_ne z.re 0 with
  | Or.inl hz_left_edge =>
      have hz_re_left : z.re ≤ 0 :=
        le_of_eq hz_left_edge
      exact
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity
          hz_re_left
  | Or.inr hz_not_left_edge =>
      exact
        poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerStripContinuation
          z hz_re_nonneg hz_re_le_one hz_im_tail hz_not_left_edge

/-- Unconditional noncircular finite-order envelope for the reflected zero-one
band.

The boundary and compact-height hypotheses used by the surrounding transport
package do not own this estimate.  The real analytic content is a finite-order
bound for `poleClearedRiemannZeta (1 - z)` while `z` remains in the same closed
band `0 ≤ Re z ≤ 1`, so the proof must come from the zero-one functional-
equation/Stirling continuation package itself, not from the later PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeroOne with
  | ⟨A, B, m, hA_pos, hB_pos, hbound⟩ =>
      exact
        ⟨A, B * (2 : ℝ) ^ m, m, hA_pos,
          mul_pos hB_pos (pow_pos zero_lt_two m),
          fun z hz_re_nonneg hz_re_le_one _hz_im_tail =>
            let w : ℂ := (1 : ℂ) - z
            let H : ℝ := 1 + ‖z‖
            have hw_re_eq : w.re = 1 - z.re := by
              calc
                w.re = ((1 : ℂ) - z).re := rfl
                _ = (1 : ℂ).re - z.re := Complex.sub_re (1 : ℂ) z
                _ = 1 - z.re := by
                  exact congrArg (fun x : ℝ => x - z.re) Complex.one_re
            have hw_re_nonneg : 0 ≤ w.re := by
              have hraw : 0 ≤ 1 - z.re :=
                sub_nonneg.mpr hz_re_le_one
              exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hw_re_eq.symm hraw
            have hw_re_le_one : w.re ≤ 1 := by
              have hraw : 1 - z.re ≤ 1 := by
                calc
                  1 - z.re ≤ 1 - 0 := sub_le_sub_left hz_re_nonneg 1
                  _ = 1 := sub_zero 1
              exact Eq.subst (motive := fun x : ℝ => x ≤ 1) hw_re_eq.symm hraw
            have hnorm_w : ‖w‖ ≤ H := by
              calc
                ‖w‖ = ‖(1 : ℂ) - z‖ := rfl
                _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le (1 : ℂ) z
                _ = 1 + ‖z‖ := by
                  exact congrArg (fun x : ℝ => x + ‖z‖)
                    (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
                _ = H := rfl
            have hH_nonneg : 0 ≤ H :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
            have hbase_w_nonneg : 0 ≤ 1 + ‖w‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
            have hbase_le : 1 + ‖w‖ ≤ 2 * H := by
              calc
                1 + ‖w‖ ≤ 1 + H := add_le_add_left hnorm_w 1
                _ = 1 + (1 + ‖z‖) := rfl
                _ = 2 + ‖z‖ := by
                  exact (add_assoc 1 1 ‖z‖).symm
                _ ≤ 2 + 2 * ‖z‖ := by
                  exact add_le_add_left
                    (le_mul_of_one_le_left (norm_nonneg z) one_le_two) 2
                _ = 2 * H := by
                  calc
                    2 + 2 * ‖z‖ = 2 * 1 + 2 * ‖z‖ := by
                      exact congrArg (fun x : ℝ => x + 2 * ‖z‖) (mul_one 2).symm
                    _ = 2 * (1 + ‖z‖) := (mul_add 2 1 ‖z‖).symm
                    _ = 2 * H := rfl
            have hpow_le : (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
              pow_le_pow_left₀ hbase_w_nonneg hbase_le m
            have htwoH_pow :
                (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
              mul_pow 2 H m
            have hexp_arg :
                B * (1 + ‖w‖) ^ m ≤ B * ((2 : ℝ) ^ m * H ^ m) :=
              mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB_pos)
            have harg_target :
                B * ((2 : ℝ) ^ m * H ^ m) =
                  (B * (2 : ℝ) ^ m) * H ^ m := by
              exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
            have hraw :
                ‖poleClearedRiemannZeta w‖ ≤
                  A * Real.exp (B * (1 + ‖w‖) ^ m) :=
              hbound w hw_re_nonneg hw_re_le_one
            have hexp_le :
                Real.exp (B * (1 + ‖w‖) ^ m) ≤
                  Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
              Real.exp_le_exp.mpr
                (le_trans hexp_arg (le_of_eq harg_target))
            have htarget :
                A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
                  A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
              mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA_pos)
            le_trans hraw htarget⟩

/-- Noncircular finite-order envelope for the reflected value in the self-
reflected zero-one strip transport.

The map `z ↦ 1 - z` preserves the closed band `0 ≤ Re z ≤ 1`; hence this is not
an Euler one-two-strip estimate in disguise.  It is the remaining analytic
interior estimate needed before the pointwise completed-functional-equation
identity can be converted into vertical-tail growth for `poleClearedRiemannZeta`
itself. -/
theorem poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_ownerSelfReflectedEnvelope
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
      hzeroOne

/-- Core self-reflected completed-functional-equation transport on `0 ≤ Re s ≤ 1`.

This is the exact remaining noncircular analytic content after the multiplier
bound has been separated: prove the pole-cleared completed-functional-equation
identity on the closed zero-one band, then combine it with a finite-order
envelope for the reflected value `poleClearedRiemannZeta (1 - z)` on the same
band.  The boundary hypotheses are available for the two vertical edges and
compact-height patching, but they do not by themselves give the interior
reflected-band envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport_core
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hmult with
  | ⟨AM, BM, mM, hAM_pos, hBM_pos, hM_bound⟩ =>
      match
          poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_ownerSelfReflectedEnvelope
            hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary with
      | ⟨Af, Bf, mf, hAf_pos, hBf_pos, hf_bound⟩ =>
          exact
            ⟨AM * Af, 2 * (BM + Bf + 1), mM + mf,
              mul_pos hAM_pos hAf_pos,
              mul_pos zero_lt_two
                (add_pos (add_pos hBM_pos hBf_pos) zero_lt_one),
              fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
                let H : ℝ := 1 + ‖z‖
                have hBM_nonneg : 0 ≤ BM :=
                  le_of_lt hBM_pos
                have hBf_nonneg : 0 ≤ Bf :=
                  le_of_lt hBf_pos
                have hAM_nonneg : 0 ≤ AM :=
                  le_of_lt hAM_pos
                have hAf_nonneg : 0 ≤ Af :=
                  le_of_lt hAf_pos
                have hM_enlarge :
                    AM * Real.exp (BM * H ^ mM) ≤
                      AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    hAM_nonneg
                    (le_refl AM)
                    (by
                      calc
                        BM ≤ BM + Bf := le_add_of_nonneg_right hBf_nonneg
                        _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
                    hBM_nonneg
                    (Nat.le_add_right mM mf)
                have hmf_le : mf ≤ mM + mf := by
                  exact Eq.subst
                    (motive := fun d : ℕ => mf ≤ d)
                    (Nat.add_comm mf mM)
                    (Nat.le_add_right mf mM)
                have hf_enlarge :
                    Af * Real.exp (Bf * H ^ mf) ≤
                      Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    hAf_nonneg
                    (le_refl Af)
                    (by
                      calc
                        Bf ≤ BM + Bf := le_add_of_nonneg_left hBM_nonneg
                        _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
                    hBf_nonneg
                    hmf_le
                have hM_target :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
                      AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  (hM_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hM_enlarge
                have hf_target :
                    ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  (hf_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hf_enlarge
                have hidentity :
                    poleClearedRiemannZeta z =
                      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                        poleClearedRiemannZeta ((1 : ℂ) - z) :=
                  poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
                    z hz_re_nonneg hz_re_le_one hz_im_tail
                have hidentity_norm :
                    ‖poleClearedRiemannZeta z‖ =
                      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ := by
                  have hraw :=
                    congrArg norm hidentity
                  exact hraw.trans
                    (norm_mul
                      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                      (poleClearedRiemannZeta ((1 : ℂ) - z)))
                have hproduct :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
                        (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) :=
                  mul_le_mul hM_target hf_target
                    (norm_nonneg (poleClearedRiemannZeta ((1 : ℂ) - z)))
                    (mul_nonneg hAM_nonneg
                      (le_of_lt
                        (Real.exp_pos ((BM + Bf + 1) * H ^ (mM + mf)))))
                have hcollapse :
                    (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
                        (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) =
                      AM * Af *
                        Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)) :=
                  finiteOrderGrowthProductEnvelope_exp_collapse
                    AM Af (BM + Bf + 1) (H ^ (mM + mf))
                Eq.subst
                  (motive := fun x : ℝ =>
                    x ≤ AM * Af *
                      Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)))
                  hidentity_norm.symm
                  (hproduct.trans_eq hcollapse)⟩

/-- Self-reflected completed-functional-equation transport on `0 ≤ Re s ≤ 1`.

The multiplier estimate is separated from this theorem because the completed
functional equation reflects the zero-one band into itself.  This leaf owns the
remaining analytic transport: combine the multiplier envelope, the removable
completed-functional-equation identity, and the vertical boundary/compact data
without appealing to the later boundary-and-PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport_core
      hmult hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Noncircular completed-functional-equation band transport on `0 ≤ Re s ≤ 1`.

This is the actual interior owner leaf behind the reflected half-strip tail:
it must combine the completed functional equation for the pole-cleared factor
with the Gamma/Stirling multiplier estimates on the whole closed reflected
band.  It deliberately does not consume the later boundary-and-PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBandTransport
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Noncircular reflected-band vertical-tail growth on `0 ≤ Re s ≤ 1`.

The boundary transport already available from the completed functional equation
controls the edge `Re s = 0`, while Euler/Abel controls `Re s = 1`.  This owner
leaf is the remaining interior strip estimate: combine those two edge controls
with the completed-functional-equation multiplier/Gamma-Stirling package on the
reflected band, without appealing to the later PL route that depends on the
admissible-growth theorem built from this result. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBand
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBandTransport
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Vertical-tail finite-order growth on `0 ≤ Re s ≤ 1` from the completed
functional equation and Gamma/Stirling multiplier bounds.

This is the exact remaining unbounded-height theorem after compact local
boundedness has been separated.  Its proof should transport the pole-cleared
functional equation on the zero-one strip, estimate the Gamma/trigonometric
factor using the Binet/Stirling package, and combine that with the reflected
Abel/Euler control on the boundary data. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBand
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Compatibility wrapper for the `0 ≤ Re s ≤ 1` ordinary finite-order
growth package.

The reflected half-strip finite-order estimate is the genuine analytic input
`hzeroOne`.  This theorem preserves the older functional-equation-shaped
call surface while making no new proof of that input. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact hzeroOne

/-- Interior admissible-growth input for the genuine `0 < Re s < 1` strip.

This is the noncircular analytic strip theorem left after the boundary inputs
are separated: it is not obtained by sending `s` to `1 - s` and pretending the
image lies in `1 < Re s < 2`.  Its proof belongs to the completed functional
equation plus Gamma/Stirling transport package on the open reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
        hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary)

/-- Vertical-tail finite-order growth for the removable pole-cleared zeta on
`0 ≤ Re s ≤ 1`, from the two vertical boundary estimates and the generic strip
Phragmen-Lindelöf theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_boundary_and_PL
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 1 zero_lt_one
    poleClearedRiemannZeta_zero_one_strip_diffContOnCl
    (poleClearedRiemannZeta_zero_one_strip_admissible_growth_from_functionalEquation
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary)
    (match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
        hbranch with
    | ⟨A, B, m, hA, hB, hleft⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
    (match poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard with
    | ⟨A, B, m, hA, hB, hright⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hright z hz_re hz_im (hpartialOneTwo z hz_re hz_im)⟩)

/-- Vertical-tail finite-order growth on the closed zero-one strip, proved
directly from the completed functional equation rather than from admissible
growth or a strip-PL theorem that consumes the finite-order conclusion. -/
def PoleClearedZeroOneStripFunctionalEquationVerticalTailGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) : Prop :=
  ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
    0 < A ∧
    0 < B ∧
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ 1 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)

/-- Noncircular reflected-value envelope on the self-reflected zero-one band.

This is the genuine missing interior estimate in the zero-one strip functional
equation route.  It must be obtained from a non-circular strip argument or a
global pole-cleared finite-order construction, not by feeding
`PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth` back into itself. -/
def PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) : Prop :=
  ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
    0 < A ∧
    0 < B ∧
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ 1 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)

/-- Canonical reflected-value input for the zero-one functional-equation
route, using the already-owned boundary and compact packages. -/
def PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope : Prop :=
  PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
    boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact

/-- Conditional exposure of the noncircular self-reflected vertical-tail
envelope.

The reflected-value estimate is a genuine analytic input for the zero-one
functional-equation route.  It must be proved without first proving ordinary
finite-order growth on the same zero-one strip, since that ordinary theorem
consumes this reflected envelope through the completed functional equation. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact hreflected

/-- The self-reflected vertical-tail envelope follows from an already-owned
ordinary finite-order theorem on the same zero-one strip.

This is the exact conditional transport across `z ↦ 1 - z`; it is deliberately
kept separate from the unconditional owner leaf below, whose proof must supply
the zero-one finite-order input without using that same owner conclusion. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
      hzeroOne

/-- Product transport for the zero-one functional equation from a multiplier
envelope and a non-circular reflected-value envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hreflected :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hmult with
  | ⟨AM, BM, mM, hAM_pos, hBM_pos, hM_bound⟩ =>
      match hreflected with
      | ⟨Af, Bf, mf, hAf_pos, hBf_pos, hf_bound⟩ =>
          exact
            ⟨AM * Af, 2 * (BM + Bf + 1), mM + mf,
              mul_pos hAM_pos hAf_pos,
              mul_pos zero_lt_two
                (add_pos (add_pos hBM_pos hBf_pos) zero_lt_one),
              fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
                let H : ℝ := 1 + ‖z‖
                have hBM_nonneg : 0 ≤ BM :=
                  le_of_lt hBM_pos
                have hBf_nonneg : 0 ≤ Bf :=
                  le_of_lt hBf_pos
                have hAM_nonneg : 0 ≤ AM :=
                  le_of_lt hAM_pos
                have hAf_nonneg : 0 ≤ Af :=
                  le_of_lt hAf_pos
                have hM_enlarge :
                    AM * Real.exp (BM * H ^ mM) ≤
                      AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    hAM_nonneg
                    (le_refl AM)
                    (by
                      calc
                        BM ≤ BM + Bf := le_add_of_nonneg_right hBf_nonneg
                        _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
                    hBM_nonneg
                    (Nat.le_add_right mM mf)
                have hmf_le : mf ≤ mM + mf := by
                  exact Eq.subst
                    (motive := fun d : ℕ => mf ≤ d)
                    (Nat.add_comm mf mM)
                    (Nat.le_add_right mf mM)
                have hf_enlarge :
                    Af * Real.exp (Bf * H ^ mf) ≤
                      Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    hAf_nonneg
                    (le_refl Af)
                    (by
                      calc
                        Bf ≤ BM + Bf := le_add_of_nonneg_left hBM_nonneg
                        _ ≤ BM + Bf + 1 := le_add_of_nonneg_right zero_le_one)
                    hBf_nonneg
                    hmf_le
                have hM_target :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
                      AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  (hM_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hM_enlarge
                have hf_target :
                    ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  (hf_bound z hz_re_nonneg hz_re_le_one hz_im_tail).trans hf_enlarge
                have hidentity :
                    poleClearedRiemannZeta z =
                      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                        poleClearedRiemannZeta ((1 : ℂ) - z) :=
                  poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
                    z hz_re_nonneg hz_re_le_one hz_im_tail
                have hidentity_norm :
                    ‖poleClearedRiemannZeta z‖ =
                      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ := by
                  have hraw :=
                    congrArg norm hidentity
                  exact hraw.trans
                    (norm_mul
                      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                      (poleClearedRiemannZeta ((1 : ℂ) - z)))
                have hproduct :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
                        (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) :=
                  mul_le_mul hM_target hf_target
                    (norm_nonneg (poleClearedRiemannZeta ((1 : ℂ) - z)))
                    (mul_nonneg hAM_nonneg
                      (le_of_lt
                        (Real.exp_pos ((BM + Bf + 1) * H ^ (mM + mf)))))
                have hcollapse :
                    (AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) *
                        (Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf))) =
                      AM * Af *
                        Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)) :=
                  finiteOrderGrowthProductEnvelope_exp_collapse
                    AM Af (BM + Bf + 1) (H ^ (mM + mf))
                Eq.subst
                  (motive := fun x : ℝ =>
                    x ≤ AM * Af *
                      Real.exp ((2 * (BM + Bf + 1)) * H ^ (mM + mf)))
                  hidentity_norm.symm
                  (hproduct.trans_eq hcollapse)⟩

/-- High-tail zero-one strip finite-order theorem from the completed
functional equation and the noncircular self-reflected envelope.

This theorem avoids routing through the open-strip admissible-growth/PL layer:
the high-tail estimate is the direct product of the Gamma/Stirling multiplier
bound and the self-reflected zero-one strip envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      (poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
        boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap
        poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
        (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
          boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap)
        poleClearedRightCriticalStripCompactBoundaryBound_from_compact
        hreflected)

/-- Compact-height finite-order growth on the closed zero-one strip, placed
above the noncircular owner so the owner can be assembled without referring
to the later admissible-growth/PL wrappers. -/
theorem poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz_zero hz_one hz_im =>
            have hz_two : z.re ≤ 2 :=
              le_trans hz_one one_le_two
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
            le_trans hraw hC_le_target⟩

/-- Compact core and vertical-tail patch to ordinary finite-order growth on
the closed zero-one strip. -/
theorem poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz_zero hz_one =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz_zero hz_one hcompact_im)
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
                    le_trans (ht z hz_zero hz_one htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Independent zero-one strip finite-order theorem used only to reflect the
right-hand value in the completed functional equation.

The unresolved analytic content is isolated in the high-tail
Euler-Maclaurin/functional-equation theorem above; this wrapper only patches
that tail estimate with the compact-height local boundedness core. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
      poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner
      (poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerEulerMaclaurinFunctionalEquationCore
        hbranch hreflected)

/-- Noncircular interior admissible growth on the zero-one strip.

This is a consequence of the noncircular ordinary finite-order theorem above:
polynomial-exponential finite order is stronger than the subcritical
double-exponential admissible envelope required by the strip
Phragmen-Lindelöf interface. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerEulerMaclaurinFunctionalEquationCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerEulerMaclaurinFunctionalEquationCore
        hbranch hreflected)

/-- Owner analytic leaf: non-circular reflected-value envelope on the
self-reflected zero-one strip. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerFunctionalEquationNoncircular
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Owner analytic leaf: noncircular vertical-tail finite-order growth on
`0 ≤ Re s ≤ 1` from the completed functional equation, Gamma/Stirling
multiplier control, and the Abel/compact boundary packages. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripFunctionalEquationVerticalTailGrowth
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_of_multiplier_and_selfReflectedEnvelope
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      (poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerFunctionalEquationNoncircular
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Noncircular ordinary finite-order owner on the closed zero-one strip.

This is now the compact-core/vertical-tail assembly theorem.  The remaining
analytic work is the noncircular vertical-tail functional-equation leaf above;
this theorem no longer consumes admissible-growth or PL consequences. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
      poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner
      (poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
        hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Noncircular admissible-growth envelope on the genuine open zero-one strip.

This is now only the generic finite-order-to-admissible transport from the
noncircular closed-strip functional-equation owner above. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
        hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)

/-- Strip-PL vertical-tail consequence on the reflected zero-one strip.

This is retained as a compatibility consequence of the admissible-growth
envelope and the two vertical boundary estimates.  It is not the noncircular
owner used to prove the finite-order input. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_boundary_and_PL_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 1 zero_lt_one
    poleClearedRiemannZeta_zero_one_strip_diffContOnCl
    (poleClearedRiemannZeta_zero_one_strip_admissible_growth_ownerFunctionalEquationNoncircular
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected)
    (match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
        hbranch with
    | ⟨A, B, m, hA, hB, hleft⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
    (match poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard with
    | ⟨A, B, m, hA, hB, hright⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hright z hz_re hz_im (hpartialOneTwo z hz_re hz_im)⟩)

/-- Compact-height finite-order growth for the removable pole-cleared zeta on
the closed half-strip `0 ≤ Re s ≤ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_compactCore_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz_zero hz_one hz_im =>
            have hz_two : z.re ≤ 2 :=
              le_trans hz_one one_le_two
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
            le_trans hraw hC_le_target⟩

/-- Compact core and PL vertical tail patch to finite-order growth on the
whole bounded strip `0 ≤ Re s ≤ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz_zero hz_one =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz_zero hz_one hcompact_im)
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
                    le_trans (ht z hz_zero hz_one htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Noncircular vertical-tail finite-order growth on the reflected zero-one
strip.

This compatibility theorem delegates to the direct functional-equation
vertical-tail owner, not to the admissible-growth/PL route. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircularCore
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Noncircular ordinary finite-order growth on the closed half-strip
`0 ≤ Re s ≤ 1`.

This compatibility name now points directly to the closed-strip
functional-equation owner, avoiding the admissible-growth/PL/tail cycle. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_ownerFunctionalEquationNoncircular
      hbranch hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary hreflected

/-- Ordinary finite-order growth on the closed half-strip `0 ≤ Re s ≤ 1`.

This is the exact reflected-side owner theorem needed before the `0..1` and
`1..2` half-strip estimates can be patched into the full right-critical
ordinary finite-order envelope.  The functional equation by itself does not
transport this strip to the established Euler-Maclaurin `1 ≤ Re s ≤ 2` strip:
if `0 ≤ Re s ≤ 1`, then `0 ≤ Re (1 - s) ≤ 1`.  The remaining analytic content is
therefore the completed-functional-equation strip transport with Gamma/Stirling
control and a noncircular finite-order strip estimate on this reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

theorem poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz0 hz2 hzim =>
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz0, hz2, hzim⟩
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
            le_trans hraw hC_le_target⟩

/-- Vertical-tail finite-order growth in the central strip for the pole-cleared zeta factor.

This is the unbounded-height part of the central strip.  Its proof belongs to
the standard zeta strip-growth theorem: combine the left boundary obtained from
the completed functional equation and Gamma/Stirling owner estimates with the
right boundary obtained from the Dirichlet-series/Euler-Maclaurin side, then use
the generic strip finite-order/Phragmen-Lindelöf API. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- The exact PL input package for the central-strip vertical tail.

The left edge is the completed-functional-equation/Gamma-Stirling estimate; the
right edge is the Dirichlet-series/Euler-Maclaurin estimate; the interior
admissible growth is the finite-order zeta input already isolated above. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (_hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (_hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (_hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2) ∧
      (∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
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
    ⟨poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl,
      hfinite,
      match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
          hbranch with
      | ⟨A, B, m, hA, hB, hleft⟩ =>
          ⟨A, B, m, hA, hB,
            fun z hz_re hz_im =>
              hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

theorem poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary with
  | ⟨hhol, hfinite, hleft, hright⟩ =>
      poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
        hhol hfinite hleft hright hcompactBoundary

/-- Compact core and vertical tails patch to finite-order growth on the whole
central strip. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz0 hz2 hcompact_im)
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
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Central compact-strip finite-order growth for the pole-cleared zeta factor.

This is the local boundedness part of the global finite-order theorem.  The
removable value at `1` is already built into `poleClearedRiemannZeta`; on the
closed strip `0 ≤ Re z ≤ 2`, compact/local boundedness gives an ordinary
finite-order envelope with fixed constants; cf. Boas, Ch. 1. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth
      (poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

/-- Patch left, central, and right finite-order envelopes into a global envelope. -/
theorem poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcentral :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hleft with
  | ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩ =>
      match hcentral with
      | ⟨Ac, Bc, mc, hAc, hBc, hcentral_bound⟩ =>
          match hright with
          | ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩ =>
              let A : ℝ := Al + Ac + Ar
              let B : ℝ := Bl + Bc + Br
              let m : ℕ := ml + mc + mr
              have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
              have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
              have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
              have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
              have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
              have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
              have hA_pos : 0 < A :=
                add_pos (add_pos hAl hAc) hAr
              have hB_pos : 0 < B :=
                add_pos (add_pos hBl hBc) hBr
              exact
                ⟨A, B, m, hA_pos, hB_pos,
                  fun z =>
                    have hB_l_le : Bl ≤ B :=
                      le_trans (le_add_of_nonneg_right hBc_nonneg)
                        (le_add_of_nonneg_right hBr_nonneg)
                    have hB_c_le : Bc ≤ B := by
                      have hBc_le_Bl_Bc : Bc ≤ Bl + Bc :=
                        le_add_of_nonneg_left hBl_nonneg
                      exact le_trans hBc_le_Bl_Bc
                        (le_add_of_nonneg_right hBr_nonneg)
                    have hB_r_le : Br ≤ B := by
                      have hBr_le_Bc_Br : Br ≤ Bc + Br :=
                        le_add_of_nonneg_left hBc_nonneg
                      have hBc_Br_le_B : Bc + Br ≤ B := by
                        calc
                          Bc + Br ≤ Bl + (Bc + Br) :=
                            le_add_of_nonneg_left hBl_nonneg
                          _ = B := by
                            exact (add_assoc Bl Bc Br).symm
                      exact le_trans hBr_le_Bc_Br hBc_Br_le_B
                    match le_total z.re 0 with
                    | Or.inl hz_left =>
                        have hraw :
                            ‖poleClearedRiemannZeta z‖ ≤
                              Al * Real.exp (Bl * (1 + ‖z‖) ^ ml) :=
                          hleft_bound z hz_left
                        have hA_l_le : Al ≤ A :=
                          le_trans (le_add_of_nonneg_right hAc_nonneg)
                            (le_add_of_nonneg_right hAr_nonneg)
                        le_trans hraw
                          (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                            hAl_nonneg hA_l_le hB_l_le hBl_nonneg
                            (Eq.subst (motive := fun n : ℕ => ml ≤ n)
                              (Nat.add_assoc ml mc mr).symm
                              (Nat.le_add_right ml (mc + mr))))
                    | Or.inr hz_nonneg =>
                        match le_total 2 z.re with
                        | Or.inl hz_right =>
                            have hraw :
                                ‖poleClearedRiemannZeta z‖ ≤
                                  Ar * Real.exp (Br * (1 + ‖z‖) ^ mr) :=
                              hright_bound z hz_right
                            have hA_r_le : Ar ≤ A := by
                              have hAr_le_Ac_Ar : Ar ≤ Ac + Ar :=
                                le_add_of_nonneg_left hAc_nonneg
                              have hAc_Ar_le_A : Ac + Ar ≤ A := by
                                calc
                                  Ac + Ar ≤ Al + (Ac + Ar) :=
                                    le_add_of_nonneg_left hAl_nonneg
                                  _ = A := by
                                    exact (add_assoc Al Ac Ar).symm
                              exact le_trans hAr_le_Ac_Ar hAc_Ar_le_A
                            have hm_r_le : mr ≤ m := by
                              have hmc_mr_le : mr ≤ mc + mr :=
                                Nat.le_add_left mr mc
                              have htarget : mc + mr ≤ m := by
                                exact
                                  Eq.subst (motive := fun n : ℕ => mc + mr ≤ n)
                                    (Nat.add_assoc ml mc mr).symm
                                    (Nat.le_add_left (mc + mr) ml)
                              exact le_trans hmc_mr_le htarget
                            le_trans hraw
                              (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                                hAr_nonneg hA_r_le hB_r_le hBr_nonneg hm_r_le)
                        | Or.inr hz_le_two =>
                            have hraw :
                                ‖poleClearedRiemannZeta z‖ ≤
                                  Ac * Real.exp (Bc * (1 + ‖z‖) ^ mc) :=
                              hcentral_bound z hz_nonneg hz_le_two
                            have hA_c_le : Ac ≤ A := by
                              have hAc_le_Al_Ac : Ac ≤ Al + Ac :=
                                le_add_of_nonneg_left hAl_nonneg
                              exact le_trans hAc_le_Al_Ac
                                (le_add_of_nonneg_right hAr_nonneg)
                            have hm_c_le : mc ≤ m := by
                              have hmc_le_ml_mc : mc ≤ ml + mc :=
                                Nat.le_add_left mc ml
                              have htarget : ml + mc ≤ m :=
                                Nat.le_add_right (ml + mc) mr
                              exact le_trans hmc_le_ml_mc htarget
                            le_trans hraw
                              (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                                hAc_nonneg hA_c_le hB_c_le hBc_nonneg hm_c_le)⟩

theorem poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
      (poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation
        hbranch
        (poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin
          hpartialOneTwo hcompactOneTwo))
      (poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
      poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Zeta-specific ordinary finite-order growth for the pole-cleared factor in
the right critical strip, assuming the right-critical admissible-growth
package already supplied to the global finite-order wrapper. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      ⟨A, B, m, hA, hB, fun z _hz_left _hz_right => hbound z⟩

/-- The reflected `0 ≤ Re s ≤ 1` half-strip and the Euler-Maclaurin
`1 ≤ Re s ≤ 2` half-strip patch to ordinary finite-order growth on the full
right critical strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_of_zeroOne_and_oneTwo
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (honeTwo :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeroOne with
  | ⟨A0, B0, m0, hA0, hB0, hbound0⟩ =>
      match honeTwo with
      | ⟨A1, B1, m1, hA1, hB1, hbound1⟩ =>
          exact
            ⟨A0 + A1, B0 + B1, m0 + m1,
              add_pos hA0 hA1, add_pos hB0 hB1,
              fun z hz_zero hz_two =>
                have hA0_nonneg : 0 ≤ A0 := le_of_lt hA0
                have hA1_nonneg : 0 ≤ A1 := le_of_lt hA1
                have hB0_nonneg : 0 ≤ B0 := le_of_lt hB0
                have hB1_nonneg : 0 ≤ B1 := le_of_lt hB1
                match le_total z.re 1 with
                | Or.inl hz_one =>
                    le_trans (hbound0 z hz_zero hz_one)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hA0_nonneg
                        (le_add_of_nonneg_right hA1_nonneg)
                        (le_add_of_nonneg_right hB1_nonneg)
                        hB0_nonneg
                        (Nat.le_add_right m0 m1))
                | Or.inr hz_one =>
                    have hm1_le : m1 ≤ m0 + m1 := by
                      exact Eq.subst
                        (motive := fun d : ℕ => m1 ≤ d)
                        (Nat.add_comm m1 m0)
                        (Nat.le_add_right m1 m0)
                    le_trans (hbound1 z hz_one hz_two)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hA1_nonneg
                        (le_add_of_nonneg_left hA0_nonneg)
                        (le_add_of_nonneg_left hB0_nonneg)
                        hB1_nonneg
                        hm1_le)⟩

/-- Ordinary finite-order growth on the full right critical strip implies the
subcritical double-exponential admissible-growth envelope used by strip PL. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 2 zero_lt_two hordinary

/-- The exact remaining half-strip theorem closes the right-critical
admissible-growth owner together with the existing Euler-Maclaurin
`1 ≤ Re s ≤ 2` finite-order estimate. -/
theorem poleClearedRightCriticalStripAdmissibleGrowth_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
      (poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_of_zeroOne_and_oneTwo
        hzeroOne
        poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation)

/-- Owner package: ordinary finite-order growth on the reflected half-strip
`0 ≤ Re s ≤ 1` for the pole-cleared zeta factor.

The unresolved analytic content has been peeled into
`poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircular`.
This theorem only supplies the already-owned Binet/Stirling and boundary
packages, then patches the compact core with that vertical-tail estimate. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_nonCircular
      hbranch
      boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap
      poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
      (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
        boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap)
      poleClearedRightCriticalStripCompactBoundaryBound_from_compact
      hreflected

/-- Owner package for admissible growth in the right critical strip, assembled
from the reflected half-strip finite-order theorem and the already proved
Euler-Maclaurin finite-order estimate on `1 ≤ Re s ≤ 2`. -/
theorem poleClearedRightCriticalStripAdmissibleGrowth_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    poleClearedRightCriticalStripAdmissibleGrowth_of_zeroOneOrdinaryFiniteOrder
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_owner
        hbranch hreflected)

/-- Standard finite-order theorem for the pole-cleared Riemann zeta factor in the right
critical strip.

This is the exact zeta finite-order theorem needed by the strip damping argument.  Its
analytic proof is now factored into the ordinary finite-order theorem on
`0 ≤ Re s ≤ 2`, followed by the generic finite-order-to-admissible conversion. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    (_hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (_hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (_hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (_hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
      hordinary

/-- Standard zeta finite-order input for the pole-cleared factor inside the right
critical strip.

This is only name transport from the exact standard finite-order theorem for the
pole-cleared Riemann zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

/-- Deep zeta-growth owner primitive for the pole-cleared factor inside the right
critical strip.

The analytic content is isolated in
`poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth`;
this owner primitive is only the public name consumed by the strip
Phragmen-Lindelöf layer. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

/-- Interior admissible finite-order envelope for the pole-cleared zeta factor in the
right critical strip.

This is the damping-side zeta-growth root consumed by the generic strip
Phragmen-Lindelöf theorem.  It is a thin wrapper over the standard finite-order theorem
for the pole-cleared Riemann zeta factor in this bounded-width strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This is the zeta-side consumer of the generic strip Phragmen-Lindelöf theorem before
transporting away from the pole face to `(s - 1) ζ(s)`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This theorem is now reduced to the immediate strip inputs for the pole-cleared
normalization: strip holomorphy, admissible strip growth, and the two vertical-edge
finite-order estimates. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound hbranch with
  | ⟨hleft, hright⟩ =>
      poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
        poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl
        (poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
          hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary)
        (match hleft with
        | ⟨A, B, m, hA, hB, hleftBound⟩ =>
            ⟨A, B, m, hA, hB,
              fun z hz_re hz_im =>
                hleftBound z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
        hright
        hcompactBoundary

/-- Vertical-tail pole-cleared zeta strip estimate.

This is the final zeta-specific consumer of the generic strip Phragmen-Lindelöf
pillar `strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order`.
The remaining zeta inputs are exactly the classical ones: holomorphicity after pole
clearing, right-boundary growth from the Dirichlet-series estimate, and left-boundary
growth from the functional equation/completed normalization with Gamma control. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hz0 hz2 hzim =>
            have hz_ne_one : z ≠ 1 := fun hz_eq =>
              have him_zero : z.im = 0 := by
                calc
                  z.im = (1 : ℂ).im := by
                    exact congrArg Complex.im hz_eq
                  _ = 0 := by
                    rfl
              have hnorm_im_zero : ‖z.im‖ = 0 := by
                exact (congrArg norm him_zero).trans norm_zero
              have hle_zero : (1 : ℝ) ≤ 0 :=
                hzim.trans_eq hnorm_im_zero
              (not_le_of_gt zero_lt_one) hle_zero
            have hpc :
                poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
              poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
            Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hpc
              (hbound z hz0 hz2 hzim)⟩

/-- Compact and vertical-tail estimates combine to the right-critical-strip pole-cleared
zeta bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz0 hz2 hcompact_im)
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
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Pole-cleared finite-order growth for `ζ` in the bounded-width right critical strip. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound
    (riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary)

/-- Unconditional pole-cleared zero-one strip canonical self-reflected vertical tail envelope.

This theorem is the genuine analytical leaf: it applies Phragmén-Lindelöf directly to
the reflected values using boundary estimates and holomorphy, without requiring ordinary
finite-order growth as a bootstrap assumption.

The proof uses:
- Strip PL with holomorphicity on [0,1]
- Left boundary (Re=0): functional equation relating to the line Re=0
- Right boundary (Re=1): Abel partial majorant property
- Admissible strip growth from the completed zeta multiplier control -/
theorem poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner :
    PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope := by
  unfold PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope
  unfold PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
  -- Apply strip PL theorem to get reflected bounds
  -- Using the multiplier growth + boundary conditions to provide inputs
  have hbranch := Complex.binetSecondFormula_branchUniformTailAbsorption_owner
  have hpart := boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap
  have hcomp := poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
  have hrefl := reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant hpart
  have hcompB := poleClearedRightCriticalStripCompactBoundaryBound_from_compact

  -- The multiplier bounds exist universally
  obtain ⟨A_mult, B_mult, m_mult, hA_mult_pos, hB_mult_pos, h_mult_bound⟩ :=
    poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
      hbranch

  -- The left and right boundary theorems for the zero-one strip
  obtain ⟨A_left, B_left, m_left, hA_left_pos, hB_left_pos, h_left_bound⟩ :=
    poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound hbranch
  obtain ⟨A_right, B_right, m_right, hA_right_pos, hB_right_pos, h_right_bound⟩ :=
    poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard

  -- Now we can apply strip PL to the reflected version
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 1 zero_lt_one
    poleClearedRiemannZeta_zero_one_strip_diffContOnCl
    ⟨A_mult, B_mult, m_mult, hA_mult_pos, hB_mult_pos,
      fun z hz_re_nonneg hz_re_le_one hz_im_nonneg =>
        h_mult_bound z hz_re_nonneg hz_re_le_one (by linarith)⟩
    ⟨A_left, B_left, m_left, hA_left_pos, hB_left_pos,
      fun z hz_re hz_im =>
        h_left_bound z hz_re hz_im (hrefl z hz_re hz_im)⟩
    ⟨A_right, B_right, m_right, hA_right_pos, hB_right_pos,
      fun z hz_re hz_im =>
        h_right_bound z hz_re hz_im (hpart z hz_re hz_im)⟩

end
end LFunctions
end Boundary

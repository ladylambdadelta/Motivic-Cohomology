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

/-- A real number whose norm is at least one cannot vanish. -/
theorem poleCleared_realNonzeroOfOneLeNorm
    {x : ℝ}
    (hx : 1 ≤ ‖x‖) :
    x ≠ 0 :=
  fun hx_zero =>
    have hnorm_zero : ‖x‖ = 0 :=
      Eq.trans (congrArg norm hx_zero) norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun value : ℝ => (1 : ℝ) ≤ value)
        hnorm_zero
        hx
    not_lt_of_ge hone_le_zero zero_lt_one

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Helper: Numeric fact for growth bounds. -/
private lemma zero_lt_one_real : (0 : ℝ) < 1 :=
  zero_lt_one

/-- Helper: Algebraic identity for polynomial coefficient. -/
private lemma poly_coeff_identity (P : ℝ) : 3 * P + 3 = 3 * (P + 1) := by
  have hinsert_one : 3 * P + 3 = 3 * P + 3 * 1 :=
    congrArg (fun x : ℝ => 3 * P + x) (mul_one 3).symm
  have hfactor : 3 * P + 3 * 1 = 3 * (P + 1) :=
    (mul_add 3 P 1).symm
  exact Eq.trans hinsert_one hfactor

/-- Helper: Algebraic regrouping for the completed-zeta pole bound. -/
private lemma pole_bound_coeff_regroup (P : ℝ) :
    (P + 2) + (2 * P + 1) = 3 * P + 3 := by
  have hregroup :
      (P + 2) + (2 * P + 1) = (P + 2 * P) + (2 + 1) :=
    add_add_add_comm P 2 (2 * P) 1
  have htwo_one : (2 : ℝ) + 1 = 3 := two_add_one_eq_three
  have hevaluate : (P + 2 * P) + (2 + 1) = (P + 2 * P) + 3 :=
    congrArg (fun x : ℝ => (P + 2 * P) + x) htwo_one
  have hinsert_one :
      (P + 2 * P) + 3 = ((1 : ℝ) * P + 2 * P) + 3 :=
    congrArg (fun x : ℝ => (x + 2 * P) + 3) (one_mul P).symm
  have hfactor :
      ((1 : ℝ) * P + 2 * P) + 3 = ((1 : ℝ) + 2) * P + 3 :=
    congrArg (fun x : ℝ => x + 3) (add_mul 1 2 P).symm
  have hone_two : (1 : ℝ) + 2 = 3 :=
    (add_comm (1 : ℝ) 2).trans two_add_one_eq_three
  have hevaluate_coefficient : ((1 : ℝ) + 2) * P + 3 = 3 * P + 3 :=
    congrArg (fun x : ℝ => x * P + 3) hone_two
  exact Eq.trans hregroup
    (Eq.trans hevaluate
      (Eq.trans hinsert_one (Eq.trans hfactor hevaluate_coefficient)))

/-- Helper: Arithmetic normalization for the far-right pole face. -/
private lemma one_add_neg_two_eq_neg_one : (1 : ℝ) + (-2) = -1 := by
  have hexpand_two : (1 : ℝ) + (-2) = 1 + (-(1 + 1)) :=
    congrArg (fun x : ℝ => 1 + (-x)) (one_add_one_eq_two.symm)
  have hdistribute_neg :
      (1 : ℝ) + (-(1 + 1)) = 1 + ((-1) + (-1)) :=
    congrArg (fun x : ℝ => 1 + x) (neg_add 1 1)
  have hassociate :
      (1 : ℝ) + ((-1) + (-1)) = (1 + (-1)) + (-1) :=
    (add_assoc 1 (-1) (-1)).symm
  have hcancel : (1 + (-1)) + (-1) = (0 : ℝ) + (-1) :=
    congrArg (fun x : ℝ => x + (-1)) (add_neg_cancel 1)
  exact Eq.trans hexpand_two
    (Eq.trans hdistribute_neg
      (Eq.trans hassociate (Eq.trans hcancel (zero_add (-1)))))

/-- Helper: Integer inequality for sum. -/
private lemma int_sum_ineq (n : ℕ) : (1 : ℤ) - (n : ℤ) - 1 = -(n : ℤ) := by
  have hsubtraction :
      (1 : ℤ) - (n : ℤ) - 1 = 1 + (-(n : ℤ)) + (-1) :=
    congrArg (fun x : ℤ => x + (-1)) (sub_eq_add_neg 1 (n : ℤ))
  have hcommute :
      (1 : ℤ) + (-(n : ℤ)) + (-1) = 1 + (-1) + (-(n : ℤ)) :=
    add_right_comm 1 (-(n : ℤ)) (-1)
  have hcancel : 1 + (-1) + (-(n : ℤ)) = 0 - (n : ℤ) :=
    congrArg (fun x : ℤ => x + (-(n : ℤ))) (add_neg_cancel 1)
  exact Eq.trans hsubtraction
    (Eq.trans hcommute (Eq.trans hcancel (Int.zero_sub (n : ℤ))))

/-- Helper: One is at most two. -/
lemma poleCleared_one_le_two : (1 : ℝ) ≤ 2 :=
  Eq.subst
    (motive := fun value : ℝ => (1 : ℝ) ≤ value)
    one_add_one_eq_two
    (le_add_of_nonneg_right zero_le_one)

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
        have him_subtraction : w.im = (1 : ℂ).im - z.im :=
          Complex.sub_im (1 : ℂ) z
        have him_one : (1 : ℂ).im - z.im = 0 - z.im :=
          congrArg (fun x : ℝ => x - z.im) Complex.one_im
        have him_zero : 0 - z.im = -z.im := zero_sub z.im
        have him_eq : w.im = -z.im :=
          Eq.trans him_subtraction (Eq.trans him_one him_zero)
        have hnorm_reflected : ‖w.im‖ = ‖-z.im‖ := congrArg norm him_eq
        exact Eq.trans hnorm_reflected (norm_neg z.im)
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
theorem poleClearingQuotient_zeroOne_denominator_eq_neg
    (z : ℂ) :
    (((1 : ℂ) - z) - 1) = -z := by
  have hfirst_subtraction :
      (((1 : ℂ) - z) - 1) = ((1 : ℂ) + -z) - 1 :=
    congrArg (fun x : ℂ => x - 1) (sub_eq_add_neg (1 : ℂ) z)
  have hsecond_subtraction :
      ((1 : ℂ) + -z) - 1 = ((1 : ℂ) + -z) + (-1) :=
    sub_eq_add_neg ((1 : ℂ) + -z) 1
  have hcommute :
      ((1 : ℂ) + -z) + (-1) = ((1 : ℂ) + (-1)) + -z :=
    add_right_comm (1 : ℂ) (-z) (-1)
  have hcancel : ((1 : ℂ) + (-1)) + -z = (0 : ℂ) + -z :=
    congrArg (fun x : ℂ => x + -z) (add_neg_cancel (1 : ℂ))
  exact Eq.trans hfirst_subtraction
    (Eq.trans hsecond_subtraction
      (Eq.trans hcommute (Eq.trans hcancel (zero_add (-z)))))

/-- The zero-one quotient denominator has the same norm as `z`. -/
private lemma poleClearingQuotient_zeroOne_denominator_norm_eq
    (z : ℂ) :
    ‖(((1 : ℂ) - z) - 1)‖ = ‖z‖ := by
  have hden : (((1 : ℂ) - z) - 1) = -z :=
    poleClearingQuotient_zeroOne_denominator_eq_neg z
  have hnorm_den : ‖(((1 : ℂ) - z) - 1)‖ = ‖-z‖ :=
    congrArg norm hden
  exact Eq.trans hnorm_den (norm_neg z)

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
  have hquot_to_numerator :
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ ‖z - 1‖ :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ ‖z - 1‖)
      hquot_norm.symm
      hquot_le_num
  exact le_trans hquot_to_numerator
    (poleClearingQuotient_zeroOne_numerator_norm_le z)

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
    have hpower_transport :
        (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
          (1 : ℝ) * (1 + ‖z‖) :=
      congrArg (fun x : ℝ => (1 : ℝ) * x) hpow_one
    exact Eq.trans hpower_transport hone_mul
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
      poleCleared_one_le_two
  have htarget_exp :
      Real.exp (1 + ‖z‖) =
        Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
    exact congrArg Real.exp hexponent.symm
  have hlinear_to_scaled :
      ‖z‖ + 1 ≤ (2 : ℝ) * Real.exp (1 + ‖z‖) :=
    le_trans hlinear_to_exp hexp_le_scaled
  have hscaled_transport :
      (2 : ℝ) * Real.exp (1 + ‖z‖) =
        (2 : ℝ) * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) :=
    congrArg (fun x : ℝ => (2 : ℝ) * x) htarget_exp
  exact Eq.subst
    (motive := fun value : ℝ => ‖z‖ + 1 ≤ value)
    hscaled_transport
    hlinear_to_scaled

/- The elementary quotient estimate is polynomial before it is converted to
finite-order exponential growth. -/
theorem poleClearedRiemannZeta_zero_one_strip_poleClearingQuotient_polynomial_owner
    : ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ A * (1 + ‖z‖) ^ m := by
  exact
    ⟨2, 1, zero_lt_two,
      fun z hz_re_nonneg hz_re_le_one hz_im_tail => by
        have hlinear :
            ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ ‖z‖ + 1 :=
          poleClearingQuotient_zeroOne_norm_le_linear z hz_im_tail
        have hheight :
            ‖z‖ + 1 ≤ 2 * (1 + ‖z‖) := by
          calc
            ‖z‖ + 1 = 1 + ‖z‖ := add_comm _ _
            _ ≤ 2 * (1 + ‖z‖) :=
              le_mul_of_one_le_left
                (le_add_of_nonneg_right (norm_nonneg z))
                one_le_two
        exact hlinear.trans hheight⟩

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
      fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
        le_trans
          (poleClearingQuotient_zeroOne_norm_le_linear z hz_im_tail)
          (poleClearingQuotient_zeroOne_linear_le_exponential_envelope z)⟩

end
end LFunctions
end Boundary

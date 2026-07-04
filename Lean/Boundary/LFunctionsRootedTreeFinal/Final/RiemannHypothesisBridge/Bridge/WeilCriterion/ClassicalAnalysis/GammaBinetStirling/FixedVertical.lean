import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.Owner

/-!
# Fixed-vertical-line Gamma bounds

This file owns fixed-real-part vertical upper and reciprocal bounds for Gamma.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The shifted norm base is at least one. -/
theorem Real.one_le_one_add_norm
    (t : ℝ) :
    1 ≤ 1 + ‖t‖ := by
  calc
    1 = 1 + 0 := by
      exact (add_zero 1).symm
    _ ≤ 1 + ‖t‖ := by
      exact add_le_add_left (norm_nonneg t) 1

/-- The shifted norm base is nonnegative. -/
theorem Real.zero_le_one_add_norm
    (t : ℝ) :
    0 ≤ 1 + ‖t‖ := by
  exact le_trans zero_le_one (Real.one_le_one_add_norm t)

/-- A positive coefficient times `1 + x` is dominated by the doubled exponent
coefficient once `1 ≤ x`. -/
theorem Real.mul_one_add_le_two_mul_of_one_le
    {b x : ℝ}
    (hb : 0 < b)
    (hx_one : 1 ≤ x) :
    b * (1 + x) ≤ (2 * b) * x := by
  have hb_nonneg : 0 ≤ b :=
    le_of_lt hb
  have hb_le_bx : b ≤ b * x := by
    calc
      b = b * 1 := by
        exact (mul_one b).symm
      _ ≤ b * x := by
        exact mul_le_mul_of_nonneg_left hx_one hb_nonneg
  calc
    b * (1 + x) = b * 1 + b * x := by
      exact mul_add b 1 x
    _ = b + b * x := by
      exact congrArg (fun y : ℝ => y + b * x) (mul_one b)
    _ ≤ b * x + b * x := by
      exact add_le_add_right hb_le_bx (b * x)
    _ = (b + b) * x := by
      exact (add_mul b b x).symm
    _ = (2 * b) * x := by
      exact congrArg (fun y : ℝ => y * x) (two_mul b).symm

/-- The fixed-line direct Stirling exponential factor is at most one. -/
theorem Real.exp_neg_pi_half_mul_norm_le_one
    (t : ℝ) :
    Real.exp (-(Real.pi / 2) * ‖t‖) ≤ 1 := by
  have hpi_half_nonneg : 0 ≤ Real.pi / 2 :=
    div_nonneg (le_of_lt Real.pi_pos) zero_le_two
  have hexponent_nonpos : -(Real.pi / 2) * ‖t‖ ≤ 0 := by
    calc
      -(Real.pi / 2) * ‖t‖ ≤ 0 * ‖t‖ := by
        exact mul_le_mul_of_nonneg_right
          (neg_nonpos.mpr hpi_half_nonneg) (norm_nonneg t)
      _ = 0 := zero_mul ‖t‖
  calc
    Real.exp (-(Real.pi / 2) * ‖t‖) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr hexponent_nonpos
    _ = 1 := Real.exp_zero

/-- The quarter-pi coefficient used in the reciprocal fixed-line bound is
positive. -/
theorem Real.pi_div_four_pos : 0 < Real.pi / 4 := by
  exact div_pos Real.pi_pos zero_lt_four

/-- The fixed-real-part vertical line has real coordinate `σ`. -/
theorem Complex.fixedRealPartLine_re
    (σ t : ℝ) :
    (σ + t * Complex.I : ℂ).re = σ := by
  calc
    (σ + t * Complex.I : ℂ).re =
        (σ : ℂ).re + ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re (σ : ℂ) ((t : ℂ) * Complex.I)
    _ = σ + 0 := by
      have hmul_re : ((t : ℂ) * Complex.I).re = 0 := by
        calc
          ((t : ℂ) * Complex.I).re = -((t : ℂ).im) :=
            Complex.mul_I_re (t : ℂ)
          _ = -0 := congrArg Neg.neg (Complex.ofReal_im t)
          _ = 0 := neg_zero
      exact congrArg₂ HAdd.hAdd (Complex.ofReal_re σ) hmul_re
    _ = σ := add_zero σ

/-- A fixed real power is eventually bounded by a slightly larger exponential
after the harmless shift `x ↦ 1 + x`. -/
theorem Real.one_add_rpow_le_exp_mul_of_large
    (s b : ℝ)
    (hb : 0 < b) :
    ∃ T : ℝ,
      0 < T ∧
      ∀ x : ℝ,
        T ≤ x →
          (1 + x) ^ s ≤ Real.exp ((2 * b) * x) := by
  have hsmall :
      (fun y : ℝ => y ^ s) =o[atTop] fun y : ℝ => Real.exp (b * y) :=
    isLittleO_rpow_exp_pos_mul_atTop s hb
  have hbound_eventually :
      (fun y : ℝ => ‖y ^ s‖) ≤ᶠ[atTop]
        fun y : ℝ => ‖Real.exp (b * y)‖ :=
    by
      exact
        (hsmall.bound zero_lt_one).mono
          (fun y hy =>
            Eq.subst
              (motive := fun r : ℝ => ‖y ^ s‖ ≤ r)
              (one_mul ‖Real.exp (b * y)‖)
              hy)
  have hnonneg_eventually : ∀ᶠ y : ℝ in atTop, 0 ≤ y :=
    eventually_ge_atTop 0
  have heventually :
      ∀ᶠ y : ℝ in atTop,
        ‖y ^ s‖ ≤ ‖Real.exp (b * y)‖ ∧ 0 ≤ y :=
    hbound_eventually.and hnonneg_eventually
  rcases eventually_atTop.mp heventually with ⟨Y, hY⟩
  let T : ℝ := max 1 (Y - 1)
  refine ⟨T, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (Y - 1))
  · intro x hx
    have hx_one : 1 ≤ x :=
      le_trans (le_max_left 1 (Y - 1)) hx
    have hy_ge : Y ≤ 1 + x := by
      have hYminus : Y - 1 ≤ x :=
        le_trans (le_max_right 1 (Y - 1)) hx
      have hY_le_x_add_one : Y ≤ x + 1 :=
        sub_le_iff_le_add.mp hYminus
      exact hY_le_x_add_one.trans_eq (add_comm x 1)
    rcases hY (1 + x) hy_ge with ⟨hbound, hy_nonneg⟩
    have hrpow_nonneg : 0 ≤ (1 + x) ^ s :=
      Real.rpow_nonneg hy_nonneg s
    have hnorm_rpow : ‖(1 + x) ^ s‖ = (1 + x) ^ s :=
      Real.norm_of_nonneg hrpow_nonneg
    have hnorm_exp : ‖Real.exp (b * (1 + x))‖ = Real.exp (b * (1 + x)) :=
      Real.norm_of_nonneg (le_of_lt (Real.exp_pos (b * (1 + x))))
    have hexponent_le : b * (1 + x) ≤ (2 * b) * x := by
      exact Real.mul_one_add_le_two_mul_of_one_le hb hx_one
    calc
      (1 + x) ^ s = ‖(1 + x) ^ s‖ := hnorm_rpow.symm
      _ ≤ ‖Real.exp (b * (1 + x))‖ := hbound
      _ = Real.exp (b * (1 + x)) := hnorm_exp
      _ ≤ Real.exp ((2 * b) * x) :=
        Real.exp_le_exp.mpr hexponent_le

/-- The fixed-line direct Stirling envelope is bounded by a polynomial on the
large vertical tail. -/
theorem Complex.fixedRealPart_vertical_stirling_upper_envelope_le_polynomial
    (σ : ℝ) :
    ∃ m : ℕ,
      ∀ t : ℝ,
        (1 / 2 : ℝ) ≤ ‖t‖ →
          Real.exp (-(Real.pi / 2) * ‖t‖) *
              (1 + ‖t‖) ^ (σ - 1 / 2) ≤
            (1 + ‖t‖) ^ m := by
  let m : ℕ := Nat.ceil (σ - 1 / 2)
  have hexponent_le : σ - 1 / 2 ≤ (m : ℝ) := by
    exact Nat.le_ceil (σ - 1 / 2)
  refine ⟨m, ?_⟩
  intro t _ht
  have hbase_one : 1 ≤ 1 + ‖t‖ := by
    exact Real.one_le_one_add_norm t
  have hbase_nonneg : 0 ≤ 1 + ‖t‖ :=
    le_trans zero_le_one hbase_one
  have hrpow_nonneg : 0 ≤ (1 + ‖t‖) ^ (σ - 1 / 2) :=
    Real.rpow_nonneg hbase_nonneg (σ - 1 / 2)
  have hexp_le_one :
      Real.exp (-(Real.pi / 2) * ‖t‖) ≤ 1 := by
    exact Real.exp_neg_pi_half_mul_norm_le_one t
  have hrpow_le_nat :
      (1 + ‖t‖) ^ (σ - 1 / 2) ≤ (1 + ‖t‖) ^ m := by
    calc
      (1 + ‖t‖) ^ (σ - 1 / 2) ≤ (1 + ‖t‖) ^ (m : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase_one hexponent_le
      _ = (1 + ‖t‖) ^ m := by
        exact Real.rpow_natCast (1 + ‖t‖) m
  calc
    Real.exp (-(Real.pi / 2) * ‖t‖) *
        (1 + ‖t‖) ^ (σ - 1 / 2) ≤
        1 * (1 + ‖t‖) ^ (σ - 1 / 2) :=
      mul_le_mul_of_nonneg_right hexp_le_one hrpow_nonneg
    _ = (1 + ‖t‖) ^ (σ - 1 / 2) := one_mul _
    _ ≤ (1 + ‖t‖) ^ m := hrpow_le_nat

/-- Large-vertical polynomial upper bound on a fixed positive real-part line,
obtained from the sectorial Binet/Stirling estimate. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_large_from_openSector
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ T : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < T ∧ 0 < C ∧
      ∀ t : ℝ,
        T ≤ ‖t‖ →
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
            C * (1 + ‖t‖) ^ m := by
  rcases
      Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical
        hbranch hcompact_half_dec height_split_dec σ with
    ⟨C, hC_pos, hstirling⟩
  rcases
      Complex.fixedRealPart_vertical_stirling_upper_envelope_le_polynomial
        σ with
    ⟨m, henvelope⟩
  refine ⟨1 / 2, C, m, half_pos zero_lt_one, hC_pos, ?_⟩
  intro t ht
  have hstirling_t :
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        C * Real.exp (-(Real.pi / 2) * ‖t‖) *
          (1 + ‖t‖) ^ (σ - 1 / 2) :=
    hstirling t ht
  have henvelope_t :
      Real.exp (-(Real.pi / 2) * ‖t‖) *
          (1 + ‖t‖) ^ (σ - 1 / 2) ≤
        (1 + ‖t‖) ^ m :=
    henvelope t ht
  have htarget :
      C * Real.exp (-(Real.pi / 2) * ‖t‖) *
          (1 + ‖t‖) ^ (σ - 1 / 2) ≤
        C * (1 + ‖t‖) ^ m := by
    calc
      C * Real.exp (-(Real.pi / 2) * ‖t‖) *
          (1 + ‖t‖) ^ (σ - 1 / 2) =
          C * (Real.exp (-(Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (σ - 1 / 2)) := by
        exact mul_assoc C
          (Real.exp (-(Real.pi / 2) * ‖t‖))
          ((1 + ‖t‖) ^ (σ - 1 / 2))
      _ ≤ C * (1 + ‖t‖) ^ m :=
        mul_le_mul_of_nonneg_left henvelope_t (le_of_lt hC_pos)
  exact le_trans hstirling_t htarget

/-- Compact-interval upper bound on a fixed positive real-part vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_compact
    (σ : ℝ)
    (hσ : 0 < σ)
    (T : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖t‖ ≤ T →
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ C := by
  have hcont : Continuous (fun t : ℝ => Complex.Gamma (σ + t * Complex.I)) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hne : ∀ m : ℕ, (σ + t * Complex.I : ℂ) ≠ -m := by
      intro m hm
      have hre_eq : (σ + t * Complex.I : ℂ).re = (-(m : ℂ)).re :=
        congrArg Complex.re hm
      have hright : (-(m : ℂ)).re = -(m : ℝ) :=
        rfl
      have hleft : (σ + t * Complex.I : ℂ).re = σ :=
        Complex.fixedRealPartLine_re σ t
      have hσ_nonpos : σ ≤ 0 := by
        calc
          σ = (σ + t * Complex.I : ℂ).re := hleft.symm
          _ = (-(m : ℂ)).re := hre_eq
          _ = -(m : ℝ) := hright
          _ ≤ 0 := by
            exact neg_nonpos.mpr (Nat.cast_nonneg m)
      exact (not_le_of_gt hσ) hσ_nonpos
    have hline_cont :
        ContinuousAt (fun u : ℝ => (σ : ℂ) + u * Complex.I) t := by
      exact
        (continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).continuousAt
    have hgamma_at :
        ContinuousAt Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      (Complex.differentiableAt_Gamma
        ((σ : ℂ) + (t : ℂ) * Complex.I) hne).continuousAt
    show ContinuousAt
      (fun u : ℝ => Complex.Gamma ((σ : ℂ) + (u : ℂ) * Complex.I)) t
    exact
      ContinuousAt.comp' hgamma_at hline_cont
  have hcompact : IsCompact (Set.Icc (-T) T) :=
    isCompact_Icc
  have hbound :
      ∃ C : ℝ, ∀ t : ℝ, t ∈ Set.Icc (-T) T → ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ C :=
    hcompact.exists_bound_of_continuousOn
      (f := fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      hcont.continuousOn
  rcases hbound with ⟨C0, hC0⟩
  refine ⟨max C0 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) < 1 := zero_lt_one
    exact lt_of_lt_of_le h1 (le_max_right C0 1)
  · intro t ht
    have hmem : t ∈ Set.Icc (-T) T := by
      have ht_abs : |t| ≤ T := by
        exact
          Eq.subst
            (motive := fun r : ℝ => r ≤ T)
            (Real.norm_eq_abs t)
            ht
      exact abs_le.mp ht_abs
    have hleC0 : ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ C0 :=
      hC0 t hmem
    exact le_trans hleC0 (le_max_left C0 1)

/-- Compact and large-vertical upper estimates assemble to a global polynomial
upper bound on a fixed positive real-part vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_assemble
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  rcases
    Complex.Gamma_fixedRealPart_vertical_upper_bound_large_from_openSector
      hbranch σ hcompact_half_dec height_split_dec with
    ⟨T, Ctail, m, hT_pos, hCtail_pos, htail⟩
  rcases
    Complex.Gamma_fixedRealPart_vertical_upper_bound_compact
      σ hσ T with
    ⟨Ccompact, hCcompact_pos, hcompact⟩
  refine ⟨max Ctail Ccompact, m, ?_, ?_⟩
  · exact lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact)
  · intro t
    match tail_split_dec T t with
    | isTrue ht_tail =>
      have htail_bound :
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
            Ctail * (1 + ‖t‖) ^ m :=
        htail t ht_tail
      have hpow_nonneg : 0 ≤ (1 + ‖t‖) ^ m :=
        pow_nonneg (Real.zero_le_one_add_norm t) m
      have hC_le : Ctail ≤ max Ctail Ccompact :=
        le_max_left Ctail Ccompact
      exact
        le_trans htail_bound
          (mul_le_mul_of_nonneg_right hC_le hpow_nonneg)
    | isFalse ht_tail =>
      have ht_compact : ‖t‖ ≤ T :=
        le_of_not_ge ht_tail
      have hcompact_bound :
          ‖Complex.Gamma (σ + t * Complex.I)‖ ≤ Ccompact :=
        hcompact t ht_compact
      have hC_le : Ccompact ≤ max Ctail Ccompact :=
        le_max_right Ctail Ccompact
      have hbase_one : 1 ≤ 1 + ‖t‖ := by
        exact Real.one_le_one_add_norm t
      have hpow_one : 1 ≤ (1 + ‖t‖) ^ m :=
        one_le_pow₀ hbase_one
      have hmax_nonneg : 0 ≤ max Ctail Ccompact :=
        le_of_lt (lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact))
      exact
        le_trans hcompact_bound
          (le_trans hC_le
            (le_mul_of_one_le_right hmax_nonneg hpow_one))

/-- Fixed-real-part vertical upper bound obtained by combining open-sector
Binet estimates for large `|t|` with compact-interval boundedness. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  exact
    Complex.Gamma_fixedRealPart_vertical_upper_bound_assemble
      hbranch σ hσ hcompact_half_dec height_split_dec tail_split_dec

/-- Fixed-real-part vertical upper bound for Gamma. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  exact
    Complex.Gamma_fixedRealPart_vertical_upper_bound_from_openSector_and_compact
      hbranch σ hσ hcompact_half_dec height_split_dec tail_split_dec

/-- Large-vertical reciprocal Gamma bound on a fixed positive real-part line,
with the correct exponential scale. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_large_from_stirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ T : ℝ, ∃ C : ℝ, ∃ A : ℝ,
      0 < T ∧ 0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        T ≤ ‖t‖ →
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
            C * Real.exp (A * ‖t‖) := by
  rcases
      Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical
        hbranch hcompact_half_dec height_split_dec σ with
    ⟨C0, hC0_pos, hstirling⟩
  let b : ℝ := Real.pi / 4
  have hb_pos : 0 < b := by
    show 0 < Real.pi / 4
    exact Real.pi_div_four_pos
  rcases
      Real.one_add_rpow_le_exp_mul_of_large
        (1 / 2 - σ) b hb_pos with
    ⟨T0, hT0_pos, hpoly_exp⟩
  let T : ℝ := max (1 / 2) T0
  let A : ℝ := Real.pi / 2 + 2 * b
  have hA_pos : 0 < A := by
    show 0 < Real.pi / 2 + 2 * b
    exact add_pos (half_pos Real.pi_pos) (mul_pos zero_lt_two hb_pos)
  refine ⟨T, C0, A, ?_, hC0_pos, hA_pos, ?_⟩
  · exact lt_of_lt_of_le (half_pos zero_lt_one) (le_max_left (1 / 2) T0)
  · intro t ht
    have ht_half : (1 / 2 : ℝ) ≤ ‖t‖ :=
      le_trans (le_max_left (1 / 2) T0) ht
    have ht_T0 : T0 ≤ ‖t‖ :=
      le_trans (le_max_right (1 / 2) T0) ht
    have hstirling_t :
        ‖(Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖ ≤
          C0 * Real.exp ((Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (1 / 2 - σ) :=
      hstirling t ht_half
    have hpoly :
        (1 + ‖t‖) ^ (1 / 2 - σ) ≤
          Real.exp ((2 * b) * ‖t‖) :=
      hpoly_exp ‖t‖ ht_T0
    have hpoly_nonneg :
        0 ≤ (1 + ‖t‖) ^ (1 / 2 - σ) := by
      exact Real.rpow_nonneg
        (add_nonneg zero_le_one (norm_nonneg t)) (1 / 2 - σ)
    have hexp_nonneg :
        0 ≤ Real.exp ((Real.pi / 2) * ‖t‖) :=
      le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖t‖))
    have henvelope :
        Real.exp ((Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (1 / 2 - σ) ≤
          Real.exp (A * ‖t‖) := by
      calc
        Real.exp ((Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (1 / 2 - σ) ≤
            Real.exp ((Real.pi / 2) * ‖t‖) *
              Real.exp ((2 * b) * ‖t‖) :=
          mul_le_mul_of_nonneg_left hpoly hexp_nonneg
        _ = Real.exp (((Real.pi / 2) + (2 * b)) * ‖t‖) := by
          calc
            Real.exp ((Real.pi / 2) * ‖t‖) *
                Real.exp ((2 * b) * ‖t‖) =
                Real.exp ((Real.pi / 2) * ‖t‖ + (2 * b) * ‖t‖) :=
              (Real.exp_add ((Real.pi / 2) * ‖t‖) ((2 * b) * ‖t‖)).symm
            _ = Real.exp (((Real.pi / 2) + (2 * b)) * ‖t‖) := by
              exact congrArg Real.exp (add_mul (Real.pi / 2) (2 * b) ‖t‖).symm
        _ = Real.exp (A * ‖t‖) := by
          rfl
    have htarget :
        C0 * Real.exp ((Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (1 / 2 - σ) ≤
          C0 * Real.exp (A * ‖t‖) := by
      calc
        C0 * Real.exp ((Real.pi / 2) * ‖t‖) *
            (1 + ‖t‖) ^ (1 / 2 - σ) =
            C0 * (Real.exp ((Real.pi / 2) * ‖t‖) *
              (1 + ‖t‖) ^ (1 / 2 - σ)) := by
          exact mul_assoc C0
            (Real.exp ((Real.pi / 2) * ‖t‖))
            ((1 + ‖t‖) ^ (1 / 2 - σ))
        _ ≤ C0 * Real.exp (A * ‖t‖) :=
          mul_le_mul_of_nonneg_left henvelope (le_of_lt hC0_pos)
    exact le_trans hstirling_t htarget

/-- Compact-interval reciprocal bound on a fixed positive real-part vertical
line, using nonvanishing of Gamma on the open right half-plane. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_compact
    (σ : ℝ)
    (hσ : 0 < σ)
    (T : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ‖t‖ ≤ T →
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ C := by
  have hcont :
      Continuous
        (fun t : ℝ => (Complex.Gamma (σ + t * Complex.I))⁻¹) := by
    refine continuous_iff_continuousAt.2 ?_
    intro t
    have hpoint_re_pos : 0 < (σ + t * Complex.I : ℂ).re := by
      exact (Complex.fixedRealPartLine_re σ t).symm ▸ hσ
    have hne : Complex.Gamma (σ + t * Complex.I) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos hpoint_re_pos
    have hgamma_cont :
        ContinuousAt (fun t : ℝ => Complex.Gamma (σ + t * Complex.I)) t := by
      have havoid : ∀ m : ℕ, (σ + t * Complex.I : ℂ) ≠ -m := by
        intro m hm
        have hre_eq : (σ + t * Complex.I : ℂ).re = (-(m : ℂ)).re :=
          congrArg Complex.re hm
        have hright : (-(m : ℂ)).re = -(m : ℝ) :=
          rfl
        have hleft : (σ + t * Complex.I : ℂ).re = σ := by
          exact Complex.fixedRealPartLine_re σ t
        have hσ_nonpos : σ ≤ 0 := by
          calc
            σ = (σ + t * Complex.I : ℂ).re := hleft.symm
            _ = (-(m : ℂ)).re := hre_eq
            _ = -(m : ℝ) := hright
            _ ≤ 0 := by
              exact neg_nonpos.mpr (Nat.cast_nonneg m)
        exact (not_le_of_gt hσ) hσ_nonpos
      exact
        have hline_cont :
            ContinuousAt (fun u : ℝ => (σ : ℂ) + u * Complex.I) t := by
          exact
            (continuous_const.add
              (Complex.continuous_ofReal.mul continuous_const)).continuousAt
        have hgamma_at :
            ContinuousAt Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) :=
          (Complex.differentiableAt_Gamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) havoid).continuousAt
        show ContinuousAt
          (fun u : ℝ => Complex.Gamma ((σ : ℂ) + (u : ℂ) * Complex.I)) t from
        ContinuousAt.comp' hgamma_at hline_cont
    exact hgamma_cont.inv₀ hne
  have hcompact : IsCompact (Set.Icc (-T) T) :=
    isCompact_Icc
  have hbound :
      ∃ C : ℝ,
        ∀ t : ℝ,
          t ∈ Set.Icc (-T) T →
            ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ C :=
    hcompact.exists_bound_of_continuousOn
      (f := fun t : ℝ => (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹)
      hcont.continuousOn
  rcases hbound with ⟨C0, hC0⟩
  refine ⟨max C0 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  · intro t ht
    have hmem : t ∈ Set.Icc (-T) T := by
      have ht_abs : |t| ≤ T := by
        exact
          Eq.subst
            (motive := fun r : ℝ => r ≤ T)
            (Real.norm_eq_abs t)
            ht
      exact abs_le.mp ht_abs
    have hleC0 :
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ C0 :=
      hC0 t hmem
    exact le_trans hleC0 (le_max_left C0 1)

/-- Compact and large-vertical reciprocal estimates assemble to the global
fixed-line exponential reciprocal bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_assemble
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  rcases
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_large_from_stirling
      hbranch σ hcompact_half_dec height_split_dec with
    ⟨T, Ctail, A, hT_pos, hCtail_pos, hA_pos, htail⟩
  rcases
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_compact
      σ hσ T with
    ⟨Ccompact, hCcompact_pos, hcompact⟩
  refine ⟨max Ctail Ccompact, A, ?_, hA_pos, ?_⟩
  · exact lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact)
  · intro t
    match tail_split_dec T t with
    | isTrue ht_tail =>
      have htail_bound :
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
            Ctail * Real.exp (A * ‖t‖) :=
        htail t ht_tail
      have hexp_nonneg : 0 ≤ Real.exp (A * ‖t‖) :=
        le_of_lt (Real.exp_pos (A * ‖t‖))
      have hC_le : Ctail ≤ max Ctail Ccompact :=
        le_max_left Ctail Ccompact
      exact
        le_trans htail_bound
          (mul_le_mul_of_nonneg_right hC_le hexp_nonneg)
    | isFalse ht_tail =>
      have ht_compact : ‖t‖ ≤ T :=
        le_of_not_ge ht_tail
      have hcompact_bound :
          ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤ Ccompact :=
        hcompact t ht_compact
      have hC_le : Ccompact ≤ max Ctail Ccompact :=
        le_max_right Ctail Ccompact
      have hA_norm_nonneg : 0 ≤ A * ‖t‖ :=
        mul_nonneg (le_of_lt hA_pos) (norm_nonneg t)
      have hexp_one : 1 ≤ Real.exp (A * ‖t‖) := by
        calc
          1 = Real.exp 0 := by
            exact Real.exp_zero.symm
          _ ≤ Real.exp (A * ‖t‖) :=
            Real.exp_le_exp.mpr hA_norm_nonneg
      have hmax_nonneg : 0 ≤ max Ctail Ccompact :=
        le_of_lt (lt_of_lt_of_le hCtail_pos (le_max_left Ctail Ccompact))
      exact
        le_trans hcompact_bound
          (le_trans hC_le
            (le_mul_of_one_le_right hmax_nonneg hexp_one))

/-- Fixed-real-part reciprocal bound from nonvanishing, compact-interval
control, and the large-vertical Stirling/Binet estimate. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  exact
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_assemble
      hbranch σ hσ hcompact_half_dec height_split_dec tail_split_dec

/-- Fixed-real-part vertical reciprocal bound for Gamma.

The reciprocal has exponential, not polynomial, vertical growth:
`1 / Γ(σ + it)` grows like `exp (π |t| / 2)` up to powers of `|t|`.
This owner statement records the correct classical growth scale. -/
theorem Complex.Gamma_fixedRealPart_vertical_lower_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (σ : ℝ)
    (hσ : 0 < σ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖))
    (tail_split_dec : ∀ T t : ℝ, Decidable (T ≤ ‖t‖)) :
    ∃ C : ℝ, ∃ A : ℝ,
      0 < C ∧ 0 < A ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * Real.exp (A * ‖t‖) := by
  exact
    Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_from_nonvanishing_and_stirling
      hbranch σ hσ hcompact_half_dec height_split_dec tail_split_dec

end

end LFunctions
end Boundary

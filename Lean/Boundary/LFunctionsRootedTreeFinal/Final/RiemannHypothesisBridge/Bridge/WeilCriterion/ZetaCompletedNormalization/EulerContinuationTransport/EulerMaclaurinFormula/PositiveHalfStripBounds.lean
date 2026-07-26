import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.PoleClearedBounds

/-!
# Positive half-strip Euler--Maclaurin bounds

This file owns the first-order Euler--Maclaurin estimates that are uniform on
`1 / 2 ≤ Re s ≤ 1`.  This is the closed positive half of the critical strip;
the completed functional equation transports the other half to this one.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open Filter MeasureTheory Set

/-- A scalar first-order Euler--Maclaurin tail is at most two once its real
exponent is bounded below by one half. -/
theorem integral_Ioi_rpow_neg_re_add_one_le_two_of_half_le
    {N σ : ℝ}
    (hN : 1 ≤ N)
    (hσ : (1 / 2 : ℝ) ≤ σ) :
    ∫ x in Set.Ioi N, x ^ (-(σ + 1)) ≤ 2 := by
  have hhalfPositive : (0 : ℝ) < 1 / 2 :=
    div_pos zero_lt_one (zero_lt_two : (0 : ℝ) < 2)
  have hNPositive : 0 < N :=
    lt_of_lt_of_le zero_lt_one hN
  have hσPositive : 0 < σ :=
    lt_of_lt_of_le hhalfPositive hσ
  have honeLtExponent : (1 : ℝ) < σ + 1 :=
    lt_add_of_pos_left 1 hσPositive
  have hpowerExponent : -(σ + 1) < -(1 : ℝ) :=
    neg_lt_neg honeLtExponent
  have hintegral :
      ∫ x in Set.Ioi N, x ^ (-(σ + 1)) =
        -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) :=
    integral_Ioi_rpow_of_lt hpowerExponent hNPositive
  have hdenominator : -(σ + 1) + 1 = -σ := by
    calc
      -(σ + 1) + 1 = (-σ + -1) + 1 := by
        exact congrArg (fun value : ℝ => value + 1) (neg_add σ 1)
      _ = -σ + (-1 + 1) := by
        exact add_assoc (-σ) (-1) 1
      _ = -σ + 0 := by
        exact congrArg (fun value : ℝ => -σ + value) (neg_add_cancel (1 : ℝ))
      _ = -σ := by
        exact add_zero (-σ)
  have hvalue :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
        N ^ (-σ) / σ := by
    have hnumerator : N ^ (-(σ + 1) + 1) = N ^ (-σ) :=
      congrArg (fun exponent : ℝ => N ^ exponent) hdenominator
    calc
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) =
          -N ^ (-σ) / (-(σ + 1) + 1) := by
        exact congrArg
          (fun value : ℝ => -value / (-(σ + 1) + 1))
          hnumerator
      _ = -N ^ (-σ) / (-σ) := by
        exact congrArg (fun value : ℝ => -N ^ (-σ) / value) hdenominator
      _ = N ^ (-σ) / σ := by
        exact neg_div_neg_eq (N ^ (-σ)) σ
  have hσNonnegative : 0 ≤ σ :=
    le_of_lt hσPositive
  have hexponentNonpositive : -σ ≤ 0 :=
    neg_nonpos.mpr hσNonnegative
  have hpowerLeOne : N ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN hexponentNonpositive
  have hquotientLe : N ^ (-σ) / σ ≤ 1 / σ :=
    div_le_div_of_nonneg_right hpowerLeOne hσNonnegative
  have hhalfReciprocal : (1 : ℝ) / (1 / 2) = 2 := by
    exact one_div_one_div (2 : ℝ)
  have honeDivLeTwo : (1 : ℝ) / σ ≤ 2 := by
    have hreciprocal : (1 : ℝ) / σ ≤ 1 / (1 / 2 : ℝ) :=
      one_div_le_one_div_of_le hhalfPositive hσ
    exact le_trans hreciprocal (le_of_eq hhalfReciprocal)
  have htailValue :
      -N ^ (-(σ + 1) + 1) / (-(σ + 1) + 1) ≤ 2 :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ 2)
      hvalue.symm
      (le_trans hquotientLe honeDivLeTwo)
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 2)
    hintegral.symm
    htailValue

/-- Positive-real complex powers have their exact real-power norm on the
half-strip; the lower bound is recorded for downstream integrability. -/
theorem eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow_halfStrip
    {x : ℝ}
    (hx : 0 < x)
    (z : ℂ) :
    ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ = x ^ (-(z.re + 1)) := by
  have hnorm :
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
        x ^ (-(z + 1)).re := by
    calc
      ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ =
          Complex.abs (((x : ℝ) : ℂ) ^ (-(z + 1))) := by
        exact Complex.norm_eq_abs (((x : ℝ) : ℂ) ^ (-(z + 1)))
      _ = x ^ (-(z + 1)).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hx (-(z + 1))
  have hrealPart : (-(z + 1)).re = -(z.re + 1) := by
    calc
      (-(z + 1)).re = -((z + 1).re) := by
        exact Complex.neg_re (z + 1)
      _ = -(z.re + (1 : ℂ).re) := by
        exact congrArg Neg.neg (Complex.add_re z 1)
      _ = -(z.re + 1) := by
        exact congrArg (fun value : ℝ => -(z.re + value)) Complex.one_re
  exact Eq.trans hnorm
    (congrArg (fun exponent : ℝ => x ^ exponent) hrealPart)

/-- The first Bernoulli remainder core is uniformly bounded by two on the
closed positive half-strip. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_two_halfStrip
    (z : ℂ)
    (hzHalf : (1 / 2 : ℝ) ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 2 := by
  let N : ℝ := ((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℝ)
  let domain : Set ℝ := Set.Ioi N
  let kernel : ℝ → ℂ :=
    fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((x : ℝ) : ℂ) ^ (-(z + 1)))
  let majorant : ℝ → ℝ :=
    fun x => x ^ (-(z.re + 1))
  have hNOne : (1 : ℝ) ≤ N :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hNPositive : 0 < N :=
    lt_of_lt_of_le zero_lt_one hNOne
  have hhalfPositive : (0 : ℝ) < 1 / 2 :=
    div_pos zero_lt_one (zero_lt_two : (0 : ℝ) < 2)
  have hzPositive : 0 < z.re :=
    lt_of_lt_of_le hhalfPositive hzHalf
  have honeLtExponent : (1 : ℝ) < z.re + 1 :=
    lt_add_of_pos_left 1 hzPositive
  have hpowerExponent : -(z.re + 1) < -(1 : ℝ) :=
    neg_lt_neg honeLtExponent
  have hmajorantIntegrable : Integrable majorant (volume.restrict domain) :=
    integrableOn_Ioi_rpow_of_lt hpowerExponent hNPositive
  have hkernelBound : ∀ᵐ x ∂volume.restrict domain, ‖kernel x‖ ≤ majorant x := by
    exact (ae_restrict_mem measurableSet_Ioi).mono
      (fun x hx =>
        have hxPositive : 0 < x := lt_trans hNPositive hx
        have hBernoulli :
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 := by
          exact eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
        have hcpow :
            ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ = majorant x :=
          eulerMaclaurin_norm_real_cpow_neg_add_one_eq_rpow_halfStrip
            hxPositive z
        have hmajorantNonnegative : 0 ≤ majorant x :=
          Real.rpow_nonneg (le_of_lt hxPositive) (-(z.re + 1))
        calc
          ‖kernel x‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
            exact norm_mul
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              (((x : ℝ) : ℂ) ^ (-(z + 1)))
          _ ≤ 1 * majorant x :=
            mul_le_mul hBernoulli (le_of_eq hcpow)
              (norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1))))
              zero_le_one
          _ = majorant x := by
            exact one_mul (majorant x))
  have hdomination :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤
        ∫ x in Set.Ioi N, x ^ (-(z.re + 1)) :=
    norm_integral_le_of_norm_le hmajorantIntegrable hkernelBound
  have htail :
      ∫ x in Set.Ioi N, x ^ (-(z.re + 1)) ≤ 2 :=
    integral_Ioi_rpow_neg_re_add_one_le_two_of_half_le hNOne hzHalf
  exact le_trans hdomination htail

/-- The height-dependent main term grows at most linearly on the positive
half-strip. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_norm_le_two_mul_height_halfStrip
    (z : ℂ)
    (hzNonnegative : 0 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 2 * (1 + ‖z‖) := by
  let N : ℕ := eulerMaclaurinPoleClearedZetaCutoff z
  have hNPositive : 0 < N :=
    eulerMaclaurinPoleClearedZetaCutoff_pos z
  have hNOne : (1 : ℝ) ≤ (N : ℝ) :=
    one_le_eulerMaclaurinPoleClearedZetaCutoff_real z
  have hnorm :
      ‖((N : ℕ) : ℂ) ^ ((1 : ℂ) - z)‖ =
        (N : ℝ) ^ (((1 : ℂ) - z).re) :=
    Complex.norm_natCast_cpow_of_pos hNPositive ((1 : ℂ) - z)
  have hrealPart : (((1 : ℂ) - z).re) = 1 - z.re := by
    exact Eq.trans
      (Complex.sub_re (1 : ℂ) z)
      (congrArg (fun value : ℝ => value - z.re) Complex.one_re)
  have hexponentLeOne : 1 - z.re ≤ 1 :=
    sub_le_self 1 hzNonnegative
  have hpowerLe : (N : ℝ) ^ (1 - z.re) ≤ (N : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNOne hexponentLeOne
  have hrpowOne : (N : ℝ) ^ (1 : ℝ) = (N : ℝ) :=
    Real.rpow_one (N : ℝ)
  have hcutoffLe : (N : ℝ) ≤ 2 + ‖z‖ := by
    unfold N
    unfold eulerMaclaurinPoleClearedZetaCutoff
    have hnonnegative : 0 ≤ 2 + ‖z‖ :=
      le_trans zero_le_two (le_add_of_nonneg_right (norm_nonneg z))
    exact Nat.floor_le hnonnegative
  have hheight : 2 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by
    calc
      2 + ‖z‖ ≤ 2 + 2 * ‖z‖ := by
        exact add_le_add_left
          (le_mul_of_one_le_left (norm_nonneg z) one_le_two) 2
      _ = 2 * (1 + ‖z‖) := by
        exact Eq.trans
          (congrArg (fun value : ℝ => value + 2 * ‖z‖) (mul_one 2).symm)
          (mul_add 2 1 ‖z‖).symm
  unfold eulerMaclaurinPoleClearedZetaMainTerm
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 2 * (1 + ‖z‖))
    hnorm.symm
    (Eq.subst
      (motive := fun exponent : ℝ =>
        (N : ℝ) ^ exponent ≤ 2 * (1 + ‖z‖))
      hrealPart.symm
      (le_trans hpowerLe
        (le_trans (le_of_eq hrpowOne) (le_trans hcutoffLe hheight))))

/-- The finite Dirichlet window contributes a quadratic height term throughout
the closed positive half-strip. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_norm_le_three_mul_height_sq_halfStrip
    (z : ℂ)
    (hzNonnegative : 0 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤
      3 * (1 + ‖z‖) ^ (2 : ℕ) := by
  let H : ℝ := 1 + ‖z‖
  have hHNonnegative : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hpole : ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hsum :
      ‖∑ n ∈ Finset.Icc 1 (eulerMaclaurinPoleClearedZetaCutoff z),
          1 / (((n : ℕ) : ℂ) ^ z)‖ ≤ 3 * H :=
    le_trans
      (eulerMaclaurinPoleClearedZetaFinitePart_sum_norm_le_card z hzNonnegative)
      (eulerMaclaurinPoleClearedZetaFinitePart_card_le_three_mul_height z)
  unfold eulerMaclaurinPoleClearedZetaFinitePart
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
        hHNonnegative
    _ = 3 * H ^ (2 : ℕ) := by
      exact Eq.trans
        (Eq.trans (mul_assoc H 3 H).symm
          (congrArg (fun value : ℝ => value * H) (mul_comm H 3)))
        (Eq.trans (mul_assoc 3 H H)
          (congrArg (fun value : ℝ => 3 * value) (pow_two H).symm))

/-- The endpoint correction is bounded by one height factor on the positive
half-strip. -/
theorem eulerMaclaurinPoleClearedZetaEndpointFactor_norm_le_height_halfStrip
    (z : ℂ) :
    ‖(z - 1) / 2‖ ≤ 1 + ‖z‖ := by
  have htwoNorm : ‖(2 : ℂ)‖ = (2 : ℝ) :=
    Complex.norm_natCast 2
  have hpole : ‖z - 1‖ ≤ 1 + ‖z‖ :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hdiv : ‖(z - 1) / (2 : ℂ)‖ = ‖z - 1‖ / 2 := by
    calc
      ‖(z - 1) / (2 : ℂ)‖ = ‖z - 1‖ / ‖(2 : ℂ)‖ := norm_div (z - 1) (2 : ℂ)
      _ = ‖z - 1‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖z - 1‖ / x) htwoNorm
  calc
    ‖(z - 1) / 2‖ = ‖z - 1‖ / 2 := hdiv
    _ ≤ (1 + ‖z‖) / 2 := by
      exact div_le_div_of_nonneg_right hpole zero_le_two
    _ ≤ 1 + ‖z‖ := by
      exact
        div_le_self
          (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z)))
          one_le_two

theorem eulerMaclaurinPoleClearedZetaEndpointProduct_norm_le_height_halfStrip
    (z : ℂ)
    (hzNonnegative : 0 ≤ z.re) :
    ‖(z - 1) / 2‖ *
        ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤
      (1 + ‖z‖) * 1 := by
  have hfactor :
      ‖(z - 1) / 2‖ ≤ 1 + ‖z‖ :=
    eulerMaclaurinPoleClearedZetaEndpointFactor_norm_le_height_halfStrip z
  have hreciprocal :
      ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 :=
    eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one z hzNonnegative
  have hfactor_nonneg : 0 ≤ 1 + ‖z‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hreciprocal_nonneg :
      0 ≤ ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ :=
    norm_nonneg _
  have hmul_left :
      ‖(z - 1) / 2‖ *
          ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤
        (1 + ‖z‖) *
          ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ :=
    mul_le_mul_of_nonneg_right hfactor hreciprocal_nonneg
  have hmul_right :
      (1 + ‖z‖) *
          ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤
        (1 + ‖z‖) * 1 :=
    mul_le_mul_of_nonneg_left hreciprocal hfactor_nonneg
  exact le_trans hmul_left hmul_right

theorem eulerMaclaurinPoleClearedZetaEndpointTerm_norm_le_height_halfStrip
    (z : ℂ)
    (hzNonnegative : 0 ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ 1 + ‖z‖ := by
  unfold eulerMaclaurinPoleClearedZetaEndpointTerm
  calc
    ‖(-((z - 1) / 2)) *
        (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ =
        ‖(z - 1) / 2‖ *
          ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ := by
      exact Eq.trans
        (norm_mul (-((z - 1) / 2))
          (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))
        (congrArg
          (fun value : ℝ => value *
            ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖)
          (norm_neg ((z - 1) / 2)))
    _ ≤ (1 + ‖z‖) * 1 := by
      exact
        eulerMaclaurinPoleClearedZetaEndpointProduct_norm_le_height_halfStrip
          z hzNonnegative
    _ = 1 + ‖z‖ := by
      exact mul_one (1 + ‖z‖)

/-- The Bernoulli remainder contributes at most two quadratic height factors
on the closed positive half-strip. -/
theorem eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_norm_le_two_mul_height_sq_halfStrip
    (z : ℂ)
    (hzHalf : (1 / 2 : ℝ) ≤ z.re) :
    ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
      2 * (1 + ‖z‖) ^ (2 : ℕ) := by
  let H : ℝ := 1 + ‖z‖
  have hHNonnegative : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hzNorm : ‖z‖ ≤ H :=
    le_add_of_nonneg_left zero_le_one
  have hzSubNorm : ‖z - 1‖ ≤ H :=
    eulerMaclaurinPoleClearedZetaFinitePart_poleFactor_norm_le_height z
  have hcore :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ ≤ 2 :=
    eulerMaclaurinPoleClearedZetaBernoulliIntegralCore_norm_le_two_halfStrip
      z hzHalf
  unfold eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder
  calc
    ‖-((z - 1) * z) * eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ =
        ‖(z - 1) * z‖ *
          ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
      exact Eq.trans
        (norm_mul (-((z - 1) * z))
          (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))
        (congrArg
          (fun value : ℝ => value *
            ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖)
          (norm_neg ((z - 1) * z)))
    _ = (‖z - 1‖ * ‖z‖) *
          ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖ := by
      exact congrArg
        (fun value : ℝ => value *
          ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z‖)
        (norm_mul (z - 1) z)
    _ ≤ (H * H) * 2 := by
      exact mul_le_mul
        (mul_le_mul hzSubNorm hzNorm (norm_nonneg z) hHNonnegative)
        hcore
        (norm_nonneg (eulerMaclaurinPoleClearedZetaBernoulliIntegralCore z))
        (mul_nonneg hHNonnegative hHNonnegative)
    _ = 2 * H ^ (2 : ℕ) := by
      exact Eq.trans
        (mul_comm (H * H) 2)
        (congrArg (fun value : ℝ => 2 * value) (pow_two H).symm)

/-- Direct first-order Euler--Maclaurin control of pole-cleared zeta on the
closed positive half of the critical strip. -/
theorem poleClearedRiemannZeta_norm_le_componentBudget_mul_height_sq_positiveHalfStrip
    (z : ℂ)
    (hzHalf : (1 / 2 : ℝ) ≤ z.re)
    (hzOne : z.re ≤ 1)
    (hzImaginaryTail : 1 ≤ ‖z.im‖) :
    ‖poleClearedRiemannZeta z‖ ≤
      (((3 : ℝ) + 2) + 1 + 2) * (1 + ‖z‖) ^ (2 : ℕ) := by
  let H : ℝ := 1 + ‖z‖
  let Q : ℝ := H ^ (2 : ℕ)
  have hhalfPositive : (0 : ℝ) < 1 / 2 :=
    div_pos zero_lt_one zero_lt_two
  have hzPositive : 0 < z.re :=
    lt_of_lt_of_le hhalfPositive hzHalf
  have hzNonnegative : 0 ≤ z.re :=
    le_of_lt hzPositive
  have hzLessThanTwo : z.re < 2 :=
    lt_of_le_of_lt hzOne one_lt_two
  have hzNotOne : z ≠ 1 := by
    intro hzEqual
    have himaginaryZero : z.im = 0 :=
      Eq.trans (congrArg Complex.im hzEqual) Complex.one_im
    have htailNormZero : (1 : ℝ) ≤ ‖(0 : ℝ)‖ :=
      Eq.subst
        (motive := fun value : ℝ => 1 ≤ ‖value‖)
        himaginaryZero
        hzImaginaryTail
    have htailZero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun value : ℝ => 1 ≤ value)
        (norm_zero : ‖(0 : ℝ)‖ = (0 : ℝ))
        htailNormZero
    exact (not_le_of_gt zero_lt_one) htailZero
  have hformula :
      poleClearedRiemannZeta z =
        eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z :=
    eulerMaclaurin_poleClearedRiemannZeta_formula_on_positivePuncturedStrip
      z hzPositive hzLessThanTwo hzNotOne
  have hHNonnegative : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hHOne : 1 ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hHLeQ : H ≤ Q := by
    have hmul : H * 1 ≤ H * H :=
      mul_le_mul_of_nonneg_left hHOne hHNonnegative
    calc
      H = H * 1 := (mul_one H).symm
      _ ≤ H * H := hmul
      _ = Q := (pow_two H).symm
  have hfinite :
      ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ 3 * Q :=
    eulerMaclaurinPoleClearedZetaFinitePart_norm_le_three_mul_height_sq_halfStrip
      z hzNonnegative
  have hmain :
      ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 2 * Q :=
    le_trans
      (eulerMaclaurinPoleClearedZetaMainTerm_norm_le_two_mul_height_halfStrip
        z hzNonnegative)
      (mul_le_mul_of_nonneg_left hHLeQ zero_le_two)
  have hendpoint :
      ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ 1 * Q :=
    le_trans
      (eulerMaclaurinPoleClearedZetaEndpointTerm_norm_le_height_halfStrip
        z hzNonnegative)
      (le_trans hHLeQ (le_of_eq (one_mul Q).symm))
  have hremainder :
      ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤ 2 * Q :=
    eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder_norm_le_two_mul_height_sq_halfStrip
      z hzHalf
  have htriangle :
      ‖eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z +
          eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
        (‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖) +
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ :=
    le_trans
      (norm_add_le
        (eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z)
        (eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z))
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
        ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖)
  have hcomponents :
      (‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖) +
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
          ‖eulerMaclaurinPoleClearedZetaBernoulliIntegralRemainder z‖ ≤
        (3 * Q + 2 * Q) + 1 * Q + 2 * Q :=
    add_le_add
      (add_le_add (add_le_add hfinite hmain) hendpoint)
      hremainder
  have hcoefficients :
      (3 * Q + 2 * Q) + 1 * Q + 2 * Q =
        (((3 : ℝ) + 2) + 1 + 2) * Q := by
    calc
      (3 * Q + 2 * Q) + 1 * Q + 2 * Q =
          ((3 + 2) * Q + 1 * Q) + 2 * Q := by
        exact congrArg (fun value : ℝ => (value + 1 * Q) + 2 * Q)
          (add_mul 3 2 Q).symm
      _ = (((3 + 2) + 1) * Q) + 2 * Q := by
        exact congrArg (fun value : ℝ => value + 2 * Q)
          (add_mul (3 + 2) 1 Q).symm
      _ = (((3 + 2) + 1) + 2) * Q := by
        exact (add_mul ((3 + 2) + 1) 2 Q).symm
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ (((3 : ℝ) + 2) + 1 + 2) * Q)
    hformula.symm
    (le_trans htriangle (le_trans hcomponents (le_of_eq hcoefficients)))

end
end LFunctions
end Boundary

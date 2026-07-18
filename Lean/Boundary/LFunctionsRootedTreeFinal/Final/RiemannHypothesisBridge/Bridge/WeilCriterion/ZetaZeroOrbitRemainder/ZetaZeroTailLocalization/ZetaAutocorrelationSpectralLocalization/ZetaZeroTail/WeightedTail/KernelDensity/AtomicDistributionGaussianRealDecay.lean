import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-!
# Shifted real Gaussian decay

This file owns the pure real-analysis fact that translated Gaussians dominate
every polynomial weight based on `1 + |y|`.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

open scoped ZeroAtInfty

/-- An unshifted Gaussian absorbs every natural power of `1 + |y|`. -/
theorem realGaussian_centeredHeight_power_tendsto_zero
    (a : ℝ)
    (ha : 0 < a)
    (degree : ℕ) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-a * y ^ 2) * (1 + |y|) ^ degree)
      (Filter.cocompact ℝ)
      (nhds 0) := by
  have hbaseRpow :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      ha (degree : ℝ)
  have hbaseNatural :
      Filter.Tendsto
        (fun y : ℝ => |y| ^ degree * Real.exp (-a * y ^ 2))
        (Filter.cocompact ℝ)
        (nhds 0) :=
    Filter.Tendsto.congr'
      (Filter.Eventually.of_forall
        (fun y : ℝ =>
          congrArg
            (fun value : ℝ => value * Real.exp (-a * y ^ 2))
            (Real.rpow_natCast |y| degree)))
      hbaseRpow
  have hupperLimitRaw :
      Filter.Tendsto
        (fun y : ℝ =>
          (2 : ℝ) ^ degree *
            (|y| ^ degree * Real.exp (-a * y ^ 2)))
        (Filter.cocompact ℝ)
        (nhds ((2 : ℝ) ^ degree * 0)) :=
    Filter.Tendsto.const_mul ((2 : ℝ) ^ degree) hbaseNatural
  have hupperLimitZero : (2 : ℝ) ^ degree * 0 = 0 :=
    mul_zero ((2 : ℝ) ^ degree)
  have hupperLimit :
      Filter.Tendsto
        (fun y : ℝ =>
          (2 : ℝ) ^ degree *
            (|y| ^ degree * Real.exp (-a * y ^ 2)))
        (Filter.cocompact ℝ)
        (nhds 0) :=
    Eq.subst
      (motive := fun limit : ℝ =>
        Filter.Tendsto
          (fun y : ℝ =>
            (2 : ℝ) ^ degree *
              (|y| ^ degree * Real.exp (-a * y ^ 2)))
          (Filter.cocompact ℝ)
          (nhds limit))
      hupperLimitZero
      hupperLimitRaw
  have habsoluteEventually :
      ∀ᶠ y : ℝ in Filter.cocompact ℝ, 1 ≤ |y| := by
    have hnormEventually :
        ∀ᶠ y : ℝ in Filter.cocompact ℝ, 1 ≤ ‖y‖ :=
      (tendsto_norm_cocompact_atTop.eventually
        (Filter.eventually_ge_atTop (1 : ℝ)))
    exact hnormEventually.mono
      (fun y hy =>
        Eq.subst
          (motive := fun value : ℝ => 1 ≤ value)
          (Real.norm_eq_abs y)
          hy)
  have hnonnegative :
      ∀ y : ℝ,
        0 ≤ Real.exp (-a * y ^ 2) * (1 + |y|) ^ degree :=
    fun y =>
      mul_nonneg
        (le_of_lt (Real.exp_pos (-a * y ^ 2)))
        (pow_nonneg
          (add_nonneg zero_le_one (abs_nonneg y)) degree)
  have hupperEventually :
      ∀ᶠ y : ℝ in Filter.cocompact ℝ,
        Real.exp (-a * y ^ 2) * (1 + |y|) ^ degree ≤
          (2 : ℝ) ^ degree *
            (|y| ^ degree * Real.exp (-a * y ^ 2)) :=
    habsoluteEventually.mono
      (fun y hy =>
        have hheight : 1 + |y| ≤ 2 * |y| := by
          have hadd : 1 + |y| ≤ |y| + |y| :=
            add_le_add_right hy |y|
          exact Eq.subst
            (motive := fun value : ℝ => 1 + |y| ≤ value)
            (two_mul |y|).symm
            hadd
        have hpower :
            (1 + |y|) ^ degree ≤ (2 * |y|) ^ degree :=
          pow_le_pow_left₀
            (add_nonneg zero_le_one (abs_nonneg y))
            hheight
            degree
        have hscaledPower :
            Real.exp (-a * y ^ 2) * (1 + |y|) ^ degree ≤
              Real.exp (-a * y ^ 2) * (2 * |y|) ^ degree :=
          mul_le_mul_of_nonneg_left hpower
            (le_of_lt (Real.exp_pos (-a * y ^ 2)))
        have hpowerProduct :
            (2 * |y|) ^ degree =
              (2 : ℝ) ^ degree * |y| ^ degree :=
          mul_pow (2 : ℝ) |y| degree
        have hreassociate :
            Real.exp (-a * y ^ 2) *
                ((2 : ℝ) ^ degree * |y| ^ degree) =
              (2 : ℝ) ^ degree *
                (|y| ^ degree * Real.exp (-a * y ^ 2)) := by
          have hfirst :
              Real.exp (-a * y ^ 2) *
                  ((2 : ℝ) ^ degree * |y| ^ degree) =
                (Real.exp (-a * y ^ 2) * (2 : ℝ) ^ degree) *
                  |y| ^ degree :=
            (mul_assoc
              (Real.exp (-a * y ^ 2))
              ((2 : ℝ) ^ degree)
              (|y| ^ degree)).symm
          have hsecond :
              (Real.exp (-a * y ^ 2) * (2 : ℝ) ^ degree) *
                  |y| ^ degree =
                ((2 : ℝ) ^ degree * Real.exp (-a * y ^ 2)) *
                  |y| ^ degree :=
            congrArg
              (fun value : ℝ => value * |y| ^ degree)
              (mul_comm
                (Real.exp (-a * y ^ 2))
                ((2 : ℝ) ^ degree))
          have hthird :
              ((2 : ℝ) ^ degree * Real.exp (-a * y ^ 2)) *
                  |y| ^ degree =
                (2 : ℝ) ^ degree *
                  (Real.exp (-a * y ^ 2) * |y| ^ degree) :=
            mul_assoc
              ((2 : ℝ) ^ degree)
              (Real.exp (-a * y ^ 2))
              (|y| ^ degree)
          have hfourth :
              (2 : ℝ) ^ degree *
                  (Real.exp (-a * y ^ 2) * |y| ^ degree) =
                (2 : ℝ) ^ degree *
                  (|y| ^ degree * Real.exp (-a * y ^ 2)) :=
            congrArg
              (fun value : ℝ => (2 : ℝ) ^ degree * value)
              (mul_comm
                (Real.exp (-a * y ^ 2))
                (|y| ^ degree))
          exact Eq.trans hfirst
            (Eq.trans hsecond (Eq.trans hthird hfourth))
        Eq.subst
          (motive := fun value : ℝ =>
            Real.exp (-a * y ^ 2) * (1 + |y|) ^ degree ≤ value)
          (Eq.trans
            (congrArg
              (fun value : ℝ => Real.exp (-a * y ^ 2) * value)
              hpowerProduct)
            hreassociate)
          hscaledPower)
  exact squeeze_zero'
    (Filter.Eventually.of_forall hnonnegative)
    hupperEventually
    hupperLimit

/-- A translated Gaussian times a natural power of `1 + |y|` tends to zero at
infinity. -/
theorem shiftedRealGaussian_centeredHeight_power_tendsto_zero
    (a shift : ℝ)
    (ha : 0 < a)
    (degree : ℕ) :
    Filter.Tendsto
      (fun y : ℝ =>
        Real.exp (-a * (y - shift) ^ 2) * (1 + |y|) ^ degree)
      (Filter.cocompact ℝ)
      (nhds 0) := by
  let translationBound : ℝ := 1 + |shift|
  have htranslationBoundNonnegative : 0 ≤ translationBound :=
    add_nonneg zero_le_one (abs_nonneg shift)
  have htranslation :
      Filter.Tendsto
        (fun y : ℝ => y - shift)
        (Filter.cocompact ℝ)
        (Filter.cocompact ℝ) :=
    (Homeomorph.subRight shift).isClosedEmbedding.tendsto_cocompact
  have hbase := realGaussian_centeredHeight_power_tendsto_zero a ha degree
  have htranslatedBase :
      Filter.Tendsto
        (fun y : ℝ =>
          Real.exp (-a * (y - shift) ^ 2) *
            (1 + |y - shift|) ^ degree)
        (Filter.cocompact ℝ)
        (nhds 0) :=
    hbase.comp htranslation
  have hupperLimitRaw :
      Filter.Tendsto
        (fun y : ℝ =>
          translationBound ^ degree *
            (Real.exp (-a * (y - shift) ^ 2) *
              (1 + |y - shift|) ^ degree))
        (Filter.cocompact ℝ)
        (nhds (translationBound ^ degree * 0)) :=
    Filter.Tendsto.const_mul
      (translationBound ^ degree)
      htranslatedBase
  have hzeroProduct : translationBound ^ degree * 0 = 0 :=
    mul_zero (translationBound ^ degree)
  have hupperLimit :
      Filter.Tendsto
        (fun y : ℝ =>
          translationBound ^ degree *
            (Real.exp (-a * (y - shift) ^ 2) *
              (1 + |y - shift|) ^ degree))
        (Filter.cocompact ℝ)
        (nhds 0) :=
    Eq.subst
      (motive := fun limit : ℝ =>
        Filter.Tendsto
          (fun y : ℝ =>
            translationBound ^ degree *
              (Real.exp (-a * (y - shift) ^ 2) *
                (1 + |y - shift|) ^ degree))
          (Filter.cocompact ℝ)
          (nhds limit))
      hzeroProduct
      hupperLimitRaw
  have hheightComparison :
      ∀ y : ℝ,
        1 + |y| ≤ translationBound * (1 + |y - shift|) := by
    intro y
    let displacement : ℝ := y - shift
    have hyDecomposition : y = displacement + shift :=
      (sub_add_cancel y shift).symm
    have habsolute : |y| ≤ |displacement| + |shift| :=
      Eq.subst
        (motive := fun value : ℝ =>
          |value| ≤ |displacement| + |shift|)
        hyDecomposition.symm
        (abs_add_le displacement shift)
    have honeAdded :
        1 + |y| ≤ 1 + (|displacement| + |shift|) :=
      add_le_add_left habsolute 1
    have hleftAssociate :
        1 + (|displacement| + |shift|) =
          (1 + |displacement|) + |shift| :=
      (add_assoc 1 |displacement| |shift|).symm
    have hproductNonnegative : 0 ≤ |shift| * |displacement| :=
      mul_nonneg (abs_nonneg shift) (abs_nonneg displacement)
    have hincrease :
        (1 + |displacement|) + |shift| ≤
          ((1 + |displacement|) + |shift|) +
            |shift| * |displacement| :=
      le_add_of_nonneg_right hproductNonnegative
    have hrightExpand :
        translationBound * (1 + |displacement|) =
          ((1 + |displacement|) + |shift|) +
            |shift| * |displacement| := by
      have hdistribute :
          (1 + |shift|) * (1 + |displacement|) =
            1 * (1 + |displacement|) +
              |shift| * (1 + |displacement|) :=
        add_mul 1 |shift| (1 + |displacement|)
      have honeProduct : 1 * (1 + |displacement|) =
          1 + |displacement| :=
        one_mul (1 + |displacement|)
      have hshiftDistribute :
          |shift| * (1 + |displacement|) =
            |shift| + |shift| * |displacement| :=
        Eq.trans
          (mul_add |shift| 1 |displacement|)
          (congrArg
            (fun value : ℝ => value + |shift| * |displacement|)
            (mul_one |shift|))
      exact Eq.trans
        hdistribute
        (Eq.trans
          (congrArg₂ Add.add honeProduct hshiftDistribute)
          (add_assoc
            (1 + |displacement|)
            |shift|
            (|shift| * |displacement|)).symm)
    exact le_trans honeAdded
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤ translationBound * (1 + |displacement|))
        hleftAssociate.symm
        (Eq.subst
          (motive := fun right : ℝ =>
            (1 + |displacement|) + |shift| ≤ right)
          hrightExpand.symm
          hincrease))
  have htargetNonnegative :
      ∀ y : ℝ,
        0 ≤ Real.exp (-a * (y - shift) ^ 2) *
          (1 + |y|) ^ degree :=
    fun y =>
      mul_nonneg
        (le_of_lt (Real.exp_pos (-a * (y - shift) ^ 2)))
        (pow_nonneg
          (add_nonneg zero_le_one (abs_nonneg y)) degree)
  have hupper :
      ∀ y : ℝ,
        Real.exp (-a * (y - shift) ^ 2) * (1 + |y|) ^ degree ≤
          translationBound ^ degree *
            (Real.exp (-a * (y - shift) ^ 2) *
              (1 + |y - shift|) ^ degree) := by
    intro y
    have hheightPower :
        (1 + |y|) ^ degree ≤
          (translationBound * (1 + |y - shift|)) ^ degree :=
      pow_le_pow_left₀
        (add_nonneg zero_le_one (abs_nonneg y))
        (hheightComparison y)
        degree
    have hscaled :
        Real.exp (-a * (y - shift) ^ 2) * (1 + |y|) ^ degree ≤
          Real.exp (-a * (y - shift) ^ 2) *
            (translationBound * (1 + |y - shift|)) ^ degree :=
      mul_le_mul_of_nonneg_left hheightPower
        (le_of_lt (Real.exp_pos (-a * (y - shift) ^ 2)))
    have hpowerProduct :
        (translationBound * (1 + |y - shift|)) ^ degree =
          translationBound ^ degree * (1 + |y - shift|) ^ degree :=
      mul_pow translationBound (1 + |y - shift|) degree
    have hreassociate :
        Real.exp (-a * (y - shift) ^ 2) *
            (translationBound ^ degree * (1 + |y - shift|) ^ degree) =
          translationBound ^ degree *
            (Real.exp (-a * (y - shift) ^ 2) *
              (1 + |y - shift|) ^ degree) :=
      Eq.trans
        (mul_assoc
          (Real.exp (-a * (y - shift) ^ 2))
          (translationBound ^ degree)
          ((1 + |y - shift|) ^ degree)).symm
        (Eq.trans
          (congrArg
            (fun value : ℝ => value * (1 + |y - shift|) ^ degree)
            (mul_comm
              (Real.exp (-a * (y - shift) ^ 2))
              (translationBound ^ degree)))
          (mul_assoc
            (translationBound ^ degree)
            (Real.exp (-a * (y - shift) ^ 2))
            ((1 + |y - shift|) ^ degree)))
    exact Eq.subst
      (motive := fun value : ℝ =>
        Real.exp (-a * (y - shift) ^ 2) * (1 + |y|) ^ degree ≤ value)
      (Eq.trans
        (congrArg
          (fun value : ℝ => Real.exp (-a * (y - shift) ^ 2) * value)
          hpowerProduct)
        hreassociate)
      hscaled
  exact squeeze_zero
    htargetNonnegative
    hupper
    hupperLimit

/-- A translated real Gaussian is bounded globally by every negative power of
the canonical height `1 + |y|`. -/
theorem exists_shiftedRealGaussian_centeredHeight_decay
    (a shift : ℝ)
    (ha : 0 < a)
    (degree : ℕ) :
    ∃ bound : ℝ,
      0 < bound ∧
      ∀ y : ℝ,
        Real.exp (-a * (y - shift) ^ 2) ≤
          bound * (1 + |y|) ^ (-(degree : ℤ)) := by
  let weightedGaussian : ℝ → ℝ :=
    fun y : ℝ =>
      Real.exp (-a * (y - shift) ^ 2) * (1 + |y|) ^ degree
  have hweightedContinuous : Continuous weightedGaussian := by
    have hdifference : Continuous (fun y : ℝ => y - shift) :=
      continuous_id.sub continuous_const
    have hsquare : Continuous (fun y : ℝ => (y - shift) ^ 2) :=
      hdifference.pow 2
    have hquadratic :
        Continuous (fun y : ℝ => -a * (y - shift) ^ 2) :=
      continuous_const.mul hsquare
    have hexponential :
        Continuous (fun y : ℝ => Real.exp (-a * (y - shift) ^ 2)) :=
      Real.continuous_exp.comp hquadratic
    have hheight : Continuous (fun y : ℝ => 1 + |y|) :=
      continuous_const.add continuous_abs
    have hheightPower :
        Continuous (fun y : ℝ => (1 + |y|) ^ degree) :=
      hheight.pow degree
    exact hexponential.mul hheightPower
  have hweightedTendsto :
      Filter.Tendsto weightedGaussian
        (Filter.cocompact ℝ) (nhds 0) :=
    shiftedRealGaussian_centeredHeight_power_tendsto_zero
      a shift ha degree
  let weightedGaussianAtInfinity : C₀(ℝ, ℝ) :=
    { toFun := weightedGaussian
      continuous_toFun := hweightedContinuous
      zero_at_infty' := hweightedTendsto }
  let bound : ℝ := ‖weightedGaussianAtInfinity.toBCF‖ + 1
  have hboundPositive : 0 < bound :=
    add_pos_of_nonneg_of_pos
      (norm_nonneg weightedGaussianAtInfinity.toBCF)
      zero_lt_one
  have hpointwise :
      ∀ y : ℝ,
        Real.exp (-a * (y - shift) ^ 2) ≤
          bound * (1 + |y|) ^ (-(degree : ℤ)) := by
    intro y
    let height : ℝ := 1 + |y|
    have hheightPositive : 0 < height :=
      add_pos_of_pos_of_nonneg zero_lt_one (abs_nonneg y)
    have hheightPowerPositive : 0 < height ^ degree :=
      pow_pos hheightPositive degree
    have hweightedNonnegative : 0 ≤ weightedGaussian y :=
      mul_nonneg
        (le_of_lt (Real.exp_pos (-a * (y - shift) ^ 2)))
        (pow_nonneg
          (add_nonneg zero_le_one (abs_nonneg y)) degree)
    have hweightedNorm : ‖weightedGaussian y‖ = weightedGaussian y :=
      Eq.trans
        (Real.norm_eq_abs (weightedGaussian y))
        (abs_of_nonneg hweightedNonnegative)
    have hnormBound :
        ‖weightedGaussianAtInfinity.toBCF y‖ ≤
          ‖weightedGaussianAtInfinity.toBCF‖ :=
      weightedGaussianAtInfinity.toBCF.norm_coe_le_norm y
    have hweightedBound : weightedGaussian y ≤ bound :=
      le_trans
        (le_of_eq hweightedNorm.symm)
        (le_trans hnormBound
          (le_add_of_nonneg_right zero_le_one))
    have hdivideBound :
        Real.exp (-a * (y - shift) ^ 2) ≤
          bound / height ^ degree :=
      (le_div_iff₀ hheightPowerPositive).mpr hweightedBound
    have hnegativePower :
        height ^ (-(degree : ℤ)) = (height ^ degree)⁻¹ :=
      Eq.trans
        (zpow_neg height (degree : ℤ))
        (congrArg Inv.inv
          (zpow_natCast height degree))
    have hdivideAsNegativePower :
        bound / height ^ degree =
          bound * height ^ (-(degree : ℤ)) :=
      Eq.trans
        (div_eq_mul_inv bound (height ^ degree))
        (congrArg (fun value : ℝ => bound * value)
          hnegativePower.symm)
    exact Eq.subst
      (motive := fun value : ℝ =>
        Real.exp (-a * (y - shift) ^ 2) ≤ value)
      hdivideAsNegativePower
      hdivideBound
  exact Exists.intro bound (And.intro hboundPositive hpointwise)

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Integral.Bochner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.FirstDerivative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Regularity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.ReciprocalDensity.Calculus.Prelude
/-!
# Reciprocal-density integral and calculus estimates

This file contains the main computational theorems for reciprocal-density integrals,
including integration bounds, by-parts identities, and calculus estimates.
-/

namespace Boundary
namespace LFunctions

open MeasureTheory
open scoped Topology

/-- Ordered lower endpoint extracted from an unordered real interval. -/
theorem real_left_le_of_mem_uIcc_of_le
    {a b x : ℝ}
    (hab : a ≤ b)
    (hx : x ∈ Set.uIcc a b) :
    a ≤ x := by
  have hset : Set.uIcc a b = Set.Icc a b :=
    Set.uIcc_of_le hab
  have hxIcc : x ∈ Set.Icc a b :=
    Eq.subst
      (motive := fun s : Set ℝ => x ∈ s)
      hset
      hx
  exact hxIcc.1

/-- Integral evaluation for the shifted-log square derivative density. -/
theorem real_intervalIntegral_log_sq_derivative_density_eq_sub
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 := by
  let F : ℝ → ℝ := fun x => (Real.log (2 + x)) ^ 2
  let G : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hderiv :
      ∀ x ∈ Set.uIcc a b, HasDerivAt F (G x) x := by
    intro x hx
    have hax : a ≤ x :=
      real_left_le_of_mem_uIcc_of_le hab hx
    have htwo_le_x : (2 : ℝ) ≤ x :=
      le_trans ha hax
    have hpos : (0 : ℝ) < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (show (0 : ℝ) ≤ 2 by exact le_of_lt zero_lt_two) htwo_le_x)
    exact real_hasDerivAt_log_two_add_sq hpos
  have hG_cont : ContinuousOn G (Set.uIcc a b) := by
    intro x hx
    have hax : a ≤ x :=
      real_left_le_of_mem_uIcc_of_le hab hx
    have htwo_le_x : (2 : ℝ) ≤ x :=
      le_trans ha hax
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) htwo_le_x)
      exact ne_of_gt harg_pos
    exact
      (scalarReciprocalDensity_logSqDerivativeDensity_continuousAt harg_ne).continuousWithinAt
  have hint : IntervalIntegrable G volume a b :=
    hG_cont.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) ≤
      (Real.log (2 + b)) ^ 2 := by
  have hset_interval :
      ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) =
        ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) :=
    (intervalIntegral.integral_of_le hab).symm
  have heval :
      ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
        (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 :=
    real_intervalIntegral_log_sq_derivative_density_eq_sub ha hab
  have hlower_nonneg : 0 ≤ (Real.log (2 + a)) ^ 2 :=
    sq_nonneg (Real.log (2 + a))
  have hsub :
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 ≤
        (Real.log (2 + b)) ^ 2 :=
    sub_le_self ((Real.log (2 + b)) ^ 2) hlower_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ (Real.log (2 + b)) ^ 2)
    hset_interval.symm
    (le_trans (le_of_eq heval) hsub)

/-- Fundamental-theorem comparison for the finite `log(2+x)/x` integral. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b)
    (hpointwise :
      ∀ x ∈ Set.Ioc a b,
        Real.log (2 + x) / x ≤
          2 * Real.log (2 + x) / (2 + x)) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hf_cont : ContinuousOn f (Set.Icc a b) := by
    intro x hx
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two (le_trans ha hx.1))
    have hlog_arg : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) (le_trans ha hx.1))
      exact ne_of_gt harg_pos
    exact
      (scalarReciprocalDensity_logTwoAdd_div_self_continuousAt
        hx_pos hlog_arg).continuousWithinAt
  have hg_cont : ContinuousOn g (Set.Icc a b) := by
    intro x hx
    have hlog_arg : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) (le_trans ha hx.1))
      exact ne_of_gt harg_pos
    exact
      (scalarReciprocalDensity_logSqDerivativeDensity_continuousAt
        hlog_arg).continuousWithinAt
  have hf : Integrable f (volume.restrict (Set.Ioc a b)) :=
    (ContinuousOn.integrableOn_Icc hf_cont).mono_set Set.Ioc_subset_Icc_self
  have hg : Integrable g (volume.restrict (Set.Ioc a b)) :=
    (ContinuousOn.integrableOn_Icc hg_cont).mono_set Set.Ioc_subset_Icc_self
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g :=
    (ae_restrict_mem measurableSet_Ioc).mono hpointwise
  have hmono :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
        ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) :=
    integral_mono_ae hf hg hle
  exact le_trans hmono
    (real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq ha hab)

/-- Canonical real-variable comparison for the finite `log(2+x)/x` integral.

On `2 ≤ a ≤ b`, the integrand is dominated by the derivative of
`(Real.log (2+x))^2`, since `1/x ≤ 2/(2+x)` and `Real.log (2+x) ≥ 0`.
This is the reusable scalar calculus theorem; the zeta cutoff theorem below is
only an endpoint instantiation. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
      ha hab
      (fun x hx =>
        real_log_two_add_div_self_le_log_sq_derivative_density
          (le_trans ha (le_of_lt hx.1)))

/-- Nonnegativity of the reciprocal-density scalar integrand after `2`. -/
theorem real_log_two_add_div_sq_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) / x ^ 2 := by
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    sq_nonneg x
  exact div_nonneg hlog_nonneg hx_sq_nonneg

/-- Concrete finite integration-by-parts identity for
`u(x)=log(2+x)` and `v(x)=-1/x` on `[2,b]`. -/
theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    let v' : ℝ → ℝ := fun x => 1 / x ^ 2
    ∫ x in (2 : ℝ)..b, u x * v' x =
      u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hu :
      ∀ x ∈ Set.uIcc (2 : ℝ) b, HasDerivAt u (u' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      real_left_le_of_mem_uIcc_of_le hb hx
    have htwo_add_pos : 0 < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (le_of_lt zero_lt_two) hleft)
    have hbase : HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
      (hasDerivAt_id x).const_add 2
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
      have hraw :
          HasDerivAt (fun y : ℝ => Real.log (2 + y)) (((2 + x)⁻¹) * 1) x :=
        (Real.hasDerivAt_log (ne_of_gt htwo_add_pos)).comp x hbase
      have hcoeff :
          ((2 + x)⁻¹) * (1 : ℝ) = (2 + x)⁻¹ :=
        mul_one ((2 + x)⁻¹)
      Eq.subst
        (motive := fun D : ℝ =>
          HasDerivAt (fun y : ℝ => Real.log (2 + y)) D x)
        hcoeff
        hraw
    have hnormal : (2 + x)⁻¹ = 1 / (2 + x) :=
      (one_div (2 + x)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt u D x)
      hnormal
      hlog
  have hv :
      ∀ x ∈ Set.uIcc (2 : ℝ) b, HasDerivAt v (v' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      real_left_le_of_mem_uIcc_of_le hb hx
    have hx_ne : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two hleft)
    have hinv :
        HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
      hasDerivAt_inv hx_ne
    have hneg :
        HasDerivAt (fun y : ℝ => -(y⁻¹)) (- (-(x ^ 2)⁻¹)) x :=
      hinv.neg
    have hlocal :
        v =ᶠ[𝓝 x] (fun y : ℝ => -(y⁻¹)) :=
      Filter.Eventually.of_forall
        (fun y : ℝ =>
          congrArg Neg.neg (one_div y))
    have hnormal : - (-(x ^ 2)⁻¹) = 1 / x ^ 2 := by
      calc
        - (-(x ^ 2)⁻¹) = (x ^ 2)⁻¹ := neg_neg ((x ^ 2)⁻¹)
        _ = 1 / x ^ 2 := (one_div (x ^ 2)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt v D x)
      hnormal
      (hneg.congr_of_eventuallyEq hlocal)
  have hu'_cont : ContinuousOn u' (Set.uIcc (2 : ℝ) b) := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      real_left_le_of_mem_uIcc_of_le hb hx
    have harg_ne : 2 + x ≠ 0 := by
      have harg_pos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) hleft)
      exact ne_of_gt harg_pos
    exact
      (continuousAt_const.div
        (continuousAt_const.add continuousAt_id)
        harg_ne).continuousWithinAt
  have hv'_cont : ContinuousOn v' (Set.uIcc (2 : ℝ) b) := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      real_left_le_of_mem_uIcc_of_le hb hx
    have hx_pos : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two hleft)
    exact
      (scalarReciprocalDensity_reciprocalSquare_continuousAt
        hx_pos).continuousWithinAt
  have hu_int : IntervalIntegrable u' volume (2 : ℝ) b :=
    hu'_cont.intervalIntegrable
  have hv_int : IntervalIntegrable v' volume (2 : ℝ) b :=
    hv'_cont.intervalIntegrable
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu_int hv_int

/-- Algebraic normalization of the finite by-parts RHS for
`u(x)=log(2+x)` and `v(x)=-1/x`. -/
theorem real_by_parts_log_two_add_endpoint_normalize
    {b : ℝ} :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    u b * v b - u 2 * v 2 =
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  have hvb : v b = -(1 / b) := rfl
  have hv2 : v 2 = -(1 / (2 : ℝ)) := rfl
  have hu2 : u 2 = Real.log 4 := by
    exact congrArg Real.log (show (2 : ℝ) + 2 = 4 by exact two_add_two_eq_four)
  have hleft :
      u b * v b = -Real.log (2 + b) / b := by
    calc
      u b * v b = Real.log (2 + b) * (-(1 / b)) := rfl
      _ = -(Real.log (2 + b) * (1 / b)) :=
        (mul_neg (Real.log (2 + b)) (1 / b))
      _ = -(Real.log (2 + b) / b) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log (2 + b)) b).symm
      _ = -Real.log (2 + b) / b :=
        neg_div' b (Real.log (2 + b))
  have hright :
      u 2 * v 2 = -Real.log 4 / 2 := by
    calc
      u 2 * v 2 = Real.log 4 * (-(1 / (2 : ℝ))) := by
        exact congrArg₂ (fun a c : ℝ => a * c) hu2 hv2
      _ = -(Real.log 4 * (1 / (2 : ℝ))) :=
        (mul_neg (Real.log 4) (1 / (2 : ℝ)))
      _ = -(Real.log 4 / 2) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log 4) (2 : ℝ)).symm
      _ = -Real.log 4 / 2 :=
        neg_div' (2 : ℝ) (Real.log 4)
  exact congrArg₂ (fun a c : ℝ => a - c) hleft hright

/-- Integral sign normalization for the finite by-parts remainder. -/
theorem real_intervalIntegral_log_two_add_by_parts_remainder_normalize
    {b : ℝ} :
    -(∫ x in (2 : ℝ)..b, ((1 : ℝ) / (2 + x)) * (-(1 / x))) =
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let r : ℝ → ℝ := fun x => (1 : ℝ) / (x * (2 + x))
  have hintegral :
      ∫ x in (2 : ℝ)..b, u' x * v x =
        ∫ x in (2 : ℝ)..b, -r x :=
    intervalIntegral.integral_congr
      (fun x _hx =>
        calc
          u' x * v x = (1 / (2 + x)) * (-(1 / x)) := rfl
          _ = -((1 / (2 + x)) * (1 / x)) :=
            mul_neg (1 / (2 + x)) (1 / x)
          _ = -((1 : ℝ) / (x * (2 + x))) := by
            exact congrArg Neg.neg
              (one_div_mul_one_div_rev (a := (2 + x)) (b := x))
          _ = -r x := rfl)
  calc
    -(∫ x in (2 : ℝ)..b, u' x * v x) =
        -(∫ x in (2 : ℝ)..b, -r x) := by
      exact congrArg Neg.neg hintegral
    _ = - (-(∫ x in (2 : ℝ)..b, r x)) := by
      exact congrArg Neg.neg
        (intervalIntegral.integral_neg (f := r) (a := (2 : ℝ)) (b := b))
    _ = ∫ x in (2 : ℝ)..b, r x :=
      neg_neg (∫ x in (2 : ℝ)..b, r x)

theorem real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize
    {b : ℝ}
    (_hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  have hendpoint :
      u b * v b - u 2 * v 2 =
        (-Real.log (2 + b) / b) - (-Real.log 4 / 2) :=
    real_by_parts_log_two_add_endpoint_normalize
  have hremainder :
      -(∫ x in (2 : ℝ)..b, u' x * v x) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_by_parts_remainder_normalize
  calc
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
        (u b * v b - u 2 * v 2) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact (sub_eq_add_neg
        (u b * v b - u 2 * v 2)
        (∫ x in (2 : ℝ)..b, u' x * v x))
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact congrArg
        (fun z : ℝ => z + -(∫ x in (2 : ℝ)..b, u' x * v x))
        hendpoint
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
      exact congrArg
        (fun z : ℝ => ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + z)
        hremainder

theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hparts :
      ∫ x in (2 : ℝ)..b, u x * v' x =
        u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core hb
  have hnormal :
      u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize hb
  exact Eq.trans hparts hnormal

/-- Algebraic normalization of the scalar reciprocal-density integrand. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) / x ^ 2 :=
    (intervalIntegral.integral_of_le hb).symm
  exact Eq.trans hset
    (intervalIntegral.integral_congr
      (fun x _hx =>
        div_eq_mul_one_div (Real.log (2 + x)) (x ^ 2)))

/-- Interval/set normalization for the by-parts remainder term. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_Ioc
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  exact intervalIntegral.integral_of_le hb

/-- Partial-fraction identity for the finite scalar reciprocal-density
integrand. -/
theorem real_one_div_mul_two_add_eq_half_sub
    {x : ℝ}
    (hx : x ≠ 0)
    (hx_two : 2 + x ≠ 0) :
    (1 : ℝ) / (x * (2 + x)) =
      (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
  let D : ℝ := x * (2 + x)
  have hdiff :
      (2 + x : ℝ) - x = 2 :=
    add_sub_cancel_right 2 x
  have hinv :
      (1 : ℝ) / x - (1 : ℝ) / (2 + x) =
        2 / (x * (2 + x)) := by
    calc
      (1 : ℝ) / x - (1 : ℝ) / (2 + x)
          = x⁻¹ - (2 + x)⁻¹ := by
              exact congrArg₂ Sub.sub (one_div x) (one_div (2 + x))
      _ = ((2 + x) - x) / (x * (2 + x)) :=
              inv_sub_inv hx hx_two
      _ = 2 / (x * (2 + x)) := by
          exact congrArg
            (fun y : ℝ => y / (x * (2 + x)))
            hdiff
  have hhalf : (1 / 2 : ℝ) * 2 = 1 := by
    have htwo_ne : (2 : ℝ) ≠ 0 :=
      two_ne_zero
    exact div_mul_cancel₀ (1 : ℝ) htwo_ne
  calc
    (1 : ℝ) / (x * (2 + x))
        = (1 : ℝ) * (1 / D) := by
            exact (one_mul ((1 : ℝ) / D)).symm
    _ = ((1 / 2 : ℝ) * 2) * (1 / D) := by
            exact congrArg (fun y : ℝ => y * (1 / D)) hhalf.symm
    _ = (1 / 2 : ℝ) * (2 * (1 / D)) := by
            exact mul_assoc (1 / 2 : ℝ) 2 (1 / D)
    _ = (1 / 2 : ℝ) * (2 / D) := by
            exact congrArg
              (fun y : ℝ => (1 / 2 : ℝ) * y)
              (div_eq_mul_one_div 2 D).symm
    _ = (1 / 2 : ℝ) * (2 / (x * (2 + x))) := by
            rfl
    _ = (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
            exact congrArg (fun y : ℝ => (1 / 2 : ℝ) * y) hinv.symm

/-- Interval integral of the first reciprocal term in the partial-fraction
expansion. -/
theorem real_intervalIntegral_one_div_eq_log_endpoint
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
      Real.log b - Real.log 2 := by
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hbase : 0 < (2 : ℝ) :=
    zero_lt_two
  have hintegral :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
        Real.log (b / 2) :=
    integral_one_div_of_pos hbase hb_pos
  have hlog :
      Real.log (b / 2) = Real.log b - Real.log 2 :=
    Real.log_div (ne_of_gt hb_pos) (ne_of_gt hbase)
  exact Eq.trans hintegral hlog

/-- Interval integral of the translated reciprocal term in the partial-fraction
expansion. -/
theorem real_intervalIntegral_one_div_two_add_eq_log_endpoint
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
      Real.log (2 + b) - Real.log 4 := by
  have hb_shift_pos : 0 < b + 2 :=
    add_pos_of_nonneg_of_pos (le_trans (le_of_lt zero_lt_two) hb) zero_lt_two
  have hfour : ((2 : ℝ) + 2) = 4 :=
    two_add_two_eq_four
  have hfour_pos : 0 < ((2 : ℝ) + 2) := by
    exact Eq.subst (motive := fun y : ℝ => 0 < y) hfour.symm zero_lt_four
  have htranslated :
      ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) =
        ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x :=
    intervalIntegral.integral_comp_add_right
      (fun y : ℝ => (1 : ℝ) / y) 2
  have hleft :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
        ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) := by
    exact intervalIntegral.integral_congr
      (fun x _hx =>
        congrArg (fun y : ℝ => (1 : ℝ) / y) (add_comm 2 x))
  have heval :
      ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x =
        Real.log (b + 2) - Real.log ((2 : ℝ) + 2) := by
    have hintegral :
        ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x =
          Real.log ((b + 2) / ((2 : ℝ) + 2)) :=
      integral_one_div_of_pos hfour_pos hb_shift_pos
    have hlog :
        Real.log ((b + 2) / ((2 : ℝ) + 2)) =
          Real.log (b + 2) - Real.log ((2 : ℝ) + 2) :=
      Real.log_div (ne_of_gt hb_shift_pos) (ne_of_gt hfour_pos)
    exact Eq.trans hintegral hlog
  have hnormalize :
      Real.log (b + 2) - Real.log ((2 : ℝ) + 2) =
        Real.log (2 + b) - Real.log 4 := by
    have hb_comm : b + 2 = 2 + b :=
      add_comm b 2
    exact Eq.trans
      (congrArg
        (fun y : ℝ => Real.log y - Real.log ((2 : ℝ) + 2))
        hb_comm)
      (congrArg
        (fun y : ℝ => Real.log (2 + b) - Real.log y)
        hfour)
  calc
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x)
        = ∫ x in (2 : ℝ)..b, (fun y : ℝ => (1 : ℝ) / y) (x + 2) :=
            hleft
    _ = ∫ x in ((2 : ℝ) + 2)..(b + 2), (1 : ℝ) / x :=
            htranslated
    _ = Real.log (b + 2) - Real.log ((2 : ℝ) + 2) :=
            heval
    _ = Real.log (2 + b) - Real.log 4 :=
            hnormalize

/-- The reciprocal function is interval-integrable on `[2,b]`. -/
theorem real_intervalIntegrable_one_div_two_to
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x) volume (2 : ℝ) b := by
  exact intervalIntegral.intervalIntegrable_one_div
    (fun x hx => by
      have hx_pos : 0 < x := by
        exact lt_of_lt_of_le zero_lt_two
          (real_left_le_of_mem_uIcc_of_le hb hx)
      exact ne_of_gt hx_pos)
    continuousOn_id

/-- The translated reciprocal function is interval-integrable on `[2,b]`. -/
theorem real_intervalIntegrable_one_div_two_add_two_to
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    IntervalIntegrable (fun x : ℝ => (1 : ℝ) / (2 + x)) volume (2 : ℝ) b := by
  exact intervalIntegral.intervalIntegrable_one_div
    (fun x hx => by
      have hx_lower : (2 : ℝ) ≤ x :=
        real_left_le_of_mem_uIcc_of_le hb hx
      have hpos : 0 < 2 + x :=
        add_pos_of_pos_of_nonneg zero_lt_two
          (le_trans (le_of_lt zero_lt_two) hx_lower)
      exact ne_of_gt hpos)
    (continuousOn_const.add continuousOn_id)

/-- Partial-fraction normalization under the interval integral. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_half_sub_integral
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      (1 / 2 : ℝ) *
        ((∫ x in (2 : ℝ)..b, (1 : ℝ) / x) -
          (∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))) := by
  have hpoint :
      Set.EqOn
        (fun x : ℝ => (1 : ℝ) / (x * (2 + x)))
        (fun x : ℝ =>
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)))
        (Set.uIcc (2 : ℝ) b) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le zero_lt_two
        (real_left_le_of_mem_uIcc_of_le hb hx)
    have hx_two_pos : 0 < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two (le_of_lt hx_pos)
    exact real_one_div_mul_two_add_eq_half_sub
      (ne_of_gt hx_pos)
      (ne_of_gt hx_two_pos)
  have hcongr :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) :=
    intervalIntegral.integral_congr hpoint
  have hone : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x) volume (2 : ℝ) b :=
    real_intervalIntegrable_one_div_two_to hb
  have htwo :
      IntervalIntegrable (fun x : ℝ => (1 : ℝ) / (2 + x)) volume (2 : ℝ) b :=
    real_intervalIntegrable_one_div_two_add_two_to hb
  have hlinear :
      ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) =
        (1 / 2 : ℝ) *
          ((∫ x in (2 : ℝ)..b, (1 : ℝ) / x) -
            (∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))) := by
    calc
      ∫ x in (2 : ℝ)..b,
          (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x))
          =
        (1 / 2 : ℝ) *
          ∫ x in (2 : ℝ)..b, ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
            exact intervalIntegral.integral_const_mul (1 / 2 : ℝ)
              (fun x : ℝ => (1 : ℝ) / x - (1 : ℝ) / (2 + x))
      _ = (1 / 2 : ℝ) *
          ((∫ x in (2 : ℝ)..b, (1 : ℝ) / x) -
            (∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))) := by
            exact congrArg
              (fun y : ℝ => (1 / 2 : ℝ) * y)
              (intervalIntegral.integral_sub hone htwo)
  exact Eq.trans hcongr hlinear

/-- Antiderivative evaluation for the reciprocal-density scalar integrand.

The antiderivative is `(log x - log (2 + x)) / 2`; the lower endpoint is
`2`, where the value is `(log 2 - log 4) / 2`. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  have hpartial :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        (1 / 2 : ℝ) *
          ((∫ x in (2 : ℝ)..b, (1 : ℝ) / x) -
            (∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))) :=
    real_intervalIntegral_one_div_mul_two_add_eq_half_sub_integral hb
  have hone :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / x =
        Real.log b - Real.log 2 :=
    real_intervalIntegral_one_div_eq_log_endpoint hb
  have htwo :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x) =
        Real.log (2 + b) - Real.log 4 :=
    real_intervalIntegral_one_div_two_add_eq_log_endpoint hb
  have hlogs :
      (1 / 2 : ℝ) *
          ((Real.log b - Real.log 2) -
            (Real.log (2 + b) - Real.log 4)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 := by
    calc
      (1 / 2 : ℝ) *
          ((Real.log b - Real.log 2) -
            (Real.log (2 + b) - Real.log 4))
          =
        ((Real.log b - Real.log 2) -
          (Real.log (2 + b) - Real.log 4)) / 2 := by
            exact
              one_div_mul_eq_div
                (2 : ℝ)
                ((Real.log b - Real.log 2) -
                  (Real.log (2 + b) - Real.log 4))
      _ = ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 := by
            have halg :
                (Real.log b - Real.log 2) -
                  (Real.log (2 + b) - Real.log 4) =
                (Real.log b - Real.log (2 + b)) -
                  (Real.log 2 - Real.log 4) := by
              exact sub_sub_sub_comm
                (Real.log b) (Real.log 2) (Real.log (2 + b)) (Real.log 4)
            exact congrArg (fun y : ℝ => y / 2) halg
  exact Eq.trans hpartial
    (Eq.trans
      (congrArg
        (fun y : ℝ => (1 / 2 : ℝ) * y)
        (Eq.trans
          (congrArg
            (fun y : ℝ =>
              y - ∫ x in (2 : ℝ)..b, (1 : ℝ) / (2 + x))
            hone)
          (congrArg
            (fun y : ℝ => (Real.log b - Real.log 2) - y)
            htwo)))
      hlogs)

/-- Endpoint evaluation of the interval integral of the scalar reciprocal
density in interval-integral notation. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  exact real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core hb

/-- Integration-by-parts identity for the finite scalar tail
`∫ log(2+x)/x²`.

This is the exact finite identity behind the tail bound:
the antiderivative of the main part is `-log(2+x)/x`, and the remaining
positive term is `1/(x*(2+x))`. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  have hmain :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) :=
    real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq hb
  have hparts :
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts hb
  have hremainder :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_one_div_mul_two_add_eq_Ioc hb
  exact Eq.trans hmain
    (Eq.trans hparts
      (congrArg
        (fun R : ℝ =>
          ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + R)
        hremainder))

/-- Elementary endpoint bound for the finite scalar tail after the
integration-by-parts identity. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    (intervalIntegral.integral_of_le hb).symm
  have heval :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs_interval hb
  exact Eq.trans hset heval

theorem real_intervalIntegral_one_div_mul_two_add_le_half_log_two
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 2 / 2 := by
  have heval :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs hb
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hb_le_two_add : b ≤ 2 + b :=
    le_add_of_nonneg_left (le_of_lt zero_lt_two)
  have hlog_le : Real.log b ≤ Real.log (2 + b) :=
    Real.log_le_log hb_pos hb_le_two_add
  have hdiff_nonpos : Real.log b - Real.log (2 + b) ≤ 0 :=
    sub_nonpos.mpr hlog_le
  have hlog_two_four :
      Real.log 2 - Real.log 4 = -(Real.log 2) := by
    have hfour : (4 : ℝ) = 2 * 2 := by
      exact
        (Eq.trans (two_mul (2 : ℝ)) two_add_two_eq_four).symm
    have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 * 2) := congrArg Real.log hfour
        _ = Real.log 2 + Real.log 2 :=
          Real.log_mul (ne_of_gt zero_lt_two) (ne_of_gt zero_lt_two)
    calc
      Real.log 2 - Real.log 4 =
          Real.log 2 - (Real.log 2 + Real.log 2) := by
        exact congrArg (fun y : ℝ => Real.log 2 - y) hlog4
      _ = -(Real.log 2) := by
        calc
          Real.log 2 - (Real.log 2 + Real.log 2) =
              (Real.log 2 - Real.log 2) - Real.log 2 := by
            exact sub_add_eq_sub_sub (Real.log 2) (Real.log 2) (Real.log 2)
          _ = 0 - Real.log 2 := by
            exact congrArg (fun y : ℝ => y - Real.log 2) (sub_self (Real.log 2))
          _ = -(Real.log 2) :=
            zero_sub (Real.log 2)
  have hnum_le :
      (Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4) ≤ Real.log 2 := by
    have hrewrite :
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) + Real.log 2 := by
      calc
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) - (-(Real.log 2)) := by
          exact congrArg
            (fun y : ℝ => (Real.log b - Real.log (2 + b)) - y)
            hlog_two_four
        _ = (Real.log b - Real.log (2 + b)) + Real.log 2 :=
          sub_neg_eq_add (Real.log b - Real.log (2 + b)) (Real.log 2)
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ Real.log 2)
      hrewrite.symm
      (calc
        (Real.log b - Real.log (2 + b)) + Real.log 2 ≤
            0 + Real.log 2 :=
          add_le_add_right hdiff_nonpos (Real.log 2)
        _ = Real.log 2 :=
          zero_add (Real.log 2))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hbound :
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 ≤ Real.log 2 / 2 :=
    div_le_div_of_nonneg_right hnum_le hhalf_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 2 / 2)
    heval.symm
    hbound

/-- Endpoint contribution after integration by parts is bounded by `log 4 / 2`. -/
theorem real_log_two_add_by_parts_endpoint_le_log_four_half
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
      Real.log 4 / 2 := by
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hlog_nonneg : 0 ≤ Real.log (2 + b) :=
    real_log_two_add_nonneg_of_two_le hb
  have hdiv_nonneg : 0 ≤ Real.log (2 + b) / b :=
    div_nonneg hlog_nonneg (le_of_lt hb_pos)
  have hneg_nonpos : -Real.log (2 + b) / b ≤ 0 := by
    have hneg : -(Real.log (2 + b) / b) ≤ 0 :=
      neg_nonpos.mpr hdiv_nonneg
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 0)
      (neg_div' b (Real.log (2 + b)))
      hneg
  calc
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) =
        (-Real.log (2 + b) / b) + Real.log 4 / 2 := by
      have hden :
          -Real.log 4 / (2 : ℝ) = -(Real.log 4 / 2) :=
        neg_div (2 : ℝ) (Real.log 4)
      calc
        (-Real.log (2 + b) / b) - (-Real.log 4 / 2) =
            (-Real.log (2 + b) / b) - (-(Real.log 4 / 2)) := by
          exact congrArg
            (fun y : ℝ => (-Real.log (2 + b) / b) - y)
            hden
        _ = (-Real.log (2 + b) / b) + Real.log 4 / 2 :=
          sub_neg_eq_add (-Real.log (2 + b) / b) (Real.log 4 / 2)
    _ ≤ 0 + Real.log 4 / 2 :=
      add_le_add_right hneg_nonpos (Real.log 4 / 2)
    _ = Real.log 4 / 2 :=
      zero_add (Real.log 4 / 2)

/-- The sharp partial-fractions remainder and endpoint estimates fit under
the available `log 4` budget. -/
theorem real_log_four_half_add_log_two_half_le_log_four :
    Real.log 4 / 2 + Real.log 2 / 2 ≤ Real.log 4 := by
  have hlog_two_le_log_four : Real.log 2 ≤ Real.log 4 :=
    Real.log_le_log zero_lt_two
      (Eq.subst
        (motive := fun y : ℝ => (2 : ℝ) ≤ y)
        (show (2 : ℝ) + 2 = 4 by exact two_add_two_eq_four)
        (le_add_of_nonneg_right (le_of_lt zero_lt_two)))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hhalf :
      Real.log 2 / 2 ≤ Real.log 4 / 2 :=
    div_le_div_of_nonneg_right hlog_two_le_log_four hhalf_nonneg
  have hsum :
      Real.log 4 / 2 + Real.log 2 / 2 ≤
        Real.log 4 / 2 + Real.log 4 / 2 :=
    add_le_add_left hhalf (Real.log 4 / 2)
  exact le_trans hsum (le_of_eq (add_halves (Real.log 4)))

theorem real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 4 := by
  have hendpoint :
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
        Real.log 4 / 2 :=
    real_log_two_add_by_parts_endpoint_le_log_four_half hb
  have hremainder :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 2 / 2 :=
    real_intervalIntegral_one_div_mul_two_add_le_half_log_two hb
  have hsum :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 / 2 + Real.log 2 / 2 :=
    add_le_add hendpoint hremainder
  exact le_trans hsum real_log_four_half_add_log_two_half_le_log_four

/-- Standard finite integration-by-parts tail estimate for
`log(2+x)/x²` from the canonical cutoff `2`.

The proof is the real-variable identity
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by the elementary
endpoint estimate
`log 4 / 2 + ∫₂^∞ 1/(x(2+x)) ≤ log 4`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have hparts :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_integral_Ioc_log_two_add_div_sq_eq_by_parts hb
  have hbound :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four hb
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 4)
    hparts.symm
    hbound

/-- Fixed improper-tail bound from the canonical cutoff `2`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts hb


end LFunctions
end Boundary

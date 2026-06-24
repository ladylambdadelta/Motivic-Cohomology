import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Order.Interval.Set.UnorderedInterval
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.HalfPlaneTail

/-!
# One-interval Bernoulli integration by parts

This file owns the local one-interval first-periodic Bernoulli calculations used
by the finite-interval Euler-Maclaurin assembly layer.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory Filter
local notation "π" => Real.pi

/-- Subtracting a real number from itself and then subtracting one half gives
negative one half. -/
theorem real_sub_self_sub_half_eq_neg_half
    (a : ℝ) :
    a - a - 1 / 2 = (-(1 / 2) : ℝ) := by
  calc
    a - a - 1 / 2 = 0 - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) (sub_self a)
    _ = (-(1 / 2) : ℝ) := by
      exact zero_sub (1 / 2)

/-- Moving one unit from `a` to `a + 1` leaves one half after subtracting
one half. -/
theorem real_add_one_sub_self_sub_half_eq_half
    (a : ℝ) :
    (a + 1) - a - 1 / 2 = (1 / 2 : ℝ) := by
  have hstep : (a + 1) - a = (1 : ℝ) := by
    calc
      (a + 1) - a = (a + 1) + -a := by
        exact sub_eq_add_neg (a + 1) a
      _ = a + (1 + -a) := by
        exact add_assoc a 1 (-a)
      _ = a + (-a + 1) := by
        exact congrArg (fun t : ℝ => a + t) (add_comm 1 (-a))
      _ = (a + -a) + 1 := by
        exact (add_assoc a (-a) 1).symm
      _ = 0 + 1 := by
        exact congrArg (fun t : ℝ => t + 1) (add_neg_cancel a)
      _ = 1 := by
        exact zero_add 1
  calc
    (a + 1) - a - 1 / 2 = 1 - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) hstep
    _ = (1 / 2 : ℝ) := by
      exact sub_half (1 : ℝ)

/-- The complex cast of one half is one half. -/
theorem complex_ofReal_half_eq_half :
    (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by
  exact Complex.ofReal_div 1 2

/-- The complex cast of negative one half is negative one half. -/
theorem complex_ofReal_neg_half_eq_neg_half :
    ((-(1 / 2) : ℝ) : ℂ) = (-(1 / 2) : ℂ) := by
  calc
    ((-(1 / 2) : ℝ) : ℂ) = -(((1 / 2 : ℝ) : ℂ)) := by
      exact Complex.ofReal_neg (1 / 2 : ℝ)
    _ = (-(1 / 2 : ℂ)) := by
      exact congrArg Neg.neg complex_ofReal_half_eq_half

/-- The endpoint algebra in one-interval integration by parts. -/
theorem complex_oneInterval_endpoint_algebra
    (I A F : ℂ) :
    F = I + A + (1 / 2 : ℂ) * F + ((1 / 2 : ℂ) * F - A - I) := by
  have htwo : (1 / 2 : ℂ) * F + (1 / 2 : ℂ) * F = F := by
    calc
      (1 / 2 : ℂ) * F + (1 / 2 : ℂ) * F
          = (((1 / 2 : ℂ) + 1 / 2) * F) := by
              exact (add_mul (1 / 2 : ℂ) (1 / 2 : ℂ) F).symm
      _ = (1 : ℂ) * F := by
              exact congrArg (fun t : ℂ => t * F) (add_halves (1 : ℂ))
      _ = F := by
              exact one_mul F
  have hcancel :
      I + A + (1 / 2 : ℂ) * F + ((1 / 2 : ℂ) * F - A - I) =
      (1 / 2 : ℂ) * F + (1 / 2 : ℂ) * F := by
    let H : ℂ := (1 / 2 : ℂ) * F
    have hsub :
        H - A - I = H - (A + I) :=
      sub_sub H A I
    have hfront :
        I + A + H + (H - (A + I)) =
          (I + A + H + H) - (A + I) := by
      exact (add_sub_assoc (I + A + H) H (A + I)).symm
    have hregroup :
        I + A + H + H = H + H + (A + I) := by
      calc
        I + A + H + H = (I + A) + H + H := by
          exact rfl
        _ = (I + A) + (H + H) := by
          exact add_assoc (I + A) H H
        _ = (H + H) + (I + A) := by
          exact add_comm (I + A) (H + H)
        _ = (H + H) + (A + I) := by
          exact congrArg (fun z : ℂ => (H + H) + z) (add_comm I A)
    calc
      I + A + (1 / 2 : ℂ) * F + ((1 / 2 : ℂ) * F - A - I) =
          I + A + H + (H - A - I) := by
        exact rfl
      _ = I + A + H + (H - (A + I)) := by
        exact congrArg (fun z : ℂ => I + A + H + z) hsub
      _ = (I + A + H + H) - (A + I) := by
        exact hfront
      _ = (H + H + (A + I)) - (A + I) := by
        exact congrArg (fun z : ℂ => z - (A + I)) hregroup
      _ = H + H := by
        exact add_sub_cancel_right (H + H) (A + I)
      _ = (1 / 2 : ℂ) * F + (1 / 2 : ℂ) * F := by
        exact rfl
  exact (hcancel.trans htwo).symm

/-- The quadratic primitive of the centered affine sawtooth has equal values
at the endpoints of a unit interval. -/
theorem real_oneInterval_centeredSawtooth_primitive_endpoint_eq
    (a : ℝ) :
    (((a + 1 - a) ^ 2) / 2 - (a + 1 - a) / 2 : ℝ) =
      (((a - a) ^ 2) / 2 - (a - a) / 2 : ℝ) := by
  have hstep : a + 1 - a = (1 : ℝ) := by
    exact add_sub_cancel_left a 1
  have hbase : a - a = (0 : ℝ) := by
    exact sub_self a
  have hone_square : ((1 : ℝ) ^ 2) = (1 : ℝ) := by
    exact one_pow 2
  have hzero_square : ((0 : ℝ) ^ 2) = (0 : ℝ) := by
    exact zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1)
  have hleft :
      (((a + 1 - a) ^ 2) / 2 - (a + 1 - a) / 2 : ℝ) =
        ((1 : ℝ) ^ 2) / 2 - (1 : ℝ) / 2 := by
    exact congrArg (fun y : ℝ => y ^ 2 / 2 - y / 2) hstep
  have hleft_zero :
      ((1 : ℝ) ^ 2) / 2 - (1 : ℝ) / 2 = (0 : ℝ) := by
    calc
      ((1 : ℝ) ^ 2) / 2 - (1 : ℝ) / 2 =
          (1 : ℝ) / 2 - (1 : ℝ) / 2 := by
        exact congrArg (fun y : ℝ => y / 2 - (1 : ℝ) / 2) hone_square
      _ = (0 : ℝ) := by
        exact sub_self ((1 : ℝ) / 2)
  have hright :
      (((a - a) ^ 2) / 2 - (a - a) / 2 : ℝ) =
        ((0 : ℝ) ^ 2) / 2 - (0 : ℝ) / 2 := by
    exact congrArg (fun y : ℝ => y ^ 2 / 2 - y / 2) hbase
  have hright_zero :
      ((0 : ℝ) ^ 2) / 2 - (0 : ℝ) / 2 = (0 : ℝ) := by
    calc
      ((0 : ℝ) ^ 2) / 2 - (0 : ℝ) / 2 =
          (0 : ℝ) / 2 - (0 : ℝ) / 2 := by
        exact congrArg (fun y : ℝ => y / 2 - (0 : ℝ) / 2) hzero_square
      _ = (0 : ℝ) := by
        exact sub_self ((0 : ℝ) / 2)
  exact Eq.trans (Eq.trans hleft hleft_zero) (Eq.trans hright hright_zero).symm

theorem eulerMaclaurinFirstPeriodicBernoulli_eq_sub_nat_sub_half_on_Ioo
    (n : ℕ)
    {x : ℝ}
    (hx : x ∈ Set.Ioo (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    eulerMaclaurinFirstPeriodicBernoulli x =
      x - ((n : ℕ) : ℝ) - 1 / 2 := by
  have hfract_shift :
      Int.fract (x - ((n : ℕ) : ℝ)) = Int.fract x :=
    Int.fract_sub_nat x n
  have hshift_nonneg : 0 ≤ x - ((n : ℕ) : ℝ) :=
    le_of_lt (sub_pos.mpr hx.1)
  have hshift_lt_one : x - ((n : ℕ) : ℝ) < 1 := by
    have hsucc :
        (((n + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + 1 := by
      exact Nat.cast_add_one n
    calc
      x - ((n : ℕ) : ℝ) <
          (((n + 1 : ℕ) : ℝ)) - ((n : ℕ) : ℝ) := by
        exact sub_lt_sub_right hx.2 (((n : ℕ) : ℝ))
      _ = (((n : ℕ) : ℝ) + 1) - ((n : ℕ) : ℝ) := by
        exact congrArg (fun t : ℝ => t - ((n : ℕ) : ℝ)) hsucc
      _ = 1 := by
        exact add_sub_cancel_left ((n : ℕ) : ℝ) 1
  have hfract_self :
      Int.fract (x - ((n : ℕ) : ℝ)) =
        x - ((n : ℕ) : ℝ) :=
    (Int.fract_eq_self).mpr ⟨hshift_nonneg, hshift_lt_one⟩
  calc
    eulerMaclaurinFirstPeriodicBernoulli x = Int.fract x - 1 / 2 := rfl
    _ =
        Int.fract (x - ((n : ℕ) : ℝ)) - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) hfract_shift.symm
    _ = x - ((n : ℕ) : ℝ) - 1 / 2 := by
      exact congrArg (fun t : ℝ => t - 1 / 2) hfract_self

/-- Affine one-unit-interval integration by parts in set-integral form.

This is the direct interval-calculus input for the first-order finite
Euler-Maclaurin formula.  It is the specialization of mathlib's interval
integration-by-parts theorem to `u(x)=x-n-1/2`, where `u'=1`,
`u(n)=-1/2`, and `u(n+1)=1/2`. -/
theorem eulerMaclaurin_affineSawtooth_oneInterval_integrationByParts
    (f f' : ℝ → ℂ)
    (n : ℕ)
    (hf_cont : ContinuousOn f
      (Set.Icc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))) :
    f (((n + 1 : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((n : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((n + 1 : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) := by
  let a : ℝ := ((n : ℕ) : ℝ)
  let b : ℝ := (((n + 1 : ℕ) : ℝ))
  let u : ℝ → ℂ := fun x : ℝ => ((x - a - 1 / 2 : ℝ) : ℂ)
  let u' : ℝ → ℂ := fun _ : ℝ => (1 : ℂ)
  have hab : a ≤ b := by
    exact Nat.cast_le.mpr (Nat.le_succ n)
  have hb_eq : b = a + 1 := by
    exact Nat.cast_add_one n
  have hu_cont : ContinuousOn u (Set.uIcc a b) := by
    exact
      (Complex.continuous_ofReal.comp
        ((continuous_id.sub continuous_const).sub continuous_const)).continuousOn
  have hf_cont_uIcc : ContinuousOn f (Set.uIcc a b) := by
    have huIcc_eq : Set.uIcc a b = Set.Icc a b := by
      exact Set.uIcc_of_le hab
    exact Eq.subst
      (motive := fun s : Set ℝ => ContinuousOn f s)
      huIcc_eq.symm
      hf_cont
  have hu_deriv : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt u (u' x) x := by
    intro x hx
    have hbase : HasDerivAt (fun y : ℝ => y - a - 1 / 2) (1 : ℝ) x := by
      exact ((hasDerivAt_id x).sub_const a).sub_const (1 / 2)
    exact hbase.ofReal_comp
  have hf_deriv_ab : ∀ x ∈ Set.Ioo (min a b) (max a b),
      HasDerivAt f (f' x) x := by
    intro x hx
    have hmin : min a b = a := min_eq_left hab
    have hmax : max a b = b := max_eq_right hab
    have hx_left : a < x :=
      Eq.subst (motive := fun t : ℝ => t < x) hmin hx.1
    have hx_right : x < b :=
      Eq.subst (motive := fun t : ℝ => x < t) hmax hx.2
    have hx_ab : x ∈ Set.Ioo a b := ⟨hx_left, hx_right⟩
    exact hf_deriv x hx_ab
  have hu'_int : IntervalIntegrable u' volume a b := by
    have hcont : ContinuousOn u' (Set.uIcc a b) := by
      exact continuous_const.continuousOn
    exact hcont.intervalIntegrable
  have hf'_intervalInt : IntervalIntegrable f' volume a b := by
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        hf'_int
  have hparts :
      (∫ x in a..b, u x * f' x) =
        u b * f b - u a * f a - ∫ x in a..b, u' x * f x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hu_cont hf_cont_uIcc hu_deriv hf_deriv_ab hu'_int hf'_intervalInt
  have hu_a : u a = (-(1 / 2 : ℂ)) := by
    calc
      u a = ((a - a - 1 / 2 : ℝ) : ℂ) := rfl
      _ = ((-(1 / 2) : ℝ) : ℂ) := by
        exact congrArg Complex.ofReal (real_sub_self_sub_half_eq_neg_half a)
      _ = (-(1 / 2 : ℂ)) := complex_ofReal_neg_half_eq_neg_half
  have hu_b : u b = (1 / 2 : ℂ) := by
    calc
      u b = ((b - a - 1 / 2 : ℝ) : ℂ) := rfl
      _ = (((a + 1) - a - 1 / 2 : ℝ) : ℂ) := by
        exact congrArg (fun t : ℝ => ((t - a - 1 / 2 : ℝ) : ℂ)) hb_eq
      _ = ((1 / 2 : ℝ) : ℂ) := by
        exact congrArg Complex.ofReal (real_add_one_sub_self_sub_half_eq_half a)
      _ = (1 / 2 : ℂ) := complex_ofReal_half_eq_half
  have hu'_pointwise_mul :
      ∀ x : ℝ, u' x * f x = f x := by
    intro x
    exact one_mul (f x)
  have hu'_mul_integral :
      (∫ x in a..b, u' x * f x) =
        ∫ x in Set.Ioc a b, f x := by
    have hinterval :
        (∫ x in a..b, u' x * f x) =
          ∫ x in Set.Ioc a b, u' x * f x :=
      intervalIntegral.integral_of_le hab
    exact Eq.trans hinterval
      (setIntegral_congr_fun measurableSet_Ioc
        (fun x _hx => hu'_pointwise_mul x))
  have hu_mul_integral :
      (∫ x in a..b, u x * f' x) =
        ∫ x in Set.Ioc a b,
          (((x - a - 1 / 2 : ℝ) : ℂ) * f' x) :=
    intervalIntegral.integral_of_le hab
  have hsolved :
      f b =
        (∫ x in Set.Ioc a b, f x) +
          (-(1 / 2 : ℂ) * f a) +
          ((1 / 2 : ℂ) * f b) +
          (∫ x in Set.Ioc a b,
            (((x - a - 1 / 2 : ℝ) : ℂ) * f' x)) := by
    have hparts_set :
        (∫ x in Set.Ioc a b,
          (((x - a - 1 / 2 : ℝ) : ℂ) * f' x)) =
          (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a -
            ∫ x in Set.Ioc a b, f x := by
      have hboundary :
          u b * f b - u a * f a =
            (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a := by
        calc
          u b * f b - u a * f a =
              (1 / 2 : ℂ) * f b - u a * f a := by
            exact congrArg (fun t : ℂ => t * f b - u a * f a) hu_b
          _ = (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a := by
            exact congrArg (fun t : ℂ => (1 / 2 : ℂ) * f b - t * f a) hu_a
      have hparts_boundary :
          (∫ x in a..b, u x * f' x) =
            (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a -
              ∫ x in a..b, u' x * f x := by
        exact Eq.trans hparts
          (congrArg
            (fun q : ℂ => q - ∫ x in a..b, u' x * f x)
            hboundary)
      have hparts_integral :
          (∫ x in a..b, u x * f' x) =
            (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a -
              ∫ x in Set.Ioc a b, f x := by
        exact Eq.trans hparts_boundary
          (congrArg
            (fun q : ℂ =>
              (1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a - q)
            hu'_mul_integral)
      exact Eq.trans hu_mul_integral.symm hparts_integral
    calc
      f b =
          (∫ x in Set.Ioc a b, f x) +
            (-(1 / 2 : ℂ) * f a) +
            ((1 / 2 : ℂ) * f b) +
            ((1 / 2 : ℂ) * f b - (-(1 / 2 : ℂ)) * f a -
              ∫ x in Set.Ioc a b, f x) := by
        exact complex_oneInterval_endpoint_algebra
          (∫ x in Set.Ioc a b, f x)
          (-(1 / 2 : ℂ) * f a)
          (f b)
      _ =
          (∫ x in Set.Ioc a b, f x) +
            (-(1 / 2 : ℂ) * f a) +
            ((1 / 2 : ℂ) * f b) +
            (∫ x in Set.Ioc a b,
              (((x - a - 1 / 2 : ℝ) : ℂ) * f' x)) := by
        exact congrArg
          (fun r : ℂ =>
            (∫ x in Set.Ioc a b, f x) +
              (-(1 / 2 : ℂ) * f a) +
              ((1 / 2 : ℂ) * f b) + r)
          hparts_set.symm
  exact hsolved

/-- On a unit interval, replacing the affine sawtooth by the first periodic
Bernoulli sawtooth preserves the derivative-remainder integral.  The
two factors agree on the open interval; the endpoint discrepancy is a null
set for the `Ioc` integral. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_oneInterval_remainder_integral_eq_affine
    (f' : ℝ → ℂ)
    (n : ℕ)
    (_hf'_int : IntegrableOn f'
      (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) := by
  let a : ℝ := ((n : ℕ) : ℝ)
  let b : ℝ := (((n + 1 : ℕ) : ℝ))
  have h_ae :
      ∀ᵐ x : ℝ, x ∈ Set.Ioc a b →
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x =
          (((x - a - 1 / 2 : ℝ) : ℂ) * f' x) := by
    have hs_singleton : ({b} : Set ℝ).Subsingleton := by
      intro x hx y hy
      have hx' : x = b :=
        Set.mem_singleton_iff.mp hx
      have hy' : y = b :=
        Set.mem_singleton_iff.mp hy
      exact Eq.trans hx' hy'.symm
    have hnot_endpoint_eventually :
        ∀ᵐ x : ℝ, x ∈ ({b} : Set ℝ)ᶜ :=
      compl_mem_ae_iff.mpr
        (Set.Subsingleton.measure_zero hs_singleton (μ := volume))
    exact hnot_endpoint_eventually.mono
      (fun x hx_not_endpoint hx_interval =>
        have hx_not_eq_endpoint : x ≠ b := by
          intro hxb
          exact hx_not_endpoint (hxb ▸ Set.mem_singleton b)
        have hx_open : x ∈ Set.Ioo a b := by
          exact ⟨hx_interval.1, lt_of_le_of_ne hx_interval.2
            hx_not_eq_endpoint⟩
        have hsaw :
            eulerMaclaurinFirstPeriodicBernoulli x =
              x - ((n : ℕ) : ℝ) - 1 / 2 := by
          exact
            eulerMaclaurinFirstPeriodicBernoulli_eq_sub_nat_sub_half_on_Ioo
              n
              hx_open
        congrArg (fun c : ℂ => c * f' x) (congrArg Complex.ofReal hsaw))
  exact
    setIntegral_congr_ae measurableSet_Ioc h_ae

/-- The centered affine sawtooth has zero integral on each unit interval. -/
theorem eulerMaclaurin_affineSawtooth_oneInterval_integral_eq_zero
    (n : ℕ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ))) = 0 := by
  let a : ℝ := ((n : ℕ) : ℝ)
  let b : ℝ := (((n + 1 : ℕ) : ℝ))
  let F : ℝ → ℂ := fun x =>
    (((x - a) ^ 2 / 2 - (x - a) / 2 : ℝ) : ℂ)
  let f : ℝ → ℂ := fun x =>
    (((x - a - 1 / 2 : ℝ) : ℂ))
  have hab : a ≤ b := by
    exact Nat.cast_le.mpr (Nat.le_succ n)
  have hb_eq : b = a + 1 := by
    exact Nat.cast_add_one n
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x := by
    intro x _hx
    have hsq :
        HasDerivAt (fun y : ℝ => (y - a) ^ 2 / 2) (x - a) x := by
      have hbase : HasDerivAt (fun y : ℝ => y - a) (1 : ℝ) x :=
        (hasDerivAt_id x).sub_const a
      have hsquare :
          HasDerivAt (fun y : ℝ => (y - a) ^ 2)
            (((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1) x :=
        hbase.pow 2
      have hpow_one :
          (x - a) ^ (2 - 1) = x - a := by
        exact pow_one (x - a)
      have hraw_deriv :
          ((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1 =
            2 * (x - a) := by
        calc
          ((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1 =
              2 * (x - a) ^ (2 - 1) * 1 := by
            rfl
          _ = 2 * (x - a) * 1 := by
            exact congrArg (fun y : ℝ => 2 * y * 1) hpow_one
          _ = 2 * (x - a) := by
            exact mul_one (2 * (x - a))
      have hsquare' :
          HasDerivAt (fun y : ℝ => (y - a) ^ 2)
            (2 * (x - a)) x :=
        Eq.subst
          (motive := fun r : ℝ =>
            HasDerivAt (fun y : ℝ => (y - a) ^ 2) r x)
          hraw_deriv
          hsquare
      have hdiv :
          HasDerivAt (fun y : ℝ => (y - a) ^ 2 / 2)
            ((2 * (x - a)) / 2) x :=
        hsquare'.div_const 2
      have hcancel :
          (2 * (x - a)) / 2 = x - a := by
        exact mul_div_cancel_left₀ (x - a) (show (2 : ℝ) ≠ 0 from two_ne_zero)
      exact Eq.subst
        (motive := fun r : ℝ =>
          HasDerivAt (fun y : ℝ => (y - a) ^ 2 / 2) r x)
        hcancel
        hdiv
    have hlin :
        HasDerivAt (fun y : ℝ => (y - a) / 2) (1 / 2 : ℝ) x :=
      ((hasDerivAt_id x).sub_const a).div_const 2
    have hreal :
        HasDerivAt
          (fun y : ℝ => (y - a) ^ 2 / 2 - (y - a) / 2)
          ((x - a) - 1 / 2) x :=
      hsq.sub hlin
    exact hreal.ofReal_comp
  have hint :
      IntervalIntegrable f volume a b := by
    have hcont : ContinuousOn f (Set.uIcc a b) := by
      exact
        (Complex.continuous_ofReal.comp
          ((continuous_id.sub continuous_const).sub continuous_const)).continuousOn
    exact hcont.intervalIntegrable
  have hinterval :
      (∫ x in a..b, f x) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hset :
      (∫ x in Set.Ioc a b, f x) = F b - F a := by
    exact Eq.trans (intervalIntegral.integral_of_le hab).symm hinterval
  have hendpoints : F b = F a := by
    have hraw :
        (((b - a) ^ 2 / 2 - (b - a) / 2 : ℝ) : ℂ) =
          (((a - a) ^ 2 / 2 - (a - a) / 2 : ℝ) : ℂ) := by
      exact congrArg Complex.ofReal
        (Eq.subst
          (motive := fun y : ℝ =>
            (((y - a) ^ 2) / 2 - (y - a) / 2 : ℝ) =
              (((a - a) ^ 2) / 2 - (a - a) / 2 : ℝ))
          hb_eq.symm
          (real_oneInterval_centeredSawtooth_primitive_endpoint_eq a))
    exact hraw
  have hzero : F b - F a = 0 := by
    exact sub_eq_zero.mpr hendpoints
  exact Eq.trans hset hzero

/-- The first moment of the centered affine sawtooth on a unit interval is
`1/12`. -/
theorem eulerMaclaurin_affineSawtooth_oneInterval_firstMoment_eq_one_twelfth
    (n : ℕ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) *
        ((((x - ((n : ℕ) : ℝ)) : ℝ) : ℂ))) =
      (1 / 12 : ℂ) := by
  let a : ℝ := ((n : ℕ) : ℝ)
  let b : ℝ := (((n + 1 : ℕ) : ℝ))
  let F : ℝ → ℂ := fun x =>
    ((((x - a) ^ 3) / 3 - ((x - a) ^ 2) / 4 : ℝ) : ℂ)
  let f : ℝ → ℂ := fun x =>
    (((x - a - 1 / 2 : ℝ) : ℂ) * ((((x - a) : ℝ) : ℂ)))
  have hab : a ≤ b := by
    exact Nat.cast_le.mpr (Nat.le_succ n)
  have hb_eq : b = a + 1 := by
    exact Nat.cast_add_one n
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt F (f x) x := by
    intro x _hx
    have hbase : HasDerivAt (fun y : ℝ => y - a) (1 : ℝ) x :=
      (hasDerivAt_id x).sub_const a
    have hcube :
        HasDerivAt (fun y : ℝ => (y - a) ^ 3)
          (((3 : ℕ) : ℝ) * (x - a) ^ (3 - 1) * 1) x :=
      hbase.pow 3
    have hcube_raw :
        ((3 : ℕ) : ℝ) * (x - a) ^ (3 - 1) * 1 =
          3 * (x - a) ^ 2 := by
      have hpred : (3 - 1 : ℕ) = 2 := rfl
      calc
        ((3 : ℕ) : ℝ) * (x - a) ^ (3 - 1) * 1 =
            3 * (x - a) ^ (3 - 1) * 1 := by
          rfl
        _ = 3 * (x - a) ^ 2 * 1 := by
          exact congrArg (fun m : ℕ => 3 * (x - a) ^ m * 1) hpred
        _ = 3 * (x - a) ^ 2 := by
          exact mul_one (3 * (x - a) ^ 2)
    have hcube' :
        HasDerivAt (fun y : ℝ => (y - a) ^ 3)
          (3 * (x - a) ^ 2) x :=
      Eq.subst
        (motive := fun r : ℝ =>
          HasDerivAt (fun y : ℝ => (y - a) ^ 3) r x)
        hcube_raw
        hcube
    have hcube_div :
        HasDerivAt (fun y : ℝ => ((y - a) ^ 3) / 3)
          ((3 * (x - a) ^ 2) / 3) x :=
      hcube'.div_const 3
    have hcube_cancel :
        (3 * (x - a) ^ 2) / 3 = (x - a) ^ 2 := by
      exact mul_div_cancel_left₀ ((x - a) ^ 2)
        (show (3 : ℝ) ≠ 0 from three_ne_zero)
    have hcube_term :
        HasDerivAt (fun y : ℝ => ((y - a) ^ 3) / 3)
          ((x - a) ^ 2) x :=
      Eq.subst
        (motive := fun r : ℝ =>
          HasDerivAt (fun y : ℝ => ((y - a) ^ 3) / 3) r x)
        hcube_cancel
        hcube_div
    have hsquare :
        HasDerivAt (fun y : ℝ => (y - a) ^ 2)
          (((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1) x :=
      hbase.pow 2
    have hsquare_raw :
        ((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1 =
          2 * (x - a) := by
      have hpow_one : (x - a) ^ (2 - 1) = x - a :=
        pow_one (x - a)
      calc
        ((2 : ℕ) : ℝ) * (x - a) ^ (2 - 1) * 1 =
            2 * (x - a) ^ (2 - 1) * 1 := by
          rfl
        _ = 2 * (x - a) * 1 := by
          exact congrArg (fun y : ℝ => 2 * y * 1) hpow_one
        _ = 2 * (x - a) := by
          exact mul_one (2 * (x - a))
    have hsquare' :
        HasDerivAt (fun y : ℝ => (y - a) ^ 2)
          (2 * (x - a)) x :=
      Eq.subst
        (motive := fun r : ℝ =>
          HasDerivAt (fun y : ℝ => (y - a) ^ 2) r x)
        hsquare_raw
        hsquare
    have hsquare_div :
        HasDerivAt (fun y : ℝ => ((y - a) ^ 2) / 4)
          ((2 * (x - a)) / 4) x :=
      hsquare'.div_const 4
    have hreal :
        HasDerivAt
          (fun y : ℝ => ((y - a) ^ 3) / 3 - ((y - a) ^ 2) / 4)
          ((x - a - 1 / 2) * (x - a)) x := by
      have hsub :
          HasDerivAt
            (fun y : ℝ => ((y - a) ^ 3) / 3 - ((y - a) ^ 2) / 4)
            ((x - a) ^ 2 - (2 * (x - a)) / 4) x :=
        hcube_term.sub hsquare_div
      have halg :
          (x - a) ^ 2 - (2 * (x - a)) / 4 =
            (x - a - 1 / 2) * (x - a) := by
        let u : ℝ := x - a
        have hsquare :
            u ^ 2 = u * u :=
          pow_two u
        have hfour :
            (4 : ℝ) = 2 * 2 := by
          have hnat : (2 * 2 : ℕ) = 4 := rfl
          exact Eq.trans (Nat.cast_mul 2 2).symm (congrArg Nat.cast hnat)
        have htwo_over_four :
            (2 * u) / 4 = u / 2 := by
          calc
            (2 * u) / 4 = (2 * u) / (2 * 2) := by
              exact congrArg (fun r : ℝ => (2 * u) / r) hfour
            _ = u / 2 := by
              exact mul_div_mul_left u 2 (show (2 : ℝ) ≠ 0 from two_ne_zero)
        have hhalf_mul :
            (1 / 2 : ℝ) * u = u / 2 :=
          one_div_mul_eq_div u 2
        calc
          (x - a) ^ 2 - (2 * (x - a)) / 4 =
              u ^ 2 - (2 * u) / 4 := by
            exact rfl
          _ = u * u - (2 * u) / 4 := by
            exact congrArg (fun r : ℝ => r - (2 * u) / 4) hsquare
          _ = u * u - u / 2 := by
            exact congrArg (fun r : ℝ => u * u - r) htwo_over_four
          _ = u * u - (1 / 2 : ℝ) * u := by
            exact congrArg (fun r : ℝ => u * u - r) hhalf_mul.symm
          _ = (u - 1 / 2) * u := by
            exact (sub_mul u (1 / 2 : ℝ) u).symm
          _ = (x - a - 1 / 2) * (x - a) := by
            exact rfl
      exact Eq.subst
        (motive := fun r : ℝ =>
          HasDerivAt
            (fun y : ℝ => ((y - a) ^ 3) / 3 - ((y - a) ^ 2) / 4)
            r x)
        halg
        hsub
    exact hreal.ofReal_comp
  have hint :
      IntervalIntegrable f volume a b := by
    have hcont : ContinuousOn f (Set.uIcc a b) := by
      exact
        ((Complex.continuous_ofReal.comp
            ((continuous_id.sub continuous_const).sub continuous_const)).mul
          (Complex.continuous_ofReal.comp
            (continuous_id.sub continuous_const))).continuousOn
    exact hcont.intervalIntegrable
  have hinterval :
      (∫ x in a..b, f x) = F b - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hset :
      (∫ x in Set.Ioc a b, f x) = F b - F a := by
    exact Eq.trans (intervalIntegral.integral_of_le hab).symm hinterval
  have hendpoint :
      F b - F a = (1 / 12 : ℂ) := by
    have hb_step : b - a = 1 := by
      exact Eq.subst
        (motive := fun y : ℝ => y - a = 1)
        hb_eq.symm
        (add_sub_cancel_left a 1)
    have ha_step : a - a = 0 :=
      sub_self a
    have hraw :
        ((((b - a) ^ 3) / 3 - ((b - a) ^ 2) / 4 : ℝ) : ℂ) -
            ((((a - a) ^ 3) / 3 - ((a - a) ^ 2) / 4 : ℝ) : ℂ) =
          (1 / 12 : ℂ) := by
      have hb_eval :
          ((b - a) ^ 3 / 3 - (b - a) ^ 2 / 4 : ℝ) =
            (1 / 12 : ℝ) := by
        have hsubst :
            ((b - a) ^ 3 / 3 - (b - a) ^ 2 / 4 : ℝ) =
              ((1 : ℝ) ^ 3 / 3 - (1 : ℝ) ^ 2 / 4) := by
          exact congrArg (fun y : ℝ => y ^ 3 / 3 - y ^ 2 / 4) hb_step
        have hone :
            ((1 : ℝ) ^ 3 / 3 - (1 : ℝ) ^ 2 / 4) =
              (1 / 12 : ℝ) := by
          have hpow3 :
              ((1 : ℝ) ^ 3) = 1 :=
            one_pow 3
          have hpow2 :
              ((1 : ℝ) ^ 2) = 1 :=
            one_pow 2
          have hthree_ne : (3 : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (show (3 : ℕ) ≠ 0 from Nat.succ_ne_zero 2)
          have hfour_ne : (4 : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (show (4 : ℕ) ≠ 0 from Nat.succ_ne_zero 3)
          have hcommon :
              (1 / 3 : ℝ) - 1 / 4 =
                ((1 : ℝ) * 4 - (1 : ℝ) * 3) / (3 * 4) := by
            exact div_sub_div (1 : ℝ) (1 : ℝ) hthree_ne hfour_ne
          have hnum :
              (1 : ℝ) * 4 - (1 : ℝ) * 3 = 1 := by
            calc
              (1 : ℝ) * 4 - (1 : ℝ) * 3 = 4 - (1 : ℝ) * 3 := by
                exact congrArg (fun r : ℝ => r - (1 : ℝ) * 3) (one_mul 4)
              _ = 4 - 3 := by
                exact congrArg (fun r : ℝ => 4 - r) (one_mul 3)
              _ = 1 := by
                exact sub_eq_iff_eq_add.mpr rfl
          have hden :
              (3 : ℝ) * 4 = 12 := by
            have hnat : (3 * 4 : ℕ) = 12 := rfl
            exact Eq.trans (Nat.cast_mul 3 4).symm (congrArg Nat.cast hnat)
          calc
            ((1 : ℝ) ^ 3 / 3 - (1 : ℝ) ^ 2 / 4) =
                1 / 3 - (1 : ℝ) ^ 2 / 4 := by
              exact congrArg (fun r : ℝ => r / 3 - (1 : ℝ) ^ 2 / 4) hpow3
            _ = 1 / 3 - 1 / 4 := by
              exact congrArg (fun r : ℝ => 1 / 3 - r / 4) hpow2
            _ = ((1 : ℝ) * 4 - (1 : ℝ) * 3) / (3 * 4) := by
              exact hcommon
            _ = 1 / (3 * 4) := by
              exact congrArg (fun r : ℝ => r / (3 * 4)) hnum
            _ = 1 / 12 := by
              exact congrArg (fun r : ℝ => 1 / r) hden
        exact Eq.trans hsubst hone
      have ha_eval :
          ((a - a) ^ 3 / 3 - (a - a) ^ 2 / 4 : ℝ) =
            0 := by
        have hsubst :
            ((a - a) ^ 3 / 3 - (a - a) ^ 2 / 4 : ℝ) =
              ((0 : ℝ) ^ 3 / 3 - (0 : ℝ) ^ 2 / 4) := by
          exact congrArg (fun y : ℝ => y ^ 3 / 3 - y ^ 2 / 4) ha_step
        have hzero_pow3 :
            ((0 : ℝ) ^ 3) = 0 :=
          zero_pow (show (3 : ℕ) ≠ 0 from Nat.succ_ne_zero 2)
        have hzero_pow2 :
            ((0 : ℝ) ^ 2) = 0 :=
          zero_pow (show (2 : ℕ) ≠ 0 from Nat.succ_ne_zero 1)
        have hzero_eval :
            ((0 : ℝ) ^ 3 / 3 - (0 : ℝ) ^ 2 / 4) = 0 := by
          calc
            ((0 : ℝ) ^ 3 / 3 - (0 : ℝ) ^ 2 / 4) =
                0 / 3 - (0 : ℝ) ^ 2 / 4 := by
              exact congrArg (fun y : ℝ => y / 3 - (0 : ℝ) ^ 2 / 4)
                hzero_pow3
            _ = 0 / 3 - 0 / 4 := by
              exact congrArg (fun y : ℝ => 0 / 3 - y / 4) hzero_pow2
            _ = 0 - 0 / 4 := by
              exact congrArg (fun y : ℝ => y - 0 / 4) (zero_div 3)
            _ = 0 - 0 := by
              exact congrArg (fun y : ℝ => 0 - y) (zero_div 4)
            _ = 0 := by
              exact sub_self 0
        exact Eq.trans hsubst hzero_eval
      calc
        ((((b - a) ^ 3) / 3 - ((b - a) ^ 2) / 4 : ℝ) : ℂ) -
            ((((a - a) ^ 3) / 3 - ((a - a) ^ 2) / 4 : ℝ) : ℂ) =
            ((1 / 12 : ℝ) : ℂ) - (0 : ℂ) := by
          exact congrArg₂ Sub.sub
            (congrArg Complex.ofReal hb_eval)
            (congrArg Complex.ofReal ha_eval)
        _ = ((1 / 12 : ℝ) : ℂ) := by
          exact sub_zero ((1 / 12 : ℝ) : ℂ)
        _ = (1 / 12 : ℂ) := by
          exact Complex.ofReal_div 1 12
    exact hraw
  exact Eq.trans hset hendpoint

/-- The first periodic Bernoulli factor has zero mean on each unit interval. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_oneInterval_integral_eq_zero
    (n : ℕ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) = 0 := by
  let f' : ℝ → ℂ := fun _x => (1 : ℂ)
  have hf'_int :
      IntegrableOn f'
        (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) := by
    have hab :
        (((n : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) :=
      Nat.cast_le.mpr (Nat.le_succ n)
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        (intervalIntegrable_const
          (μ := volume)
          (a := (((n : ℕ) : ℝ)))
          (b := (((n + 1 : ℕ) : ℝ)))
          (c := (1 : ℂ)))
  have hperiodic :
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) :=
    eulerMaclaurin_firstPeriodicBernoulli_oneInterval_remainder_integral_eq_affine
      f' n hf'_int
  have hleft :
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioc
      (fun x _hx =>
        mul_one ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
  have hright :
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ))) :=
    setIntegral_congr_fun measurableSet_Ioc
      (fun x _hx =>
        mul_one (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ)))
  calc
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
      exact hleft.symm
    _ =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) :=
      hperiodic
    _ =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ)) ) := by
      exact hright
    _ = 0 :=
      eulerMaclaurin_affineSawtooth_oneInterval_integral_eq_zero n

/-- First centered moment of the first-periodic Bernoulli factor on one unit
interval.

On `(n,n+1)`, the factor is `x - n - 1/2`; multiplying by `x - n` and
integrating over one unit interval gives `1/12`.  This is the local moment used
by the Taylor-linear part of the sharp boundary-growth estimate. -/
theorem eulerMaclaurinFirstPeriodicBernoulli_oneInterval_firstMoment_eq_one_twelfth
    (n : ℕ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x - ((n : ℕ) : ℝ)) : ℝ) : ℂ))) =
      (1 / 12 : ℂ) := by
  let f' : ℝ → ℂ := fun x =>
    ((((x - ((n : ℕ) : ℝ)) : ℝ) : ℂ))
  have hf'_int :
      IntegrableOn f'
        (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) := by
    have hab :
        (((n : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) :=
      Nat.cast_le.mpr (Nat.le_succ n)
    have hcont : ContinuousOn f'
        (Set.uIcc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) := by
      exact
        (Complex.continuous_ofReal.comp
          (continuous_id.sub continuous_const)).continuousOn
    exact
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
        hcont.intervalIntegrable
  have hperiodic :
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) :=
    eulerMaclaurin_firstPeriodicBernoulli_oneInterval_remainder_integral_eq_affine
      f' n hf'_int
  exact Eq.trans hperiodic
    (eulerMaclaurin_affineSawtooth_oneInterval_firstMoment_eq_one_twelfth n)

/-- One-unit-interval integration-by-parts identity for the first periodic
Bernoulli factor.

On `(n, n+1)`, `Int.fract x = x - n`, so the sawtooth is
`x - n - 1/2`.  Integrating by parts against `f'` gives the local
Euler-Maclaurin correction with the strict-right endpoint convention
`- f(n)/2 + f(n+1)/2`. -/
theorem eulerMaclaurin_firstPeriodicBernoulli_oneInterval_integrationByParts
    (f f' : ℝ → ℂ)
    (n : ℕ)
    (hf_cont : ContinuousOn f
      (Set.Icc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))))
    (hf_deriv : ∀ x : ℝ,
      x ∈ Set.Ioo (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)) →
        HasDerivAt f (f' x) x)
    (hf'_int : IntegrableOn f'
      (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))) :
    f (((n + 1 : ℕ) : ℝ)) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)), f x) +
        (-(1 / 2 : ℂ) * f (((n : ℕ) : ℝ))) +
        ((1 / 2 : ℂ) * f (((n + 1 : ℕ) : ℝ))) +
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) := by
  have haffine :
      f (((n + 1 : ℕ) : ℝ)) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)), f x) +
          (-(1 / 2 : ℂ) * f (((n : ℕ) : ℝ))) +
          ((1 / 2 : ℂ) * f (((n + 1 : ℕ) : ℝ))) +
          (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
            (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) :=
    eulerMaclaurin_affineSawtooth_oneInterval_integrationByParts
      f f' n hf_cont hf_deriv hf'_int
  have hremainder :
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * f' x) =
        (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (((x - ((n : ℕ) : ℝ) - 1 / 2 : ℝ) : ℂ) * f' x)) :=
    eulerMaclaurin_firstPeriodicBernoulli_oneInterval_remainder_integral_eq_affine
      f' n hf'_int
  exact
    Eq.subst
      (motive := fun R : ℂ =>
        f (((n + 1 : ℕ) : ℝ)) =
          (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)), f x) +
            (-(1 / 2 : ℂ) * f (((n : ℕ) : ℝ))) +
            ((1 / 2 : ℂ) * f (((n + 1 : ℕ) : ℝ))) +
            R)
      hremainder.symm
      haffine

end
end LFunctions
end Boundary

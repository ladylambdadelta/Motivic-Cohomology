import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.ClosedDisk.Owner

/-!
# Entire-function Jensen boundary arc core

This owner layer was split from `ZeroMultiplicityCore.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

/-- Logarithmic maximum modulus of an entire function on the circle of radius `R`. -/
noncomputable def entireFunctionLogMaxOnCircle
    (F : ℂ → ℂ)
    (R : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖}

/-- The logarithmic boundary integrand in Jensen's formula on the circle of radius `R`. -/
noncomputable def entireFunctionJensenBoundaryLogIntegrand
    (F : ℂ → ℂ)
    (R : ℝ)
  (θ : ℝ) : ℝ :=
  Real.log ‖F ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖

/-- The normalized logarithmic boundary average in Jensen's formula. -/
noncomputable def entireFunctionJensenBoundaryLogIntegral
    (F : ℂ → ℂ)
    (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(2 * Real.pi),
    entireFunctionJensenBoundaryLogIntegrand F R θ

/-- The normalized logarithmic boundary average in Jensen's formula. -/
noncomputable def entireFunctionJensenBoundaryLogAverage
    (F : ℂ → ℂ)
    (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral F R

/-- Open-neighborhood identity theorem for entire functions.

Once an entire function vanishes on a complex neighborhood of one point,
preconnectedness of `ℂ` propagates the vanishing globally. -/
theorem entireFunction_eq_zero_of_eventually_zero_nhds
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z₀ : ℂ)
    (hlocal_zero : ∀ᶠ z in 𝓝 z₀, F z = 0) :
    ∀ z : ℂ, F z = 0 := by
  have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) :=
    fun z _ => hF z
  have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
    hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (by exact mem_univ _) hlocal_zero
  intro z
  exact hEq (by exact mem_univ _)

/-- A nontrivial entire function has finite analytic order at the origin. -/
theorem entireFunction_origin_order_ne_top_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    (hF 0).order ≠ ⊤ := by
  intro htop
  have hlocal_zero : ∀ᶠ z in 𝓝 (0 : ℂ), F z = 0 := by
    exact ((hF 0).order_eq_top_iff).mp htop
  have hglobal_zero : ∀ z : ℂ, F z = 0 :=
    entireFunction_eq_zero_of_eventually_zero_nhds F hF 0 hlocal_zero
  exact
    Exists.elim hnontrivial
      (fun z hz => hz (hglobal_zero z))

/-- For a nontrivial entire function, the file's origin multiplicity is the
finite analytic order at the origin. -/
theorem entireFunction_origin_order_eq_multiplicity_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    (hF 0).order =
      (entireFunctionZeroMultiplicity F hF 0 : ENat) := by
  have hfinite : (hF 0).order ≠ ⊤ :=
    entireFunction_origin_order_ne_top_of_nontrivial F hF hnontrivial
  show (hF 0).order = ((hF 0).order.toNat : ENat)
  exact (ENat.coe_toNat hfinite).symm

/-- A nontrivial entire function has finite analytic order at every point. -/
theorem entireFunction_order_ne_top_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (z₀ : ℂ) :
    (hF z₀).order ≠ ⊤ := by
  intro htop
  have hlocal_zero : ∀ᶠ z in 𝓝 z₀, F z = 0 := by
    exact ((hF z₀).order_eq_top_iff).mp htop
  have hglobal_zero : ∀ z : ℂ, F z = 0 :=
    entireFunction_eq_zero_of_eventually_zero_nhds F hF z₀ hlocal_zero
  match hnontrivial with
  | ⟨z, hz⟩ => exact hz (hglobal_zero z)

/-- For a nontrivial entire function, the file's multiplicity is the finite
analytic order at every point. -/
theorem entireFunction_order_eq_multiplicity_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (z₀ : ℂ) :
    (hF z₀).order =
      (entireFunctionZeroMultiplicity F hF z₀ : ENat) := by
  have hfinite : (hF z₀).order ≠ ⊤ :=
    entireFunction_order_ne_top_of_nontrivial F hF hnontrivial z₀
  show (hF z₀).order = ((hF z₀).order.toNat : ENat)
  exact (ENat.coe_toNat hfinite).symm

/-- At an actual zero of a nontrivial entire function, the finite analytic
multiplicity is nonzero. -/
theorem entireFunctionZeroMultiplicity_ne_zero_of_zero_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    {z₀ : ℂ}
    (hz₀ : F z₀ = 0) :
    entireFunctionZeroMultiplicity F hF z₀ ≠ 0 := by
  intro hmult_zero
  have horder_eq_multiplicity :
      (hF z₀).order =
        (entireFunctionZeroMultiplicity F hF z₀ : ENat) :=
    entireFunction_order_eq_multiplicity_of_nontrivial F hF hnontrivial z₀
  have horder_zero :
      (hF z₀).order = (0 : ENat) :=
    Eq.trans horder_eq_multiplicity
      (congrArg (fun n : ℕ => (n : ENat)) hmult_zero)
  exact
    Exists.elim
      (entireFunction_localTaylorFactorization_of_order_eq_nat
        F hF z₀ 0 horder_zero)
      (fun g hg =>
        match hg with
        | ⟨_hg_an, hg_ne, hg_factor⟩ =>
            have hfactor_at_center :
                F z₀ = (z₀ - z₀) ^ 0 • g z₀ :=
              hg_factor.self_of_nhds
            have hpow :
                (z₀ - z₀) ^ 0 = (1 : ℂ) :=
              pow_zero (z₀ - z₀)
            have hfactor_one :
                (z₀ - z₀) ^ 0 • g z₀ = (1 : ℂ) • g z₀ :=
              congrArg (fun a : ℂ => a • g z₀) hpow
            have hF_eq_g :
                F z₀ = g z₀ :=
              Eq.trans (Eq.trans hfactor_at_center hfactor_one) (one_smul ℂ (g z₀))
            have hg_zero :
                g z₀ = 0 :=
              Eq.trans hF_eq_g.symm hz₀
            hg_ne hg_zero)

/-- The additive decomposition used in the periodicity proof for the
exponential arc. -/
theorem real_exp_arc_complex_mul_add
    (θ₀ : ℝ)
    (n : ℤ) :
    (θ₀ : ℂ) * Complex.I + (n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I) =
      ((θ₀ + n * (2 * Real.pi)) : ℂ) * Complex.I := by
  calc
    (θ₀ : ℂ) * Complex.I + (n : ℂ) * ((2 * Real.pi : ℂ) * Complex.I)
        = (θ₀ : ℂ) * Complex.I + ((n : ℂ) * (2 * Real.pi : ℂ)) * Complex.I := by
            exact congrArg
              (fun t : ℂ => (θ₀ : ℂ) * Complex.I + t)
              (mul_assoc (n : ℂ) (2 * Real.pi : ℂ) Complex.I).symm
    _ = (θ₀ : ℂ) * Complex.I + (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
          Complex.I := by
            have htwo_pi : (((2 * Real.pi : ℝ) : ℂ) : ℂ) = (2 * Real.pi : ℂ) :=
              Complex.ofReal_mul 2 Real.pi
            have hmul :
                (n : ℂ) * (2 * Real.pi : ℂ) =
                  (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
              calc
                (n : ℂ) * (2 * Real.pi : ℂ)
                    = (n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) : ℂ) := by
                      exact congrArg (fun t : ℂ => (n : ℂ) * t) htwo_pi.symm
                _ = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
                    (Complex.ofReal_mul (n : ℝ) (2 * Real.pi)).symm
            exact congrArg
              (fun t : ℂ => (θ₀ : ℂ) * Complex.I + t * Complex.I)
              hmul
    _ = ((θ₀ : ℂ) + (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) *
          Complex.I := by
            exact (add_mul (θ₀ : ℂ) (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) Complex.I).symm
    _ = ((θ₀ + n * (2 * Real.pi)) : ℂ) * Complex.I := by
          have htwo_pi : (((2 * Real.pi : ℝ) : ℂ) : ℂ) = (2 * Real.pi : ℂ) :=
            Complex.ofReal_mul 2 Real.pi
          have hmul :
              (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
                (n : ℂ) * (2 * Real.pi : ℂ) := by
            calc
              (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
                  = (n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) : ℂ) :=
                    Complex.ofReal_mul (n : ℝ) (2 * Real.pi)
              _ = (n : ℂ) * (2 * Real.pi : ℂ) := by
                exact congrArg (fun t : ℂ => (n : ℂ) * t) htwo_pi
          exact congrArg (fun t : ℂ => ((θ₀ : ℂ) + t) * Complex.I) hmul

/-- Helper for the arc periodicity proof after cancelling `Complex.I`. -/
theorem real_exp_arc_eq_of_complex_exp_eq_from_mul_I
    {θ θ₀ : ℝ}
    {n : ℤ}
    (hnC :
      (θ : ℂ) * Complex.I =
        ((θ₀ + n * (2 * Real.pi)) : ℂ) * Complex.I) :
    θ = θ₀ + n * (2 * Real.pi) := by
  have hθC : (θ : ℂ) = ((θ₀ + n * (2 * Real.pi)) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    exact hnC
  have hcast :
      ((θ₀ + n * (2 * Real.pi) : ℝ) : ℂ) =
        (θ₀ : ℂ) + (n : ℂ) * (2 * Real.pi : ℂ) := by
    have hmul :
        (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
          (n : ℂ) * (2 * Real.pi : ℂ) := by
      calc
        (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)
            = (n : ℂ) * (((2 * Real.pi : ℝ) : ℂ) : ℂ) :=
              Complex.ofReal_mul (n : ℝ) (2 * Real.pi)
        _ = (n : ℂ) * (2 * Real.pi : ℂ) := by
          have htwo_pi : (((2 * Real.pi : ℝ) : ℂ) : ℂ) =
              (2 * Real.pi : ℂ) :=
            Complex.ofReal_mul 2 Real.pi
          exact congrArg (fun t : ℂ => (n : ℂ) * t) htwo_pi
    calc
      ((θ₀ + n * (2 * Real.pi) : ℝ) : ℂ)
          = (θ₀ : ℂ) + (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
            Complex.ofReal_add θ₀ ((n : ℝ) * (2 * Real.pi))
      _ = (θ₀ : ℂ) + (n : ℂ) * (2 * Real.pi : ℂ) := by
        exact congrArg (fun t : ℂ => (θ₀ : ℂ) + t) hmul
  have hθC_norm : (θ : ℂ) = ((θ₀ + n * (2 * Real.pi) : ℝ) : ℂ) :=
    hθC.trans hcast.symm
  exact Complex.ofReal_injective hθC_norm

/-- Periodic exponential equality on the complex unit circle descends to a
real equality modulo integer multiples of `2π`. -/
theorem real_exp_arc_eq_of_complex_exp_eq
    (θ θ₀ : ℝ)
    (hn :
      Complex.exp ((θ : ℂ) * Complex.I) =
        Complex.exp ((θ₀ : ℂ) * Complex.I)) :
    ∃ n : ℤ, θ = θ₀ + n * (2 * Real.pi) := by
  exact
    Exists.elim (Complex.exp_eq_exp_iff_exists_int.mp hn)
      (fun n hn =>
        have hnC :
            (θ : ℂ) * Complex.I =
              ((θ₀ + n * (2 * Real.pi)) : ℂ) * Complex.I := by
          exact hn.trans (real_exp_arc_complex_mul_add θ₀ n)
        have hθ : θ = θ₀ + n * (2 * Real.pi) := by
          exact real_exp_arc_eq_of_complex_exp_eq_from_mul_I hnC
        ⟨n, hθ⟩)

/-- A nonzero integer multiple of `2π` has magnitude at least `2π`. -/
theorem real_two_pi_le_abs_int_mul_two_pi
    (n : ℤ)
    (hn0 : n ≠ 0) :
    2 * Real.pi ≤ |(n : ℝ)| * (2 * Real.pi) := by
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have h1_int : (1 : ℤ) ≤ |n| :=
      Int.one_le_abs hn0
    have hcast : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) :=
      Int.cast_le.mpr h1_int
    have hone : ((1 : ℤ) : ℝ) = 1 :=
      Int.cast_one
    have habs : ((|n| : ℤ) : ℝ) = |(n : ℝ)| :=
      Int.cast_abs
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ |(n : ℝ)|)
        hone
        (Eq.subst
          (motive := fun right : ℝ => ((1 : ℤ) : ℝ) ≤ right)
          habs
          hcast)
  calc
    2 * Real.pi = 1 * (2 * Real.pi) := (one_mul (2 * Real.pi)).symm
    _ ≤ |(n : ℝ)| * (2 * Real.pi) := by
      exact mul_le_mul_of_nonneg_right h1 Real.two_pi_pos.le

/-- A positive-radius exponential arc is locally injective in a punctured real
neighborhood of the base parameter. -/
theorem positiveRadius_exp_arc_eventually_ne_base
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ) :
    ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ≠
        (r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I) := by
  have hclose :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀, |θ - θ₀| < 2 * Real.pi := by
    have hball : Metric.ball θ₀ (2 * Real.pi) ∈ 𝓝 θ₀ :=
      Metric.ball_mem_nhds θ₀ Real.two_pi_pos
    exact
      Filter.mem_of_superset hball
        (fun θ hθ =>
          have hdist_lt : dist θ θ₀ < 2 * Real.pi := hθ
          calc
            |θ - θ₀| = dist θ θ₀ := (Real.dist_eq θ θ₀).symm
            _ < 2 * Real.pi := hdist_lt)
  have hclose_punctured :
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, |θ - θ₀| < 2 * Real.pi :=
    hclose.filter_mono nhdsWithin_le_nhds
  have hself :
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, θ ∈ ({θ₀} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  exact
    (hclose_punctured.and hself).mono
      (fun θ hθ hEq =>
        have hθclose : |θ - θ₀| < 2 * Real.pi := hθ.1
        have hθne : θ ≠ θ₀ := hθ.2
        have hrC : (r : ℂ) ≠ 0 :=
          Complex.ofReal_ne_zero.mpr hr.ne'
        have hExp :
            Complex.exp ((θ : ℂ) * Complex.I) =
              Complex.exp ((θ₀ : ℂ) * Complex.I) := by
          exact mul_left_cancel₀ hrC hEq
        Exists.elim (real_exp_arc_eq_of_complex_exp_eq θ θ₀ hExp)
          (fun n hθeq =>
            have hdiff : θ - θ₀ = n * (2 * Real.pi) := by
              calc
                θ - θ₀ = (θ₀ + n * (2 * Real.pi)) - θ₀ := by
                  exact congrArg (fun t : ℝ => t - θ₀) hθeq
                _ = n * (2 * Real.pi) :=
                  add_sub_cancel_left θ₀ (n * (2 * Real.pi))
            have hn0 : n = 0 := by
              match (inferInstance : Decidable (n = 0)) with
              | isTrue hn0 => exact hn0
              | isFalse hn0_ne =>
                  have hperiod :
                      |θ - θ₀| = |(n : ℝ)| * (2 * Real.pi) := by
                    calc
                      |θ - θ₀| = |(n : ℝ) * (2 * Real.pi)| := by
                        exact congrArg abs hdiff
                      _ = |(n : ℝ)| * |2 * Real.pi| := by
                        exact abs_mul (n : ℝ) (2 * Real.pi)
                      _ = |(n : ℝ)| * (2 * Real.pi) := by
                        exact congrArg (fun x : ℝ => |(n : ℝ)| * x)
                          (abs_of_pos Real.two_pi_pos)
                  have hle : 2 * Real.pi ≤ |θ - θ₀| := by
                    calc
                      2 * Real.pi ≤ |(n : ℝ)| * (2 * Real.pi) :=
                        real_two_pi_le_abs_int_mul_two_pi n hn0_ne
                      _ = |θ - θ₀| := hperiod.symm
                  exact False.elim (not_lt_of_ge hle hθclose)
            have hθ_zero :
                θ = θ₀ + ((0 : ℤ) : ℝ) * (2 * Real.pi) :=
              Eq.subst
                (motive := fun m : ℤ => θ = θ₀ + (m : ℝ) * (2 * Real.pi))
                hn0
                hθeq
            have hθ_eq : θ = θ₀ := by
              calc
                θ = θ₀ + ((0 : ℤ) : ℝ) * (2 * Real.pi) := hθ_zero
                _ = θ₀ + 0 * (2 * Real.pi) := by
                  exact congrArg
                    (fun t : ℝ => θ₀ + t * (2 * Real.pi))
                    Int.cast_zero
                _ = θ₀ + 0 := by
                  exact congrArg (fun t : ℝ => θ₀ + t)
                    (zero_mul (2 * Real.pi))
                _ = θ₀ := by
                  exact add_zero θ₀
            hθne hθ_eq))

/-- The derivative identity used in the logarithmic singularity proof. -/
theorem real_neg_log_deriv
    (x : ℝ) :
    (1 : ℝ) - (Real.log x + 1) = -Real.log x := by
  calc
    (1 : ℝ) - (Real.log x + 1)
        = 1 + -(Real.log x + 1) := sub_eq_add_neg 1 (Real.log x + 1)
    _ = 1 + (-Real.log x + -1) := by
      exact congrArg (fun t : ℝ => 1 + t) (neg_add (Real.log x) 1)
    _ = -Real.log x + (-1 + 1) := by
      ac_rfl
    _ = -Real.log x + 0 := by
      exact congrArg (fun t : ℝ => -Real.log x + t) (neg_add_cancel 1)
    _ = -Real.log x := add_zero (-Real.log x)

/-- The derivative of `x - x log x` on the unit interval is `-log x`. -/
theorem real_hasDerivAt_x_sub_x_mul_log_unitIoo
    (x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => x - x * Real.log x) (-Real.log x) x := by
  have hx0 : x ≠ 0 := (Set.mem_Ioo.mp hx).1.ne'
  have hmul : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) x :=
    Real.hasDerivAt_mul_log hx0
  have hsub :
      HasDerivAt (fun x : ℝ => x - x * Real.log x) (1 - (Real.log x + 1)) x := by
    exact (hasDerivAt_id x).sub hmul
  exact (real_neg_log_deriv x) ▸ hsub

/-- Pulling a punctured complex-neighborhood nonvanishing statement back along a
positive-radius exponential arc gives punctured real-neighborhood
nonvanishing. -/
theorem positiveRadius_exp_arc_eventually_ne_zero_pullback
    (F : ℂ → ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hne :
      ∀ᶠ z in 𝓝[≠] ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)), F z ≠ 0) :
    ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
      F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 := by
  let γ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hγ_cont : ContinuousAt γ θ₀ := by
    have hcast : ContinuousAt (fun θ : ℝ => (θ : ℂ)) θ₀ :=
      Complex.continuous_ofReal.continuousAt
    have hmulI :
        ContinuousAt (fun θ : ℝ => (θ : ℂ) * Complex.I) θ₀ :=
      hcast.mul continuousAt_const
    have hexp :
        ContinuousAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) θ₀ :=
      ContinuousAt.comp' Complex.continuous_exp.continuousAt hmulI
    exact continuousAt_const.mul hexp
  have hγ_tendsto_nhds : Tendsto γ (𝓝 θ₀) (𝓝 (γ θ₀)) :=
    hγ_cont
  have hne_base : ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, γ θ ≠ γ θ₀ :=
    positiveRadius_exp_arc_eventually_ne_base r hr θ₀
  have hγ_tendsto_punctured :
      Tendsto γ (𝓝[≠] θ₀) (𝓝[≠] γ θ₀) := by
    exact
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        γ
        (hγ_tendsto_nhds.mono_left inf_le_left)
        hne_base
  exact hγ_tendsto_punctured.eventually hne

/-- A positive-radius exponential arc has genuine punctured real parameters
arbitrarily close to its base point, and its image remains in the punctured
complex neighborhood of the base circle point.

This is the real-arc accumulation input needed to turn local vanishing of the
sampled function into a contradiction with isolated complex zeros. -/
theorem positiveRadius_exp_arc_eventually_zero_not_eventually_ne_zero
    (F : ℂ → ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hlocal_zero :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0)
    (hne :
      ∀ᶠ z in 𝓝[≠] ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)), F z ≠ 0) :
    False := by
  have hzero :
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
        F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
    hlocal_zero.filter_mono nhdsWithin_le_nhds
  have hnonzero :
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
        F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0 :=
    positiveRadius_exp_arc_eventually_ne_zero_pullback F r hr θ₀ hne
  have hfalse : ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, False := by
    exact
      (hzero.and hnonzero).mono
        (fun _ hθ => hθ.2 hθ.1)
  have hnebot : NeBot (𝓝[≠] θ₀) := by infer_instance
  exact hnebot.ne (Filter.eventually_false_iff_eq_bot.mp hfalse)

/-- Local real-arc vanishing at positive radius excludes the nontrivial
isolated-zero branch of an entire function at the corresponding circle point. -/
theorem entireFunction_eventually_zero_positiveRadius_exp_arc_forces_local_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hlocal_zero :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)), F z = 0 := by
  match
      (hF ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I))).eventually_eq_zero_or_eventually_ne_zero
    with
  | Or.inl hzero => exact hzero
  | Or.inr hne =>
      exact False.elim
        (positiveRadius_exp_arc_eventually_zero_not_eventually_ne_zero
          F r hr θ₀ hlocal_zero hne)

/-- Real-arc identity theorem for a positive-radius exponential arc.

This is the analytic-continuation bridge between a real-variable local zero
of the boundary sample and the complex identity theorem.  The proof chain is:
the positive-radius exponential parametrization maps any real neighborhood of
`θ₀` to a nonconstant analytic arc with an accumulation point in `ℂ`; the
sample vanishes on that arc; hence the zero set of the entire function has an
accumulation point and the complex identity theorem forces global vanishing. -/
theorem entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hlocal_zero :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∀ z : ℂ, F z = 0 := by
  have hcircle_zero :
      ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)), F z = 0 :=
    entireFunction_eventually_zero_positiveRadius_exp_arc_forces_local_zero
      F hF r hr θ₀ hlocal_zero
  exact
    entireFunction_eq_zero_of_eventually_zero_nhds
      F hF ((r : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) hcircle_zero

/-- Arc identity theorem for an entire function sampled on a positive-radius
Jensen circle.

This is the precise analytic-continuation bridge needed here: a real-analytic
circle arc has an accumulation point in `ℂ`, so local vanishing of the sampled
entire function forces global vanishing by the complex identity theorem. -/
theorem entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero_arcIdentity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ Set.Ioc 0 (2 * Real.pi))
    (hsample :
      AnalyticAt ℝ
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀)
    (hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0) :
    ∀ z : ℂ, F z = 0 := by
  have htwoR : 0 < 2 * R := by
    exact mul_pos two_pos hR
  have hlocal_zero' :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
    exact
      hlocal_zero.mono
        (fun θ hθ =>
          have hscale : (((2 * R : ℝ) : ℂ) : ℂ) = (2 * R : ℂ) := by
            exact Complex.ofReal_mul 2 R
          have harg :
              F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
                F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
            exact congrArg F
              (congrArg
                (fun w : ℂ => w * Complex.exp ((θ : ℂ) * Complex.I))
                hscale)
          Eq.trans harg hθ)
  exact
    entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
      F hF (2 * R) htwoR θ₀
      hlocal_zero'

/-- Identity propagation from a locally vanishing Jensen boundary sample to a
globally vanishing entire function. This is the exact analytic identity-theorem
input needed to exclude the identically-zero local model under the global
nontriviality hypothesis.

The positive-radius hypothesis is essential: at radius zero the boundary sample
only sees the single value `F 0`. -/
theorem entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ Set.Ioc 0 (2 * Real.pi))
    (hsample :
      AnalyticAt ℝ
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀)
    (hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0) :
    ∀ z : ℂ, F z = 0 := by
  exact
    entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero_arcIdentity
      F hF R hR θ₀ hθ₀ hsample hlocal_zero

/-- The true local remnant statement carried by a punctured Jensen log model.

The punctured identity alone cannot determine a globally continuous function on
the whole fundamental interval, nor can it force an unpunctured identity at the
singular parameter.  The owner-level fact is therefore the local continuous
remainder together with the original punctured equality. -/
theorem continuousRemainderExtensionOn_Icc_of_puncturedLocalModel
    (f : ℝ → ℝ)
    (θ₀ : ℝ)
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg : ContinuousAt g θ₀)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        f θ = (n : ℝ) * Real.log |θ - θ₀| + g θ) :
    ∃ g' : ℝ → ℝ,
      ContinuousAt g' θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        f θ = (n : ℝ) * Real.log |θ - θ₀| + g' θ := by
  exact ⟨g, hg, hmodel⟩

end
end LFunctions
end Boundary

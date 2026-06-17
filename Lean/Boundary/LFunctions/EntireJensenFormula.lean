import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Jensen formula for entire functions

This file owns the generic entire-function Jensen formula API used by the
completed-zeta zero-counting lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Zeros of an entire function. -/
abbrev EntireFunctionZero
    (F : ℂ → ℂ) : Type :=
  {z : ℂ // F z = 0}

/-- Analytic multiplicity of a zero of an entire function. -/
noncomputable def entireFunctionZeroMultiplicity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ) : ℕ :=
  (hF z).order.toNat

/-- The local first-nonzero Taylor factor at a point where the analytic order is `n`.

This is the local multiplicity input used by Jensen's formula: near `z`, an
analytic function with vanishing order `n` is `(w - z)^n` times an analytic
factor nonzero at `z`. -/
theorem entireFunction_localTaylorFactorization_of_order_eq_nat
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ)
    (n : ℕ)
    (horder : (hF z).order = (n : ENat)) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z ∧
      g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z, F w = (w - z) ^ n • g w := by
  exact ((hF z).order_eq_nat_iff n).mp horder

/-- The local first-nonzero Taylor factor stated with the file's multiplicity
definition. -/
theorem entireFunction_localMultiplicityFactorization
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ)
    (horder :
      (hF z).order =
        (entireFunctionZeroMultiplicity F hF z : ENat)) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g z ∧
      g z ≠ 0 ∧
      ∀ᶠ w in 𝓝 z,
        F w =
          (w - z) ^ entireFunctionZeroMultiplicity F hF z • g w := by
  exact
    entireFunction_localTaylorFactorization_of_order_eq_nat
      F hF z (entireFunctionZeroMultiplicity F hF z) horder

/-- The norm contribution of the local Taylor factor. -/
theorem entireFunction_localTaylorFactor_norm
    (F : ℂ → ℂ)
    (z : ℂ)
    (n : ℕ)
    (g : ℂ → ℂ)
    (hfactor :
      ∀ᶠ w in 𝓝 z, F w = (w - z) ^ n • g w) :
    ∀ᶠ w in 𝓝 z,
      ‖F w‖ = ‖w - z‖ ^ n * ‖g w‖ := by
  filter_upwards [hfactor] with w hw
  calc
    ‖F w‖ = ‖(w - z) ^ n • g w‖ := by
      exact congrArg norm hw
    _ = ‖(w - z) ^ n‖ * ‖g w‖ := by
      exact norm_smul ((w - z) ^ n) (g w)
    _ = ‖w - z‖ ^ n * ‖g w‖ := by
      exact congrArg (fun x : ℝ => x * ‖g w‖) (norm_pow (w - z) n)

/-- The logarithmic local contribution of the first nonzero Taylor factor away
from its zero. -/
theorem entireFunction_localTaylorFactor_logContribution
    (F : ℂ → ℂ)
    (z : ℂ)
    (n : ℕ)
    (g : ℂ → ℂ)
    (hg_an : AnalyticAt ℂ g z)
    (hg_ne : g z ≠ 0)
    (hfactor :
      ∀ᶠ w in 𝓝 z, F w = (w - z) ^ n • g w) :
    ∀ᶠ w in 𝓝[≠] z,
      Real.log ‖F w‖ =
        (n : ℝ) * Real.log ‖w - z‖ + Real.log ‖g w‖ := by
  have hnorm :
      ∀ᶠ w in 𝓝 z, ‖F w‖ = ‖w - z‖ ^ n * ‖g w‖ :=
    entireFunction_localTaylorFactor_norm F z n g hfactor
  have hg_eventually_ne : ∀ᶠ w in 𝓝 z, g w ≠ 0 :=
    hg_an.continuousAt.eventually_ne hg_ne
  filter_upwards
    [hnorm.filter_mono nhdsWithin_le_nhds,
      hg_eventually_ne.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
    with w hnorm_w hg_w_ne hw_ne
  have hsub_ne : w - z ≠ 0 :=
    sub_ne_zero.mpr hw_ne
  have hnorm_sub_ne : ‖w - z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hsub_ne
  have hpow_ne : ‖w - z‖ ^ n ≠ 0 :=
    pow_ne_zero n hnorm_sub_ne
  have hg_norm_ne : ‖g w‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hg_w_ne
  calc
    Real.log ‖F w‖ =
        Real.log (‖w - z‖ ^ n * ‖g w‖) := by
      exact congrArg Real.log hnorm_w
    _ = Real.log (‖w - z‖ ^ n) + Real.log ‖g w‖ := by
      exact Real.log_mul hpow_ne hg_norm_ne
    _ = (n : ℝ) * Real.log ‖w - z‖ + Real.log ‖g w‖ := by
      exact congrArg (fun x : ℝ => x + Real.log ‖g w‖)
        (Real.log_pow ‖w - z‖ n)

/-- Multiplicity summand for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  else
    0

/-- Multiplicity count for entire-function zeros inside a closed disk. -/
noncomputable def entireFunctionZeroMultiplicityCountingInClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ) : ℝ :=
  ∑' z : EntireFunctionZero F,
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z

/-- Entire-function closed-disk multiplicity summands are nonnegative. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_nonnegative
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) :
    0 ≤ entireFunctionZeroMultiplicityClosedDiskSummand F hF R z := by
  unfold entireFunctionZeroMultiplicityClosedDiskSummand
  by_cases hz : ‖(z : ℂ)‖ ≤ R
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hz).symm
      (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF (z : ℂ)))
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hz).symm
      (le_refl (0 : ℝ))

/-- Entire-function closed-disk multiplicity summands are monotone in the disk radius. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_mono
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R S : ℝ}
    (hRS : R ≤ S)
    (z : EntireFunctionZero F) :
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z ≤
      entireFunctionZeroMultiplicityClosedDiskSummand F hF S z := by
  unfold entireFunctionZeroMultiplicityClosedDiskSummand
  by_cases hzR : ‖(z : ℂ)‖ ≤ R
  · have hzS : ‖(z : ℂ)‖ ≤ S :=
      le_trans hzR hRS
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if ‖(z : ℂ)‖ ≤ S then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) else 0)
      (if_pos hzR).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) ≤ x)
        (if_pos hzS).symm
        (le_refl (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)))
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if ‖(z : ℂ)‖ ≤ S then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) else 0)
      (if_neg hzR).symm
      (entireFunctionZeroMultiplicityClosedDiskSummand_nonnegative F hF S z)

/-- Entire-function closed-disk multiplicity counts are monotone when the two summand
families are summable. The analytic Jensen root supplies such finiteness in applications. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mono_of_summable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R S : ℝ}
    (hRS : R ≤ S)
    (hR :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z))
    (hS :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF S z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF S := by
  unfold entireFunctionZeroMultiplicityCountingInClosedDisk
  exact tsum_le_tsum
    (fun z : EntireFunctionZero F =>
      entireFunctionZeroMultiplicityClosedDiskSummand_mono F hF hRS z)
    hR
    hS

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
  Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖

/-- The normalized logarithmic boundary average in Jensen's formula. -/
noncomputable def entireFunctionJensenBoundaryLogAverage
    (F : ℂ → ℂ)
    (R : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      entireFunctionJensenBoundaryLogIntegrand F R θ

/-- A nonnegative real radius has the same norm after embedding in `ℂ`. -/
theorem complex_norm_ofReal_of_nonnegative
    {r : ℝ}
    (hr : 0 ≤ r) :
    ‖(r : ℂ)‖ = r := by
  have hnorm_real : ‖(r : ℂ)‖ = ‖r‖ :=
    Complex.norm_real r
  have hreal_norm_abs : ‖r‖ = |r| :=
    Real.norm_eq_abs r
  have habs : |r| = r :=
    abs_of_nonneg hr
  exact hnorm_real.trans (hreal_norm_abs.trans habs)

/-- The Jensen circle parametrization has the requested radius. -/
theorem entireFunctionJensenBoundaryCircle_norm
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R := by
  have hR_norm : ‖(R : ℂ)‖ = R :=
    complex_norm_ofReal_of_nonnegative hR
  have hExp_norm : ‖Complex.exp (θ * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I θ
  calc
    ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ =
        ‖(R : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
      exact norm_mul (R : ℂ) (Complex.exp (θ * Complex.I))
    _ = R * 1 := by
      exact congrArg₂ HMul.hMul hR_norm hExp_norm
    _ = R := mul_one R

/-- The boundary logarithmic integrand is bounded by the logarithmic maximum once the
circle log set is known to be bounded above. -/
theorem entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (θ : ℝ) :
    entireFunctionJensenBoundaryLogIntegrand F R θ ≤
      entireFunctionLogMaxOnCircle F R := by
  unfold entireFunctionJensenBoundaryLogIntegrand
  unfold entireFunctionLogMaxOnCircle
  exact le_csSup hbdd
    ⟨(R : ℂ) * Complex.exp (θ * Complex.I),
      entireFunctionJensenBoundaryCircle_norm hR,
      rfl⟩

/-- The normalized Jensen boundary average is bounded by the logarithmic maximum. -/
theorem entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (hint :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogAverage F R ≤
      entireFunctionLogMaxOnCircle F R := by
  unfold entireFunctionJensenBoundaryLogAverage
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    le_of_lt Real.two_pi_pos
  have hconst_int :
      IntervalIntegrable
        (fun _ : ℝ => entireFunctionLogMaxOnCircle F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    Continuous.intervalIntegrable continuous_const (0 : ℝ) (2 * Real.pi)
  have hintegral_le :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        ∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R := by
    exact intervalIntegral.integral_mono_on
      htwo_pi_nonneg
      hint
      hconst_int
      (fun θ _hθ =>
        entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle F hR hbdd θ)
  have hconst_eval :
      (∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R) =
        (2 * Real.pi) * entireFunctionLogMaxOnCircle F R := by
    simp [intervalIntegral.integral_const, sub_zero, Algebra.id.smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc]
  have hscale_nonneg : 0 ≤ (2 * Real.pi)⁻¹ :=
    inv_nonneg.mpr htwo_pi_nonneg
  have hscaled :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) := by
    exact mul_le_mul_of_nonneg_left
      (hintegral_le.trans_eq hconst_eval)
      hscale_nonneg
  have hcollapse :
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
        entireFunctionLogMaxOnCircle F R := by
    calc
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
          ((2 * Real.pi)⁻¹ * (2 * Real.pi)) *
            entireFunctionLogMaxOnCircle F R := by
        ring
      _ = 1 * entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x * entireFunctionLogMaxOnCircle F R)
          (inv_mul_cancel₀ Real.two_pi_pos.ne')
      _ = entireFunctionLogMaxOnCircle F R := one_mul _
  exact hscaled.trans_eq hcollapse

/-- Boundary regularity for Jensen's logarithmic average on doubled circles.

For a nontrivial entire function, the boundary logarithm has only isolated
logarithmic singularities on each circle.  Consequently the circle log set is
bounded above and the logarithmic boundary integrand is interval-integrable. -/
theorem entireFunction_jensenBoundaryLogSet_bddAbove
  (F : ℂ → ℂ)
  (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
  (R : ℝ) :
    BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} := by
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous fun z : ℂ => ‖F z‖ :=
    continuous_norm.comp hcontF
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (2 * R)) := by
    simpa [Metric.closedBall, dist_eq_norm] using
      (isCompact_closedBall (0 : ℂ) (2 * R))
  obtain ⟨M, hM⟩ := hcompact.bddAbove_image hcont_norm.continuousOn
  refine ⟨M, ?_⟩
  intro x hx
  rcases hx with ⟨z, hz, rfl⟩
  have hzball : z ∈ Metric.closedBall (0 : ℂ) (2 * R) := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using le_of_eq hz
  have hnorm_le : ‖F z‖ ≤ M := by
    exact hM ⟨z, hzball, rfl⟩
  exact le_trans (Real.log_le_self (norm_nonneg (F z))) hnorm_le

/-- The logarithmic singularity `-log` is interval-integrable on `[0,1]`. -/
theorem real_intervalIntegrable_neg_log_unitInterval :
    IntervalIntegrable (fun x : ℝ => -Real.log x) MeasureTheory.volume 0 1 := by
  have hcont :
      ContinuousOn (fun x : ℝ => x - x * Real.log x) (Set.Icc (0 : ℝ) 1) := by
    simpa [sub_eq_add_neg] using
      (continuous_id.sub Real.continuous_mul_log).continuousOn
  have hderiv :
      ∀ x ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => x - x * Real.log x) (-Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := (Set.mem_Ioo.mp hx).1.ne'
    have hmul : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) x :=
      Real.hasDerivAt_mul_log hx0
    have hsub :
        HasDerivAt (fun x : ℝ => x - x * Real.log x) (1 - (Real.log x + 1)) x := by
      simpa [sub_eq_add_neg] using (hasDerivAt_id x).sub hmul
    convert hsub using 1 <;> ring
  have hnonneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ -Real.log x := by
    intro x hx
    have hx0 : 0 < x := (Set.mem_Ioo.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioo.mp hx).2.le
    exact neg_nonneg.mpr (Real.log_nonpos hx0.le hx1)
  simpa using
    (intervalIntegral.intervalIntegrable_deriv_of_nonneg hcont hderiv hnonneg)

/-- The real logarithm is interval-integrable on `[0,1]`. -/
theorem real_intervalIntegrable_log_unitInterval :
    IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 1 := by
  simpa using real_intervalIntegrable_neg_log_unitInterval.neg

theorem entireFunction_jensenBoundaryLogAverage_regularity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) := by
  sorry

/-- Jensen's formula relates multiplicity-aware closed-disk zero counting to the
normalized logarithmic boundary average on the doubled circle, with the standard
`log 2` loss.

This is the classical analytic root: after factoring the first nonzero Taylor
term at the origin, Jensen's formula bounds zeros in `closedDisk R` by the
boundary average of `log ‖F‖` on the circle of radius `2R`, divided by
`log 2`; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  sorry

/-- Multiplicity-aware closed-disk zero counting is bounded by the doubled-circle
boundary logarithmic average with the standard `log 2` factor. -/
theorem entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
        IntervalIntegrable
          (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
          MeasureTheory.volume
          (0 : ℝ)
          (2 * Real.pi) ∧
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  match
    entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial with
  | ⟨J, hcount⟩ =>
      refine ⟨J, ?_⟩
      intro R hR
      match entireFunction_jensenBoundaryLogAverage_regularity F hF hnontrivial R hR with
      | ⟨hbdd, hint⟩ =>
          exact ⟨hbdd, hint, hcount R hR⟩

/-- Jensen's formula converts the boundary-log-average estimate into the log-max
closed-disk zero-counting bound. -/
theorem entireFunction_jensenFormula_zeroMultiplicityCounting_closedDisk_le_logMax
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ * entireFunctionLogMaxOnCircle F (2 * R) := by
  match
    entireFunctionZeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
      F hF hnontrivial with
  | ⟨J, hJ⟩ =>
      refine ⟨J, ?_⟩
      intro R hR
      have hR_nonneg : 0 ≤ R :=
        le_trans zero_le_one hR
      have htwoR_nonneg : 0 ≤ 2 * R :=
        mul_nonneg zero_le_two hR_nonneg
      match hJ R hR with
      | ⟨hbdd, hint, hcount⟩ =>
          have havg :
              entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                entireFunctionLogMaxOnCircle F (2 * R) :=
            entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
              F
              htwoR_nonneg
              hbdd
              hint
          have hlog_two_nonneg : 0 ≤ (Real.log 2)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (Real.log_pos one_lt_two))
          have hwith_constant :
              J + (Real.log 2)⁻¹ *
                  entireFunctionJensenBoundaryLogAverage F (2 * R) ≤
                J + (Real.log 2)⁻¹ *
                  entireFunctionLogMaxOnCircle F (2 * R) :=
            add_le_add_left
              (mul_le_mul_of_nonneg_left havg hlog_two_nonneg)
              J
          exact le_trans hcount hwith_constant

end

end LFunctions
end Boundary

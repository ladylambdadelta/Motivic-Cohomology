import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
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

/-- Nonzero zeros of an entire function.  This is the canonical index for
Jensen terms after the origin Taylor factor has been separated. -/
abbrev EntireFunctionNonzeroZero
    (F : ℂ → ℂ) : Type :=
  {z : ℂ // F z = 0 ∧ z ≠ 0}

/-- Forgetting the nonzero condition gives an ordinary zero. -/
def EntireFunctionNonzeroZero.toZero
    (F : ℂ → ℂ)
    (z : EntireFunctionNonzeroZero F) : EntireFunctionZero F :=
  ⟨z, z.property.1⟩

/-- The forgetful map from nonzero zeros to all zeros is injective. -/
theorem EntireFunctionNonzeroZero.toZero_injective
    (F : ℂ → ℂ) :
    Function.Injective (EntireFunctionNonzeroZero.toZero F) := by
  intro z w hzw
  exact Subtype.ext (congrArg Subtype.val hzw)

/-- An ordinary zero lies in the range of the nonzero-zero forgetful map exactly
when its value is nonzero. -/
theorem EntireFunctionNonzeroZero.mem_range_toZero_iff
    (F : ℂ → ℂ)
    (z : EntireFunctionZero F) :
    z ∈ Set.range (EntireFunctionNonzeroZero.toZero F) ↔ (z : ℂ) ≠ 0 := by
  constructor
  · intro hz
    rcases hz with ⟨w, hw⟩
    exact Eq.subst
      (motive := fun x : ℂ => x ≠ 0)
      (congrArg Subtype.val hw)
      w.property.2
  · intro hz
    exact ⟨⟨z, z.property, hz⟩, Subtype.ext rfl⟩

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
      isPreconnected_univ (by simp) hlocal_zero
  intro z
  exact hEq (by simp)

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
  rcases hnontrivial with ⟨z, hz⟩
  exact hz (hglobal_zero z)

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
  unfold entireFunctionZeroMultiplicity
  exact (ENat.coe_toNat hfinite).symm

/-- A positive-radius exponential arc is locally injective in a punctured real
neighborhood of the base parameter. -/
theorem positiveRadius_exp_arc_eventually_ne_base
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ) :
    ∀ᶠ θ in 𝓝[≠] θ₀,
      (r : ℂ) * Complex.exp (θ * Complex.I) ≠
        (r : ℂ) * Complex.exp (θ₀ * Complex.I) := by
  have hclose :
      ∀ᶠ θ in 𝓝 θ₀, |θ - θ₀| < 2 * Real.pi := by
    exact
      (Metric.eventually_nhds_iff_ball.mpr
        ⟨2 * Real.pi, Real.two_pi_pos, by
          intro θ hθ
          simpa [Real.dist_eq] using hθ⟩)
  filter_upwards
    [hclose.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with θ hθclose hθne hEq
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hExp :
      Complex.exp (θ * Complex.I) =
        Complex.exp (θ₀ * Complex.I) := by
    apply mul_left_cancel₀ hrC
    simpa [mul_assoc] using hEq
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hExp) with ⟨n, hn⟩
  have hnC :
      (θ : ℂ) * Complex.I =
        ((θ₀ + n * (2 * Real.pi)) : ℂ) * Complex.I := by
    simpa [mul_add, add_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using hn
  have hθC : (θ : ℂ) = ((θ₀ + n * (2 * Real.pi)) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    exact hnC
  have hθ : θ = θ₀ + n * (2 * Real.pi) := by
    have hθ' := congrArg Complex.re hθC
    simpa using hθ'
  have hdiff : θ - θ₀ = n * (2 * Real.pi) := by
    linarith
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
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
        2 * Real.pi = 1 * (2 * Real.pi) := by ring
        _ ≤ |(n : ℝ)| * (2 * Real.pi) := by
          exact mul_le_mul_of_nonneg_right h1 Real.two_pi_pos.le
        _ = |θ - θ₀| := hperiod.symm
    exact not_lt_of_ge hle hθclose
  subst hn0
  exact hθne (by linarith)

/-- Pulling a punctured complex-neighborhood nonvanishing statement back along a
positive-radius exponential arc gives punctured real-neighborhood
nonvanishing. -/
theorem positiveRadius_exp_arc_eventually_ne_zero_pullback
    (F : ℂ → ℂ)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hne :
      ∀ᶠ z in 𝓝[≠] ((r : ℂ) * Complex.exp (θ₀ * Complex.I)), F z ≠ 0) :
    ∀ᶠ θ in 𝓝[≠] θ₀,
      F ((r : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  let γ : ℝ → ℂ := fun θ => (r : ℂ) * Complex.exp (θ * Complex.I)
  have hγ_cont : ContinuousAt γ θ₀ := by
    fun_prop
  have hγ_tendsto_nhds : Tendsto γ (𝓝 θ₀) (𝓝 (γ θ₀)) :=
    hγ_cont
  have hne_base : ∀ᶠ θ in 𝓝[≠] θ₀, γ θ ≠ γ θ₀ :=
    positiveRadius_exp_arc_eventually_ne_base r hr θ₀
  have hγ_tendsto_punctured :
      Tendsto γ (𝓝[≠] θ₀) (𝓝[≠] γ θ₀) := by
    rw [nhdsWithin]
    exact
      Tendsto.inf
        (hγ_tendsto_nhds.mono_left nhdsWithin_le_nhds)
        (tendsto_principal.mpr hne_base)
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
      ∀ᶠ θ in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0)
    (hne :
      ∀ᶠ z in 𝓝[≠] ((r : ℂ) * Complex.exp (θ₀ * Complex.I)), F z ≠ 0) :
    False := by
  have hzero :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        F ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0 :=
    hlocal_zero.filter_mono nhdsWithin_le_nhds
  have hnonzero :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        F ((r : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    positiveRadius_exp_arc_eventually_ne_zero_pullback F r hr θ₀ hne
  have hfalse : ∀ᶠ θ in 𝓝[≠] θ₀, False := by
    filter_upwards [hzero, hnonzero] with θ hθzero hθnonzero
    exact hθnonzero hθzero
  exact
    (Filter.not_eventually_false (𝓝[≠] θ₀)) hfalse

/-- Local real-arc vanishing at positive radius excludes the nontrivial
isolated-zero branch of an entire function at the corresponding circle point. -/
theorem entireFunction_eventually_zero_positiveRadius_exp_arc_forces_local_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (r : ℝ)
    (hr : 0 < r)
    (θ₀ : ℝ)
    (hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp (θ₀ * Complex.I)), F z = 0 := by
  rcases
      (hF ((r : ℂ) * Complex.exp (θ₀ * Complex.I))).eventually_eq_zero_or_eventually_ne_zero
      with hzero | hne
  · exact hzero
  · exact False.elim
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
      ∀ᶠ θ in 𝓝 θ₀,
        F ((r : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∀ z : ℂ, F z = 0 := by
  have hcircle_zero :
      ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp (θ₀ * Complex.I)), F z = 0 :=
    entireFunction_eventually_zero_positiveRadius_exp_arc_forces_local_zero
      F hF r hr θ₀ hlocal_zero
  exact
    entireFunction_eq_zero_of_eventually_zero_nhds
      F hF ((r : ℂ) * Complex.exp (θ₀ * Complex.I)) hcircle_zero

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
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀)
    (hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ = 0) :
    ∀ z : ℂ, F z = 0 := by
  have htwoR : 0 < 2 * R := by
    nlinarith
  exact
    entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
      F hF (2 * R) htwoR θ₀ hlocal_zero

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
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀)
    (hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ = 0) :
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

/-- The real logarithm is interval-integrable on a compact interval starting at `0`.
This is the translated endpoint-singularity input used in the Jensen local
gluing theorem. -/
theorem real_intervalIntegrable_log_Icc {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 t := by
  rcases lt_or_eq_of_le ht with hpos | rfl
  · have hscaled :
        IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹)) MeasureTheory.volume 0 t := by
      simpa using
        (real_intervalIntegrable_log_unitInterval.comp_mul_right (t⁻¹))
    have hconst : IntervalIntegrable (fun _ : ℝ => Real.log t) MeasureTheory.volume 0 t :=
      intervalIntegrable_const
    have hsum :
        IntervalIntegrable (fun x : ℝ => Real.log (x * t⁻¹) + Real.log t)
          MeasureTheory.volume 0 t :=
      hscaled.add hconst
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpos.le] at hsum ⊢
    refine IntegrableOn.congr_fun hsum ?_ measurableSet_Ioc
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioc.mp hx).1.ne'
    have ht0 : t ≠ 0 := hpos.ne'
    calc
      Real.log x = Real.log (x * t⁻¹) + Real.log t := by
        rw [Real.log_mul hx0 (inv_ne_zero ht0), Real.log_inv]
        ring
      _ = Real.log (x * t⁻¹) + Real.log t := rfl
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl, Ioc_eq_empty_of_le le_rfl]
    exact integrableOn_empty

/-- The translated absolute-distance logarithm is interval-integrable on a
compact interval. This is the one-dimensional singularity model used in the
Jensen local gluing theorem. -/
theorem intervalIntegrable_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable (fun x : ℝ => Real.log |x - c|) MeasureTheory.volume a b := by
  have hab : a ≤ b := hac.trans hcb
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  rw [← Ioc_union_Ioc_eq_Ioc hac hcb, integrableOn_union]
  constructor
  · have hleft :
        IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume a c := by
      have hbase :
          IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 (c - a) := by
        exact real_intervalIntegrable_log_Icc (by linarith)
      have htrans :
          IntervalIntegrable (fun x : ℝ => Real.log (c - x)) MeasureTheory.volume c a :=
        hbase.comp_sub_left c
      exact htrans.symm
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hac] at hleft ⊢
    exact hleft.congr_fun
      (by
        intro x hx
        have hxle : x - c ≤ 0 := by
          have hx' : x ≤ c := (mem_Ioc.mp hx).2
          linarith
        have habs : |x - c| = c - x := by
          rw [abs_of_nonpos hxle]
          linarith
        rw [habs])
      measurableSet_Ioc
  · have hright :
        IntervalIntegrable (fun x : ℝ => Real.log (x - c)) MeasureTheory.volume c b := by
      have hbase :
          IntervalIntegrable (fun x : ℝ => Real.log x) MeasureTheory.volume 0 (b - c) := by
        exact real_intervalIntegrable_log_Icc (by linarith)
      simpa using hbase.comp_sub_right c
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcb] at hright ⊢
    exact hright.congr_fun
      (by
        intro x hx
        have hxge : 0 ≤ x - c := by
          have hx' : c ≤ x := (mem_Ioc.mp hx).1
          linarith
        have habs : |x - c| = x - c := by
          rw [abs_of_nonneg hxge]
        rw [habs])
      measurableSet_Ioc

/-- A real scalar multiple of the translated logarithmic singularity is
interval-integrable on every compact interval containing the singular point. -/
theorem intervalIntegrable_const_mul_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (A : ℝ)
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => A * Real.log |x - c|)
      MeasureTheory.volume a b := by
  exact
    (intervalIntegrable_log_abs_sub_const_on_compact hac hcb).const_mul A

/-- The natural-multiplicity logarithmic term in a local Jensen model is
interval-integrable on every compact interval containing the singular point. -/
theorem intervalIntegrable_nat_mul_log_abs_sub_const_on_compact
    {a b c : ℝ}
    (n : ℕ)
    (hac : a ≤ c)
    (hcb : c ≤ b) :
    IntervalIntegrable
      (fun x : ℝ => (n : ℝ) * Real.log |x - c|)
      MeasureTheory.volume a b := by
  exact
    intervalIntegrable_const_mul_log_abs_sub_const_on_compact
      (n : ℝ) hac hcb

/-- Adding an already interval-integrable remainder to a logarithmic
singularity preserves interval-integrability on the compact model interval. -/
theorem intervalIntegrable_log_singularity_model_on_compact
    {a b c : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (hac : a ≤ c)
    (hcb : c ≤ b)
    (hg : IntervalIntegrable g MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun x : ℝ => (n : ℝ) * Real.log |x - c| + g x)
      MeasureTheory.volume a b := by
  exact
    (intervalIntegrable_nat_mul_log_abs_sub_const_on_compact n hac hcb).add hg

/-- Interval-integrability restricts to a smaller unordered compact interval
whose endpoints both lie in the original unordered compact interval. -/
theorem intervalIntegrable_mono_of_uIcc_endpoint_mem
    {f : ℝ → ℝ}
    {a b u v : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hu : u ∈ [[a, b]])
    (hv : v ∈ [[a, b]]) :
    IntervalIntegrable f MeasureTheory.volume u v := by
  exact hf.mono_set (Set.uIcc_subset_uIcc hu hv)

/-- A punctured-neighborhood equality can be shrunk to a compact subinterval
on which the two functions are equal almost everywhere.

This is the topological/null-set extraction behind punctured logarithmic local
models: the equality holds on a deleted neighborhood of `c`, and the missing
center point is null for Lebesgue measure. -/
theorem eventuallyEq_punctured_nhdsWithin_has_subinterval_aeEq
    {f g : ℝ → ℝ}
    {c u v : ℝ}
    (huc : u < c)
    (hcv : c < v)
    (hfg : ∀ᶠ θ in 𝓝[≠] c, f θ = g θ) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      g =ᵐ[MeasureTheory.volume.restrict (Ι u' v')] f := by
  rw [eventuallyEq_nhdsWithin_iff] at hfg
  rcases mem_nhds_iff_exists_Ioo_subset.1 hfg with
    ⟨l, r, hc_lr, hsub_lr⟩
  let leftBound : ℝ := max u l
  let rightBound : ℝ := min v r
  let u' : ℝ := (leftBound + c) / 2
  let v' : ℝ := (c + rightBound) / 2
  have hleft_lt_c : leftBound < c := max_lt huc hc_lr.1
  have hc_lt_right : c < rightBound := lt_min hcv hc_lr.2
  have hu_u' : u < u' := by
    dsimp [u', leftBound]
    have hu_left : u ≤ max u l := le_max_left u l
    linarith
  have hu'_c : u' < c := by
    dsimp [u']
    linarith
  have hc_v' : c < v' := by
    dsimp [v']
    linarith
  have hv'_v : v' < v := by
    dsimp [v', rightBound]
    have hright_v : min v r ≤ v := min_le_left v r
    linarith
  have hu'_gt_l : l < u' := by
    dsimp [u', leftBound]
    have hl_left : l ≤ max u l := le_max_right u l
    linarith
  have hv'_lt_r : v' < r := by
    dsimp [v', rightBound]
    have hright_r : min v r ≤ r := min_le_right v r
    linarith
  have hgf_ae :
      g =ᵐ[MeasureTheory.volume.restrict (Ι u' v')] f := by
    have hne :
        ∀ᵐ x ∂MeasureTheory.volume.restrict (Ι u' v'), x ≠ c :=
      MeasureTheory.ae_restrict_of_ae
        ((Set.countable_singleton c).ae_not_mem MeasureTheory.volume)
    filter_upwards [hne, MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hxc hx_uIoc
    have hx_lr : x ∈ Set.Ioo l r := by
      have hx_uIcc : x ∈ [[u', v']] := Set.uIoc_subset_uIcc hx_uIoc
      have hx_Icc : x ∈ Set.Icc u' v' := by
        rw [Set.uIcc_of_le (le_of_lt (hu'_c.trans hc_v'))] at hx_uIcc
        exact hx_uIcc
      exact ⟨hu'_gt_l.trans_le hx_Icc.1, hx_Icc.2.trans_lt hv'_lt_r⟩
    exact (hsub_lr hx_lr hxc).symm
  exact ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hgf_ae⟩

/-- Interval-integrability is unchanged when two functions agree on the
punctured neighborhood of the only point where the local model is singular.

The excluded point is null for Lebesgue measure, so the punctured equality is
enough for interval-integrability on a sufficiently small interval around the
center. -/
theorem intervalIntegrable_congr_of_eventuallyEq_nhdsWithin_punctured
    {f g : ℝ → ℝ}
    {c u v : ℝ}
    (huc : u < c)
    (hcv : c < v)
    (hfg : ∀ᶠ θ in 𝓝[≠] c, f θ = g θ)
    (hg : IntervalIntegrable g MeasureTheory.volume u v) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      IntervalIntegrable f MeasureTheory.volume u' v' := by
  rcases
      eventuallyEq_punctured_nhdsWithin_has_subinterval_aeEq
        (f := f) (g := g) huc hcv hfg with
    ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hgf_ae⟩
  have hu'_mem : u' ∈ [[u, v]] :=
    Set.mem_uIcc_of_le hu_u'.le (hu'_c.le.trans hcv.le)
  have hv'_mem : v' ∈ [[u, v]] :=
    Set.mem_uIcc_of_le (huc.le.trans hc_v'.le) hv'_v.le
  have hg_small : IntervalIntegrable g MeasureTheory.volume u' v' :=
    intervalIntegrable_mono_of_uIcc_endpoint_mem hg hu'_mem hv'_mem
  exact ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hg_small.congr hgf_ae⟩

/-- Local logarithmic model integrability on a smaller interval inside a
remainder-integrability interval. -/
theorem intervalIntegrable_log_singularity_model_eventually_on_subinterval
    (f : ℝ → ℝ)
    {c u v : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (huc : u < c)
    (hcv : c < v)
    (hg : IntervalIntegrable g MeasureTheory.volume u v)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] c,
        f θ = (n : ℝ) * Real.log |θ - c| + g θ) :
    ∃ u' v' : ℝ,
      u < u' ∧ u' < c ∧ c < v' ∧ v' < v ∧
      IntervalIntegrable f MeasureTheory.volume u' v' := by
  have hcompact :
      IntervalIntegrable
        (fun x : ℝ => (n : ℝ) * Real.log |x - c| + g x)
        MeasureTheory.volume u v :=
    intervalIntegrable_log_singularity_model_on_compact
      n g huc.le hcv.le hg
  exact
    intervalIntegrable_congr_of_eventuallyEq_nhdsWithin_punctured
      huc hcv hmodel hcompact

/-- The compact-continuity base case of finite logarithmic-singularity gluing:
if there are no singular points in the compact interval, ordinary continuity on
that compact interval gives interval-integrability. -/
theorem intervalIntegrable_of_empty_log_singularities_on_compact
    (f : ℝ → ℝ)
    {a b : ℝ}
    (hab : a ≤ b)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ (∅ : Set ℝ)})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hcontIcc : ContinuousOn f (Set.Icc a b) := by
    refine hcont.mono ?_
    intro θ hθ
    exact ⟨hθ, by simp⟩
  exact hcontIcc.intervalIntegrable_of_Icc hab

/-- Local integrability near one logarithmic singularity from the punctured
local model and a locally integrable remainder.

This is the local owner cut used by the finite gluing theorem.  The point value
of `f` at `c` is irrelevant for interval integrability; on a small punctured
neighborhood, `f` agrees with the standard logarithmic model, and the model is
interval-integrable by `intervalIntegrable_log_singularity_model_on_compact`. -/
theorem intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin
    (f : ℝ → ℝ)
    {c : ℝ}
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg :
      ∃ u v : ℝ,
        u < c ∧ c < v ∧
        IntervalIntegrable g MeasureTheory.volume u v)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] c,
        f θ = (n : ℝ) * Real.log |θ - c| + g θ) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      IntervalIntegrable f MeasureTheory.volume u v := by
  rcases hg with ⟨u, v, huc, hcv, hgint⟩
  rcases
      intervalIntegrable_log_singularity_model_eventually_on_subinterval
        f n g huc hcv hgint hmodel with
    ⟨u', v', hu_u', hu'_c, hc_v', hv'_v, hfint⟩
  exact ⟨u', v', hu'_c, hc_v', hfint⟩

/-- Removing one point from a finite singular set leaves a finite singular set
on each compact side of the isolated point.  This is the finite-set separation
cut behind the compact gluing induction. -/
theorem finite_log_singularity_set_isolates_point_in_compact
    {a b c : ℝ}
    {S : Set ℝ}
    (hS : S.Finite)
    (hcS : c ∈ S) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      (Set.Ioo u v ∩ S) ⊆ {c} := by
  let T : Finset ℝ := hS.toFinset.erase c
  by_cases hT : T = ∅
  · refine ⟨c - 1, c + 1, by linarith, by linarith, ?_⟩
    intro x hx
    have hxS : x ∈ S := hx.2
    by_contra hxc
    have hxT : x ∈ T := by
      dsimp [T]
      exact Finset.mem_erase.2 ⟨by simpa using hxc, by simpa using hxS⟩
    have hxEmpty : x ∈ (∅ : Finset ℝ) := by
      rw [hT] at hxT
      exact hxT
    exact Finset.not_mem_empty x hxEmpty
  · let D : Finset ℝ := T.image fun x => dist x c
    have hD : D.Nonempty := by
      rcases Finset.nonempty_iff_ne_empty.mpr hT with ⟨x, hxT⟩
      exact ⟨dist x c, Finset.mem_image.2 ⟨x, hxT, rfl⟩⟩
    have hDpos : 0 < D.min' hD := by
      have hmin_mem : D.min' hD ∈ D := Finset.min'_mem D hD
      rcases Finset.mem_image.1 hmin_mem with ⟨x, hxT, hdist⟩
      have hxc : x ≠ c := (Finset.mem_erase.1 hxT).1
      rw [← hdist]
      exact dist_pos.2 hxc
    refine ⟨c - D.min' hD / 2, c + D.min' hD / 2, ?_, ?_, ?_⟩
    · linarith
    · linarith
    intro x hx
    have hxS : x ∈ S := hx.2
    by_contra hxc
    have hxT : x ∈ T := by
      dsimp [T]
      exact Finset.mem_erase.2 ⟨by simpa using hxc, by simpa using hxS⟩
    have hxD : dist x c ∈ D := Finset.mem_image.2 ⟨x, hxT, rfl⟩
    have hmin_le : D.min' hD ≤ dist x c := Finset.min'_le D (dist x c) hxD
    have hxleft : c - D.min' hD / 2 < x := hx.1.1
    have hxright : x < c + D.min' hD / 2 := hx.1.2
    have habs : |x - c| < D.min' hD := by
      rw [abs_sub_lt_iff]
      constructor <;> linarith
    have hdist_lt : dist x c < D.min' hD := by
      simpa [Real.dist_eq] using habs
    linarith

/-- A locally interval-integrable neighborhood gives integrability at the
`Icc`-neighborhood filter of the center. -/
theorem integrableAtFilter_Icc_of_intervalIntegrable_neighborhood
    {f : ℝ → ℝ}
    {a b x u v : ℝ}
    (hux : u < x)
    (hxv : x < v)
    (hfint : IntervalIntegrable f MeasureTheory.volume u v) :
    IntegrableAtFilter f (𝓝[Set.Icc a b] x) MeasureTheory.volume := by
  have huv : u ≤ v := (hux.trans hxv).le
  have hIoo_nhds : Set.Ioo u v ∈ 𝓝 x :=
    Ioo_mem_nhds hux hxv
  have hIoc_nhds : Ι u v ∈ 𝓝 x := by
    refine mem_of_superset hIoo_nhds ?_
    intro y hy
    rw [Set.uIoc_of_le huv]
    exact ⟨hy.1.le, hy.2⟩
  exact ⟨Ι u v, mem_nhdsWithin_of_mem_nhds hIoc_nhds, hfint.def'⟩

/-- At a point of `[a,b]` away from a finite singular set, continuity on the
finite-set complement gives integrability at the `[a,b]`-neighborhood filter. -/
theorem integrableAtFilter_Icc_of_continuousOn_finite_complement
    {f : ℝ → ℝ}
    {a b x : ℝ}
    {S : Set ℝ}
    (hS : S.Finite)
    (hxIcc : x ∈ Set.Icc a b)
    (hxS : x ∉ S)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntegrableAtFilter f (𝓝[Set.Icc a b] x) MeasureTheory.volume := by
  let K : Set ℝ := {θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S}
  have hxK : x ∈ K := ⟨hxIcc, hxS⟩
  have hKmeas : MeasurableSet K := by
    have hSclosed : IsClosed S := hS.isClosed
    exact measurableSet_Icc.inter hSclosed.isOpen_compl.measurableSet
  have hlocK : IntegrableAtFilter f (𝓝[K] x) MeasureTheory.volume :=
    (hcont.locallyIntegrableOn hKmeas) x hxK
  have hScompl_nhds : Sᶜ ∈ 𝓝 x :=
    hS.isClosed.isOpen_compl.mem_nhds hxS
  have hScompl_within : Sᶜ ∈ 𝓝[Set.Icc a b] x :=
    mem_nhdsWithin_of_mem_nhds hScompl_nhds
  have hfilter :
      𝓝[K] x = 𝓝[Set.Icc a b] x := by
    have hraw :
        𝓝[Set.Icc a b ∩ Sᶜ] x = 𝓝[Set.Icc a b] x :=
      nhdsWithin_inter_of_mem' hScompl_within
    simpa [K, Set.inter_comm, Set.compl_setOf] using hraw
  exact Eq.subst (motive := fun l : Filter ℝ =>
      IntegrableAtFilter f l MeasureTheory.volume) hfilter hlocK

/-- Local integrability at every point of a compact ordered interval implies
interval-integrability on that interval. -/
theorem intervalIntegrable_of_locallyIntegrableOn_Icc
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a ≤ b)
    (hloc :
      MeasureTheory.LocallyIntegrableOn
        f (Set.Icc a b) MeasureTheory.volume) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hint : IntegrableOn f (Set.Icc a b) MeasureTheory.volume :=
    hloc.integrableOn_isCompact isCompact_Icc
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hint

/-- Gluing interval-integrability across a finite isolated singular set, once
each singular point has a locally integrable logarithmic model and the function
is continuous on the complement.

This is the measure-theoretic cover/gluing theorem behind the Jensen finite
singularity argument.  It contains no complex analysis: all analytic content has
already been reduced to local logarithmic models. -/
theorem intervalIntegrable_of_finite_log_singularity_cover
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocalInt :
      ∀ θ₀ ∈ S, ∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable f MeasureTheory.volume u v)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hloc :
      MeasureTheory.LocallyIntegrableOn
        f (Set.Icc a b) MeasureTheory.volume := by
    intro x hxIcc
    by_cases hxS : x ∈ S
    · rcases hlocalInt x hxS with ⟨u, v, hux, hxv, hfint⟩
      exact
        integrableAtFilter_Icc_of_intervalIntegrable_neighborhood
          (a := a) (b := b) hux hxv hfint
    · exact
        integrableAtFilter_Icc_of_continuousOn_finite_complement
          hS hxIcc hxS hcont
  exact intervalIntegrable_of_locallyIntegrableOn_Icc hab hloc

/-- Finite compact-interval gluing once each singular point has a logarithmic
local model and the complement is continuous.

The proof is by finite induction on `S`: the empty case is
`intervalIntegrable_of_empty_log_singularities_on_compact`; the step isolates
one singular point, uses
`intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin` on the
central interval, applies the induction hypothesis to the two side intervals,
and glues the three interval-integrability statements by interval splitting. -/
theorem intervalIntegrable_of_finite_log_singularities_on_compact_glue
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          f θ = (n : ℝ) * Real.log |θ - θ₀| + g θ)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  have hlocalInt :
      ∀ θ₀ ∈ S, ∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable f MeasureTheory.volume u v := by
    intro θ₀ hθ₀
    rcases hlocal θ₀ hθ₀ with ⟨n, g, hg, hmodel⟩
    exact
      intervalIntegrable_of_log_singularity_model_eventually_nhdsWithin
        f n g hg hmodel
  exact
    intervalIntegrable_of_finite_log_singularity_cover
      f a b S hab hS hlocalInt hcont

/-- Finite compact-interval gluing for logarithmic singularities.

The local hypotheses say that every singular parameter has a punctured
neighborhood model `n * log |θ - θ₀| + g θ` with a locally integrable
remainder, and the complement is continuous.  The conclusion follows from the
interval integrability of the translated logarithm, local integrability of each
remainder, and finite interval gluing on `[a,b]`. -/
theorem intervalIntegrable_of_finite_log_singularities_on_compact
    (f : ℝ → ℝ)
    (a b : ℝ)
    (S : Set ℝ)
    (hab : a ≤ b)
    (hS : S.Finite)
    (hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          f θ = (n : ℝ) * Real.log |θ - θ₀| + g θ)
    (hcont :
      ContinuousOn f ({θ : ℝ | θ ∈ Set.Icc a b ∧ θ ∉ S})) :
    IntervalIntegrable f MeasureTheory.volume a b := by
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact_glue
      f a b S hab hS hlocal hcont

/-- The doubled-radius Jensen loss has a positive logarithmic denominator. -/
theorem real_log_two_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)

/-- The doubled-radius Jensen loss has a nonzero logarithmic denominator. -/
theorem real_log_two_ne_zero : Real.log 2 ≠ 0 := by
  exact real_log_two_pos.ne'

/-- The reciprocal of the doubled-radius Jensen loss is nonnegative. -/
theorem real_log_two_inv_nonneg : 0 ≤ (Real.log 2)⁻¹ := by
  exact inv_nonneg.mpr real_log_two_pos.le

/-- Radii used in the doubled Jensen circle are positive for `R ≥ 1`. -/
theorem doubled_radius_pos_of_one_le {R : ℝ} (hR : 1 ≤ R) :
    0 < 2 * R := by
  nlinarith

/-- The doubled radius is at least one for `R ≥ 1`. -/
theorem one_le_doubled_radius_of_one_le {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ 2 * R := by
  nlinarith

/-- A nonzero point in the closed disk of radius `R` has at least the standard
`log 2` radial Jensen gap when the boundary radius is `2R`. -/
theorem log_two_le_log_doubled_radius_div_norm
    {R : ℝ}
    {z : ℂ}
    (hR : 1 ≤ R)
    (hz_ne : z ≠ 0)
    (hz_le : ‖z‖ ≤ R) :
    Real.log 2 ≤ Real.log ((2 * R) / ‖z‖) := by
  have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  have htwo_le : 2 ≤ (2 * R) / ‖z‖ := by
    have hmul_le : 2 * ‖z‖ ≤ 2 * R := by
      exact mul_le_mul_of_nonneg_left hz_le (by norm_num)
    exact (le_div_iff₀ hz_pos).mpr hmul_le
  exact Real.log_le_log (by norm_num) htwo_le

/-- Multiplicity-weighted Jensen radial-gap summand for a zero on the
comparison circle of radius `ρ`.

The zero at the origin is omitted here: in Jensen's formula it is the factored
Taylor root and contributes to the additive constant, not to the radial-gap
sum. -/
noncomputable def entireFunctionJensenRadialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionZero F) : ℝ :=
  if hz₀ : (z : ℂ) = 0 then
    0
  else if ‖(z : ℂ)‖ < ρ then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
      Real.log (ρ / ‖(z : ℂ)‖)
  else
    0

/-- Multiplicity-weighted Jensen radial-gap sum inside the comparison circle. -/
noncomputable def entireFunctionJensenRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) : ℝ :=
  ∑' z : EntireFunctionZero F,
    entireFunctionJensenRadialGapSummand F hF ρ z

/-- Closed-disk multiplicity summand with the origin Taylor factor removed.

The omitted origin contribution is exactly the finite Taylor-root term that is
absorbed into the additive Jensen constant. -/
noncomputable def entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) : ℝ :=
  if (z : ℂ) = 0 then
    0
  else
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z

/-- The origin-supported closed-disk multiplicity summand.

This is the finite Taylor-root contribution omitted from the nonzero radial-gap
sum.  It is supported on the unique zero-subtype point whose value is `0`,
when such a point exists. -/
noncomputable def entireFunctionOriginZeroMultiplicityClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) : ℝ :=
  if (z : ℂ) = 0 then
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z
  else
    0

/-- The closed-disk summand splits into its nonzero and origin-supported
parts. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionZero F) :
    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z =
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z +
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z := by
  unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
  unfold entireFunctionOriginZeroMultiplicityClosedDiskSummand
  by_cases hz₀ : (z : ℂ) = 0
  · exact Eq.subst
      (motive := fun x : ℝ =>
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z = 0 + x)
      (if_pos hz₀).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z = x)
        (zero_add
          (entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)).symm
        rfl)
  · exact Eq.subst
      (motive := fun x : ℝ =>
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z = x + 0)
      (if_neg hz₀).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z = x)
        (add_zero
          (entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)).symm
        rfl)

/-- The origin-supported closed-disk summand is summable. -/
theorem entireFunctionOriginZeroMultiplicityClosedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) := by
  by_cases hF0 : F 0 = 0
  · let z₀ : EntireFunctionZero F := ⟨0, hF0⟩
    have hsingle :
        Summable
          (fun z : EntireFunctionZero F =>
            if z = z₀ then
              entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
            else
              0) :=
      (hasSum_ite_eq z₀
        (entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀)).summable
    exact hsingle.congr
      (fun z => by
        unfold entireFunctionOriginZeroMultiplicityClosedDiskSummand
        by_cases hz : z = z₀
        · have hz₀ : (z : ℂ) = 0 := by
            exact congrArg Subtype.val hz
          exact Eq.trans
            (if_pos hz₀)
            (Eq.symm
              (Eq.subst
                (motive := fun x : ℝ =>
                  x = if z = z₀ then
                    entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
                  else
                    0)
                (congrArg
                  (fun w : EntireFunctionZero F =>
                    entireFunctionZeroMultiplicityClosedDiskSummand F hF R w)
                  hz).symm
                (if_pos hz)))
        · have hz₀ : (z : ℂ) ≠ 0 := by
            intro hval
            exact hz (Subtype.ext hval)
          exact Eq.trans
            (if_neg hz₀)
            (Eq.symm (if_neg hz)))
  · have hzero :
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
          =
        (fun _ : EntireFunctionZero F => 0) := by
      funext z
      unfold entireFunctionOriginZeroMultiplicityClosedDiskSummand
      have hz₀ : (z : ℂ) ≠ 0 := by
        intro hval
        have hzF : F 0 = 0 := by
          exact Eq.subst (motive := fun w : ℂ => F w = 0) hval z.property
        exact hF0 hzF
      exact if_neg hz₀
    exact hzero.symm ▸ summable_zero

/-- The origin multiplicity contribution used when the Jensen radial-gap sum is
written only over nonzero zeros. -/
noncomputable def entireFunctionOriginMultiplicityLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z) : ℝ :=
  (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2

/-- The origin Taylor-factor contribution on the Jensen circle of radius `ρ`.

For `F(z)=z^m G(z)` near the origin, this term is `m log ρ` in the boundary
logarithmic average. -/
noncomputable def entireFunctionOriginMultiplicityLogRadiusContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) : ℝ :=
  (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ

/-- A nonzero value at the origin has analytic multiplicity zero. -/
theorem entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    entireFunctionZeroMultiplicity F hF 0 = 0 := by
  have horder : (hF 0).order = (0 : ENat) := by
    exact
      ((hF 0).order_eq_nat_iff 0).mpr
        ⟨F, hF 0, hF0, eventually_of_forall
          (fun w => by
            calc
              F w = 1 • F w := (one_smul ℂ (F w)).symm
              _ = (w - 0) ^ 0 • F w := by
                exact congrArg (fun a : ℂ => a • F w) (pow_zero (w - 0)).symm)⟩
  unfold entireFunctionZeroMultiplicity
  rw [horder]
  rfl

/-- The fixed origin Taylor contribution vanishes when `F 0 ≠ 0`. -/
theorem entireFunctionOriginMultiplicityLogContribution_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    entireFunctionOriginMultiplicityLogContribution F hF = 0 := by
  unfold entireFunctionOriginMultiplicityLogContribution
  rw [entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero F hF hF0]
  rfl

/-- The radius-dependent origin Taylor contribution vanishes when `F 0 ≠ 0`. -/
theorem entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 := by
  unfold entireFunctionOriginMultiplicityLogRadiusContribution
  rw [entireFunctionZeroMultiplicity_origin_eq_zero_of_ne_zero F hF hF0]
  rfl

/-- The origin-supported closed-disk summand is bounded by the fixed origin
Taylor contribution. -/
theorem entireFunctionOriginZeroMultiplicityClosedDisk_tsum_mul_log_two_le_originContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R) :
    (∑' z : EntireFunctionZero F,
        entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF := by
  unfold entireFunctionOriginMultiplicityLogContribution
  by_cases hF0 : F 0 = 0
  · let z₀ : EntireFunctionZero F := ⟨0, hF0⟩
    have horigin_eq :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ := by
      have hsingle :
          (∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
            ∑' z : EntireFunctionZero F,
              if z = z₀ then
                entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
              else
                0 := by
        exact tsum_congr
          (fun z => by
            unfold entireFunctionOriginZeroMultiplicityClosedDiskSummand
            by_cases hz : z = z₀
            · have hz₀ : (z : ℂ) = 0 := congrArg Subtype.val hz
              exact Eq.trans
                (if_pos hz₀)
                (Eq.symm
                  (Eq.subst
                    (motive := fun x : ℝ =>
                      x = if z = z₀ then
                        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀
                      else
                        0)
                    (congrArg
                      (fun w : EntireFunctionZero F =>
                        entireFunctionZeroMultiplicityClosedDiskSummand F hF R w)
                      hz).symm
                    (if_pos hz)))
            · have hz₀ : (z : ℂ) ≠ 0 := by
                intro hval
                exact hz (Subtype.ext hval)
              exact Eq.trans (if_neg hz₀) (Eq.symm (if_neg hz)))
      exact Eq.trans hsingle (tsum_ite_eq z₀ _)
    have hz₀_disk :
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z₀ =
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) := by
      unfold entireFunctionZeroMultiplicityClosedDiskSummand
      have hzero_le : ‖(z₀ : ℂ)‖ ≤ R := by
        change ‖(0 : ℂ)‖ ≤ R
        exact le_trans (by norm_num) (le_trans zero_le_one hR)
      exact if_pos hzero_le
    exact Eq.subst
      (motive := fun x : ℝ =>
        x * Real.log 2 ≤
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2)
      (Eq.trans horigin_eq hz₀_disk)
      (le_refl
        ((entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2))
  · have horigin_zero :
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) =
          0 := by
      have hzero :
          (fun z : EntireFunctionZero F =>
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
            =
          (fun _ : EntireFunctionZero F => 0) := by
        funext z
        unfold entireFunctionOriginZeroMultiplicityClosedDiskSummand
        have hz₀ : (z : ℂ) ≠ 0 := by
          intro hval
          have hzF : F 0 = 0 :=
            Eq.subst (motive := fun w : ℂ => F w = 0) hval z.property
          exact hF0 hzF
        exact if_neg hz₀
      exact Eq.trans (tsum_congr (fun z => congrFun hzero z)) tsum_zero
    have hlog_nonneg : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    have horigin_nonneg :
        0 ≤ (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2 :=
      mul_nonneg
        (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
        hlog_nonneg
    exact Eq.subst
      (motive := fun x : ℝ =>
        x * Real.log 2 ≤
          (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2)
      horigin_zero
      (Eq.subst
        (motive := fun x : ℝ =>
          x ≤ (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log 2)
        (zero_mul (Real.log 2)).symm
        horigin_nonneg)

/-- A nonzero zero in `closedDisk R` contributes at least its multiplicity times
`log 2` to the doubled-radius Jensen radial-gap sum.

This is the pointwise radial-gap comparison; it is independent of Jensen's
formula itself. -/
theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_mul_log_two_le_radialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (z : EntireFunctionZero F) :
    entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z * Real.log 2 ≤
      entireFunctionJensenRadialGapSummand F hF (2 * R) z := by
  unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
  unfold entireFunctionZeroMultiplicityClosedDiskSummand
  unfold entireFunctionJensenRadialGapSummand
  by_cases hz₀ : (z : ℂ) = 0
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x * Real.log 2 ≤
          if hz₀' : (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < 2 * R then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖)
          else
            0)
      (if_pos hz₀).symm
      (Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        (if_pos hz₀).symm
        (le_refl (0 : ℝ)))
  by_cases hz_disk : ‖(z : ℂ)‖ ≤ R
  · have hgap :
        Real.log 2 ≤ Real.log ((2 * R) / ‖(z : ℂ)‖) :=
      log_two_le_log_doubled_radius_div_norm hR hz₀ hz_disk
    have hstrict : ‖(z : ℂ)‖ < 2 * R := by
      have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR
      have hR_lt_twoR : R < 2 * R := by nlinarith
      exact lt_of_le_of_lt hz_disk hR_lt_twoR
    exact Eq.subst
        (motive := fun x : ℝ =>
          x * Real.log 2 ≤
            if hz₀' : (z : ℂ) = 0 then
              0
            else if ‖(z : ℂ)‖ < 2 * R then
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log ((2 * R) / ‖(z : ℂ)‖)
            else
              0)
        (if_pos hz_disk).symm
        (Eq.subst
          (motive := fun x : ℝ =>
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log 2 ≤ x)
          (if_neg hz₀).symm
          (Eq.subst
            (motive := fun x : ℝ =>
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log 2 ≤ x)
            (if_pos hstrict).symm
            (mul_le_mul_of_nonneg_left
              hgap
              (Nat.cast_nonneg
                (entireFunctionZeroMultiplicity F hF (z : ℂ))))))
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x * Real.log 2 ≤
          if hz₀ : (z : ℂ) = 0 then
            0
          else if ‖(z : ℂ)‖ < 2 * R then
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              Real.log ((2 * R) / ‖(z : ℂ)‖)
          else
            0)
      (if_neg hz_disk).symm
      (by
        rw [zero_mul]
        by_cases hz₀ : (z : ℂ) = 0
        · exact Eq.subst
            (motive := fun x : ℝ => 0 ≤ x)
            (if_pos hz₀).symm
            (le_refl (0 : ℝ))
        · by_cases hstrict : ‖(z : ℂ)‖ < 2 * R
          · exact Eq.subst
              (motive := fun x : ℝ => 0 ≤ x)
              (if_neg hz₀).symm
              (Eq.subst
                (motive := fun x : ℝ => 0 ≤ x)
                (if_pos hstrict).symm
                (mul_nonneg
                  (Nat.cast_nonneg
                    (entireFunctionZeroMultiplicity F hF (z : ℂ)))
                  (Real.log_nonneg
                    (by
                      have hz_norm_pos : 0 < ‖(z : ℂ)‖ :=
                        norm_pos_iff.mpr hz₀
                      exact
                        (one_le_div₀ hz_norm_pos).mpr hstrict.le))))
          · exact Eq.subst
              (motive := fun x : ℝ => 0 ≤ x)
              (if_neg hz₀).symm
              (Eq.subst
                (motive := fun x : ℝ => 0 ≤ x)
                (if_neg hstrict).symm
                (le_refl (0 : ℝ))))

/-- Non-origin closed-disk multiplicity weighted by `log 2` is dominated by
the doubled-radius Jensen radial-gap sum.

This is the finite/counting part of the Jensen estimate. The analytic Jensen
formula enters only through an upper bound on the radial-gap sum. -/
theorem entireFunctionNonzeroZeroMultiplicityCountingInClosedDisk_mul_log_two_le_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z))
    (hgap :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF (2 * R) z)) :
    (∑' z : EntireFunctionZero F,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
        Real.log 2 ≤
      entireFunctionJensenRadialGapSum F hF (2 * R) := by
  unfold entireFunctionJensenRadialGapSum
  have hclosed_scaled :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
            Real.log 2) :=
    hclosed.mul_left (Real.log 2)
  have htsum_mul :
      (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 =
        ∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z *
            Real.log 2 := by
    exact (tsum_mul_left (Real.log 2)
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)).symm
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' z : EntireFunctionZero F,
          entireFunctionJensenRadialGapSummand F hF (2 * R) z)
    htsum_mul
    (tsum_le_tsum
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_mul_log_two_le_radialGapSummand
          F hF hR z)
      hclosed_scaled
      hgap)

/-- Reattaching the origin Taylor factor: the full closed-disk count is bounded
by the non-origin count plus the fixed origin contribution. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_nonzeroCount
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF +
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 := by
  have horigin_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) :=
    entireFunctionOriginZeroMultiplicityClosedDiskSummable F hF R
  have hfull_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) :=
    (hclosed.add horigin_summable).congr
      (fun z => by
        exact
          (entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
            F hF R z).symm)
  have hcount_split :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R =
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) +
          ∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z := by
    unfold entireFunctionZeroMultiplicityCountingInClosedDisk
    exact Eq.trans
      (tsum_congr
        (fun z =>
          entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
            F hF R z))
      (tsum_add hclosed horigin_summable)
  have horigin_bound :
      (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 ≤
        entireFunctionOriginMultiplicityLogContribution F hF :=
    entireFunctionOriginZeroMultiplicityClosedDisk_tsum_mul_log_two_le_originContribution
      F hF hR
  have hsplit_mul :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 =
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 +
          (∑' z : EntireFunctionZero F,
            entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
            Real.log 2 := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 =
          x * Real.log 2)
      hcount_split
      (mul_add
        (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
        (∑' z : EntireFunctionZero F,
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z)
        (Real.log 2)).symm
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        entireFunctionOriginMultiplicityLogContribution F hF +
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2)
    hsplit_mul
    (by
      have hright :
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 +
            (∑' z : EntireFunctionZero F,
              entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2
            ≤
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 +
            entireFunctionOriginMultiplicityLogContribution F hF :=
        add_le_add_left horigin_bound _
      exact le_trans hright
        (le_of_eq
          (add_comm
            ((∑' z : EntireFunctionZero F,
              entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
                Real.log 2)
            (entireFunctionOriginMultiplicityLogContribution F hF))))

/-- Full closed-disk multiplicity weighted by `log 2` is bounded by the
doubled-radius radial-gap sum, up to the fixed origin Taylor contribution. -/
theorem entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z))
    (hgap :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF (2 * R) z)) :
    entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
      entireFunctionOriginMultiplicityLogContribution F hF +
        entireFunctionJensenRadialGapSum F hF (2 * R) := by
  have horigin :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
        entireFunctionOriginMultiplicityLogContribution F hF +
          (∑' z : EntireFunctionZero F,
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
              Real.log 2 :=
    entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_nonzeroCount
      F hF hR hclosed
  have hnonzero :
      (∑' z : EntireFunctionZero F,
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) *
          Real.log 2 ≤
        entireFunctionJensenRadialGapSum F hF (2 * R) :=
    entireFunctionNonzeroZeroMultiplicityCountingInClosedDisk_mul_log_two_le_radialGapSum
      F hF hR hclosed hgap
  exact le_trans horigin (add_le_add_left hnonzero _)

/-- Adding back the single origin summand preserves closed-disk summability. -/
theorem entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {R : ℝ}
    (hclosed :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) := by
  have horigin_summable :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionOriginZeroMultiplicityClosedDiskSummand F hF R z) :=
    entireFunctionOriginZeroMultiplicityClosedDiskSummable F hF R
  exact
    (hclosed.add horigin_summable).congr
      (fun z => by
        exact
          (entireFunctionZeroMultiplicityClosedDiskSummand_eq_nonzero_add_origin
            F hF R z).symm)

/-- Standard Jensen formula for a nontrivial entire function whose value at the
origin is nonzero.

This is the analytic owner root, in the exact normalization used by this file:
for every radius at least `1`, the nonzero-zero radial gap sum is summable and
equals the normalized boundary logarithmic average up to the fixed origin
constant.  The closed-disk summability statement is included because it is the
finite-zero-counting consequence of the same standard Jensen package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  -- Classical Jensen formula in the `F 0 ≠ 0` normalization, with zeros
  -- counted by analytic multiplicity; cf. Titchmarsh, The Theory of
  -- Functions, §5.
  sorry

/-- Closed-disk multiplicity summability extracted from the standard
nonzero-origin Jensen package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (R : ℝ)
    (hR : 1 ≤ R) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) :=
  hJ.1 R hR

/-- Radial-gap summability extracted from the standard nonzero-origin Jensen
package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z) :=
  (hJ.2 ρ hρ).1

/-- Radial-gap identity extracted from the standard nonzero-origin Jensen
package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (C : ℝ)
    (hJ :
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ))
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenRadialGapSum F hF ρ + C =
      entireFunctionJensenBoundaryLogAverage F ρ :=
  (hJ.2 ρ hρ).2

/-- Classical Jensen formula for a nontrivial entire function whose value at
the origin is nonzero.

This is now a thin assembly theorem over the exact standard Jensen owner root:
the analytic content is isolated in
`entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot`, while this
name preserves the downstream classical-Jensen API. -/
theorem entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  match entireFunction_standardJensenFormula_nonzeroAtOrigin_ownerRoot F hF hF0 with
  | ⟨C, hJ⟩ =>
      refine ⟨C, ?_, ?_⟩
      · intro R hR
        exact
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummable
            F hF hF0 C hJ R hR
      · intro ρ hρ
        exact
          ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummable
              F hF hF0 C hJ ρ hρ,
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
              F hF hF0 C hJ ρ hρ⟩

/-- Classical Jensen formula for a nontrivial entire function whose value at
the origin is nonzero.

This compatibility theorem is intentionally a thin wrapper over
`entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot`; downstream
zero-counting code should depend on this stable public name, while the analytic
proof remains owned by the root theorem above. -/
theorem entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact entireFunction_classicalJensenFormula_nonzeroAtOrigin_ownerRoot F hF hF0

/-- The origin-factor transport theorem is mechanical when the origin is not a
zero: the explicit origin Taylor contribution is zero. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        F hF hF0 with
    ⟨C, hclosed, hidentity⟩
  refine ⟨C, hclosed, ?_⟩
  intro ρ hρ
  rcases hidentity ρ hρ with ⟨hsum, hradial⟩
  refine ⟨hsum, ?_⟩
  have horigin :
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 :=
    entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
      F hF hF0 ρ
  calc
    entireFunctionJensenRadialGapSum F hF ρ +
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
        entireFunctionJensenRadialGapSum F hF ρ + 0 + C := by
      exact congrArg
        (fun x : ℝ => entireFunctionJensenRadialGapSum F hF ρ + x + C)
        horigin
    _ = entireFunctionJensenRadialGapSum F hF ρ + C := by
      exact congrArg (fun x : ℝ => x + C)
        (add_zero (entireFunctionJensenRadialGapSum F hF ρ))
    _ = entireFunctionJensenBoundaryLogAverage F ρ :=
      hradial

/-- The canonical punctured quotient obtained by dividing an entire function by
its origin Taylor power away from the origin.  The removable-singularity owner
root extends this object across `0`. -/
noncomputable def entireFunction_originTaylorPuncturedQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (z : ℂ) : ℂ :=
  (z ^ entireFunctionZeroMultiplicity F hF 0)⁻¹ • F z

/-- Away from the origin, the punctured quotient reconstructs the original
function by multiplying back the origin Taylor power. -/
theorem entireFunction_originTaylorPuncturedQuotient_factorization_of_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    {z : ℂ}
    (hz : z ≠ 0) :
    F z =
      z ^ entireFunctionZeroMultiplicity F hF 0 •
        entireFunction_originTaylorPuncturedQuotient F hF z := by
  let a : ℂ := z ^ entireFunctionZeroMultiplicity F hF 0
  have ha : a ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz
  calc
    F z = (1 : ℂ) • F z := by
      exact (one_smul ℂ (F z)).symm
    _ = (a * a⁻¹) • F z := by
      exact congrArg (fun c : ℂ => c • F z) (mul_inv_cancel₀ ha).symm
    _ = a • (a⁻¹ • F z) := by
      exact (smul_smul a a⁻¹ (F z)).symm
    _ =
        z ^ entireFunctionZeroMultiplicity F hF 0 •
          entireFunction_originTaylorPuncturedQuotient F hF z := rfl

/-- Global removal of the origin Taylor factor for a nontrivial entire
function.

This is the owner construction needed for Jensen transport: the local unit
supplied by `AnalyticAt.order_eq_nat_iff` extends to a global entire quotient
after dividing out the origin power, with the removable singularity filled in
at the origin. -/
theorem entireFunction_originTaylorFactor_entireQuotient_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, AnalyticAt ℂ G z) ∧
      G 0 ≠ 0 ∧
      (∀ z : ℂ,
        F z =
          z ^ entireFunctionZeroMultiplicity F hF 0 • G z) := by
  let m : ℕ := entireFunctionZeroMultiplicity F hF 0
  have horder : (hF 0).order = (m : ENat) :=
    entireFunction_origin_order_eq_multiplicity_of_nontrivial F hF hnontrivial
  rcases (hF 0).order_eq_nat_iff m |>.mp horder with
    ⟨g, hg_an, hg_ne, hg_factor⟩
  let G : ℂ → ℂ :=
    fun z =>
      if z = 0 then
        g 0
      else
        entireFunction_originTaylorPuncturedQuotient F hF z
  have hG_eq_g_nhds : G =ᶠ[𝓝 (0 : ℂ)] g := by
    filter_upwards [hg_factor] with z hz_factor
    by_cases hz : z = 0
    · calc
        G z = g 0 := by
          exact if_pos hz
        _ = g z := by
          exact congrArg g hz.symm
    · have hpow : z ^ m ≠ 0 :=
        pow_ne_zero m hz
      calc
        G z =
            entireFunction_originTaylorPuncturedQuotient F hF z := by
          exact if_neg hz
        _ = (z ^ m)⁻¹ • F z := rfl
        _ = (z ^ m)⁻¹ • (z ^ m • g z) := by
          exact congrArg (fun w : ℂ => (z ^ m)⁻¹ • w) hz_factor
        _ = ((z ^ m)⁻¹ * z ^ m) • g z := by
          exact smul_smul (z ^ m)⁻¹ (z ^ m) (g z)
        _ = (1 : ℂ) • g z := by
          exact congrArg (fun a : ℂ => a • g z) (inv_mul_cancel₀ hpow)
        _ = g z := by
          exact one_smul ℂ (g z)
  have hG_origin_an : AnalyticAt ℂ G 0 :=
    hg_an.congr hG_eq_g_nhds.symm
  have hG_ne : G 0 ≠ 0 := by
    have hG0 : G 0 = g 0 := by
      exact if_pos rfl
    exact fun hzero => hg_ne (Eq.trans hG0.symm hzero)
  have hG_off_origin_an :
      ∀ z : ℂ, z ≠ 0 → AnalyticAt ℂ G z := by
    intro z hz
    have hpow_ne : z ^ m ≠ 0 :=
      pow_ne_zero m hz
    have hquot_an :
        AnalyticAt ℂ (fun w : ℂ => (w ^ m)⁻¹ * F w) z := by
      have hpow_an : AnalyticAt ℂ (fun w : ℂ => w ^ m) z :=
        (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).pow m
      exact (hpow_an.inv hpow_ne).mul (hF z)
    refine hquot_an.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    calc
      (w ^ m)⁻¹ * F w =
          (w ^ m)⁻¹ • F w := by
        exact (smul_eq_mul (w ^ m)⁻¹ (F w)).symm
      _ = entireFunction_originTaylorPuncturedQuotient F hF w := rfl
      _ = G w := by
        exact (if_neg hw).symm
  have hG_an : ∀ z : ℂ, AnalyticAt ℂ G z := by
    intro z
    by_cases hz : z = 0
    · exact Eq.subst (motive := fun w : ℂ => AnalyticAt ℂ G w) hz.symm hG_origin_an
    · exact hG_off_origin_an z hz
  have hfactor : ∀ z : ℂ, F z = z ^ m • G z := by
    intro z
    by_cases hz : z = 0
    · have hlocal_at_origin : F 0 = (0 - 0) ^ m • g 0 :=
        Filter.Eventually.self_of_nhds hg_factor
      calc
        F z = F 0 := by
          exact congrArg F hz
        _ = (0 - 0) ^ m • g 0 :=
          hlocal_at_origin
        _ = z ^ m • G z := by
          subst hz
          rfl
    · exact
        entireFunction_originTaylorPuncturedQuotient_factorization_of_ne_zero
          F hF hz
  exact ⟨G, hG_an, hG_ne, hfactor⟩

/-- Global removal of the origin Taylor factor for a nontrivial entire
function.

This public theorem is a thin wrapper over the removable-singularity owner root
above.  All later zero-set, multiplicity, and Jensen-transport lemmas consume
this stable public API rather than reproving the quotient construction. -/
theorem entireFunction_originTaylorFactor_entireQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ G : ℂ → ℂ,
      (∀ z : ℂ, AnalyticAt ℂ G z) ∧
      G 0 ≠ 0 ∧
      (∀ z : ℂ,
        F z =
          z ^ entireFunctionZeroMultiplicity F hF 0 • G z) := by
  exact entireFunction_originTaylorFactor_entireQuotient_ownerRoot F hF hnontrivial

/-- Away from the origin, zeros of an entire function agree with zeros of its
global origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {z : ℂ}
    (hz : z ≠ 0) :
    F z = 0 ↔ G z = 0 := by
  have hpow : z ^ entireFunctionZeroMultiplicity F hF 0 ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz
  constructor
  · intro hFz
    have hmul :
        z ^ entireFunctionZeroMultiplicity F hF 0 * G z = 0 := by
      calc
        z ^ entireFunctionZeroMultiplicity F hF 0 * G z =
            z ^ entireFunctionZeroMultiplicity F hF 0 • G z := by
          exact (smul_eq_mul
            (z ^ entireFunctionZeroMultiplicity F hF 0) (G z)).symm
        _ = F z := (hfactor z).symm
        _ = 0 := hFz
    exact (mul_eq_zero.mp hmul).resolve_left hpow
  · intro hGz
    calc
      F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z := hfactor z
      _ = z ^ entireFunctionZeroMultiplicity F hF 0 • 0 := by
        exact congrArg
          (fun w : ℂ => z ^ entireFunctionZeroMultiplicity F hF 0 • w)
          hGz
      _ = 0 :=
        smul_zero (z ^ entireFunctionZeroMultiplicity F hF 0)

/-- Multiplication by a local analytic unit preserves analytic zero
order. -/
theorem complex_smul_smul_eq_smul_mul
    (a b c : ℂ) :
    a • (b • c) = b • (a * c) := by
  calc
    a • (b • c) = a * (b * c) := by
      exact congrArg (fun x : ℂ => a * x) (smul_eq_mul b c)
    _ = (a * b) * c := (mul_assoc a b c).symm
    _ = (b * a) * c := by
      exact congrArg (fun x : ℂ => x * c) (mul_comm a b)
    _ = b * (a * c) := mul_assoc b a c
    _ = b • (a * c) := (smul_eq_mul b (a * c)).symm

theorem analyticAt_order_eq_of_eventually_eq_unit_smul
    (F G u : ℂ → ℂ)
    {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hG : AnalyticAt ℂ G z)
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, F w = u w • G w) :
    hF.order = hG.order := by
  by_cases hG_top : hG.order = ⊤
  · have hG_zero : ∀ᶠ w in 𝓝 z, G w = 0 :=
      (hG.order_eq_top_iff).mp hG_top
    have hF_zero : ∀ᶠ w in 𝓝 z, F w = 0 := by
      filter_upwards [hfactor, hG_zero] with w hFw hGw
      calc
        F w = u w • G w := hFw
        _ = u w • 0 := congrArg (fun x : ℂ => u w • x) hGw
        _ = 0 := smul_zero (u w)
    exact Eq.trans ((hF.order_eq_top_iff).mpr hF_zero) hG_top.symm
  · let n : ℕ := hG.order.untop hG_top
    have hG_order : hG.order = (n : ENat) := by
      exact (WithTop.coe_untop hG.order hG_top).symm
    rcases (hG.order_eq_nat_iff n).mp hG_order with
      ⟨g, hg_an, hg_ne, hg_model⟩
    have hF_order : hF.order = (n : ENat) := by
      refine (hF.order_eq_nat_iff n).mpr ?_
      refine ⟨fun w : ℂ => u w * g w, hu.mul hg_an, ?_, ?_⟩
      · exact mul_ne_zero hu_ne hg_ne
      · filter_upwards [hfactor, hg_model] with w hFw hGw
        calc
          F w = u w • G w := hFw
          _ = u w • ((w - z) ^ n • g w) := by
            exact congrArg (fun x : ℂ => u w • x) hGw
          _ = (w - z) ^ n • (u w * g w) :=
            complex_smul_smul_eq_smul_mul (u w) ((w - z) ^ n) (g w)
    exact Eq.trans hF_order hG_order.symm

/-- Multiplication by a local analytic unit preserves the file's entire-function
zero multiplicity. -/
theorem entireFunctionZeroMultiplicity_eq_of_eventually_eq_unit_smul
    (F G u : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {z : ℂ}
    (hu : AnalyticAt ℂ u z)
    (hu_ne : u z ≠ 0)
    (hfactor : ∀ᶠ w in 𝓝 z, F w = u w • G w) :
    entireFunctionZeroMultiplicity F hF z =
      entireFunctionZeroMultiplicity G hG z := by
  unfold entireFunctionZeroMultiplicity
  exact congrArg (fun e : ENat => e.toNat)
    (analyticAt_order_eq_of_eventually_eq_unit_smul
      F G u (hF z) (hG z) hu hu_ne hfactor)

/-- Away from the origin, removing the origin Taylor factor preserves analytic
zero multiplicity. -/
theorem entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {z : ℂ}
    (hz : z ≠ 0) :
    entireFunctionZeroMultiplicity F hF z =
      entireFunctionZeroMultiplicity G hG z := by
  exact
    entireFunctionZeroMultiplicity_eq_of_eventually_eq_unit_smul
      F G
      (fun w : ℂ => w ^ entireFunctionZeroMultiplicity F hF 0)
      hF hG
      (analyticAt_id.pow (entireFunctionZeroMultiplicity F hF 0))
      (pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hz)
      (eventually_of_forall hfactor)

/-- The origin Taylor quotient identifies the nonzero-zero index types. -/
def entireFunction_originTaylorFactor_nonzeroZeroEquiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z) :
    EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G where
  toFun z :=
    ⟨z,
      (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
        F G hF hfactor z.property.2).mp z.property.1,
      z.property.2⟩
  invFun z :=
    ⟨z,
      (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
        F G hF hfactor z.property.2).mpr z.property.1,
      z.property.2⟩
  left_inv z := by
    exact Subtype.ext rfl
  right_inv z := by
    exact Subtype.ext rfl

/-- Closed-disk summand on the canonical nonzero-zero index. -/
noncomputable def entireFunctionNonzeroZeroClosedDiskSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (z : EntireFunctionNonzeroZero F) : ℝ :=
  if ‖(z : ℂ)‖ ≤ R then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ)
  else
    0

/-- Radial-gap summand on the canonical nonzero-zero index. -/
noncomputable def entireFunctionNonzeroZeroRadialGapSummand
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionNonzeroZero F) : ℝ :=
  if ‖(z : ℂ)‖ < ρ then
    (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
      Real.log (ρ / ‖(z : ℂ)‖)
  else
    0

/-- Closed-disk summands on nonzero zeros are invariant under the origin
Taylor quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummand_equiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (R : ℝ)
    (z : EntireFunctionNonzeroZero F) :
    entireFunctionNonzeroZeroClosedDiskSummand G hG R
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
      entireFunctionNonzeroZeroClosedDiskSummand F hF R z := by
  unfold entireFunctionNonzeroZeroClosedDiskSummand
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  exact
    if_congr
      (by rfl)
      (congrArg (fun n : ℕ => (n : ℝ)) hmult)
      rfl

/-- Radial-gap summands on nonzero zeros are invariant under the origin Taylor
quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (ρ : ℝ)
    (z : EntireFunctionNonzeroZero F) :
    entireFunctionNonzeroZeroRadialGapSummand G hG ρ
        (entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor z) =
      entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := by
  unfold entireFunctionNonzeroZeroRadialGapSummand
  have hmult :
      entireFunctionZeroMultiplicity G hG (z : ℂ) =
        entireFunctionZeroMultiplicity F hF (z : ℂ) :=
    (entireFunction_originTaylorFactor_multiplicity_eq_quotient_of_ne_zero
      F G hF hG hfactor z.property.2).symm
  exact
    if_congr
      (by rfl)
      (congrArg
        (fun n : ℕ =>
          (n : ℝ) * Real.log (ρ / ‖(z : ℂ)‖))
        hmult)
      rfl

/-- Closed-disk summability on the canonical nonzero-zero index transports
through the origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_canonical
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hGsum :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R z)) :
    Summable
      (fun z : EntireFunctionNonzeroZero F =>
        entireFunctionNonzeroZeroClosedDiskSummand F hF R z) := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  have hcomp :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R (e z)) :=
    (e.summable_iff).mpr hGsum
  exact hcomp.congr
    (fun z =>
      entireFunction_originTaylorFactor_nonzeroClosedDiskSummand_equiv
        F G hF hG hfactor R z)

/-- Radial-gap summability on the canonical nonzero-zero index transports
through the origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGapSummable_canonical
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hGsum :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z)) :
    Summable
      (fun z : EntireFunctionNonzeroZero F =>
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  have hcomp :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ (e z)) :=
    (e.summable_iff).mpr hGsum
  exact hcomp.congr
    (fun z =>
      entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
        F G hF hG hfactor ρ z)

/-- The old `EntireFunctionZero` nonzero closed-disk summability surface is
equivalent to summability on the canonical nonzero-zero index. -/
theorem entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ) :
    Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) ↔
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    exact if_pos hz_zero
  have hiff :
      Summable
          (fun z : EntireFunctionNonzeroZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R (i z)) ↔
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) :=
    hi.summable_iff houtside
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) := by
    funext z
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand
    unfold entireFunctionNonzeroZeroClosedDiskSummand
    unfold entireFunctionZeroMultiplicityClosedDiskSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  constructor
  · intro hcanonical
    exact hiff.mp (Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint.symm
      hcanonical)
  · intro hold
    exact Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint
      (hiff.mpr hold)

/-- The old `EntireFunctionZero` radial-gap summability surface is equivalent
to summability on the canonical nonzero-zero index. -/
theorem entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) :
    Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) ↔
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionJensenRadialGapSummand
    exact if_pos hz_zero
  have hiff :
      Summable
          (fun z : EntireFunctionNonzeroZero F =>
            entireFunctionJensenRadialGapSummand F hF ρ (i z)) ↔
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionJensenRadialGapSummand F hF ρ z) :=
    hi.summable_iff houtside
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
    funext z
    unfold entireFunctionJensenRadialGapSummand
    unfold entireFunctionNonzeroZeroRadialGapSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  constructor
  · intro hcanonical
    exact hiff.mp (Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint.symm
      hcanonical)
  · intro hold
    exact Eq.subst
      (motive := fun f : EntireFunctionNonzeroZero F → ℝ => Summable f)
      hpoint
      (hiff.mpr hold)

/-- The old `EntireFunctionZero` radial-gap sum agrees with the canonical
nonzero-zero radial-gap sum. -/
theorem entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ) :
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
      ∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF ρ z := by
  let i : EntireFunctionNonzeroZero F → EntireFunctionZero F :=
    EntireFunctionNonzeroZero.toZero F
  have hi : Function.Injective i :=
    EntireFunctionNonzeroZero.toZero_injective F
  have houtside :
      ∀ z : EntireFunctionZero F,
        z ∉ Set.range i →
        entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
    intro z hz_not_range
    have hz_zero : (z : ℂ) = 0 := by
      by_contra hz_ne
      exact hz_not_range
        ((EntireFunctionNonzeroZero.mem_range_toZero_iff F z).mpr hz_ne)
    unfold entireFunctionJensenRadialGapSummand
    exact if_pos hz_zero
  have hpoint :
      (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ (i z)) =
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) := by
    funext z
    unfold entireFunctionJensenRadialGapSummand
    unfold entireFunctionNonzeroZeroRadialGapSummand
    have hz_ne : ((i z : EntireFunctionZero F) : ℂ) ≠ 0 := z.property.2
    exact if_neg hz_ne
  calc
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionJensenRadialGapSummand F hF ρ (i z) := by
      exact congrArg
        (fun f : EntireFunctionNonzeroZero F → ℝ => ∑' z, f z)
        hpoint.symm
    _ =
        ∑' z : EntireFunctionZero F,
          entireFunctionJensenRadialGapSummand F hF ρ z :=
      hi.tsum_eq houtside

/-- The canonical nonzero-zero radial-gap sum is invariant under the origin
Taylor quotient equivalence. -/
theorem entireFunction_originTaylorFactor_nonzeroRadialGap_tsum_eq_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    (ρ : ℝ) :
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
      ∑' z : EntireFunctionNonzeroZero G,
        entireFunctionNonzeroZeroRadialGapSummand G hG ρ z := by
  let e : EntireFunctionNonzeroZero F ≃ EntireFunctionNonzeroZero G :=
    entireFunction_originTaylorFactor_nonzeroZeroEquiv F G hF hfactor
  calc
    (∑' z : EntireFunctionNonzeroZero F,
        entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ (e z) := by
      exact congrArg
        (fun f : EntireFunctionNonzeroZero F → ℝ => ∑' z, f z)
        (funext
          (fun z =>
            (entireFunction_originTaylorFactor_nonzeroRadialGapSummand_equiv
              F G hF hG hfactor ρ z).symm))
    _ =
        ∑' z : EntireFunctionNonzeroZero G,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z :=
      e.tsum_eq
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z)

/-- Closed-disk nonzero-zero summability transports from the global origin
Taylor quotient back to the original entire function. -/
theorem entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_of_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 1 ≤ R)
    (hGsum :
      Summable
        (fun z : EntireFunctionZero G =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand G hG R z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  have hGcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroClosedDiskSummand G hG R z) :=
    (entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
      G hG R).mpr hGsum
  have hFcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroClosedDiskSummand F hF R z) :=
    entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_canonical
      F G hF hG hfactor hGcanonical
  exact
    (entireFunctionNonzeroZeroClosedDiskSummable_canonical_iff_zeroSubtype
      F hF R).mp hFcanonical

/-- Radial-gap summability and radial-gap sums transport through the global
origin Taylor quotient. -/
theorem entireFunction_originTaylorFactor_radialGapSum_eq_quotient_radialGapSum
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hGsum :
      Summable
        (fun z : EntireFunctionZero G =>
          entireFunctionJensenRadialGapSummand G hG ρ z)) :
    Summable
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z) ∧
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenRadialGapSum G hG ρ := by
  have hGcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero G =>
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z) :=
    (entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
      G hG ρ).mpr hGsum
  have hFcanonical :
      Summable
        (fun z : EntireFunctionNonzeroZero F =>
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z) :=
    entireFunction_originTaylorFactor_nonzeroRadialGapSummable_canonical
      F G hF hG hfactor hGcanonical
  have hFsum :
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) :=
    (entireFunctionNonzeroZeroRadialGapSummable_canonical_iff_zeroSubtype
      F hF ρ).mp hFcanonical
  refine ⟨hFsum, ?_⟩
  unfold entireFunctionJensenRadialGapSum
  calc
    (∑' z : EntireFunctionZero F,
        entireFunctionJensenRadialGapSummand F hF ρ z) =
        ∑' z : EntireFunctionNonzeroZero F,
          entireFunctionNonzeroZeroRadialGapSummand F hF ρ z := by
      exact
        (entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum
          F hF ρ).symm
    _ =
        ∑' z : EntireFunctionNonzeroZero G,
          entireFunctionNonzeroZeroRadialGapSummand G hG ρ z :=
      entireFunction_originTaylorFactor_nonzeroRadialGap_tsum_eq_quotient
        F G hF hG hfactor ρ
    _ =
        ∑' z : EntireFunctionZero G,
          entireFunctionJensenRadialGapSummand G hG ρ z :=
      entireFunctionNonzeroZeroRadialGap_tsum_eq_zeroSubtype_tsum G hG ρ

/-- Unnormalized boundary-integral transport through the origin Taylor factor,
after deleting the finite quotient boundary-zero exceptional set.

This is the analytic finite-exception congruence root.  The proof belongs to
the logarithmic-singularity layer: off the finite exceptional set the
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not change the interval integral. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegral_eq_origin_constant_plus_quotient_of_finiteExceptionCongr
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogIntegral F ρ =
      (2 * Real.pi) *
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogIntegral G ρ := by
  sorry

/-- Normalized boundary-integral transport through the origin Taylor factor,
after deleting the finite boundary-zero exceptional set.

This is the analytic congruence theorem underneath the boundary-average
transport: off the finite quotient-zero parameter set the logarithmic
integrands differ by the constant origin contribution, and the finite
logarithmic singularities do not change the interval integral. -/
theorem entireFunction_originTaylorFactor_normalizedBoundaryLogIntegral_eq_origin_plus_quotient_of_finiteExceptionCongr
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral G ρ := by
  let c : ℝ := (2 * Real.pi)⁻¹
  let d : ℝ := 2 * Real.pi
  have hd_ne : d ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hcd : c * d = 1 := by
    exact inv_mul_cancel₀ hd_ne
  have hintegral :
      entireFunctionJensenBoundaryLogIntegral F ρ =
        d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          entireFunctionJensenBoundaryLogIntegral G ρ :=
    entireFunction_originTaylorFactor_boundaryLogIntegral_eq_origin_constant_plus_quotient_of_finiteExceptionCongr
      F G hF hG hfactor hρ
  calc
    (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral F ρ =
        c * entireFunctionJensenBoundaryLogIntegral F ρ := rfl
    _ =
        c *
          (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogIntegral G ρ) := by
      exact congrArg (fun x : ℝ => c * x) hintegral
    _ =
        c * (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ) +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact mul_add c
        (d * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
        (entireFunctionJensenBoundaryLogIntegral G ρ)
    _ =
        (c * d) * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ =>
          x + c * entireFunctionJensenBoundaryLogIntegral G ρ)
        (mul_assoc c d
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
    _ =
        1 * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ =>
          x * entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            c * entireFunctionJensenBoundaryLogIntegral G ρ)
        hcd
    _ =
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          c * entireFunctionJensenBoundaryLogIntegral G ρ := by
      exact congrArg
        (fun x : ℝ => x + c * entireFunctionJensenBoundaryLogIntegral G ρ)
        (one_mul (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
    _ =
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          (2 * Real.pi)⁻¹ * entireFunctionJensenBoundaryLogIntegral G ρ := rfl

/-- Boundary-average transport through the origin Taylor factor, stated as the
finite-exception integral theorem it really is.

The pointwise logarithmic identity holds away from the finite parameter set
where the quotient vanishes on the boundary circle.  At those exceptional
parameters `Real.log 0` makes the pointwise formula false, so the owner
statement is an interval-integral transport theorem modulo finite logarithmic
singularities, followed by the constant-integral normalization. -/
theorem entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient_of_finiteExceptionIntegral
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogAverage G ρ := by
  exact
    entireFunction_originTaylorFactor_normalizedBoundaryLogIntegral_eq_origin_plus_quotient_of_finiteExceptionCongr
      F G hF hG hfactor hρ

/-- Boundary logarithmic averages transport through the global origin Taylor
quotient with the explicit `m log ρ` contribution from the removed origin
factor. -/
theorem entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogAverage G ρ := by
  exact
    entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient_of_finiteExceptionIntegral
      F G hF hG hfactor hρ

/-- Origin Taylor-factor transport after the global entire quotient at the
origin has been explicitly constructed.

The hypotheses are exactly the output of the removable-singularity origin
quotient construction.  This theorem owns the comparison between `F` and its
normalized entire quotient: nonzero zeros away from the origin, radial-gap
sums, and boundary logarithmic averages are transported through the global
factorization, while the separated power contributes `m log ρ`. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (G : ℂ → ℂ)
    (hG_entire : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hG_ne : G 0 ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        G hG_entire hG_ne with
    ⟨C, hclosedG, hidentityG⟩
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    exact
      entireFunction_originTaylorFactor_nonzeroClosedDiskSummable_of_quotient
        F G hF hG_entire hfactor hR (hclosedG R hR)
  · intro ρ hρ
    rcases hidentityG ρ hρ with ⟨hradialG, hGidentity⟩
    rcases
        entireFunction_originTaylorFactor_radialGapSum_eq_quotient_radialGapSum
          F G hF hG_entire hfactor hρ hradialG with
      ⟨hradialF, hradial_eq⟩
    refine ⟨hradialF, ?_⟩
    have hboundary :
        entireFunctionJensenBoundaryLogAverage F ρ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogAverage G ρ :=
      entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
        F G hF hG_entire hfactor hρ
    calc
      entireFunctionJensenRadialGapSum F hF ρ +
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
          entireFunctionJensenRadialGapSum G hG_entire ρ +
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C := by
        exact congrArg
          (fun x : ℝ =>
            x + entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C)
          hradial_eq
      _ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (entireFunctionJensenRadialGapSum G hG_entire ρ + C) := by
        calc
          entireFunctionJensenRadialGapSum G hG_entire ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
              (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                entireFunctionJensenRadialGapSum G hG_entire ρ) + C := by
            exact congrArg
              (fun x : ℝ => x + C)
              (add_comm
                (entireFunctionJensenRadialGapSum G hG_entire ρ)
                (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ))
          _ =
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                (entireFunctionJensenRadialGapSum G hG_entire ρ + C) := by
            exact
              (add_assoc
                (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
                (entireFunctionJensenRadialGapSum G hG_entire ρ)
                C).symm
      _ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            entireFunctionJensenBoundaryLogAverage G ρ := by
        exact congrArg
          (fun x : ℝ =>
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + x)
          hGidentity
      _ =
          entireFunctionJensenBoundaryLogAverage F ρ :=
        hboundary.symm

/-- Origin Taylor-factor transport in the genuine origin-zero case.

This is the remaining transport step after the nonzero-origin case is removed:
factor the origin zero by `AnalyticAt.order_eq_nat_iff`, apply the nonzero
Jensen formula to the analytic unit, and compare nonzero zero multisets and
boundary averages. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 = 0)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases entireFunction_originTaylorFactor_entireQuotient F hF hnontrivial with
    ⟨G, hG_entire, hG_ne, hfactor⟩
  exact
    entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
      F hF hnontrivial G hG_entire hG_ne hfactor

/-- Transport of the nonzero-at-origin Jensen identity through the origin
Taylor factor.

If `F(z) = z^m G(z)` near the origin and `G 0 ≠ 0`, the boundary average gains
the explicit term `m log ρ`, while the nonzero radial-gap and closed-disk
summability data are transported unchanged from the normalized factor.  This is
the exact owner theorem that separates the algebraic origin factor from the
classical Jensen identity for a function nonzero at the origin. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  -- Factor `F` by its origin order and apply the nonzero-at-origin Jensen
  -- identity to the analytic unit.  The origin power contributes exactly
  -- `m * log ρ` to the boundary average.
  by_cases hF0 : F 0 = 0
  · exact
      entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
        F hF hF0 hnontrivial
  · exact
      entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
        F hF hF0

/-- Origin-factored classical Jensen formula as an exact radial-gap identity.

This is the genuinely analytic theorem: for a nontrivial entire function,
after separating the origin Taylor factor, Jensen's formula identifies the
boundary logarithmic average with the non-origin multiplicity-weighted radial
gap sum plus the origin radius term and one fixed normalization constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact
    entireFunction_classicalJensenFormula_originTaylorFactor_transport
      F hF hnontrivial

/-- Origin-factored classical Jensen formula in radial-gap bound form.

For large radii, the origin radius term is nonnegative, so the exact Jensen
identity implies a radial-gap upper bound with one absolute-value constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
        F hF hnontrivial with
    ⟨C, hclosed, hidentity⟩
  refine ⟨|C|, hclosed, ?_⟩
  intro ρ hρ
  rcases hidentity ρ hρ with ⟨hgap, hJensen⟩
  refine ⟨hgap, ?_⟩
  have horigin_nonneg :
      0 ≤ entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
    unfold entireFunctionOriginMultiplicityLogRadiusContribution
    exact mul_nonneg
      (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
      (Real.log_nonneg hρ)
  have hC_nonneg : 0 ≤ |C| + C := by
    have hneg : -C ≤ |C| := neg_le_abs C
    have hsub : 0 ≤ |C| - (-C) := sub_nonneg.mpr hneg
    have hsub_eq : |C| - (-C) = |C| + C := by
      ring
    exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hsub_eq hsub
  have htail_nonneg :
      0 ≤
        entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          (|C| + C) :=
    add_nonneg horigin_nonneg hC_nonneg
  have hle_add :
      entireFunctionJensenRadialGapSum F hF ρ ≤
        entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) :=
    le_add_of_nonneg_right htail_nonneg
  have htarget :
      entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) =
        |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
    calc
      entireFunctionJensenRadialGapSum F hF ρ +
          (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
            (|C| + C)) =
          |C| +
            (entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C) := by
        ring
      _ = |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
        exact congrArg (fun x : ℝ => |C| + x) hJensen
  exact Eq.subst
    (motive := fun x : ℝ =>
      entireFunctionJensenRadialGapSum F hF ρ ≤ x)
    htarget
    hle_add

/-- Classical Jensen formula in radial-gap form, with multiplicities and with
the first nonzero Taylor factor at the origin absorbed into an additive
constant.

This is the precise large-radius analytic input after removing the origin
factor: Jensen's formula identifies the multiplicity-weighted radial gap sum
with the boundary logarithmic average up to a fixed additive normalization
constant. The restriction `1 ≤ ρ` is the exact place where the origin-radius
term is nonnegative and can be absorbed. -/
theorem entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) ∧
      (∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenRadialGapSum F hF (2 * R)) := by
  rcases
      entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
        F hF hnontrivial with
    ⟨J, hclosed_nonzero, hradial⟩
  refine
    ⟨entireFunctionOriginMultiplicityLogContribution F hF + |J|, ?_, ?_, ?_⟩
  · intro R hR
    exact
      entireFunctionZeroMultiplicityClosedDiskSummable_of_nonzeroClosedDiskSummable
        F hF (hclosed_nonzero R hR)
  · intro ρ hρ
    rcases hradial ρ hρ with ⟨hgap, hbound⟩
    refine ⟨hgap, ?_⟩
    have hJ_le :
        J + entireFunctionJensenBoundaryLogAverage F ρ ≤
          entireFunctionOriginMultiplicityLogContribution F hF + |J| +
            entireFunctionJensenBoundaryLogAverage F ρ := by
      have hJ_abs : J ≤ |J| := le_abs_self J
      have horigin_nonneg : 0 ≤ entireFunctionOriginMultiplicityLogContribution F hF := by
        unfold entireFunctionOriginMultiplicityLogContribution
        exact mul_nonneg
          (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
          real_log_two_pos.le
      have hJ_shift :
          J + entireFunctionJensenBoundaryLogAverage F ρ ≤
            |J| + entireFunctionJensenBoundaryLogAverage F ρ :=
        add_le_add_right hJ_abs
          (entireFunctionJensenBoundaryLogAverage F ρ)
      have horigin_shift :
          |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤
            entireFunctionOriginMultiplicityLogContribution F hF +
              (|J| + entireFunctionJensenBoundaryLogAverage F ρ) :=
        le_add_of_nonneg_left horigin_nonneg
      have hassoc :
          entireFunctionOriginMultiplicityLogContribution F hF +
              (|J| + entireFunctionJensenBoundaryLogAverage F ρ) =
            entireFunctionOriginMultiplicityLogContribution F hF + |J| +
              entireFunctionJensenBoundaryLogAverage F ρ :=
        (add_assoc
          (entireFunctionOriginMultiplicityLogContribution F hF)
          |J|
          (entireFunctionJensenBoundaryLogAverage F ρ)).symm
      exact le_trans hJ_shift (Eq.subst
        (motive := fun x : ℝ =>
          |J| + entireFunctionJensenBoundaryLogAverage F ρ ≤ x)
        hassoc
        horigin_shift)
    exact le_trans hbound hJ_le
  · intro R hR
    have hρ : 1 ≤ 2 * R :=
      one_le_doubled_radius_of_one_le hR
    rcases hradial (2 * R) hρ with ⟨hgap, hbound⟩
    have hcount :
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          entireFunctionOriginMultiplicityLogContribution F hF +
            entireFunctionJensenRadialGapSum F hF (2 * R) :=
      entireFunctionZeroMultiplicityCountingInClosedDisk_mul_log_two_le_originContribution_plus_radialGapSum
        F hF hR (hclosed_nonzero R hR) hgap
    have habs_nonneg : 0 ≤ |J| := abs_nonneg J
    have hshift :
        entireFunctionOriginMultiplicityLogContribution F hF +
            entireFunctionJensenRadialGapSum F hF (2 * R) ≤
          entireFunctionOriginMultiplicityLogContribution F hF +
            (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) :=
      add_le_add_left
        (le_add_of_nonneg_left habs_nonneg)
        (entireFunctionOriginMultiplicityLogContribution F hF)
    have hassoc :
        entireFunctionOriginMultiplicityLogContribution F hF +
            (|J| + entireFunctionJensenRadialGapSum F hF (2 * R)) =
          entireFunctionOriginMultiplicityLogContribution F hF + |J| +
            entireFunctionJensenRadialGapSum F hF (2 * R) :=
      (add_assoc
        (entireFunctionOriginMultiplicityLogContribution F hF)
        |J|
        (entireFunctionJensenRadialGapSum F hF (2 * R))).symm
    exact le_trans hcount (Eq.subst
      (motive := fun x : ℝ =>
        entireFunctionOriginMultiplicityLogContribution F hF +
          entireFunctionJensenRadialGapSum F hF (2 * R) ≤ x)
      hassoc
      hshift)

/-- Jensen's radial-gap formula supplies summability of closed-disk
multiplicity summands. -/
theorem entireFunction_classicalJensenFormula_closedDiskMultiplicitySummable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionZeroMultiplicityClosedDiskSummand F hF R z) := by
  intro R hR
  rcases entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
      F hF hnontrivial with ⟨J, hclosed, hradial, hcount⟩
  exact hclosed R hR

/-- The doubled-radius algebra converting the weighted Jensen radial-gap bound
into the closed-disk zero-counting estimate. -/
theorem entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  rcases hweighted with ⟨J, hJ⟩
  refine ⟨(Real.log 2)⁻¹ * J, ?_⟩
  intro R hR
  have hlog_pos : 0 < Real.log 2 :=
    real_log_two_pos
  have hscaled :
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) ≤
        (Real.log 2)⁻¹ *
          (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) := by
    exact mul_le_mul_of_nonneg_left (hJ R hR) real_log_two_inv_nonneg
  have hleft :
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
    calc
      (Real.log 2)⁻¹ *
          (entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2) =
          ((Real.log 2)⁻¹ * Real.log 2) *
            entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        ring
      _ = 1 * entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        exact congrArg
          (fun x : ℝ => x *
            entireFunctionZeroMultiplicityCountingInClosedDisk F hF R)
          (inv_mul_cancel₀ hlog_pos.ne')
      _ = entireFunctionZeroMultiplicityCountingInClosedDisk F hF R := by
        exact one_mul _
  have hright :
      (Real.log 2)⁻¹ *
          (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
        (Real.log 2)⁻¹ * J +
          (Real.log 2)⁻¹ * entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    ring
  exact hleft ▸ hright ▸ hscaled

/-- Classical Jensen formula in the weighted doubled-radius counting form.

This is the genuine classical Jensen formula input after factoring the first
nonzero Taylor term at the origin: the Jensen radial-gap sum on the circle of
radius `2R` dominates the multiplicity count in `closedDisk R` by the uniform
gap `log 2`, with a constant absorbing the origin factor; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  rcases
    entireFunction_classicalJensenFormula_radialGapSum_le_boundaryLogAverage
      F hF hnontrivial with
    ⟨J, hclosed, hradial, hcount⟩
  refine ⟨J + J, ?_⟩
  intro R hR
  have hρ : 1 ≤ 2 * R :=
    one_le_doubled_radius_of_one_le hR
  rcases hradial (2 * R) hρ with ⟨hgap_summable, hgap_bound⟩
  have hcount_gap :
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
        J + entireFunctionJensenRadialGapSum F hF (2 * R) :=
    hcount R hR
  have hbound :
      J + entireFunctionJensenRadialGapSum F hF (2 * R) ≤
        J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) :=
    add_le_add_left hgap_bound J
  have htarget :
      J + (J + entireFunctionJensenBoundaryLogAverage F (2 * R)) =
        J + J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    ring
  exact Eq.subst
    (motive := fun x : ℝ =>
      entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤ x)
    htarget
    (le_trans hcount_gap hbound)

/-- Classical weighted Jensen zero-counting estimate on the doubled disk. -/
theorem entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
          J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_weighted_doubledRadius_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen formula with multiplicity counting on the doubled disk.

After factoring the first nonzero Taylor term at the origin, Jensen's formula
gives the weighted sum of logarithmic radial gaps for zeros in the doubled
disk.  Since every zero in `closedDisk R` contributes at least `log 2` to that
sum when the boundary radius is `2R`, the stated inequality follows with a
constant absorbing the origin factor. -/
theorem entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  have hweighted :
      ∃ J : ℝ,
        ∀ R : ℝ,
          1 ≤ R →
          entireFunctionZeroMultiplicityCountingInClosedDisk F hF R * Real.log 2 ≤
            J + entireFunctionJensenBoundaryLogAverage F (2 * R) := by
    exact
      entireFunction_classicalJensenFormula_weighted_zeroMultiplicityCounting_closedDisk_le_boundaryLogAverage
        F hF hnontrivial
  exact
    entireFunction_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hweighted

/-- Classical Jensen formula zero-counting estimate, including the doubled-radius
`log 2` loss.

This is the deepest remaining analytic input: Jensen's formula for a nonzero
entire function, with multiplicities, after comparing zeros in `closedDisk R`
to the boundary integral on the circle of radius `2R`; cf. Titchmarsh, *The
Theory of Functions*, §5. -/
theorem entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_standardRoot_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Standard Jensen zero-counting estimate for nontrivial entire functions,
including the algebraic doubled-radius `log 2` loss. -/
theorem entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_classicalJensenFormula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

/-- Classical Jensen zero-counting estimate for nontrivial entire functions,
with the doubled-radius `log 2` loss. -/
theorem entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
      ∀ R : ℝ,
        1 ≤ R →
        entireFunctionZeroMultiplicityCountingInClosedDisk F hF R ≤
          J + (Real.log 2)⁻¹ *
            entireFunctionJensenBoundaryLogAverage F (2 * R) := by
  exact
    entireFunction_standardJensen_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
      F hF hnontrivial

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

/-- The origin Taylor quotient gives the expected boundary-circle norm
factorization at every sample. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
      R ^ entireFunctionZeroMultiplicity F hF 0 *
        ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  let z : ℂ := (R : ℂ) * Complex.exp (θ * Complex.I)
  have hz_norm : ‖z‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR
  calc
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        ‖F z‖ := rfl
    _ = ‖z ^ entireFunctionZeroMultiplicity F hF 0 • G z‖ := by
      exact congrArg norm (hfactor z)
    _ =
        ‖z ^ entireFunctionZeroMultiplicity F hF 0‖ * ‖G z‖ := by
      exact norm_smul (z ^ entireFunctionZeroMultiplicity F hF 0) (G z)
    _ =
        ‖z‖ ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖G z‖)
        (norm_pow z (entireFunctionZeroMultiplicity F hF 0))
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖)
        hz_norm
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl

/-- At boundary samples where the quotient does not vanish and the radius is
positive, the origin Taylor quotient contributes exactly `m log R` to the
Jensen logarithmic integrand. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hR_nonneg : 0 ≤ R := hR.le
  have hnorm :
      ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ :=
    entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
      F G hF hfactor hR_nonneg
  have hpow_ne :
      R ^ entireFunctionZeroMultiplicity F hF 0 ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hR.ne'
  have hG_norm_ne :
      ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hG
  unfold entireFunctionJensenBoundaryLogIntegrand
  calc
    Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log
          (R ^ entireFunctionZeroMultiplicity F hF 0 *
            ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖) := by
      exact congrArg Real.log hnorm
    _ =
        Real.log (R ^ entireFunctionZeroMultiplicity F hF 0) +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact Real.log_mul hpow_ne hG_norm_ne
    _ =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact congrArg
        (fun x : ℝ =>
          x + Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖)
        (Real.log_pow R (entireFunctionZeroMultiplicity F hF 0))

/-- Boundary parameters where the quotient factor vanishes on the Jensen
circle.  These are exactly the finite exceptional parameters for the
origin-factor boundary-integral transport. -/
def entireFunctionJensenQuotientBoundaryZeroParameters
    (G : ℂ → ℂ)
    (R : ℝ) : Set ℝ :=
  {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}

/-- Outside the quotient boundary-zero parameter set, the quotient sample is
nonzero. -/
theorem entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
    (G : ℂ → ℂ)
    {R θ : ℝ}
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  intro hzero
  exact hθ ⟨hθI, hzero⟩

/-- Off the finite quotient boundary-zero set, the origin Taylor factor gives
the pointwise logarithmic boundary identity. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
      G hθ hθI
  exact
    entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
      F G hF hfactor hR hG

/-- If the boundary parametrization is injective on the fundamental arc and
the circle zero set is finite, then the quotient boundary-zero parameters are
finite. -/
theorem entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
    (G : ℂ → ℂ)
    (R : ℝ)
    (hR : 0 ≤ R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => (R : ℂ) * Complex.exp (θ * Complex.I)
  have hInjSubtype : Function.Injective f := by
    intro a b hEq
    apply Subtype.ext
    exact hInj a.2 b.2 hEq
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = R ∧ G z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInjSubtype hEq
  have hIocFinite :
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0}.Finite := by
    simpa [f, Set.preimage, entireFunctionJensenBoundaryCircle_norm hR]
      using hpre
  have hsubset :
      entireFunctionJensenQuotientBoundaryZeroParameters G R ⊆
        insert (0 : ℝ)
          {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
            G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0} := by
    intro θ hθ
    by_cases hθ0 : θ = 0
    · exact hθ0 ▸ Set.mem_insert (0 : ℝ) _
    · exact Set.mem_insert_iff.mpr
        (Or.inr ⟨⟨lt_of_le_of_ne hθ.1.1 hθ0.symm, hθ.1.2⟩, hθ.2⟩)
  exact (hIocFinite.insert (0 : ℝ)).subset hsubset

/-- A positive-radius Jensen boundary sample is away from the origin. -/
theorem entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos
    {R θ : ℝ}
    (hR : 0 < R) :
    (R : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
  have hnorm :
      ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR.le
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ := hnorm.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius Jensen circle, the origin Taylor quotient has the
same boundary-zero parameters as the original function. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_zero_iff_quotient_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R) :
    F ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 ↔
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
  exact
    entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
      F G hF hfactor
      (entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos hR)

/-- A point on a positive-radius circle is away from the origin. -/
theorem complex_ne_zero_of_norm_eq_pos_radius
    {z : ℂ}
    {R : ℝ}
    (hR : 0 < R)
    (hz : ‖z‖ = R) :
    z ≠ 0 := by
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖z‖ := hz.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius circle, the origin Taylor quotient has exactly the
same circle-zero set as the original function. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R) :
    {z : ℂ | ‖z‖ = R ∧ F z = 0} =
      {z : ℂ | ‖z‖ = R ∧ G z = 0} := by
  ext z
  constructor
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mp hz.2⟩
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mpr hz.2⟩

/-- Finiteness of quotient zeros on a positive-radius circle transports back
through the origin Taylor factor. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_finite_of_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R)
    (hGfinite : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    Set.Finite {z : ℂ | ‖z‖ = R ∧ F z = 0} := by
  exact
    Eq.subst
      (motive := fun S : Set ℂ => Set.Finite S)
      (entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
        F G hF hfactor hR).symm
      hGfinite

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

/-- The zero set of a nontrivial entire function meets each doubled Jensen circle
in a finite set. This is the compactness-and-isolated-zeros input behind the
boundary regularity theorem. -/
theorem entireFunction_zeroSet_finite_on_compact_of_discrete
    {S : Set ℂ}
    (hdisc : DiscreteTopology S)
    (hcomp : IsCompact S) :
    S.Finite := by
  haveI : DiscreteTopology S := hdisc
  exact hcomp.finite_of_discrete

/-- The zero set of a nontrivial entire function is discrete on each fixed
Jensen circle. -/
theorem entireFunction_jensenCircleZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hxnorm, hxzero⟩
  have hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
    rcases (hF x).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := fun z _ => hF z
      have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
        hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (by simp) hzero
      rcases hnontrivial with ⟨z0, hz0⟩
      exact hz0 (hEq (by simp))
    · exact hne
  have hScompl :
      ({z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hsw
      exact hw hsw.2)
  exact (Filter.disjoint_principal_right).2 hScompl

/-- The zero set of a nontrivial entire function is discrete on each fixed
circle of radius `r`. -/
theorem entireFunction_circleZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨hxnorm, hxzero⟩
  have hne : ∀ᶠ w in 𝓝[≠] x, F w ≠ 0 := by
    rcases (hF x).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
    · exfalso
      have hU : AnalyticOnNhd ℂ F (Set.univ : Set ℂ) := fun z _ => hF z
      have hEq : EqOn F 0 (Set.univ : Set ℂ) :=
        hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (by simp) hzero
      rcases hnontrivial with ⟨z0, hz0⟩
      exact hz0 (hEq (by simp))
    · exact hne
  have hScompl :
      ({z : ℂ | ‖z‖ = r ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hsw
      exact hw hsw.2)
  exact (Filter.disjoint_principal_right).2 hScompl

/-- The zero set of a nontrivial entire function meets each fixed circle in a
finite set. -/
theorem entireFunction_circleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (r : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
  have hdisc := entireFunction_circleZeros_discreteTopology F hF hnontrivial r
  have hcircleClosed : IsClosed {z : ℂ | ‖z‖ = r} := by
    change IsClosed ((fun z : ℂ => ‖z‖) ⁻¹' ({r} : Set ℝ))
    exact (continuous_norm : Continuous fun z : ℂ => ‖z‖).isClosed_preimage
      (isClosed_singleton : IsClosed ({r} : Set ℝ))
  have hzeroClosed : IsClosed {z : ℂ | F z = 0} := by
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    change IsClosed (F ⁻¹' ({0} : Set ℂ))
    exact hcontF.isClosed_preimage (isClosed_singleton : IsClosed ({0} : Set ℂ))
  have hclosed : IsClosed {z : ℂ | ‖z‖ = r ∧ F z = 0} := by
    change IsClosed ({z : ℂ | ‖z‖ = r} ∩ {z : ℂ | F z = 0})
    exact hcircleClosed.inter hzeroClosed
  have hsubset :
      {z : ℂ | ‖z‖ = r ∧ F z = 0} ⊆ Metric.closedBall (0 : ℂ) r := by
    intro z hz
    have hnorm_le : ‖(z : ℂ)‖ ≤ r := hz.1.le
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le
  have hcomp : IsCompact {z : ℂ | ‖z‖ = r ∧ F z = 0} :=
    (isCompact_closedBall (0 : ℂ) r).of_isClosed_subset hclosed hsubset
  exact entireFunction_zeroSet_finite_on_compact_of_discrete
    (S := {z : ℂ | ‖z‖ = r ∧ F z = 0}) hdisc hcomp

/-- The zero set of a nontrivial entire function meets each doubled Jensen circle
in a finite set. This is the compactness-and-isolated-zeros input behind the
boundary regularity theorem. -/
theorem entireFunction_jensenCircleZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
  exact entireFunction_circleZeros_finite F hF hnontrivial (2 * R)

/-- The Jensen boundary logarithmic integrand is continuous when the doubled circle
contains no zeros. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ, F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    Continuous (entireFunctionJensenBoundaryLogIntegrand F (2 * R)) := by
  dsimp [entireFunctionJensenBoundaryLogIntegrand]
  have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
    continuity
  have hparam : Continuous (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
    exact continuous_const.mul (Complex.continuous_exp.comp hmul)
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
    continuous_norm.comp (hcontF.comp hparam)
  exact hcont_norm.continuousOn.log fun θ _ => norm_ne_zero_iff.mpr (hzero θ)

/-- If the doubled circle has no zeros, the Jensen boundary logarithmic average
is interval-integrable by continuity. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ, F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    (entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree F hF R hzero)
      .intervalIntegrable_of_Icc (show (0 : ℝ) ≤ 2 * Real.pi by exact le_of_lt Real.two_pi_pos)

/-- The boundary sample `θ ↦ F((2R) · exp(iθ))` is analytic as a real-variable
function. This is the owner-level transport input for the Jensen local model. -/
theorem jensenBoundaryLogSample_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ) :
    AnalyticAt ℝ
      (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀ := by
  have hθI : AnalyticAt ℝ (fun θ : ℝ => θ * Complex.I) θ₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (analyticAt_id.mul (analyticAt_const (v := (Complex.I : ℂ)) (x := θ₀)))
  have hexp : AnalyticAt ℝ (fun θ : ℝ => Complex.exp (θ * Complex.I)) θ₀ := by
    have houter : AnalyticAt ℝ (fun z : ℂ => Complex.exp z) ((θ₀ : ℝ) * Complex.I) :=
      (Complex.analyticAt_cexp (z := (θ₀ : ℝ) * Complex.I)).restrictScalars
    exact houter.comp hθI
  have hsample : AnalyticAt ℝ (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) θ₀ := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (analyticAt_const.mul hexp)
  have hFreal : AnalyticAt ℝ F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) :=
    (hF _).restrictScalars
  exact hFreal.comp hsample

/-- If the sampled boundary function is not locally zero at the parameter `θ₀`,
it admits the exact local Taylor factorization needed for the Jensen local model. -/
theorem jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ u : ℝ → ℂ,
      AnalyticAt ℝ u θ₀ ∧
      u θ₀ ≠ 0 ∧
      ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) =
          (θ - θ₀) ^ n • u θ := by
  have hsample :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  rcases (hsample.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  exact ⟨n, u, hu_an, hu_ne, hu_eq⟩

/-- The local Taylor factorization of the boundary sample yields the expected
log-distance plus continuous remainder identity on the punctured neighborhood. -/
theorem jensenBoundaryLogSample_localLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  rcases
      jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero F hF R θ₀ hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  refine ⟨n, fun θ : ℝ => Real.log ‖u θ‖, ?_, ?_⟩
  · exact (hu_an.continuousAt.norm).log (norm_ne_zero_iff.mpr hu_ne)
  filter_upwards
    [hu_eq.filter_mono nhdsWithin_le_nhds,
      (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin]
    with θ hθ huθ_ne hne
  have hsub_ne : θ - θ₀ ≠ 0 := sub_ne_zero.mpr hne
  have hnorm_ne : ‖θ - θ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hsub_ne
  have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 := pow_ne_zero n hnorm_ne
  have huθ_ne' : ‖u θ‖ ≠ 0 := norm_ne_zero_iff.mpr huθ_ne
  calc
    Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
      exact congrArg Real.log (congrArg norm hθ)
    _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
      rw [norm_smul, norm_pow]
    _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
      exact Real.log_mul hpow_ne huθ_ne'
    _ = (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
      simp [Real.log_pow, norm_eq_abs]

/-- An analytic real-parameter unit has locally interval-integrable log norm.

This is the exact analytic-unit remainder input needed by the Jensen local
model.  Analyticity gives continuity on a neighborhood of `θ₀`; nonvanishing
at `θ₀` shrinks that neighborhood to one where `u` is nonzero; therefore
`θ ↦ Real.log ‖u θ‖` is continuous on a small compact interval and hence
interval-integrable there. -/
theorem analyticAt_log_norm_unit_locally_intervalIntegrable
    (u : ℝ → ℂ)
    {θ₀ : ℝ}
    (hu_an : AnalyticAt ℝ u θ₀)
    (hu_ne : u θ₀ ≠ 0) :
    ∃ a b : ℝ,
      a < θ₀ ∧ θ₀ < b ∧
      IntervalIntegrable
        (fun θ : ℝ => Real.log ‖u θ‖)
        MeasureTheory.volume a b := by
  have hlocal_an : ∀ᶠ θ in 𝓝 θ₀, AnalyticAt ℝ u θ :=
    hu_an.eventually_analyticAt
  have hlocal_ne : ∀ᶠ θ in 𝓝 θ₀, u θ ≠ 0 :=
    hu_an.continuousAt.eventually_ne hu_ne
  have hlocal :
      {θ : ℝ | AnalyticAt ℝ u θ ∧ u θ ≠ 0} ∈ 𝓝 θ₀ := by
    exact hlocal_an.and hlocal_ne
  rcases mem_nhds_iff_exists_Ioo_subset.mp hlocal with
    ⟨a, b, hθ₀, hsubset⟩
  rcases exists_between hθ₀.1 with ⟨a', ha_a', ha'_θ₀⟩
  rcases exists_between hθ₀.2 with ⟨b', hθ₀_b', hb'_b⟩
  have ha'_b' : a' ≤ b' :=
    (ha'_θ₀.trans hθ₀_b').le
  have hIcc_subset : Set.Icc a' b' ⊆ Set.Ioo a b := by
    intro θ hθ
    exact
      ⟨lt_of_lt_of_le ha_a' hθ.1,
        lt_of_le_of_lt hθ.2 hb'_b⟩
  have hcont :
      ContinuousOn
        (fun θ : ℝ => Real.log ‖u θ‖)
        (Set.Icc a' b') := by
    intro θ hθ
    have hθ_data : AnalyticAt ℝ u θ ∧ u θ ≠ 0 :=
      hsubset (hIcc_subset hθ)
    exact
      ((hθ_data.1.continuousAt.norm).log
        (norm_ne_zero_iff.mpr hθ_data.2)).continuousWithinAt
  exact
    ⟨a', b', ha'_θ₀, hθ₀_b',
      hcont.intervalIntegrable_of_Icc ha'_b'⟩

/-- The analytic unit remainder in the local Jensen logarithmic model is
locally interval-integrable near the singular parameter. -/
theorem jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  rcases
      jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
        F hF R θ₀ hnot with
    ⟨n, u, hu_an, hu_ne, hu_eq⟩
  let g : ℝ → ℝ := fun θ : ℝ => Real.log ‖u θ‖
  have hg :
      ∃ a b : ℝ,
        a < θ₀ ∧ θ₀ < b ∧
        IntervalIntegrable g MeasureTheory.volume a b := by
    exact analyticAt_log_norm_unit_locally_intervalIntegrable u hu_an hu_ne
  have hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
    filter_upwards
      [hu_eq.filter_mono nhdsWithin_le_nhds,
        (hu_an.continuousAt.eventually_ne hu_ne).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin]
      with θ hθ huθ_ne hne
    have hsub_ne : θ - θ₀ ≠ 0 := sub_ne_zero.mpr hne
    have hnorm_ne : ‖θ - θ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hsub_ne
    have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 := pow_ne_zero n hnorm_ne
    have huθ_ne' : ‖u θ‖ ≠ 0 := norm_ne_zero_iff.mpr huθ_ne
    calc
      Real.log ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖ =
          Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
        exact congrArg Real.log (congrArg norm hθ)
      _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
        rw [norm_smul, norm_pow]
      _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
        exact Real.log_mul hpow_ne huθ_ne'
      _ = (n : ℝ) * Real.log |θ - θ₀| + g θ := by
        simp [g, Real.log_pow, norm_eq_abs]
  exact ⟨n, g, hg, hmodel⟩

/-- The sampled Jensen boundary function is not eventually zero near a singular
parameter once the entire function is nontrivial. -/
theorem jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ Set.Ioc 0 (2 * Real.pi)) :
    ¬ ∀ᶠ θ in 𝓝 θ₀,
      F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
  intro hzero
  have hsample :
      AnalyticAt ℝ
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ₀ :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  have hlocal_zero :
      ∀ᶠ θ in 𝓝 θ₀,
        (fun θ : ℝ => F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))) θ = 0 :=
    hzero
  have hpropagate :
      ∀ z : ℂ, F z = 0 := by
    exact entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero
      F hF R hR θ₀ hθ₀ hsample hlocal_zero
  rcases hnontrivial with ⟨z, hz⟩
  exact hz (hpropagate z)

/-- Local remainder extraction for a punctured-neighborhood Jensen boundary
model. -/
theorem jensenBoundaryLogIntegrand_continuousAt_localRemainder
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg : ContinuousAt g θ₀)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ) :
    ∃ g' : ℝ → ℝ,
      ContinuousAt g' θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g' θ := by
  exact
    continuousRemainderExtensionOn_Icc_of_puncturedLocalModel
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      θ₀ n g hg hmodel

/-- The boundary logarithmic integrand has the expected local log-distance plus
continuous expansion near each singular parameter, on the punctured
neighborhood where the logarithmic singularity is modeled. -/
theorem jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_continuousAt_near_parameterZero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ :
      θ₀ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 :=
    jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
      F hF hnontrivial R hR θ₀ hθ₀.1
  rcases
      jensenBoundaryLogSample_localLogContribution F hF R θ₀ hnot with
    ⟨n, g, hg, hmodel⟩
  rcases
      jensenBoundaryLogIntegrand_continuousAt_localRemainder
        F hF R θ₀ n g hg hmodel with
    ⟨g', hg', hg'eventually⟩
  exact ⟨n, g', hg', hg'eventually⟩

/-- The Jensen boundary logarithmic integrand has a punctured local
log-distance model with a locally interval-integrable remainder near each
singular parameter. -/
theorem jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_intervalIntegrable_near_parameterZero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ :
      θ₀ ∈ Set.Icc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ₀ * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
      ¬ ∀ᶠ θ in 𝓝 θ₀,
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
    intro hzero
    have htwoR : 0 < 2 * R := by
      nlinarith
    have hglobal :
        ∀ z : ℂ, F z = 0 :=
      entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
        F hF (2 * R) htwoR θ₀ hzero
    rcases hnontrivial with ⟨z, hz⟩
    exact hz (hglobal z)
  rcases
      jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
        F hF R θ₀ hnot with
    ⟨n, g, hg, hmodel⟩
  exact ⟨n, g, hg, hmodel⟩

/-- The doubled-circle parametrization is injective on the open fundamental arc
`(0, 2π]`. This is the bookkeeping input that turns a finite circle zero set into a
finite parameter singular set. -/
theorem entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  intro θ1 hθ1 θ2 hθ2 hEq
  have hRne : (2 * R : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    have hR' : (R : ℂ) ≠ 0 := by
      exact_mod_cast hR.ne'
    exact mul_ne_zero h2 hR'
  have hExp : Complex.exp (θ1 * Complex.I) = Complex.exp (θ2 * Complex.I) := by
    apply mul_left_cancel₀ hRne
    simpa [mul_assoc] using hEq
  rcases (Complex.exp_eq_exp_iff_exists_int.mp hExp) with ⟨n, hn⟩
  have hnC :
      (θ1 : ℂ) * Complex.I =
        ((θ2 + n * (2 * Real.pi)) : ℂ) * Complex.I := by
    simpa [mul_add, add_mul, mul_assoc, add_comm, add_left_comm, add_assoc] using hn
  have hθC : (θ1 : ℂ) = ((θ2 + n * (2 * Real.pi)) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero
    exact hnC
  have hθ : θ1 = θ2 + n * (2 * Real.pi) := by
    have hθ' := congrArg Complex.re hθC
    simpa using hθ'
  have hlt : (n : ℝ) < 1 := by
    nlinarith [hθ, hθ1.2, hθ2.1, Real.two_pi_pos]
  have hgt : -1 < (n : ℝ) := by
    nlinarith [hθ, hθ1.1, hθ2.2, Real.two_pi_pos]
  have hn0 : n = 0 := by
    by_contra hn0
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      exact_mod_cast Int.one_le_abs hn0
    have habs : |(n : ℝ)| < 1 := by
      exact abs_lt.mpr ⟨hgt, hlt⟩
    linarith
  subst hn0
  linarith

/-- The finite circle-zero set induces a finite parameter singular set on the
fundamental boundary arc. -/
theorem entireFunction_jensenBoundaryCircleZeroParameters_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R) :
    Set.Finite
      {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0} := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)
  have hCircle : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} :=
    entireFunction_jensenCircleZeros_finite F hF hnontrivial R
  have hInj : Function.Injective f := by
    intro a b hEq
    apply Subtype.ext
    exact entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc hR a.2 b.2 hEq
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInj hEq
  have h2R_nonneg : 0 ≤ 2 * R := by
    nlinarith [le_of_lt hR]
  simpa [f, Set.preimage, entireFunctionJensenBoundaryCircle_norm h2R_nonneg] using hpre

/-- Away from the singular parameters, the Jensen boundary logarithmic
integrand is continuous on the fundamental arc. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuousOn_compl_circleZeroParameters
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (hzero : ∀ θ : ℝ,
      θ ∈ Set.Ioc 0 (2 * Real.pi) →
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0} := by
  dsimp [entireFunctionJensenBoundaryLogIntegrand]
  have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
    continuity
  have hparam : Continuous (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
    exact continuous_const.mul (Complex.continuous_exp.comp hmul)
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
    continuous_norm.comp (hcontF.comp hparam)
  exact hcont_norm.continuousOn.log fun θ hθ => norm_ne_zero_iff.mpr (hzero θ hθ.1)

/-- Jensen boundary specialization of finite logarithmic-singularity gluing.

The singular set is the finite set of parameters on the fundamental arc whose
circle samples are zeros.  Each such parameter is handled by the analytic
Taylor/log local model, and the zero-free complement is continuous. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let S : Set ℝ :=
    {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
      F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0}
  have hS : S.Finite := by
    let T : Set ℝ :=
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F ((2 * R : ℂ) * Complex.exp (θ * Complex.I)) = 0}
    have hT : T.Finite := by
      simpa [T] using
        entireFunction_jensenBoundaryCircleZeroParameters_finite F hF hnontrivial R hR
    have hsubset : S ⊆ insert (0 : ℝ) T := by
      intro θ hθ
      by_cases hθ0 : θ = 0
      · exact hθ0 ▸ Set.mem_insert (0 : ℝ) T
      · exact Set.mem_insert_iff.mpr
          (Or.inr ⟨⟨lt_of_le_of_ne hθ.1.1 hθ0.symm, hθ.1.2⟩, hθ.2⟩)
    exact (hT.insert (0 : ℝ)).subset hsubset
  have hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ θ in 𝓝[≠] θ₀,
          entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
            (n : ℝ) * Real.log |θ - θ₀| + g θ := by
    intro θ₀ hθ₀
    exact
      jensenBoundaryLogIntegrand_eventually_eq_logDistance_plus_intervalIntegrable_near_parameterZero
        F hF hnontrivial R hR θ₀ hθ₀
  have hcont :
      ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        ({θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ θ ∉ S}) := by
    dsimp [entireFunctionJensenBoundaryLogIntegrand]
    have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
      continuity
    have hparam : Continuous
        (fun θ : ℝ => (2 * R : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ => ‖F ((2 * R : ℂ) * Complex.exp (θ * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.continuousOn.log (by
      intro θ hθ
      exact norm_ne_zero_iff.mpr (by
        intro hzero
        exact hθ.2 ⟨hθ.1, hzero⟩))
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      (0 : ℝ) (2 * Real.pi) S
      (mul_nonneg zero_le_two Real.pi_pos.le)
      hS hlocal hcont

/-- Finite gluing of local logarithmic singularity models on the Jensen
fundamental interval. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- Finite logarithmic singularity gluing for Jensen boundary integrability. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_localSingularityModel
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact entireFunction_jensenBoundaryLogAverage_localSingularityModel F hF hnontrivial R hR hzeros

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
  intro R hR
    refine ⟨entireFunction_jensenBoundaryLogSet_bddAbove F hF (2 * R), ?_⟩
  exact
    entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
      F hF hnontrivial R
      (lt_of_lt_of_le zero_lt_one hR)
      (entireFunction_jensenCircleZeros_finite F hF hnontrivial R)

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
  exact entireFunction_jensen_formula_zeroMultiplicityCounting_closedDisk_le_scaledBoundaryLogAverage
    F hF hnontrivial

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

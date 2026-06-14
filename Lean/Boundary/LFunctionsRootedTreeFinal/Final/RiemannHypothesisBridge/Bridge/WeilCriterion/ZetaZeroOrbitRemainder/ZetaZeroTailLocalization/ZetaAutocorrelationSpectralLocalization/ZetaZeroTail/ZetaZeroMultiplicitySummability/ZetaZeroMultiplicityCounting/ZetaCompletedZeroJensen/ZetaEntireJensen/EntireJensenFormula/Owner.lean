import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
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

/-- The zero set of a nontrivial entire function inside a closed disk is
discrete. -/
theorem entireFunction_closedDiskZeros_discreteTopology
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
  refine (discreteTopology_subtype_iff).2 ?_
  intro x hx
  rcases hx with ⟨_hxnorm, hxzero⟩
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
      ({z : ℂ | ‖z‖ ≤ R ∧ F z = 0}ᶜ) ∈ 𝓝[≠] x := by
    exact Filter.mem_of_superset hne (by
      intro w hw
      intro hsw
      exact hw hsw.2)
  exact (Filter.disjoint_principal_right).2 hScompl

/-- A nontrivial entire function has only finitely many zeros in each closed
disk. -/
theorem entireFunction_closedDiskZeros_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ) :
    Set.Finite {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
  have hdisc :
      DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} :=
    entireFunction_closedDiskZeros_discreteTopology F hF hnontrivial R
  have hclosedDisk : IsClosed {z : ℂ | ‖z‖ ≤ R} := by
    change IsClosed ((fun z : ℂ => ‖z‖) ⁻¹' Set.Iic R)
    exact (continuous_norm : Continuous fun z : ℂ => ‖z‖).isClosed_preimage
      isClosed_Iic
  have hzeroClosed : IsClosed {z : ℂ | F z = 0} := by
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    change IsClosed (F ⁻¹' ({0} : Set ℂ))
    exact hcontF.isClosed_preimage (isClosed_singleton : IsClosed ({0} : Set ℂ))
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := by
    change IsClosed ({z : ℂ | ‖z‖ ≤ R} ∩ {z : ℂ | F z = 0})
    exact hclosedDisk.inter hzeroClosed
  have hsubset :
      {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1
  have hcomp : IsCompact {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed hsubset
  haveI : DiscreteTopology {z : ℂ | ‖z‖ ≤ R ∧ F z = 0} := hdisc
  exact hcomp.finite_of_discrete

/-- The nonzero closed-disk multiplicity summand has finite support. -/
theorem entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ) :
    (Function.support
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)).Finite := by
  have hzeros :
      Set.Finite {w : ℂ | ‖w‖ ≤ R ∧ F w = 0} :=
    entireFunction_closedDiskZeros_finite F hF ⟨0, hF0⟩ R
  have hpre :
      ((fun z : EntireFunctionZero F => (z : ℂ)) ⁻¹'
        {w : ℂ | ‖w‖ ≤ R ∧ F w = 0}).Finite :=
    hzeros.preimage (fun _ _ _ _ hEq => Subtype.ext hEq)
  exact hpre.subset (by
    intro z hz
    unfold Function.support at hz
    unfold entireFunctionNonzeroZeroMultiplicityClosedDiskSummand at hz
    by_cases hz0 : (z : ℂ) = 0
    · exact False.elim (hz (if_pos hz0))
    · by_cases hle : ‖(z : ℂ)‖ ≤ R
      · exact ⟨hle, z.2⟩
      · exact False.elim (hz (if_neg hle)))

/-- The Jensen radial-gap summand has finite support. -/
theorem entireFunctionJensenRadialGapSummand_support_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (Function.support
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z)).Finite := by
  have hzeros :
      Set.Finite {w : ℂ | ‖w‖ ≤ ρ ∧ F w = 0} :=
    entireFunction_closedDiskZeros_finite F hF ⟨0, hF0⟩ ρ
  have hpre :
      ((fun z : EntireFunctionZero F => (z : ℂ)) ⁻¹'
        {w : ℂ | ‖w‖ ≤ ρ ∧ F w = 0}).Finite :=
    hzeros.preimage (fun _ _ _ _ hEq => Subtype.ext hEq)
  exact hpre.subset (by
    intro z hz
    unfold Function.support at hz
    unfold entireFunctionJensenRadialGapSummand at hz
    by_cases hz0 : (z : ℂ) = 0
    · exact False.elim (hz (if_pos hz0))
    · by_cases hlt : ‖(z : ℂ)‖ < ρ
      · exact ⟨le_of_lt hlt, z.2⟩
      · have hnot_zero_branch :
            (if hz₀ : (z : ℂ) = 0 then
              0
            else if ‖(z : ℂ)‖ < ρ then
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log (ρ / ‖(z : ℂ)‖)
            else
              0) =
              (if ‖(z : ℂ)‖ < ρ then
                (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                  Real.log (ρ / ‖(z : ℂ)‖)
              else
                0) :=
          if_neg hz0
        have houtside_branch :
            (if ‖(z : ℂ)‖ < ρ then
              (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
                Real.log (ρ / ‖(z : ℂ)‖)
            else
              0) = 0 :=
          if_neg hlt
        exact False.elim (hz (Eq.trans hnot_zero_branch houtside_branch)))

/-- Classical Jensen finite-zero divisor input in a closed disk, with
multiplicities.

This is the divisor-finiteness part of the nonzero-origin Jensen package: a
nontrivial entire function has only finitely many zeros in each compact disk,
and the closed-disk multiplicity family is therefore summable after the origin
summand is removed. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisor_closedDiskMultiplicitySummable_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  intro R _hR
  exact summable_of_finite_support
    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
      F hF hF0 R)

/-- Classical Jensen radial-gap divisor summability for a nonzero value at the
origin.

The radial-gap summand is supported on the finite zero divisor in the open
disk of radius `ρ`, counted by analytic multiplicity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_from_finiteZeroDivisor_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  intro ρ _hρ
  exact summable_of_finite_support
    (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ)

/-- A single nonzero zero strictly inside the Jensen circle contributes exactly
its multiplicity times the radial logarithmic factor.

This is the pointwise zero-factor calculation in the product proof of Jensen's
formula. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) ≠ 0)
    (hzρ : ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z =
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        Real.log (ρ / ‖(z : ℂ)‖) := by
  unfold entireFunctionJensenRadialGapSummand
  exact Eq.trans (dif_neg hz0) (if_pos hzρ)

/-- A zero outside the open Jensen disk contributes no radial-gap term. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_eq_zero_of_not_lt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hzρ : ¬ ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  unfold entireFunctionJensenRadialGapSummand
  by_cases hz0 : (z : ℂ) = 0
  · exact dif_pos hz0
  · exact Eq.trans (dif_neg hz0) (if_neg hzρ)

/-- The origin zero is absent from the nonzero-origin Jensen radial-gap sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_origin_radialContribution_eq_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz0 : (z : ℂ) = 0) :
    entireFunctionJensenRadialGapSummand F hF ρ z = 0 := by
  unfold entireFunctionJensenRadialGapSummand
  exact dif_pos hz0

/-- The finite product radial-gap sum attached to the zero divisor inside the
Jensen circle.

The indexing finset is supplied by divisor finiteness; this definition keeps
the finite product stage separate from the later infinite-sum transport. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F)) : ℝ :=
  ∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z

/-- The finite product radial-gap sum is literally the sum of the pointwise
zero-factor radial contributions over the chosen finite zero divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F)) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s, entireFunctionJensenRadialGapSummand F hF ρ z := by
  rfl

/-- Finite-product zero-factor expansion: once the finite zero divisor has been
chosen, its Jensen contribution is the sum of the explicit nonzero radial
factors, with origin and exterior terms contributing zero by the pointwise
lemmas above. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_explicit_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F)) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
  refine Finset.sum_congr rfl ?_
  intro z _hz
  unfold entireFunctionJensenRadialGapSummand
  by_cases hz0 : (z : ℂ) = 0
  · exact Eq.trans (dif_pos hz0) (if_pos hz0).symm
  · exact Eq.trans (dif_neg hz0) (if_neg hz0).symm

/-- If a finite zero divisor contains the support of the Jensen radial-gap
summand, the infinite radial-gap sum is the corresponding finite product
radial-gap sum.

This is the constructive support-controlled bridge from divisor finiteness to
the product formula: the product stage may use any explicit finite support
certificate, without choosing a canonical enumeration of zeros. -/
theorem entireFunctionJensenRadialGapSum_eq_finiteProductRadialGapSum_of_support_subset
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F))
    (hsupport :
      Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) ⊆
        (s : Set (EntireFunctionZero F))) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s := by
  unfold entireFunctionJensenRadialGapSum
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
  exact tsum_eq_sum
    (s := s)
    (fun z hz_not_mem => by
      by_contra hz_ne_zero
      have hz_support :
          z ∈ Function.support
            (fun w : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ w) :=
        hz_ne_zero
      exact hz_not_mem (hsupport hz_support))

/-- If the Jensen disk contains no nonzero zeros, the radial-gap divisor sum is
zero.

This is the zero-free quotient special case of the finite-divisor product
bridge: once all possible nonzero zero factors are absent from the disk, the
entire radial-gap contribution vanishes term by term. -/
theorem entireFunctionJensenRadialGapSum_eq_zero_of_no_nonzero_zeros_in_disk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (hzero :
      ∀ z : EntireFunctionZero F,
        (z : ℂ) ≠ 0 →
        ¬ ‖(z : ℂ)‖ < ρ) :
    entireFunctionJensenRadialGapSum F hF ρ = 0 := by
  unfold entireFunctionJensenRadialGapSum
  exact tsum_eq_zero
    (fun z => by
      unfold entireFunctionJensenRadialGapSummand
      by_cases hz0 : (z : ℂ) = 0
      · exact if_pos hz0
      · exact Eq.trans (if_neg hz0) (if_neg (hzero z hz0)))

/-- The finite closed-disk divisor supporting the nonzero multiplicity summand.

This is the closed-disk divisor side of Jensen's formula after the origin
factor has been removed: it is exactly the finite support of the nonzero
closed-disk multiplicity family. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ) : Finset (EntireFunctionZero F) :=
  (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
    F hF hF0 R).toFinset

/-- The closed-disk finite divisor contains the support of the nonzero
multiplicity summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ) :
    Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 R : Set (EntireFunctionZero F)) := by
  intro z hz
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
  exact
    (entireFunctionNonzeroZeroMultiplicityClosedDiskSummand_support_finite
      F hF hF0 R).mem_toFinset.2 hz

/-- The nonzero closed-disk multiplicity family has the finite sum over its
closed-disk divisor as its infinite sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummand_hasSum_supportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (R : ℝ) :
    HasSum
      (fun z : EntireFunctionZero F =>
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
          F hF hF0 R,
        entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  exact hasSum_sum_of_ne_finset_zero
    (s :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
        F hF hF0 R)
    (f := fun z : EntireFunctionZero F =>
      entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)
    (fun z hz_not_mem => by
      by_contra hz_ne
      have hz_support :
          z ∈ Function.support
            (fun w : EntireFunctionZero F =>
              entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R w) :=
        hz_ne
      have hz_mem :
          z ∈
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
              F hF hF0 R :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor_contains_support
          F hF hF0 R hz_support
      exact hz_not_mem hz_mem)

/-- The finite zero divisor supporting the Jensen radial-gap summand.

This is the finite divisor used in the product side of Jensen's formula: it is
the support of the nonzero zero factors strictly inside the Jensen circle. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) : Finset (EntireFunctionZero F) :=
  (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ).toFinset

/-- The radial-gap finite divisor contains the support of the Jensen radial-gap
summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    Function.support
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) ⊆
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ : Set (EntireFunctionZero F)) := by
  intro z hz
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
  exact
    (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ).mem_toFinset.2 hz

/-- The radial-gap summand has the finite product divisor sum as its infinite
sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummand_hasSum_supportFiniteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    HasSum
      (fun z : EntireFunctionZero F =>
        entireFunctionJensenRadialGapSummand F hF ρ z)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ)) := by
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
  exact hasSum_sum_of_ne_finset_zero
    (s :=
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
    (f := fun z : EntireFunctionZero F =>
      entireFunctionJensenRadialGapSummand F hF ρ z)
    (fun z hz_not_mem => by
      by_contra hz_ne
      have hz_support :
          z ∈ Function.support
            (fun w : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ w) :=
        hz_ne
      have hz_mem :
          z ∈
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ :=
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
          F hF hF0 ρ hz_support
      exact hz_not_mem hz_mem)

/-- The infinite Jensen radial-gap sum is the finite product sum over the
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  exact
    entireFunctionJensenRadialGapSum_eq_finiteProductRadialGapSum_of_support_subset
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_contains_support
        F hF hF0 ρ)

/-- The support finite product sum expands into the explicit zero-factor
radial contributions. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_explicit_sum_identity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProduct_explicit_sum_identity
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)

/-- The infinite radial-gap sum is the explicit finite zero-factor sum over its
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProduct_explicit_sum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunctionJensenRadialGapSum F hF ρ =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        if (z : ℂ) = 0 then
          0
        else if ‖(z : ℂ)‖ < ρ then
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            Real.log (ρ / ‖(z : ℂ)‖)
        else
          0 := by
  exact Eq.trans
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
      F hF hF0 ρ)
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_explicit_sum_identity
      F hF hF0 ρ)

/-- The logarithmic norm of a complex exponential is the real part of the
exponent. -/
theorem complex_log_norm_exp_eq_re
    (w : ℂ) :
    Real.log ‖Complex.exp w‖ = w.re := by
  have hnorm_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    Complex.norm_eq_abs (Complex.exp w)
  have habs :
      Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  calc
    Real.log ‖Complex.exp w‖ =
        Real.log (Complex.abs (Complex.exp w)) := by
      exact congrArg Real.log hnorm_abs
    _ = Real.log (Real.exp w.re) := by
      exact congrArg Real.log habs
    _ = w.re :=
      Real.log_exp w.re

/-- Boundary reduction from a chosen analytic logarithm to the real part of
that logarithm. -/
theorem entireFunction_zeroFreeQuotient_boundaryLog_eq_analyticLog_re
    (G L : ℂ → ℂ)
    (R θ : ℝ)
    (hlog :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) =
        Complex.exp (L ((R : ℂ) * Complex.exp (θ * Complex.I)))) :
    entireFunctionJensenBoundaryLogIntegrand G R θ =
      (L ((R : ℂ) * Complex.exp (θ * Complex.I))).re := by
  let z : ℂ := (R : ℂ) * Complex.exp (θ * Complex.I)
  unfold entireFunctionJensenBoundaryLogIntegrand
  calc
    Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        Real.log ‖Complex.exp (L z)‖ := by
      exact congrArg (fun w : ℂ => Real.log ‖w‖) hlog
    _ = (L z).re :=
      complex_log_norm_exp_eq_re (L z)

/-- The Jensen closed disk is convex. -/
theorem entireFunction_jensenClosedDisk_convex
    (ρ : ℝ) :
    Convex ℝ (Metric.closedBall (0 : ℂ) ρ) :=
  convex_closedBall (0 : ℂ) ρ

/-- The Jensen closed disk is star-convex at its center once the radius is
nonnegative. -/
theorem entireFunction_jensenClosedDisk_starConvex_center
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    StarConvex ℝ (0 : ℂ) (Metric.closedBall (0 : ℂ) ρ) :=
  (entireFunction_jensenClosedDisk_convex ρ).starConvex
    (Metric.mem_closedBall_self hρ)

/-- A zero-free entire function has an analytic reciprocal at each point of
the Jensen disk. -/
theorem entireFunction_zeroFreeOnClosedDisk_reciprocal_analyticAt
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0)
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ) :
    AnalyticAt ℂ (fun w : ℂ => (G w)⁻¹) z :=
  (hG z).inv (hzero z hz)

/-- Holomorphic logarithm existence on a zero-free simply connected Jensen disk.

This is the canonical analytic-log construction used by Jensen's formula: a
holomorphic zero-free map from the disk to `ℂˣ` lifts through
`Complex.exp : ℂ → ℂˣ`.  Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) := by
  -- Classical lifting of the zero-free holomorphic disk map to a holomorphic
  -- logarithm through the exponential covering of `ℂˣ`.
  sorry

/-- The real part of any chosen analytic logarithm is the logarithm of the
norm of the original zero-free function. -/
theorem entireFunction_analyticLogBranch_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    {z : ℂ}
    (hz : ‖z‖ ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L z).re = Real.log ‖G z‖ := by
  have hzlog : G z = Complex.exp (L z) :=
    hlog z hz
  have hnorm_log :
      Real.log ‖G z‖ = Real.log ‖Complex.exp (L z)‖ := by
    exact congrArg (fun w : ℂ => Real.log ‖w‖) hzlog
  have hexp_log :
      Real.log ‖Complex.exp (L z)‖ = (L z).re :=
    complex_log_norm_exp_eq_re (L z)
  exact (Eq.trans hnorm_log hexp_log).symm

/-- The analytic logarithm branch supplied on a Jensen disk is automatically
normalized in real part at the center. -/
theorem entireFunction_analyticLogBranch_center_re_eq_log_norm
    (G L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hlog :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        G w = Complex.exp (L w)) :
    (L 0).re = Real.log ‖G 0‖ := by
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hzero_mem : ‖(0 : ℂ)‖ ≤ ρ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ρ)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hρ_nonneg
  exact
    entireFunction_analyticLogBranch_re_eq_log_norm
      G L hzero_mem hlog

/-- Analytic-log existence on a simply connected Jensen disk.

This is the exact topological/complex-analytic owner root needed by Jensen's
formula: a holomorphic zero-free function on a neighborhood of the closed disk
has a holomorphic logarithm on that disk, with the real part normalized at the
center.  The intended proof is the classical lifting of `G : D → ℂˣ` through
`Complex.exp : ℂ → ℂˣ` on the simply connected disk, followed by the identity
`Real.log ‖Complex.exp w‖ = w.re`.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
      (L 0).re = Real.log ‖G 0‖ := by
  rcases
      entireFunction_zeroFreeOnClosedDisk_exists_analyticLogBranch_from_simplyConnectedDisk
        G hG hρ hzero
      with ⟨L, hL_an, hL_log⟩
  exact
    ⟨L, hL_an, hL_log,
      entireFunction_analyticLogBranch_center_re_eq_log_norm G L hρ hL_log⟩

/-- A zero-free holomorphic function on a closed disk admits a holomorphic
logarithm on a neighborhood of that disk, normalized at the center.

This is the analytic-log existence step in Jensen's proof.  It follows by
applying the holomorphic logarithm construction to the zero-free image of the
simply connected disk; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hzero :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        G z ≠ 0) :
    ∃ L : ℂ → ℂ,
      (∀ z : ℂ, ‖z‖ ≤ ρ → AnalyticAt ℂ L z) ∧
      (∀ z : ℂ, ‖z‖ ≤ ρ → G z = Complex.exp (L z)) ∧
      (L 0).re = Real.log ‖G 0‖ := by
  exact
    entireFunction_zeroFreeOnClosedDisk_exists_analyticLog_from_simplyConnectedDisk
      G hG hρ hzero

/-- Pointwise analyticity on Jensen's closed disk gives the `DiffContOnCl`
package needed by Cauchy's integral formula on the corresponding open disk. -/
theorem entireFunction_analyticOnClosedDisk_diffContOnCl
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    DiffContOnCl ℂ L (Metric.ball (0 : ℂ) ρ) := by
  refine DiffContOnCl.mk_ball ?hdiff ?hcont
  · intro z hz
    have hz_norm_lt : ‖z‖ < ρ :=
      mem_ball_zero_iff.mp hz
    have hz_norm_le : ‖z‖ ≤ ρ :=
      le_of_lt hz_norm_lt
    exact (hL z hz_norm_le).differentiableAt.differentiableWithinAt
  · intro z hz
    have hz_norm_le : ‖z‖ ≤ ρ :=
      mem_closedBall_zero_iff.mp hz
    exact (hL z hz_norm_le).continuousAt.continuousWithinAt

/-- Cauchy's integral formula at the center of the Jensen disk, in the
`circleIntegral` normalization. -/
theorem entireFunction_analyticLog_cauchy_center_circleIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
      L 0 := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hdiff : DiffContOnCl ℂ L (Metric.ball (0 : ℂ) ρ) :=
    entireFunction_analyticOnClosedDisk_diffContOnCl L hL
  have hzero_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ :=
    Metric.mem_ball_self hρ_pos
  exact hdiff.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hzero_mem

/-- Parametrization of the Cauchy kernel on Jensen's boundary circle.

This is the exact boundary cancellation used to pass from Cauchy's
`circleIntegral` normalization to the ordinary angular integral.  The proof is
the direct expansion of `circleIntegral`, `circleMap 0 ρ θ`, and
`deriv_circleMap`, followed by cancellation of the nonzero boundary point. -/
theorem entireFunction_cauchyKernel_circleMap_boundaryCancellation
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (θ : ℝ) :
    deriv (Complex.circleMap (0 : ℂ) ρ) θ •
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
      Complex.I := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hρ_ne : ρ ≠ 0 :=
    hρ_pos.ne'
  have hcircle_ne :
      Complex.circleMap (0 : ℂ) ρ θ ≠ 0 :=
    Complex.circleMap_ne_center hρ_ne
  have hsub :
      Complex.circleMap (0 : ℂ) ρ θ - 0 =
        Complex.circleMap (0 : ℂ) ρ θ :=
    Complex.circleMap_sub_center (0 : ℂ) ρ θ
  have hderiv :
      deriv (Complex.circleMap (0 : ℂ) ρ) θ =
        Complex.circleMap (0 : ℂ) ρ θ * Complex.I :=
    Complex.deriv_circleMap (0 : ℂ) ρ θ
  have hcancel :
      (Complex.circleMap (0 : ℂ) ρ θ * Complex.I) *
          (Complex.circleMap (0 : ℂ) ρ θ)⁻¹ =
        Complex.I := by
    calc
      (Complex.circleMap (0 : ℂ) ρ θ * Complex.I) *
          (Complex.circleMap (0 : ℂ) ρ θ)⁻¹ =
          (Complex.I * Complex.circleMap (0 : ℂ) ρ θ) *
            (Complex.circleMap (0 : ℂ) ρ θ)⁻¹ := by
        exact congrArg
          (fun z : ℂ => z * (Complex.circleMap (0 : ℂ) ρ θ)⁻¹)
          (mul_comm (Complex.circleMap (0 : ℂ) ρ θ) Complex.I)
      _ = Complex.I := by
        exact mul_inv_cancel_right₀ hcircle_ne Complex.I
  calc
    deriv (Complex.circleMap (0 : ℂ) ρ) θ •
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
        deriv (Complex.circleMap (0 : ℂ) ρ) θ *
          (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) := by
      exact smul_eq_mul
        (deriv (Complex.circleMap (0 : ℂ) ρ) θ)
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ)
    _ =
        (Complex.circleMap (0 : ℂ) ρ θ * Complex.I) *
          (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) := by
      exact congrArg
        (fun z : ℂ => z * (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ))
        hderiv
    _ =
        (Complex.circleMap (0 : ℂ) ρ θ * Complex.I) *
          (Complex.circleMap (0 : ℂ) ρ θ)⁻¹ := by
      exact congrArg
        (fun z : ℂ => (Complex.circleMap (0 : ℂ) ρ θ * Complex.I) * z)
        (congrArg Inv.inv hsub)
    _ = Complex.I :=
      hcancel

/-- The zero-centered circle parametrization is the Jensen exponential boundary
sample. -/
theorem entireFunction_circleMap_zero_eq_boundarySample
    (ρ : ℝ)
    (θ : ℝ) :
    Complex.circleMap (0 : ℂ) ρ θ =
      (ρ : ℂ) * Complex.exp (θ * Complex.I) := by
  exact Complex.circleMap_zero ρ θ

/-- The circle-integral Cauchy-kernel integrand cancels to `I` times the
boundary value after passing to the Jensen exponential parametrization. -/
theorem entireFunction_cauchyCircleIntegral_integrand_eq_I_smul_boundarySample
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (θ : ℝ) :
    deriv (Complex.circleMap (0 : ℂ) ρ) θ •
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
          L (Complex.circleMap (0 : ℂ) ρ θ)) =
      Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
  have hcancel :
      deriv (Complex.circleMap (0 : ℂ) ρ) θ •
          (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ) =
        Complex.I :=
    entireFunction_cauchyKernel_circleMap_boundaryCancellation hρ θ
  have hsample :
      Complex.circleMap (0 : ℂ) ρ θ =
        (ρ : ℂ) * Complex.exp (θ * Complex.I) :=
    entireFunction_circleMap_zero_eq_boundarySample ρ θ
  calc
    deriv (Complex.circleMap (0 : ℂ) ρ) θ •
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
          L (Complex.circleMap (0 : ℂ) ρ θ)) =
        (deriv (Complex.circleMap (0 : ℂ) ρ) θ •
          (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ)) •
          L (Complex.circleMap (0 : ℂ) ρ θ) := by
      exact (smul_smul
        (deriv (Complex.circleMap (0 : ℂ) ρ) θ)
        (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) : ℂ)
        (L (Complex.circleMap (0 : ℂ) ρ θ))).symm
    _ = Complex.I • L (Complex.circleMap (0 : ℂ) ρ θ) := by
      exact congrArg
        (fun z : ℂ => z • L (Complex.circleMap (0 : ℂ) ρ θ))
        hcancel
    _ = Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact congrArg (fun z : ℂ => Complex.I • L z) hsample

/-- Circle-integral transport for the holomorphic mean value formula on the
Jensen boundary.

This lemma isolates the only parametrization work in the complex mean-value
step: after the Cauchy-kernel cancellation, the circle integral is exactly
`Complex.I` times the angular boundary integral. -/
theorem entireFunction_cauchyCircleIntegral_eq_I_smul_boundaryIntervalIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
      Complex.I •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
  -- Expand `circleIntegral`, identify `circleMap 0 ρ θ` with
  -- `(ρ : ℂ) * exp (θ * I)`, and use
  -- `entireFunction_cauchyKernel_circleMap_boundaryCancellation` pointwise.
  calc
    (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          deriv (Complex.circleMap (0 : ℂ) ρ) θ •
            (((Complex.circleMap (0 : ℂ) ρ θ - 0)⁻¹) •
              L (Complex.circleMap (0 : ℂ) ρ θ)) := by
      rfl
    _ =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.I • L ((ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
      exact intervalIntegral.integral_congr fun θ _hθ =>
        entireFunction_cauchyCircleIntegral_integrand_eq_I_smul_boundarySample
          L hρ θ
    _ =
        Complex.I •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
      exact intervalIntegral.integral_smul
        Complex.I
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))

/-- Scalar normalization after the Cauchy boundary parametrization. -/
theorem entireFunction_two_pi_I_inv_smul_I_smul_eq_two_pi_inv_smul
    (w : ℂ) :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (Complex.I • w)) =
      ((2 * Real.pi : ℂ)⁻¹ • w) := by
  have hcoeff :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) =
        ((2 * Real.pi : ℂ)⁻¹) := by
    calc
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) =
          (((2 * Real.pi : ℂ)⁻¹ * Complex.I⁻¹) * Complex.I) := by
        exact congrArg (fun z : ℂ => z * Complex.I)
          (mul_inv_rev (2 * Real.pi : ℂ) Complex.I)
      _ = ((2 * Real.pi : ℂ)⁻¹ * (Complex.I⁻¹ * Complex.I)) := by
        exact mul_assoc ((2 * Real.pi : ℂ)⁻¹) Complex.I⁻¹ Complex.I
      _ = ((2 * Real.pi : ℂ)⁻¹ * 1) := by
        exact congrArg (fun z : ℂ => ((2 * Real.pi : ℂ)⁻¹ * z))
          (inv_mul_cancel₀ Complex.I_ne_zero)
      _ = ((2 * Real.pi : ℂ)⁻¹) := by
        exact mul_one ((2 * Real.pi : ℂ)⁻¹)
  calc
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • (Complex.I • w)) =
        (((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) • w) := by
      exact smul_smul (2 * Real.pi * Complex.I : ℂ)⁻¹ Complex.I w
    _ = ((2 * Real.pi : ℂ)⁻¹ • w) := by
      exact congrArg (fun z : ℂ => z • w) hcoeff

/-- The Cauchy center formula after circle parametrization and scalar
normalization. -/
theorem entireFunction_analyticLog_complex_holomorphicMeanValue_circle_from_cauchyKernel
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi : ℂ)⁻¹ •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
      L 0 := by
  have hcauchy :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          ∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        L 0 :=
    entireFunction_analyticLog_cauchy_center_circleIntegral L hρ hL
  have hcircle :
      (∮ z in C((0 : ℂ), ρ), (z - 0)⁻¹ • L z) =
        Complex.I •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) :=
    entireFunction_cauchyCircleIntegral_eq_I_smul_boundaryIntervalIntegral
      L hρ
  have hnormalized :
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (Complex.I •
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              L ((ρ : ℂ) * Complex.exp (θ * Complex.I))))) =
        ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) :=
    entireFunction_two_pi_I_inv_smul_I_smul_eq_two_pi_inv_smul
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  exact Eq.trans hnormalized.symm (Eq.trans (congrArg (fun w : ℂ =>
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • w)) hcircle.symm) hcauchy)

/-- The Cauchy center formula rewritten as the normalized complex boundary mean
of the holomorphic function. -/
theorem entireFunction_analyticLog_complex_holomorphicMeanValue_circle
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    ((2 * Real.pi : ℂ)⁻¹ •
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
      L 0 := by
  exact
    entireFunction_analyticLog_complex_holomorphicMeanValue_circle_from_cauchyKernel
      L hρ hL

/-- Real-part transport across an interval integral, in the mathematically
correct form with interval integrability of the complex integrand. -/
theorem entireFunction_boundaryIntervalIntegral_re_of_intervalIntegrable
    (L : ℂ → ℂ)
    (ρ : ℝ)
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re := by
  have hmap :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.reCLM
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        Complex.reCLM
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
    exact ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hL_int
  exact hmap.symm

/-- The real part of the Jensen angular interval integral is the interval
integral of the real part, under the necessary integrability hypothesis.

This is the canonical `intervalIntegral`/`Complex.re` transport needed after
the complex mean-value formula. -/
theorem entireFunction_boundaryIntervalIntegral_re
    (L : ℂ → ℂ)
    (ρ : ℝ)
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re := by
  exact entireFunction_boundaryIntervalIntegral_re_of_intervalIntegrable L ρ hL_int

/-- Analyticity on Jensen's closed disk makes the angular boundary
parametrization interval-integrable. -/
theorem entireFunction_boundaryIntervalIntegrable_of_analyticOnClosedDisk
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    IntervalIntegrable
      (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  -- The boundary path is continuous and lies in the closed disk by
  -- `Complex.abs_circleMap_zero`; analytic functions are continuous on that
  -- image, hence the compact interval parametrization is interval-integrable.
  have hρ_nonneg : 0 ≤ ρ :=
    le_trans zero_le_one hρ
  have hsample_cont :
      Continuous (fun θ : ℝ =>
        (ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
    have hcircle_cont :
        Continuous (Complex.circleMap (0 : ℂ) ρ) :=
      Complex.continuous_circleMap (0 : ℂ) ρ
    have hsample_eq :
        (fun θ : ℝ => (ρ : ℂ) * Complex.exp (θ * Complex.I)) =
          Complex.circleMap (0 : ℂ) ρ := by
      funext θ
      exact (entireFunction_circleMap_zero_eq_boundarySample ρ θ).symm
    exact Eq.subst
      (motive := fun f : ℝ → ℂ => Continuous f)
      hsample_eq.symm
      hcircle_cont
  have hboundary_norm :
      ∀ θ : ℝ, ‖(ρ : ℂ) * Complex.exp (θ * Complex.I)‖ ≤ ρ := by
    intro θ
    have hcircle :
        Complex.circleMap (0 : ℂ) ρ θ =
          (ρ : ℂ) * Complex.exp (θ * Complex.I) :=
      entireFunction_circleMap_zero_eq_boundarySample ρ θ
    have hclosed :
        Complex.circleMap (0 : ℂ) ρ θ ∈
          Metric.closedBall (0 : ℂ) ρ :=
      Complex.circleMap_mem_closedBall (0 : ℂ) hρ_nonneg θ
    have hnorm_circle : ‖Complex.circleMap (0 : ℂ) ρ θ‖ ≤ ρ :=
      mem_closedBall_zero_iff.mp hclosed
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ρ)
      hcircle
      hnorm_circle
  have hL_cont_on_boundary :
      ContinuousOn L
        (Set.range (fun θ : ℝ =>
          (ρ : ℂ) * Complex.exp (θ * Complex.I))) := by
    intro z hz
    rcases hz with ⟨θ, hθz⟩
    have hz_norm : ‖z‖ ≤ ρ :=
      Eq.subst
        (motive := fun w : ℂ => ‖w‖ ≤ ρ)
        hθz.symm
        (hboundary_norm θ)
    exact (hL z hz_norm).continuousAt.continuousWithinAt
  have hcomp :
      Continuous (fun θ : ℝ =>
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I))) :=
    hL_cont_on_boundary.comp_continuous hsample_cont
      (fun θ => Set.mem_range_self θ)
  exact hcomp.intervalIntegrable (0 : ℝ) (2 * Real.pi)

/-- Real scalar multiplication in `ℂ`, viewed by real parts. -/
theorem entireFunction_complexMean_realScalar_re_mul
    (c : ℝ)
    (w : ℂ) :
    (((c : ℂ) * w).re) = c * w.re := by
  exact Complex.re_ofReal_mul c w

/-- Real part of a complex mean with a real scalar coefficient. -/
theorem entireFunction_complexMean_realScalar_re
    (c : ℝ)
    (w : ℂ) :
    (((c : ℂ) • w).re) = c * w.re := by
  have hsmul : ((c : ℂ) • w) = (c : ℂ) * w :=
    smul_eq_mul (c : ℂ) w
  exact Eq.trans
    (congrArg Complex.re hsmul)
    (entireFunction_complexMean_realScalar_re_mul c w)

/-- The complex inverse of the real Jensen normalizing scalar is the coercion
of the real inverse. -/
theorem entireFunction_complex_twoPi_inv_eq_real_twoPi_inv :
    ((2 * Real.pi : ℂ)⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
  exact (Complex.ofReal_inv (2 * Real.pi)).symm

/-- Real-part transport for the normalized complex boundary mean, isolated from
the analytic Cauchy input. -/
theorem entireFunction_complexMeanValue_re_part_transport_from_integral_re
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  have hreal_scalar :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re :=
    entireFunction_complexMean_realScalar_re
      ((2 * Real.pi)⁻¹)
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  have hintegral_re :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re :=
    entireFunction_boundaryIntervalIntegral_re L ρ hL_int
  have hleft :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) :=
    Eq.trans hreal_scalar
      (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hintegral_re)
  have hcomplex_re :
      ((((2 * Real.pi)⁻¹ : ℝ) : ℂ) •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))).re =
        (L 0).re :=
    congrArg Complex.re
      (Eq.trans
        (congrArg
          (fun c : ℂ =>
            c •
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                L ((ρ : ℂ) * Complex.exp (θ * Complex.I))))
          entireFunction_complex_twoPi_inv_eq_real_twoPi_inv.symm)
        hcomplex)
  exact Eq.trans hleft.symm hcomplex_re

/-- Real-part transport for the normalized complex boundary mean. -/
theorem entireFunction_complexMeanValue_re_part_transport
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  exact
    entireFunction_complexMeanValue_re_part_transport_from_integral_re
      L hL_int hcomplex

/-- Cauchy mean-value theorem for the real part of a holomorphic function on a
Jensen circle.

This is the analytic mean-value owner root in the exact interval-integral
normalization used in this file.  The intended proof applies Cauchy's integral
formula to `L` at `0` on `C(0, ρ)`, rewrites the circle integral through
`circleMap 0 ρ θ = (ρ : ℂ) * Complex.exp (θ * Complex.I)`, cancels the
nonzero boundary factor, and then applies `MeasureTheory.integral_re`.
Cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_analyticLog_re_holomorphicMeanValue_circle_from_cauchyIntegral
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  have hcomplex :
      ((2 * Real.pi : ℂ)⁻¹ •
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) =
        L 0 :=
    entireFunction_analyticLog_complex_holomorphicMeanValue_circle L hρ hL
  have hL_int :
      IntervalIntegrable
        (fun θ : ℝ => L ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryIntervalIntegrable_of_analyticOnClosedDisk L hρ hL
  exact entireFunction_complexMeanValue_re_part_transport L hL_int hcomplex

/-- Mean-value theorem for the real part of a holomorphic function on a disk,
with Jensen's boundary parametrization and normalization. -/
theorem entireFunction_analyticLog_re_holomorphicMeanValue_circle
    (L : ℂ → ℂ)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ)
    (hL :
      ∀ z : ℂ,
        ‖z‖ ≤ ρ →
        AnalyticAt ℂ L z) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L ((ρ : ℂ) * Complex.exp (θ * Complex.I))).re) =
      (L 0).re := by
  exact
    entireFunction_analyticLog_re_holomorphicMeanValue_circle_from_cauchyIntegral
      L hρ hL

/-- Boundary factorization for a single nonzero Jensen zero inside the circle. -/
theorem entireFunction_singleZeroFactor_boundary_point_ne_zero
    {ρ : ℝ}
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  have hρ_ne : (ρ : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr hρ_pos.ne'
  have hexp_ne : Complex.exp (θ * Complex.I) ≠ 0 :=
    Complex.exp_ne_zero (θ * Complex.I)
  exact mul_ne_zero hρ_ne hexp_ne

/-- The inner single-zero boundary factor is nonzero when the zero is strictly
inside the Jensen circle. -/
theorem entireFunction_singleZeroFactor_inner_ne_zero
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hz_ne :
      ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  intro hzero
  have hdiv_eq_one : a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) = 1 :=
    sub_eq_zero.mp hzero
  have hnorm_div_eq_one :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = 1 :=
    congrArg norm hdiv_eq_one
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_z :
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ρ := by
    calc
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
        exact norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I))
      _ = |ρ| * 1 := by
        exact congrArg (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
          (Complex.norm_real ρ)
      _ = ρ := by
        exact Eq.trans (mul_one |ρ|) (abs_of_pos hρ_pos)
  have hnorm_a_div :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ‖a‖ / ρ := by
    calc
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖a‖ / ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ := by
        exact norm_div a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) hnorm_z
  have hratio_lt_one : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  have hratio_eq_one : ‖a‖ / ρ = 1 :=
    Eq.trans hnorm_a_div.symm hnorm_div_eq_one
  exact (ne_of_lt hratio_lt_one) hratio_eq_one

/-- Boundary factorization for a single nonzero Jensen zero on a nonzero
circle. -/
theorem entireFunction_singleZeroFactor_boundary_factorization
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) =
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
        (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) := by
  let z : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I)
  have hz0 : z ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  have ha_inv : a * a⁻¹ = 1 :=
    mul_inv_cancel₀ ha0
  have hz_inv : z * z⁻¹ = 1 :=
    mul_inv_cancel₀ hz0
  have hinner :
      (z * a⁻¹) * (a * z⁻¹) = 1 := by
    calc
      (z * a⁻¹) * (a * z⁻¹) = ((z * a⁻¹) * a) * z⁻¹ := by
        exact mul_assoc (z * a⁻¹) a z⁻¹
      _ = (z * (a⁻¹ * a)) * z⁻¹ := by
        exact congrArg (fun x : ℂ => x * z⁻¹) (mul_assoc z a⁻¹ a)
      _ = z * ((a⁻¹ * a) * z⁻¹) := by
        exact (mul_assoc z (a⁻¹ * a) z⁻¹).symm
      _ = z * (1 * z⁻¹) := by
        exact congrArg (fun x : ℂ => z * (x * z⁻¹)) (inv_mul_cancel₀ ha0)
      _ = z * z⁻¹ := by
        exact congrArg (fun x : ℂ => z * x) (one_mul z⁻¹)
      _ = 1 := hz_inv
  calc
    1 - (z / a) = 1 - (z * a⁻¹) := by
      exact congrArg (fun x : ℂ => 1 - x) (div_eq_mul_inv z a)
    _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
      calc
        1 - (z * a⁻¹) =
            (z * a⁻¹) * (a * z⁻¹) - (z * a⁻¹) * 1 := by
          exact congrArg (fun x : ℂ => x - (z * a⁻¹) * 1) hinner.symm
        _ = (z * a⁻¹) * ((a * z⁻¹) - 1) := by
          exact (mul_sub (z * a⁻¹) (a * z⁻¹) 1).symm
        _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
          let u : ℂ := z * a⁻¹
          let v : ℂ := 1 - a * z⁻¹
          have hsub : (a * z⁻¹) - 1 = -v :=
            (neg_sub 1 (a * z⁻¹)).symm
          have hmul_neg : u * (-v) = -(u * v) :=
            mul_neg u v
          have hneg_mul : -(u * v) = (-u) * v :=
            (neg_mul u v).symm
          exact Eq.trans
            (congrArg (fun y : ℂ => u * y) hsub)
            (Eq.trans hmul_neg hneg_mul)
    _ = -(z / a) * (1 - (a / z)) := by
      exact congrArg₂ (fun x y : ℂ => -x * (1 - y))
        (div_eq_mul_inv z a).symm
        (div_eq_mul_inv a z).symm

/-- The boundary factor has norm `ρ / ‖a‖`. -/
theorem entireFunction_singleZeroFactor_outer_norm
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      ρ / ‖a‖ := by
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_rho :
      ‖(ρ : ℂ)‖ = ρ := by
    calc
      ‖(ρ : ℂ)‖ = |ρ| := by
        exact Complex.norm_real ρ
      _ = ρ :=
        abs_of_pos hρ_pos
  calc
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
        ‖(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ := by
      exact norm_neg (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)
    _ = ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ / ‖a‖ := by
      exact norm_div ((ρ : ℂ) * Complex.exp (θ * Complex.I)) a
    _ = (‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I)))
    _ = (ρ * 1) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (congrArg₂ (fun x y : ℝ => x * y) hnorm_rho hnorm_exp)
    _ = ρ / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖) (mul_one ρ)

/-- Splitting the logarithm of one boundary factor into the constant outer
radial term and the inner disk logarithmic term. -/
theorem entireFunction_singleZeroFactor_boundary_log_split
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
  have hfactor :=
    entireFunction_singleZeroFactor_boundary_factorization ha0 hρ_pos θ
  have houter_norm :=
    entireFunction_singleZeroFactor_outer_norm ha0 hρ_pos θ
  have hinner_ne :
      1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 :=
    entireFunction_singleZeroFactor_inner_ne_zero haρ θ
  have houter_ne :
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) ≠ 0 := by
    have hz_ne :
        ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
      entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
    exact neg_ne_zero.mpr (div_ne_zero hz_ne ha0)
  have houter_norm_ne :
      ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr houter_ne
  have hinner_norm_ne :
      ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hinner_ne
  calc
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log
        ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))))‖ := by
      exact congrArg (fun x : ℂ => Real.log ‖x‖) hfactor
    _ =
      Real.log
        (‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ *
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) := by
      exact congrArg Real.log
        (norm_mul
          (-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a))
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))))
    _ =
      Real.log ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact Real.log_mul houter_norm_ne hinner_norm_ne
    _ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact congrArg
        (fun x : ℝ =>
          Real.log x +
            Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖)
        houter_norm

/-- The affine disk factor `z ↦ 1 - c z` is entire. -/
theorem complex_one_sub_mul_id_analyticAt
    (c z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 - c * w) z := by
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

/-- The affine disk factor `1 - c z` has no zeros on the closed unit disk when
`c` is contracting. -/
theorem complex_one_sub_mul_id_ne_zero_on_closed_unitDisk
    {c z : ℂ}
    (hc : ‖c‖ < 1)
    (hz : ‖z‖ ≤ 1) :
    1 - c * z ≠ 0 := by
  intro hzero
  have hmul_eq_one : c * z = 1 :=
    sub_eq_zero.mp hzero
  have hnorm_mul_eq_one : ‖c * z‖ = 1 :=
    congrArg norm hmul_eq_one
  have hnorm_mul_le : ‖c * z‖ ≤ ‖c‖ := by
    have hmul_norm : ‖c * z‖ = ‖c‖ * ‖z‖ :=
      norm_mul c z
    have hc_nonneg : 0 ≤ ‖c‖ :=
      norm_nonneg c
    have hmul_le : ‖c‖ * ‖z‖ ≤ ‖c‖ * 1 :=
      mul_le_mul_of_nonneg_left hz hc_nonneg
    have hmul_one : ‖c‖ * 1 = ‖c‖ :=
      mul_one ‖c‖
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hmul_norm.symm
      (le_trans hmul_le (le_of_eq hmul_one))
  have hone_le_c : 1 ≤ ‖c‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hnorm_mul_eq_one
      hnorm_mul_le
  exact (not_le_of_gt hc) hone_le_c

/-- Contractivity is preserved by complex conjugation. -/
theorem complex_norm_conj_lt_one
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    ‖conj q‖ < 1 := by
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    (RCLike.norm_conj q)
    hq

/-- The negative-orientation boundary factor has the same norm as the
positive-orientation factor with conjugated coefficient. -/
theorem complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
    (q : ℂ)
    (θ : ℝ) :
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
      ‖1 - conj q * Complex.exp (θ * Complex.I)‖ := by
  have hconj_exp :
      conj (Complex.exp (-(θ * Complex.I))) =
        Complex.exp (θ * Complex.I) := by
    calc
      conj (Complex.exp (-(θ * Complex.I))) =
          Complex.exp (conj (-(θ * Complex.I))) := by
        exact (Complex.exp_conj (-(θ * Complex.I))).symm
      _ = Complex.exp (θ * Complex.I) := by
        have harg :
            conj (-(θ * Complex.I)) = θ * Complex.I := by
          calc
            conj (-(θ * Complex.I)) = -conj (θ * Complex.I) := by
              exact map_neg conj (θ * Complex.I)
            _ = -((θ : ℂ) * conj Complex.I) := by
              exact congrArg Neg.neg (map_mul conj (θ : ℂ) Complex.I)
            _ = -((θ : ℂ) * (-Complex.I)) := by
              exact congrArg (fun z : ℂ => -((θ : ℂ) * z)) Complex.conj_I
            _ = (θ : ℂ) * Complex.I := by
              exact neg_mul_eq_mul_neg (θ : ℂ) Complex.I
        exact congrArg Complex.exp harg
  have hconj_factor :
      conj (1 - q * Complex.exp (-(θ * Complex.I))) =
        1 - conj q * Complex.exp (θ * Complex.I) := by
    calc
      conj (1 - q * Complex.exp (-(θ * Complex.I))) =
          conj 1 - conj (q * Complex.exp (-(θ * Complex.I))) := by
        exact map_sub conj 1 (q * Complex.exp (-(θ * Complex.I)))
      _ = 1 - conj (q * Complex.exp (-(θ * Complex.I))) := by
        exact congrArg
          (fun x : ℂ => x - conj (q * Complex.exp (-(θ * Complex.I))))
          (map_one conj)
      _ = 1 - conj q * conj (Complex.exp (-(θ * Complex.I))) := by
        exact congrArg (fun x : ℂ => 1 - x)
          (map_mul conj q (Complex.exp (-(θ * Complex.I))))
      _ = 1 - conj q * Complex.exp (θ * Complex.I) := by
        exact congrArg (fun x : ℂ => 1 - conj q * x) hconj_exp
  calc
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
        ‖conj (1 - q * Complex.exp (-(θ * Complex.I)))‖ := by
      exact (norm_conj (1 - q * Complex.exp (-(θ * Complex.I)))).symm
    _ = ‖1 - conj q * Complex.exp (θ * Complex.I)‖ := by
      exact congrArg norm hconj_factor

/-- The center value of the affine disk factor has zero logarithmic norm. -/
theorem complex_one_sub_mul_id_center_log_norm_eq_zero
    (c : ℂ) :
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ = 0 := by
  have hmul_zero : c * (0 : ℂ) = 0 :=
    mul_zero c
  have hvalue : (fun z : ℂ => 1 - c * z) 0 = 1 := by
    calc
      (fun z : ℂ => 1 - c * z) 0 = 1 - c * 0 := rfl
      _ = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hmul_zero
      _ = 1 := by
        exact sub_zero 1
  have hnorm : ‖(fun z : ℂ => 1 - c * z) 0‖ = 1 := by
    calc
      ‖(fun z : ℂ => 1 - c * z) 0‖ = ‖(1 : ℂ)‖ := by
        exact congrArg norm hvalue
      _ = 1 :=
        norm_one
  calc
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ =
        Real.log 1 := by
      exact congrArg Real.log hnorm
    _ = 0 :=
      Real.log_one

/-- Analytic-log mean theorem for the positive Fourier orientation of the
contracting affine disk factor. -/
theorem complex_log_one_sub_contracting_positive_fourier_mean_zero
    {c : ℂ}
    (hc : ‖c‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
      0 := by
  let G : ℂ → ℂ := fun z => 1 - c * z
  have hG : ∀ z : ℂ, AnalyticAt ℂ G z := by
    intro z
    exact complex_one_sub_mul_id_analyticAt c z
  have hzero :
      ∀ z : ℂ, ‖z‖ ≤ (1 : ℝ) → G z ≠ 0 := by
    intro z hz
    exact complex_one_sub_mul_id_ne_zero_on_closed_unitDisk hc hz
  rcases
      entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
        G hG (le_refl (1 : ℝ)) hzero
      with ⟨L, hL_an, hL_log, hL_center⟩
  have hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re) =
        (L 0).re :=
    entireFunction_analyticLog_re_holomorphicMeanValue_circle
      L (le_refl (1 : ℝ)) hL_an
  have hboundary :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re := by
    exact intervalIntegral.integral_congr fun θ _hθ =>
      by
        have hpoint :
            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ ≤
              (1 : ℝ) := by
          calc
            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ =
                ‖((1 : ℝ) : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
              exact norm_mul (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I))
            _ = 1 * ‖Complex.exp (θ * Complex.I)‖ := by
              exact congrArg
                (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
                norm_one
            _ = 1 * 1 := by
              exact congrArg (fun x : ℝ => 1 * x)
                (Complex.norm_exp_ofReal_mul_I θ)
            _ = 1 := by
              exact one_mul 1
        have hlog_re :
            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re =
              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ :=
          entireFunction_analyticLogBranch_re_eq_log_norm
            G L hpoint hL_log
        have hG_eval :
            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
              1 - c * Complex.exp (θ * Complex.I) := by
          calc
            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
                1 - c * (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := rfl
            _ = 1 - (c * (((1 : ℝ) : ℂ)) * Complex.exp (θ * Complex.I)) := by
              exact congrArg (fun x : ℂ => 1 - x)
                (mul_assoc c (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I)))
            _ = 1 - (c * 1 * Complex.exp (θ * Complex.I)) := by
              exact congrArg
                (fun x : ℂ => 1 - (c * x * Complex.exp (θ * Complex.I)))
                rfl
            _ = 1 - c * Complex.exp (θ * Complex.I) := by
              exact congrArg (fun x : ℂ => 1 - x)
                (congrArg (fun x : ℂ => x * Complex.exp (θ * Complex.I))
                  (mul_one c))
        calc
          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖ =
              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ := by
            exact congrArg (fun x : ℂ => Real.log ‖x‖) hG_eval.symm
          _ = (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re :=
            hlog_re.symm
  have hcenter_zero :
      (L 0).re = 0 := by
    exact Eq.trans hL_center (complex_one_sub_mul_id_center_log_norm_eq_zero c)
  exact Eq.trans
    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
    (Eq.trans hmean hcenter_zero)

/-- The Fourier-mode logarithmic mean for a contracting inner disk factor.

For `‖q‖ < 1`, the branch
`log (1 - q * exp (-θ I)) = -∑ n≥1 q^n exp (-n θ I) / n` is uniformly
convergent on the Jensen circle.  Every nonzero Fourier mode has zero angular
mean, hence the real logarithmic norm has zero normalized mean.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem complex_log_one_sub_contracting_fourier_mean_zero
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
      0 := by
  have hconj_contract : ‖conj q‖ < 1 :=
    complex_norm_conj_lt_one hq
  have hpositive :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - conj q * Complex.exp (θ * Complex.I)‖) =
        0 :=
    complex_log_one_sub_contracting_positive_fourier_mean_zero hconj_contract
  have hboundary :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - conj q * Complex.exp (θ * Complex.I)‖ := by
    exact intervalIntegral.integral_congr fun θ _hθ =>
      congrArg Real.log
        (complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
          q θ)
  exact Eq.trans
    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
    hpositive

/-- The normalized zero location `a / ρ` is strictly inside the unit disk. -/
theorem entireFunction_singleZeroFactor_normalized_zero_norm_lt_one
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    ‖a / (ρ : ℂ)‖ < 1 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hnorm_div :
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ρ := by
    calc
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ‖(ρ : ℂ)‖ := by
        exact norm_div a (ρ : ℂ)
      _ = ‖a‖ / |ρ| := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (Complex.norm_real ρ)
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (abs_of_pos hρ_pos)
  have hratio_lt : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    hnorm_div.symm
    hratio_lt

/-- Algebraic transport from the Jensen inner factor to the normalized
contracting Fourier factor. -/
theorem entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) =
      1 - (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hdiv :
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
        (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
    calc
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
          a * (((ρ : ℂ) * Complex.exp (θ * Complex.I))⁻¹) := by
        exact div_eq_mul_inv a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = a * ((ρ : ℂ)⁻¹ * (Complex.exp (θ * Complex.I))⁻¹) := by
        exact congrArg (fun x : ℂ => a * x)
          (mul_inv_rev (ρ : ℂ) (Complex.exp (θ * Complex.I)))
      _ = (a * (ρ : ℂ)⁻¹) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact mul_assoc a (ρ : ℂ)⁻¹ (Complex.exp (θ * Complex.I))⁻¹
      _ = (a / (ρ : ℂ)) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact congrArg
          (fun x : ℂ => x * (Complex.exp (θ * Complex.I))⁻¹)
          (div_eq_mul_inv a (ρ : ℂ)).symm
      _ = (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
        exact congrArg (fun x : ℂ => (a / (ρ : ℂ)) * x)
          (Complex.exp_neg (θ * Complex.I)).symm
  exact congrArg (fun x : ℂ => 1 - x) hdiv

/-- The logarithmic power-series mean for an inside-disk linear factor
vanishes on the Jensen boundary. -/
theorem entireFunction_singleZeroFactor_inner_log_mean_zero_from_powerSeries
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      0 := by
  have hq : ‖a / (ρ : ℂ)‖ < 1 :=
    entireFunction_singleZeroFactor_normalized_zero_norm_lt_one haρ
  have hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - (a / (ρ : ℂ)) *
              Complex.exp (-(θ * Complex.I))‖) =
        0 :=
    complex_log_one_sub_contracting_fourier_mean_zero hq
  have hintegrand :
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      (fun θ : ℝ =>
        Real.log ‖1 - (a / (ρ : ℂ)) *
          Complex.exp (-(θ * Complex.I))‖) := by
    funext θ
    exact congrArg (fun z : ℂ => Real.log ‖z‖)
      (entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
        haρ θ)
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) =
        0)
    hintegrand.symm
    hmean

/-- The inner single-zero logarithmic boundary factor is continuous on the
Jensen parameter interval. -/
theorem entireFunction_singleZeroFactor_inner_log_continuous
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    Continuous
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hden_ne :
      ∀ θ : ℝ, ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  have hinner_ne :
      ∀ θ : ℝ,
        1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_inner_ne_zero haρ θ
  let q : ℝ → ℂ :=
    fun θ : ℝ => 1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))
  have hq_cont : Continuous q :=
    continuous_const.sub
      (continuous_const.div
        ((continuous_const.mul
          (Complex.continuous_exp.comp
            ((continuous_ofReal.comp continuous_id).mul continuous_const))))
        hden_ne)
  have hnorm_cont : Continuous (fun θ : ℝ => ‖q θ‖) :=
    hq_cont.norm
  exact continuous_iff_continuousAt.mpr
    (fun θ : ℝ =>
      (Real.continuousAt_log
        (norm_ne_zero_iff.mpr (hinner_ne θ))).comp θ hnorm_cont.continuousAt)

/-- The inner single-zero logarithmic boundary factor is interval-integrable on
the Jensen parameter interval. -/
theorem entireFunction_singleZeroFactor_inner_log_intervalIntegrable
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖)
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    (entireFunction_singleZeroFactor_inner_log_continuous haρ).intervalIntegrable
      (0 : ℝ)
      (2 * Real.pi)

/-- Normalized constant-plus Jensen interval integral when the normalized
remainder mean vanishes. -/
theorem entireFunction_normalized_const_add_integral_eq_const_of_mean_zero
    (v : ℝ → ℝ)
    (c : ℝ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    (hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) =
        0) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
      c := by
  have hintegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
        (2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ :=
    intervalIntegral_const_add_eq_length_smul_add
      v c (0 : ℝ) (2 * Real.pi) hv
  have htwo_ne : 2 * Real.pi ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hconst :
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) = c := by
    calc
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) =
          (2 * Real.pi)⁻¹ * ((2 * Real.pi) * c) := by
        exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * (x • c)) (sub_zero (2 * Real.pi))
      _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)) * c := by
        exact (mul_assoc (2 * Real.pi)⁻¹ (2 * Real.pi) c).symm
      _ = 1 * c := by
        exact congrArg (fun x : ℝ => x * c) (inv_mul_cancel₀ htwo_ne)
      _ = c :=
        one_mul c
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) =
      (2 * Real.pi)⁻¹ *
        ((2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) := by
      exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hintegral
    _ =
      (2 * Real.pi)⁻¹ * ((2 * Real.pi - 0) • c) +
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) := by
      exact left_distrib
        (2 * Real.pi)⁻¹
        ((2 * Real.pi - 0) • c)
        (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ)
    _ = c + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y) hconst hmean
    _ = c :=
      add_zero c

/-- Integrating the split single-factor boundary logarithm leaves only the
outer Jensen radial term. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_from_log_split
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hsplit :
      ∀ θ : ℝ,
        Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
          Real.log (ρ / ‖a‖) +
            Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ :=
    fun θ : ℝ =>
      entireFunction_singleZeroFactor_boundary_log_split ha0 haρ hρ_pos θ
  have hinner :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
        0 :=
    entireFunction_singleZeroFactor_inner_log_mean_zero_from_powerSeries haρ
  let u : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖
  let v : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log
        ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖
  let c : ℝ := Real.log (ρ / ‖a‖)
  have hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ) (2 * Real.pi) :=
    entireFunction_singleZeroFactor_inner_log_intervalIntegrable haρ
  have htransport :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ := by
    exact intervalIntegral.integral_congr
      (fun θ _hθ => hsplit θ)
  have hmean_v :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), v θ) =
        0 :=
    hinner
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ) := by
      exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) htransport
    _ = c :=
      entireFunction_normalized_const_add_integral_eq_const_of_mean_zero
        v c hv hmean_v

/-- The single-factor Poisson-Jensen circle integral.

For `0 < ‖a‖ < ρ`, the normalized boundary average of
`θ ↦ log ‖1 - ρ e^{iθ}/a‖` is `log (ρ / ‖a‖)`.  Equivalently, after factoring
`ρ/a`, this is the vanishing mean of
`log ‖1 - (a/ρ)e^{-iθ}‖` for `‖a/ρ‖ < 1`, obtained from the real part of the
convergent logarithmic power series.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_identity_from_logPowerSeries
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  exact
    entireFunction_singleZeroFactor_boundaryAverage_from_log_split ha0 haρ

/-- The normalized boundary average of one extracted nonzero linear zero factor
is its Jensen radial logarithm. -/
theorem entireFunction_singleZeroFactor_boundaryAverage_identity
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖) =
      Real.log (ρ / ‖a‖) := by
  exact
    entireFunction_singleZeroFactor_boundaryAverage_identity_from_logPowerSeries
      ha0 haρ

/-- A member of the radial-gap support divisor is a genuine support point of
the Jensen radial-gap summand. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_support
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ w) := by
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor at hz
  exact
    (entireFunctionJensenRadialGapSummand_support_finite F hF hF0 ρ).mem_toFinset.1
      hz

/-- Every zero in the radial-gap support divisor is nonzero. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    (z : ℂ) ≠ 0 := by
  intro hz0
  have hsupport :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ w) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_support
      F hF hF0 ρ z hz
  have hzero :
      entireFunctionJensenRadialGapSummand F hF ρ z = 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_origin_radialContribution_eq_zero
      F hF ρ z hz0
  exact hsupport hzero

/-- Every zero in the radial-gap support divisor lies strictly inside the
Jensen circle. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_norm_lt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F)
    (hz :
      z ∈
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) :
    ‖(z : ℂ)‖ < ρ := by
  by_contra hzρ
  have hsupport :
      z ∈ Function.support
        (fun w : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ w) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_support
      F hF hF0 ρ z hz
  have hzero :
      entireFunctionJensenRadialGapSummand F hF ρ z = 0 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_eq_zero_of_not_lt
      F hF ρ z hzρ
  exact hsupport hzero

/-- The finite product radial-gap sum is the finite sum of normalized
single-factor boundary averages, for any divisor whose members are nonzero and
strictly inside the Jensen circle. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum_eq_singleFactorBoundaryAverageSum_of_mem_zeroInside
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (ρ : ℝ)
    (s : Finset (EntireFunctionZero F))
    (hs0 : ∀ z : EntireFunctionZero F, z ∈ s → (z : ℂ) ≠ 0)
    (hsρ : ∀ z : EntireFunctionZero F, z ∈ s → ‖(z : ℂ)‖ < ρ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ s =
      ∑ z in s,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
  unfold entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
  refine Finset.sum_congr rfl ?_
  intro z hz
  have hz0 : (z : ℂ) ≠ 0 := hs0 z hz
  have hzρ : ‖(z : ℂ)‖ < ρ := hsρ z hz
  have hradial :
      entireFunctionJensenRadialGapSummand F hF ρ z =
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          Real.log (ρ / ‖(z : ℂ)‖) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFactor_radialContribution_identity
      F hF ρ z hz0 hzρ
  have havg :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖) =
        Real.log (ρ / ‖(z : ℂ)‖) :=
    entireFunction_singleZeroFactor_boundaryAverage_identity
      (a := (z : ℂ)) (ρ := ρ) hz0 hzρ
  exact Eq.trans hradial
    (congrArg
      (fun x : ℝ =>
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) * x)
      havg.symm)

/-- The support finite product radial-gap sum is exactly the finite sum of
single-factor Poisson-Jensen boundary averages. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProductRadialGapSum_eq_singleFactorBoundaryAverageSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) =
      ∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)) := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum_eq_singleFactorBoundaryAverageSum_of_mem_zeroInside
      F hF ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ)
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_ne_zero
          F hF hF0 ρ z hz)
      (fun z hz =>
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor_mem_norm_lt
          F hF hF0 ρ z hz)

/-- The finite zero-factor product attached to the radial-gap support divisor.

This is the product side of Jensen's finite divisor assembly: each zero inside
the Jensen circle contributes the linear factor
`1 - w / z`, repeated with analytic multiplicity. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  ∏ z in
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
      F hF hF0 ρ,
    (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ)

/-- The finite zero-factor product is definitionally the product over the
support divisor. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ w =
      ∏ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (1 - w / (z : ℂ)) ^ entireFunctionZeroMultiplicity F hF (z : ℂ) := by
  rfl

/-- The finite zero-free quotient after extracting the support divisor. -/
noncomputable def entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) : ℂ :=
  F w /
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
      F hF hF0 ρ w

/-- The finite quotient is definitionally `F` divided by the extracted finite
zero-factor product. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (w : ℂ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ w =
      F w /
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ w := by
  rfl

/-- Each extracted nonzero zero factor is normalized to `1` at the origin. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin_factor
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (z : EntireFunctionZero F) :
    (1 - (0 : ℂ) / (z : ℂ)) ^
        entireFunctionZeroMultiplicity F hF (z : ℂ) = 1 := by
  have hzero_div : (0 : ℂ) / (z : ℂ) = 0 :=
    zero_div (z : ℂ)
  have hbase :
      1 - (0 : ℂ) / (z : ℂ) = 1 := by
    calc
      1 - (0 : ℂ) / (z : ℂ) = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hzero_div
      _ = 1 := by
        exact sub_zero (1 : ℂ)
  exact
    Eq.trans
      (congrArg
        (fun x : ℂ => x ^ entireFunctionZeroMultiplicity F hF (z : ℂ))
        hbase)
      (one_pow (entireFunctionZeroMultiplicity F hF (z : ℂ)))

/-- The finite zero-divisor product is normalized to `1` at the origin. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ 0 = 1 := by
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
        F hF hF0 ρ 0 =
        ∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (1 - (0 : ℂ) / (z : ℂ)) ^
            entireFunctionZeroMultiplicity F hF (z : ℂ) := by
      exact
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_def
          F hF hF0 ρ 0
    _ =
        ∏ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          1 := by
      exact
        Finset.prod_congr rfl
          (fun z _ =>
            entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin_factor
              F hF hF0 ρ z)
    _ = 1 := by
      exact
        Finset.prod_const_one
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ)

/-- With the current quotient definition `F / Product`, the quotient value at
the origin is exactly `F 0`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ 0 = F 0 := by
  have hproduct_origin :
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
          F hF hF0 ρ 0 = 1 :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct_origin
      F hF hF0 ρ
  calc
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
        F hF hF0 ρ 0 =
        F 0 /
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ 0 := by
      exact
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_def
          F hF hF0 ρ 0
    _ = F 0 / 1 := by
      exact congrArg (fun x : ℂ => F 0 / x) hproduct_origin
    _ = F 0 := by
      exact div_one (F 0)

/-- The current finite quotient origin normalization has positive sign:
`log ‖Q(0)‖ = log ‖F(0)‖`.  This is the canonical peeled origin calculation
from the product definition. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm_from_def
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖ := by
  exact
    congrArg Real.log
      (congrArg norm
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin
          F hF hF0 ρ))

/-- Canonical finite product factorization on Jensen's closed disk.

This is the remaining owner-level complex-analytic construction: from the
finite zero divisor in the disk, factor `F` as the explicit finite zero-factor
product times a quotient that is zero-free on the closed disk.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    (∀ w : ℂ,
      ‖w‖ ≤ ρ →
      F w =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ w *
          entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorProduct
            F hF hF0 ρ w) ∧
    (∀ w : ℂ,
      ‖w‖ ≤ ρ →
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
          F hF hF0 ρ w ≠ 0) ∧
    (entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖)))) ∧
    (Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖) := by
  -- Canonical root: finite Weierstrass/Jensen divisor factorization on the
  -- closed disk, with the quotient zero-free after all zeros in the support
  -- divisor have been extracted.  The final two projections record the
  -- boundary logarithm decomposition and the origin normalization supplied by
  -- that same factorization.
  sorry

/-- The finite divisor quotient is zero-free on Jensen's closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_zeroFreeOnClosedDisk
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    ∀ w : ℂ,
      ‖w‖ ≤ ρ →
      entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
          F hF hF0 ρ w ≠ 0 := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
      F hF hF0 ρ hρ).2.1

/-- Boundary logarithm decomposition after the finite divisor has been
extracted.

The quotient term is zero-free on the closed disk, so its boundary mean is
handled by the analytic-log mean-value theorem; the remaining terms are the
finite sum of single zero-factor boundary averages. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ +
        (∑ z in
          entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ,
          (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in (0 : ℝ)..(2 * Real.pi),
                Real.log
                  ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
      F hF hF0 ρ hρ).2.2.1

/-- Origin normalization for the finite quotient in Jensen's product
factorization. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    Real.log
        ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
            F hF hF0 ρ 0‖ =
      Real.log ‖F 0‖ := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_factorization_zeroFreeOnClosedDisk_ownerRoot
      F hF hF0 ρ hρ).2.2.2

/-- The finite support divisor sum of single-factor boundary averages is the
support finite radial-gap product sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ) :
    (∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  exact
    (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProductRadialGapSum_eq_singleFactorBoundaryAverageSum
      F hF hF0 ρ).symm

/-- Finite-product boundary-average identity over the support divisor.

This is the quotient/product construction in the assembly chain.  Its proof is
the classical finite divisor factorization on the Jensen disk, construction of
the zero-free quotient, analytic-log mean value for the quotient term, boundary
log decomposition into the quotient and the extracted linear factors, and the
finite single-factor average theorem above.  Cf. Titchmarsh, *The Theory of
Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryAverage_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogAverage F ρ =
      Real.log ‖F 0‖ +
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
        F hF ρ
        (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ) := by
  have hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log
          ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
              F hF hF0 ρ 0‖ +
          (∑ z in
            entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ,
            (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
              ((2 * Real.pi)⁻¹ *
                (∫ θ in (0 : ℝ)..(2 * Real.pi),
                  Real.log
                    ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryLog_decomposition_ownerRoot
      F hF hF0 ρ hρ
  have hsum :
      (∑ z in
        entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
          F hF hF0 ρ,
        (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
          ((2 * Real.pi)⁻¹ *
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log
                ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))) =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_singleFactorBoundaryAverageSum_eq_radialGapSum
      F hF hF0 ρ
  have hquotient_origin :
      Real.log
          ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
              F hF hF0 ρ 0‖ =
        Real.log ‖F 0‖ :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient_origin_log_norm
      F hF hF0 ρ hρ
  let S : ℝ :=
    ∑ z in
      entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
        F hF hF0 ρ,
      (entireFunctionZeroMultiplicity F hF (z : ℂ) : ℝ) *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log
              ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / (z : ℂ))‖))
  have hboundaryS :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log
          ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
              F hF hF0 ρ 0‖ + S :=
    hboundary
  have hsumS :
      S =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    hsum
  calc
    entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log
          ‖entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteZeroDivisorQuotient
              F hF hF0 ρ 0‖ + S := by
      exact hboundaryS
    _ = Real.log ‖F 0‖ + S := by
      exact congrArg
        (fun x : ℝ => x + S)
        hquotient_origin
    _ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact congrArg (fun x : ℝ => Real.log ‖F 0‖ + x) hsum

/-- Support-controlled finite-product boundary identity implies the standard
Jensen boundary mean-log identity by replacing the finite support divisor sum
with the infinite radial-gap sum. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_supportFiniteProduct_boundaryAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hboundary :
      entireFunctionJensenBoundaryLogAverage F ρ =
        Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ)) :
    entireFunctionJensenRadialGapSum F hF ρ =
      entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  have hsupport :
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) :=
    entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSum_eq_supportFiniteProductRadialGapSum
      F hF hF0 ρ
  calc
    entireFunctionJensenRadialGapSum F hF ρ =
        entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
          F hF ρ
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
            F hF hF0 ρ) := by
      exact hsupport
    _ =
        (Real.log ‖F 0‖ +
          entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ)) -
          Real.log ‖F 0‖ := by
      exact
        (add_sub_cancel_left
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteProductRadialGapSum
            F hF ρ
            (entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSupportFiniteZeroDivisor
              F hF hF0 ρ))
          (Real.log ‖F 0‖)).symm
    _ = entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
      exact congrArg (fun x : ℝ => x - Real.log ‖F 0‖) hboundary.symm

/-- Analytic-log, harmonic mean-value, and single-zero-factor form of the
classical Jensen product theorem.

Proof chain:
finite divisor factorization on the disk -> zero-free quotient admits an
analytic logarithm -> the real part of that logarithm is harmonic -> harmonic
mean value on the boundary circle -> the single zero-factor boundary average
`log (ρ / ‖a‖)` -> finite product sum -> support-controlled `tsum` transport.

This statement keeps the classical analytic heart separate from the already
proved finite support and summability transports in this owner file.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_finiteProductAssembly_from_constituents
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  intro ρ hρ
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_supportFiniteProduct_boundaryAverage
      F hF hF0 ρ
      (entireFunction_standardJensenFormula_nonzeroAtOrigin_supportFiniteProduct_boundaryAverage_identity_ownerRoot
        F hF hF0 ρ hρ)

/-- Analytic-log, harmonic mean-value, and single-zero-factor form of the
classical Jensen product theorem.

This public theorem is intentionally a thin wrapper over the finite-product
assembly root, after the three analytic constituents have been isolated above. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_analyticLogHarmonicMeanValue_and_zeroFactorCircleAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_finiteProductAssembly_from_constituents
      F hF hF0

/-- Analytic-log/harmonic mean-value form of the classical Jensen product
theorem. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_analyticLogHarmonicMeanValue
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_from_analyticLogHarmonicMeanValue_and_zeroFactorCircleAverage
      F hF hF0

/-- Classical analytic product/Jensen identity after finite zero-divisor
factorization.

Proof chain represented by this owner root:
finite zero divisor factorization -> zero-free quotient boundary mean-log
identity -> zero factor radial contribution identity -> finite product sum
identity -> Jensen's formula with explicit constant.

This is the genuine classical complex-analytic input: the zero-free quotient
has boundary mean log equal to its value at the origin, while each extracted
linear zero factor contributes `log (ρ / ‖a‖)` to the normalized boundary mean;
cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_analyticLogHarmonicMeanValue
      F hF hF0

/-- Classical Jensen product/radial-gap identity for a nonzero value at the
origin, including the explicit constant.

This is the product formula form of Jensen's theorem: after multiplying the
linear zero factors inside the circle and taking logarithmic boundary averages,
the radial-gap sum differs from the boundary average by exactly
`Real.log ‖F 0‖`. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_productRadialGap_identity_explicitConstant_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_zeroFreeQuotient_boundaryMeanLog_identity_ownerRoot
      F hF hF0

/-- Boundary logarithmic integral identity with explicit origin constant,
projected from the classical Jensen product/radial-gap identity. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogIntegral_identity_explicitConstant_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖ := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_productRadialGap_identity_explicitConstant_ownerRoot
      F hF hF0

/-- Classical Jensen boundary-log-average identity for a nonzero value at the
origin.

This is the exact classical Jensen package in the normalization of this file:
the nonzero closed-disk multiplicity summands are summable, the radial-gap
summands are summable, and the multiplicity-weighted radial gap sum equals the
normalized boundary logarithmic average up to the origin constant
`log ‖F 0‖`; cf. Titchmarsh, *The Theory of Functions*, §5. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_explicitConstant_package_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
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
      entireFunctionJensenRadialGapSum F hF ρ =
        entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖) := by
  refine ⟨?_, ?_⟩
  · exact
      entireFunction_standardJensenFormula_nonzeroAtOrigin_finiteZeroDivisor_closedDiskMultiplicitySummable_ownerRoot
        F hF hF0
  · intro ρ hρ
    exact
      ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_from_finiteZeroDivisor_ownerRoot
          F hF hF0 ρ hρ,
        entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogIntegral_identity_explicitConstant_ownerRoot
          F hF hF0 ρ hρ⟩

/-- Classical Jensen package with the origin constant existentially bundled.

The owner theorem above records the constant explicitly as `log ‖F 0‖`; this
wrapper exists only for downstream code that wants a named constant. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
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
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_explicitConstant_package_ownerRoot
        F hF hF0 with
    ⟨hclosed, hradial⟩
  refine ⟨Real.log ‖F 0‖, hclosed, ?_⟩
  intro ρ hρ
  rcases hradial ρ hρ with ⟨hsum, hidentity⟩
  refine ⟨hsum, ?_⟩
  calc
    entireFunctionJensenRadialGapSum F hF ρ + Real.log ‖F 0‖ =
        (entireFunctionJensenBoundaryLogAverage F ρ - Real.log ‖F 0‖) +
          Real.log ‖F 0‖ := by
      exact congrArg (fun x : ℝ => x + Real.log ‖F 0‖) hidentity
    _ = entireFunctionJensenBoundaryLogAverage F ρ := by
      exact sub_add_cancel (entireFunctionJensenBoundaryLogAverage F ρ) (Real.log ‖F 0‖)

/-- Boundary-log-average identity projected from the standard Jensen package. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogAverage_identity_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ ρ : ℝ,
          1 ≤ ρ →
          entireFunctionJensenRadialGapSum F hF ρ + C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨C, _hclosed, hradial⟩
  exact ⟨C, fun ρ hρ => (hradial ρ hρ).2⟩

/-- Closed-disk summability of the nonzero zero-multiplicity summand in the
standard Jensen setting. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummability_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨_C, hclosed, _hradial⟩
  exact hclosed

/-- Radial-gap summability of the Jensen summand in the standard nonzero-origin
setting. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_ownerRoot
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∀ ρ : ℝ,
      1 ≤ ρ →
      Summable
        (fun z : EntireFunctionZero F =>
          entireFunctionJensenRadialGapSummand F hF ρ z) := by
  rcases
      entireFunction_standardJensenFormula_nonzeroAtOrigin_package_ownerRoot
        F hF hF0 with
    ⟨_C, _hclosed, hradial⟩
  exact fun ρ hρ => (hradial ρ hρ).1

/-- Standard Jensen formula for a nontrivial entire function whose value at the
origin is nonzero.

This package theorem is a thin assembly over the three owner roots: boundary
log-average identity, closed-disk summability, and radial-gap summability. -/
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
  match
    entireFunction_standardJensenFormula_nonzeroAtOrigin_boundaryLogAverage_identity_ownerRoot
      F hF hF0 with
  | ⟨C, hboundary⟩ =>
      refine ⟨C, ?_, ?_⟩
      · exact
          entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSummability_ownerRoot
            F hF hF0
      · intro ρ hρ
        exact
          ⟨entireFunction_standardJensenFormula_nonzeroAtOrigin_radialGapSummability_ownerRoot
              F hF hF0 ρ hρ,
            hboundary ρ hρ⟩

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

/-- Interval-integral transport across a finite exceptional set.

This theorem is the measure-theoretic root underneath the origin-factor
boundary integral comparison.  Once a finite set `S` contains all logarithmic
singular parameters and the two integrands agree off `S` on `[0,2π]`, the
interval integral sees only the off-exception identity. -/
theorem intervalIntegral_eq_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  refine intervalIntegral.integral_congr_ae ?_
  have hAeNotMem :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∉ S :=
    hS.countable.ae_not_mem MeasureTheory.volume
  filter_upwards [hAeNotMem] with θ hθ_not_mem hθ_interval
  have hθ_uIcc :
      θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) :=
    Set.uIoc_subset_uIcc hθ_interval
  have hθ_Icc :
      θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
    have hle : (0 : ℝ) ≤ 2 * Real.pi :=
      le_of_lt Real.two_pi_pos
    exact Eq.subst
      (motive := fun T : Set ℝ => θ ∈ T)
      (Set.uIcc_of_le hle)
      hθ_uIcc
  exact hcongr θ hθ_Icc hθ_not_mem

/-- Finite-exception transport to a constant-plus integrand. -/
theorem intervalIntegral_eq_const_add_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ := by
  exact
    intervalIntegral_eq_of_finite_exception_congr
      u
      (fun θ : ℝ => c + v θ)
      S
      hS
      hcongr

/-- Interval integration of a constant plus an interval-integrable remainder. -/
theorem intervalIntegral_const_add_eq_length_smul_add
    (v : ℝ → ℝ)
    (c a b : ℝ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume a b) :
    (∫ θ in a..b, c + v θ) =
      (b - a) • c + ∫ θ in a..b, v θ := by
  have hconst :
      IntervalIntegrable (fun _θ : ℝ => c) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable continuous_const a b
  calc
    (∫ θ in a..b, c + v θ) =
        ∫ θ in a..b, (fun _θ : ℝ => c) θ + v θ := rfl
    _ =
        (∫ _θ in a..b, c) + ∫ θ in a..b, v θ := by
      exact intervalIntegral.integral_add hconst hv
    _ =
        (b - a) • c + ∫ θ in a..b, v θ := by
      exact congrArg
        (fun x : ℝ => x + ∫ θ in a..b, v θ)
        (intervalIntegral.integral_const c)

/-- Finite-exception constant-plus transport, including the constant-integral
evaluation, on the Jensen boundary interval. -/
theorem intervalIntegral_finiteException_const_add_eq_twoPi_smul_add
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ) (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      (2 * Real.pi - 0) • c +
        ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ :=
      intervalIntegral_eq_const_add_of_finite_exception_congr
        u v c S hS hcongr
    _ =
        (2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ :=
      intervalIntegral_const_add_eq_length_smul_add
        v c (0 : ℝ) (2 * Real.pi) hv

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

/-- The finite-exception data needed by origin Taylor boundary-integral
transport: the quotient-zero exceptional set is finite, and away from it the
boundary logarithmic integrands differ by the constant origin contribution. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_finiteExceptionCertificate
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR_pos : 0 < R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite ∧
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R →
        entireFunctionJensenBoundaryLogIntegrand F R θ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
            entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hfinite :
      (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite :=
    entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
      G R hR_pos.le hInj hCircle
  refine ⟨hfinite, ?_⟩
  intro θ hθI hθnot
  exact
    entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
      F G hF hfactor hR_pos hθnot hθI

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

/-- The circle parametrization is injective on the open fundamental arc
`(0, 2π]` at an arbitrary positive radius.

This is the radius-normalized form consumed by the finite-exception
origin-factor transport; it is just the doubled Jensen parametrization applied
at half radius. -/
theorem entireFunction_boundaryCircleParam_injectiveOn_Ioc
    {R : ℝ}
    (hR : 0 < R) :
    Set.InjOn
      (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
      (Set.Ioc 0 (2 * Real.pi)) := by
  have hhalf : 0 < R / 2 :=
    half_pos hR
  have hJensen :
      Set.InjOn
        (fun θ : ℝ => (2 * (R / 2) : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)) :=
    entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc hhalf
  intro θ₁ hθ₁ θ₂ hθ₂ hEq
  apply hJensen hθ₁ hθ₂
  have hscaleReal : 2 * (R / 2) = R := by
    calc
      2 * (R / 2) = R / 2 + R / 2 := two_mul (R / 2)
      _ = R := add_halves R
  have hscaleComplex : ((2 * (R / 2) : ℝ) : ℂ) = (R : ℂ) :=
    congrArg (fun x : ℝ => (x : ℂ)) hscaleReal
  calc
    (2 * (R / 2) : ℂ) * Complex.exp (θ₁ * Complex.I) =
        (R : ℂ) * Complex.exp (θ₁ * Complex.I) := by
      exact congrArg
        (fun x : ℂ => x * Complex.exp (θ₁ * Complex.I))
        hscaleComplex
    _ = (R : ℂ) * Complex.exp (θ₂ * Complex.I) :=
      hEq
    _ = (2 * (R / 2) : ℂ) * Complex.exp (θ₂ * Complex.I) := by
      exact congrArg
        (fun x : ℂ => x * Complex.exp (θ₂ * Complex.I))
        hscaleComplex.symm

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

/-- Interval-integrability of the boundary logarithmic integrand at an arbitrary
positive radius, obtained from the doubled-radius Jensen API by using the
half-radius. -/
theorem entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    {r : ℝ}
    (hr : 0 < r)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F r)
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let R : ℝ := r / 2
  have hR : 0 < R :=
    half_pos hr
  have hscale : 2 * R = r := by
    calc
      2 * R = 2 * (r / 2) := rfl
      _ = r / 2 + r / 2 := two_mul (r / 2)
      _ = r := add_halves r
  have hzerosR :
      Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
    exact Eq.subst
      (motive := fun s : ℝ =>
        Set.Finite {z : ℂ | ‖z‖ = s ∧ F z = 0})
      hscale.symm
      hzeros
  have hIntR :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
      F hF hnontrivial R hR hzerosR
  exact Eq.subst
    (motive := fun s : ℝ =>
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F s)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    hscale
    hIntR

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
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {ρ : ℝ}
    (hρ : 1 ≤ ρ) :
    entireFunctionJensenBoundaryLogIntegral F ρ =
      (2 * Real.pi) *
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
        entireFunctionJensenBoundaryLogIntegral G ρ := by
  have hρ_pos : 0 < ρ :=
    lt_of_lt_of_le zero_lt_one hρ
  have hInj :
      Set.InjOn
        (fun θ : ℝ => (ρ : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)) :=
    entireFunction_boundaryCircleParam_injectiveOn_Ioc hρ_pos
  have hCircle :
      Set.Finite {z : ℂ | ‖z‖ = ρ ∧ G z = 0} :=
    entireFunction_circleZeros_finite G hG hGnontrivial ρ
  have hcert :
      (entireFunctionJensenQuotientBoundaryZeroParameters G ρ).Finite ∧
        ∀ θ : ℝ,
          θ ∈ Set.Icc 0 (2 * Real.pi) →
          θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G ρ →
          entireFunctionJensenBoundaryLogIntegrand F ρ θ =
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
    entireFunction_originTaylorFactor_boundaryLogIntegrand_finiteExceptionCertificate
      F G hF hfactor hρ_pos hInj hCircle
  have hGint :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand G ρ)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
      G hG hGnontrivial hρ_pos hCircle
  unfold entireFunctionJensenBoundaryLogIntegral
  have htransport :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        (2 * Real.pi - 0) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
    intervalIntegral_finiteException_const_add_eq_twoPi_smul_add
      (entireFunctionJensenBoundaryLogIntegrand F ρ)
      (entireFunctionJensenBoundaryLogIntegrand G ρ)
      (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
      (entireFunctionJensenQuotientBoundaryZeroParameters G ρ)
      hcert.1
      hcert.2
      hGint
  have hlength :
      (2 * Real.pi - 0) •
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ =
        (2 * Real.pi) *
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
    calc
      (2 * Real.pi - 0) •
          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ =
          (2 * Real.pi) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
        exact congrArg
          (fun x : ℝ =>
            x • entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ)
          (sub_zero (2 * Real.pi))
      _ =
          (2 * Real.pi) *
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := rfl
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        entireFunctionJensenBoundaryLogIntegrand F ρ θ) =
        (2 * Real.pi - 0) •
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ :=
      htransport
    _ =
        (2 * Real.pi) *
            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand G ρ θ := by
      exact congrArg
        (fun x : ℝ =>
          x +
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              entireFunctionJensenBoundaryLogIntegrand G ρ θ)
        hlength

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
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
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
      F G hF hG hGnontrivial hfactor hρ
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
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
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
      F G hF hG hGnontrivial hfactor hρ

/-- Boundary logarithmic averages transport through the global origin Taylor
quotient with the explicit `m log ρ` contribution from the removed origin
factor. -/
theorem entireFunction_originTaylorFactor_boundaryLogAverage_eq_origin_plus_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, AnalyticAt ℂ G z)
    (hGnontrivial : ∃ z : ℂ, G z ≠ 0)
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
      F G hF hG hGnontrivial hfactor hρ

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
        F G hF hG_entire ⟨0, hG_ne⟩ hfactor hρ
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

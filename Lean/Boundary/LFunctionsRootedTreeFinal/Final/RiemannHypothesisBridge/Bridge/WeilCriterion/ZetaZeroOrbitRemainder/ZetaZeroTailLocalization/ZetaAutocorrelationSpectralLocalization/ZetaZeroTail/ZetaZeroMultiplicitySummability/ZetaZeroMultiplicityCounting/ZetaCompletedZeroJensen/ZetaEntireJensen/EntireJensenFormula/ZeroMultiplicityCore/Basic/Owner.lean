import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Entire-function zero multiplicity and radial-gap core

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

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
  exact Subtype.ext (congrArg (fun q : EntireFunctionZero F => (q : ℂ)) hzw)

/-- An ordinary zero lies in the range of the nonzero-zero forgetful map exactly
when its value is nonzero. -/
theorem EntireFunctionNonzeroZero.mem_range_toZero_iff
    (F : ℂ → ℂ)
    (z : EntireFunctionZero F) :
    z ∈ Set.range (EntireFunctionNonzeroZero.toZero F) ↔ (z : ℂ) ≠ 0 := by
  constructor
  · intro hz
    exact
      Exists.elim hz
        (fun w hw =>
          Eq.subst
            (motive := fun x : ℂ => x ≠ 0)
            (congrArg Subtype.val hw)
            w.property.2)
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
  exact
    hfactor.mono
      (fun w hw =>
        calc
          ‖F w‖ = ‖(w - z) ^ n • g w‖ := by
            exact congrArg norm hw
          _ = ‖(w - z) ^ n‖ * ‖g w‖ := by
            exact norm_smul ((w - z) ^ n) (g w)
          _ = ‖w - z‖ ^ n * ‖g w‖ := by
            exact congrArg (fun x : ℝ => x * ‖g w‖) (norm_pow (w - z) n))

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
  have hnorm_punctured :
      ∀ᶠ w in 𝓝[≠] z, ‖F w‖ = ‖w - z‖ ^ n * ‖g w‖ :=
    hnorm.filter_mono nhdsWithin_le_nhds
  have hg_punctured :
      ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    hg_eventually_ne.filter_mono nhdsWithin_le_nhds
  have hself :
      ∀ᶠ w in 𝓝[≠] z, w ∈ ({z} : Set ℂ)ᶜ :=
    self_mem_nhdsWithin
  exact
    ((hnorm_punctured.and hg_punctured).and hself).mono
      (fun w hw =>
        have hnorm_w : ‖F w‖ = ‖w - z‖ ^ n * ‖g w‖ := hw.1.1
        have hg_w_ne : g w ≠ 0 := hw.1.2
        have hw_ne : w ≠ z := hw.2
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
              (Real.log_pow ‖w - z‖ n))

end
end LFunctions
end Boundary

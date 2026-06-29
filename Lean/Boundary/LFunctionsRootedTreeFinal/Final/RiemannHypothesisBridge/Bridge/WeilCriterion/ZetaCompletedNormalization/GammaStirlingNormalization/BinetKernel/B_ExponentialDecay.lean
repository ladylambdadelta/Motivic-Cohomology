import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.A_RealAnalysisBounds

import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteFormula
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetTailContour
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner

/-!
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open scoped ENNReal
open MeasureTheory
open Set

/-- Real-variable exponential lower bound for the Binet scalar tail beginning
at a cutoff `a ≥ 1`.

This is the one-dimensional owner primitive behind the complex
`‖w‖ / 2`-cutoff lower bound. -/
def Real.BinetSecondFormulaKernelMajorantTailExpLower : Prop :=
  ∃ c : ℝ,
    0 < c ∧
    ∀ a : ℝ,
      1 ≤ a →
        c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) ≤
          ∫ t : ℝ in Set.Ioi a,
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- Unit-interval lower bound for the Binet scalar kernel.

This is the local positivity estimate on the first unit interval of the tail:
for `a ≥ 1`, the interval contribution already has exponential size
`exp (-π a)`. -/
def Real.BinetSecondFormulaKernelMajorantUnitIntervalExpLower : Prop :=
  ∃ c : ℝ,
    0 < c ∧
    ∀ a : ℝ,
      1 ≤ a →
        c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) ≤
          ∫ t : ℝ in Set.Ioc a (a + 1),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- Monotonicity from the first unit interval into the full Binet scalar tail. -/
def Real.BinetSecondFormulaKernelMajorantUnitIntervalLeTail : Prop :=
  ∀ a : ℝ,
    1 ≤ a →
      ∫ t : ℝ in Set.Ioc a (a + 1),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        ∫ t : ℝ in Set.Ioi a,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

theorem Real.exp_neg_pi_tail_integral_le_exp
    (a : ℝ) :
    ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) ≤
      Real.exp (-Real.pi * a) := by
  have hpi_pos : 0 < Real.pi :=
    Real.pi_pos
  have hchange :
      ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) =
        Real.pi⁻¹ * ∫ u : ℝ in Set.Ioi (Real.pi * a), Real.exp (-u) := by
    calc
      ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) =
          ∫ t : ℝ in Set.Ioi a, (fun u : ℝ => Real.exp (-u)) (Real.pi * t) := by
        exact
          setIntegral_congr_fun measurableSet_Ioi
            (fun t _ht =>
              congrArg Real.exp (neg_mul Real.pi t))
      _ =
          Real.pi⁻¹ •
            ∫ u : ℝ in Set.Ioi (Real.pi * a), Real.exp (-u) :=
        integral_comp_mul_left_Ioi
          (fun u : ℝ => Real.exp (-u)) a hpi_pos
      _ =
          Real.pi⁻¹ * ∫ u : ℝ in Set.Ioi (Real.pi * a), Real.exp (-u) := by
        rfl
  have htail_exact :
      ∫ u : ℝ in Set.Ioi (Real.pi * a), Real.exp (-u) =
        Real.exp (-(Real.pi * a)) :=
    integral_exp_neg_Ioi (Real.pi * a)
  have htail_scaled :
      ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) =
        Real.pi⁻¹ * Real.exp (-Real.pi * a) := by
    calc
      ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) =
          Real.pi⁻¹ * ∫ u : ℝ in Set.Ioi (Real.pi * a), Real.exp (-u) :=
        hchange
      _ = Real.pi⁻¹ * Real.exp (-(Real.pi * a)) := by
        exact congrArg (fun x : ℝ => Real.pi⁻¹ * x) htail_exact
      _ = Real.pi⁻¹ * Real.exp (-Real.pi * a) := by
        exact
          congrArg
            (fun x : ℝ => Real.pi⁻¹ * Real.exp x)
            (neg_mul Real.pi a).symm
  have hpi_inv_le_one : Real.pi⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_two.trans Real.two_le_pi)
  have hexp_nonneg : 0 ≤ Real.exp (-Real.pi * a) :=
    le_of_lt (Real.exp_pos (-Real.pi * a))
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ Real.exp (-Real.pi * a))
      htail_scaled.symm
      (mul_le_of_le_one_left hexp_nonneg hpi_inv_le_one)

/-- The Binet majorant tail integral decays exponentially from any lower
cutoff at least `1`.

This is the real inequality that will eventually feed the full-sector tail
absorption theorem. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_integral_le_exp
    {a : ℝ}
    (ha : 1 ≤ a) :
    ∫ t : ℝ in Set.Ioi a,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      2 * Real.exp (-Real.pi * a) := by
  have htail_bound :
      ∀ t : ℝ,
        t ∈ Set.Ioi a →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
            2 * Real.exp (-Real.pi * t) :=
    fun t ht =>
      Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp
      (lt_of_le_of_lt ha ht)
  have hpos : 0 < Real.pi := Real.pi_pos
  have htail : IntegrableOn (fun t : ℝ => Real.exp (-Real.pi * t)) (Set.Ioi a) :=
    exp_neg_integrableOn_Ioi a hpos
  have hexp_int :
      IntegrableOn (fun t : ℝ => 2 * Real.exp (-Real.pi * t)) (Set.Ioi a) := by
    exact htail.const_mul (2 : ℝ)
  have hmajorant_int :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi a) := by
    exact
      Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty.mono_set
        (fun t ht => lt_of_le_of_lt ha ht)
  have hmono :
      ∫ t : ℝ in Set.Ioi a,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      ∫ t : ℝ in Set.Ioi a, 2 * Real.exp (-Real.pi * t) := by
    exact setIntegral_mono_on
      hmajorant_int
      hexp_int
      measurableSet_Ioi
      (fun t ht => by
        have hnonneg : 0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          exact le_of_lt (Real.binetSecondFormula_kernel_majorant_pos
            (lt_trans zero_lt_one (lt_of_le_of_lt ha ht)))
        have hnorm_le :
            ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
              2 * Real.exp (-Real.pi * t) :=
          htail_bound t ht
        exact
          Eq.subst
            (motive := fun x : ℝ => x ≤ 2 * Real.exp (-Real.pi * t))
            (Eq.trans
              (Real.norm_eq_abs
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
              (abs_of_nonneg hnonneg))
            hnorm_le)
  have hexp_tail :
      ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) ≤
        Real.exp (-Real.pi * a) :=
    Real.exp_neg_pi_tail_integral_le_exp a
  have hscaled_tail :
      ∫ t : ℝ in Set.Ioi a, 2 * Real.exp (-Real.pi * t) ≤
        2 * Real.exp (-Real.pi * a) := by
    calc
      ∫ t : ℝ in Set.Ioi a, 2 * Real.exp (-Real.pi * t) =
          2 * ∫ t : ℝ in Set.Ioi a, Real.exp (-Real.pi * t) := by
        exact integral_mul_left 2 (fun t : ℝ => Real.exp (-Real.pi * t))
      _ ≤ 2 * Real.exp (-Real.pi * a) :=
        mul_le_mul_of_nonneg_left hexp_tail zero_le_two
  exact le_trans hmono hscaled_tail

/-- A reusable norm-transport lemma for complex quotients. -/
theorem Real.binetSecondFormula_kernel_majorant_unitInterval_expLower_owner :
    Real.BinetSecondFormulaKernelMajorantUnitIntervalExpLower := by
  let c : ℝ := Real.exp (-((2 : ℝ) * Real.pi))
  have hc_pos : 0 < c :=
    Real.exp_pos (-((2 : ℝ) * Real.pi))
  exact
    ⟨c, hc_pos,
      fun a ha =>
        let L : ℝ := a * Real.exp (-((2 : ℝ) * Real.pi) * (a + 1))
        have hpointwise :
            ∀ t : ℝ,
              t ∈ Set.Ioc a (a + 1) →
                L ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          intro t ht
          have ht_ge_one : (1 : ℝ) ≤ t :=
            le_trans ha (le_of_lt ht.1)
          have ht_le_a_one : t ≤ a + 1 :=
            ht.2
          let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
          let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * (a + 1))
          have hD_pos : 0 < D :=
            Real.binetSecondFormula_kernel_majorant_denominator_pos
              (lt_of_lt_of_le zero_lt_one ht_ge_one)
          have hE_pos : 0 < E :=
            Real.exp_pos ((2 : ℝ) * Real.pi * (a + 1))
          have hcoeff_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
            le_of_lt (mul_pos two_pos Real.pi_pos)
          have hexp_le :
              Real.exp ((2 : ℝ) * Real.pi * t) ≤
                Real.exp ((2 : ℝ) * Real.pi * (a + 1)) :=
            Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left ht_le_a_one hcoeff_nonneg)
          have hD_le_E : D ≤ E := by
            calc
              D = Real.exp ((2 : ℝ) * Real.pi * t) - 1 := rfl
              _ ≤ Real.exp ((2 : ℝ) * Real.pi * t) := by
                exact sub_le_self
                  (Real.exp ((2 : ℝ) * Real.pi * t))
                  zero_le_one
              _ ≤ E := hexp_le
          have hreciprocal :
              1 / E ≤ 1 / D :=
            one_div_le_one_div_of_le hD_pos hD_le_E
          have ha_nonneg : 0 ≤ a :=
            le_trans zero_le_one ha
          have ha_over_E_le :
              a / E ≤ a / D :=
            div_le_div_of_nonneg_left ha_nonneg hD_pos hD_le_E
          have hlinear :
              a / D ≤ t / D :=
            div_le_div_of_nonneg_right (le_of_lt ht.1) (le_of_lt hD_pos)
          have hL_eq : L = a / E := by
            calc
              L = a * Real.exp (-((2 : ℝ) * Real.pi * (a + 1))) := by
                exact congrArg (fun x : ℝ => a * Real.exp x)
                  (neg_mul ((2 : ℝ) * Real.pi) (a + 1))
              _ = a * (Real.exp ((2 : ℝ) * Real.pi * (a + 1)))⁻¹ := by
                exact congrArg (fun x : ℝ => a * x)
                  (Real.exp_neg ((2 : ℝ) * Real.pi * (a + 1)))
              _ = a / E := by
                rfl
          exact
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
              hL_eq.symm
              (le_trans ha_over_E_le hlinear)
        have hL_integrable :
            IntegrableOn (fun _t : ℝ => L) (Set.Ioc a (a + 1)) :=
          integrableOn_const.mpr
            (Or.inr measure_Ioc_lt_top)
        have hK_integrable :
            IntegrableOn
              (fun t : ℝ =>
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
              (Set.Ioc a (a + 1)) :=
          Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty.mono_set
            (fun t ht => lt_of_le_of_lt ha ht.1)
        have hintegral_lower :
            ∫ t : ℝ in Set.Ioc a (a + 1), L ≤
              ∫ t : ℝ in Set.Ioc a (a + 1),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          setIntegral_mono_on
            hL_integrable
            hK_integrable
            measurableSet_Ioc
            hpointwise
        have hconst_integral :
            ∫ t : ℝ in Set.Ioc a (a + 1), L = L := by
          have hvolume :
              volume (Set.Ioc a (a + 1)) =
                ENNReal.ofReal ((a + 1) - a) :=
            Real.volume_Ioc
          have hlength : (a + 1) - a = (1 : ℝ) :=
            add_sub_cancel_left a 1
          have hvolume_one :
              (volume (Set.Ioc a (a + 1))).toReal = (1 : ℝ) := by
            calc
              (volume (Set.Ioc a (a + 1))).toReal =
                  (ENNReal.ofReal ((a + 1) - a)).toReal := by
                exact congrArg ENNReal.toReal hvolume
              _ = (ENNReal.ofReal (1 : ℝ)).toReal := by
                exact congrArg (fun x : ℝ => (ENNReal.ofReal x).toReal) hlength
              _ = (1 : ℝ) := by
                exact ENNReal.toReal_ofReal zero_le_one
          calc
            ∫ t : ℝ in Set.Ioc a (a + 1), L =
                (volume (Set.Ioc a (a + 1))).toReal • L := by
              exact setIntegral_const L
            _ = (volume (Set.Ioc a (a + 1))).toReal * L := by
              rfl
            _ = L * (volume (Set.Ioc a (a + 1))).toReal := by
              exact mul_comm (volume (Set.Ioc a (a + 1))).toReal L
            _ = L * 1 := by
              exact congrArg (fun x : ℝ => L * x) hvolume_one
            _ = L := mul_one L
        have hscale : c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) = L := by
          calc
            c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) =
                a *
                  (Real.exp (-((2 : ℝ) * Real.pi)) *
                    Real.exp (-((2 : ℝ) * Real.pi) * a)) := by
              calc
                c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) =
                    (Real.exp (-((2 : ℝ) * Real.pi)) * a) *
                      Real.exp (-((2 : ℝ) * Real.pi) * a) := rfl
                _ = a *
                    (Real.exp (-((2 : ℝ) * Real.pi)) *
                      Real.exp (-((2 : ℝ) * Real.pi) * a)) := by
                  calc
                    (Real.exp (-((2 : ℝ) * Real.pi)) * a) *
                        Real.exp (-((2 : ℝ) * Real.pi) * a) =
                      a * Real.exp (-((2 : ℝ) * Real.pi)) *
                        Real.exp (-((2 : ℝ) * Real.pi) * a) := by
                        exact congrArg
                          (fun x : ℝ => x * Real.exp (-((2 : ℝ) * Real.pi) * a))
                          (mul_comm (Real.exp (-((2 : ℝ) * Real.pi)) ) a)
                    _ = a *
                        (Real.exp (-((2 : ℝ) * Real.pi)) *
                          Real.exp (-((2 : ℝ) * Real.pi) * a)) := by
                      exact (mul_assoc a
                        (Real.exp (-((2 : ℝ) * Real.pi)))
                        (Real.exp (-((2 : ℝ) * Real.pi) * a))
                        )
            _ = a * Real.exp
                  (-((2 : ℝ) * Real.pi) +
                    (-((2 : ℝ) * Real.pi) * a)) := by
              exact congrArg (fun x : ℝ => a * x)
                (Real.exp_add (-((2 : ℝ) * Real.pi))
                  (-((2 : ℝ) * Real.pi) * a)).symm
            _ = a * Real.exp (-((2 : ℝ) * Real.pi) * (a + 1)) := by
              exact
                congrArg (fun x : ℝ => a * Real.exp x)
                  (calc
                    -((2 : ℝ) * Real.pi) +
                        (-((2 : ℝ) * Real.pi) * a) =
                      -((2 : ℝ) * Real.pi) * 1 +
                        -((2 : ℝ) * Real.pi) * a := by
                        exact congrArg (fun x : ℝ => x + (-((2 : ℝ) * Real.pi) * a))
                          (mul_one (-((2 : ℝ) * Real.pi))).symm
                    _ = -((2 : ℝ) * Real.pi) * (1 + a) := by
                      exact (mul_add (-((2 : ℝ) * Real.pi)) 1 a).symm
                    _ = -((2 : ℝ) * Real.pi) * (a + 1) := by
                      exact congrArg (fun x : ℝ => -((2 : ℝ) * Real.pi) * x)
                        (add_comm 1 a))
        calc
          c * a * Real.exp (-((2 : ℝ) * Real.pi) * a) = L := hscale
          _ =
              ∫ t : ℝ in Set.Ioc a (a + 1), L :=
            hconst_integral.symm
          _ ≤
              ∫ t : ℝ in Set.Ioc a (a + 1),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
            hintegral_lower⟩

/-- Owner real-variable leaf: the first unit interval is bounded by the full
Binet scalar tail. -/
theorem Real.binetSecondFormula_kernel_majorant_unitInterval_le_tail_owner :
    Real.BinetSecondFormulaKernelMajorantUnitIntervalLeTail := by
  intro a ha
  let M : ℝ → ℝ :=
    fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  have hM_integrable_tail :
      IntegrableOn M (Set.Ioi a) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty.mono_set
      (fun t ht => lt_of_le_of_lt ha ht)
  have hM_nonneg_tail :
      0 ≤ᵐ[volume.restrict (Set.Ioi a)] M :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht =>
        Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
          (lt_trans zero_lt_one (lt_of_le_of_lt ha ht)))
  have hunit_subset_tail :
      Set.Ioc a (a + 1) ≤ᵐ[volume] Set.Ioi a :=
    Filter.Eventually.of_forall
      (fun t ht => ht.1)
  exact
    setIntegral_mono_set
      hM_integrable_tail
      hM_nonneg_tail
      hunit_subset_tail


end
end LFunctions
end Boundary

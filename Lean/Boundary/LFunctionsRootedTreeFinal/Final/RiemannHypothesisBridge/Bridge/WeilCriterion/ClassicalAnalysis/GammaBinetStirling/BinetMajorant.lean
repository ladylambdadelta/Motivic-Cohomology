import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Real majorants for the Binet kernel

This file owns the elementary real estimates used to dominate the Binet
arctangent kernel and its differentiated kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Strict positivity of the Binet real exponential denominator at every
positive point. -/
theorem Real.binetSecondFormula_exp_denominator_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  have htwo_pi_pos : 0 < (2 : ℝ) * Real.pi :=
    mul_pos two_pos Real.pi_pos
  have hexponent_pos : 0 < (2 : ℝ) * Real.pi * t :=
    mul_pos htwo_pi_pos ht
  have hone_lt_exp :
      1 < Real.exp ((2 : ℝ) * Real.pi * t) := by
    calc
      1 = Real.exp 0 := by
        exact Real.exp_zero.symm
      _ < Real.exp ((2 : ℝ) * Real.pi * t) :=
        Real.exp_lt_exp.mpr hexponent_pos
  exact sub_pos.mpr hone_lt_exp

/-- Positivity removes the norm from the Binet real denominator. -/
theorem Real.binetSecondFormula_exp_denominator_norm_eq
    {t : ℝ}
    (ht : 0 < t) :
    ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ =
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  exact
    Real.norm_of_nonneg
      (le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht))

/-- Strict positivity of the Binet majorant denominator at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  exact Real.binetSecondFormula_exp_denominator_pos ht

/-- Nonvanishing of the Binet majorant denominator at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_ne_zero
    {t : ℝ}
    (ht : 0 < t) :
    Real.exp ((2 : ℝ) * Real.pi * t) - 1 ≠ 0 :=
  ne_of_gt
    (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Positivity of the Binet real majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    div_pos ht
      (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Nonnegativity of the Binet real majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht
  exact le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht)

/-- Exponential lower bound giving cancellation of the zero of
`exp (2πt) - 1` at the origin. -/
theorem Real.two_pi_mul_le_exp_two_pi_mul_sub_one
    {t : ℝ}
    (ht : 0 ≤ t) :
    (2 : ℝ) * Real.pi * t ≤
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  let x : ℝ := (2 : ℝ) * Real.pi * t
  have hx_nonneg : 0 ≤ x :=
    mul_nonneg (le_of_lt (mul_pos two_pos Real.pi_pos)) ht
  have hlower : x + 1 ≤ Real.exp x :=
    Real.add_one_le_exp x
  change x ≤ Real.exp x - 1
  linarith

/-- Division form of the zero-cancellation estimate for the Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_le_one_div_two_pi
    {t : ℝ}
    (ht : 0 < t) :
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      1 / ((2 : ℝ) * Real.pi) := by
  let a : ℝ := (2 : ℝ) * Real.pi
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have ha_pos : 0 < a :=
    mul_pos two_pos Real.pi_pos
  have hd_pos : 0 < d :=
    Real.binetSecondFormula_kernel_majorant_denominator_pos ht
  have had_le : a * t ≤ d := by
    exact Real.two_pi_mul_le_exp_two_pi_mul_sub_one (le_of_lt ht)
  have hmul : a * (t / d) ≤ 1 := by
    have hle_div : a * t / d ≤ d / d :=
      div_le_div_of_nonneg_right had_le (le_of_lt hd_pos)
    have hd_div : d / d = 1 :=
      div_self (ne_of_gt hd_pos)
    calc
      a * (t / d) = a * t / d := by ring
      _ ≤ d / d := hle_div
      _ = 1 := hd_div
  have hdiv :
      t / d ≤ 1 / a := by
    have hmul_commuted : t / d * a ≤ 1 := by
      calc
        t / d * a = a * (t / d) := mul_comm (t / d) a
        _ ≤ 1 := hmul
    exact (le_div_iff₀ ha_pos).mpr hmul_commuted
  exact hdiv

/-- Pointwise zero-cancellation bound for the Binet majorant on `(0,1]`.

The analytic root is the elementary inequality
`t / (exp (2πt) - 1) ≤ 1 / (2π)`, obtained from
`1 + 2πt ≤ exp (2πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise
    {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      1 / ((2 : ℝ) * Real.pi) := by
  have hpos :
      0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht.1)
  have hle :
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        1 / ((2 : ℝ) * Real.pi) :=
    Real.binetSecondFormula_kernel_majorant_le_one_div_two_pi ht.1
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1 / ((2 : ℝ) * Real.pi))
      (Real.norm_of_nonneg hpos).symm
      hle

/-- The Binet majorant is bounded near zero after cancellation of the simple
zero in `exp (2πt)-1`. -/
theorem Real.binetSecondFormula_kernel_majorant_bounded_zero_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioc (0 : ℝ) 1 →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤ C := by
  refine ⟨1 / ((2 : ℝ) * Real.pi), ?_, ?_⟩
  · exact one_div_pos.mpr (mul_pos two_pos Real.pi_pos)
  · intro t ht
    exact
      Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise ht

/-- A bounded a.e.-measurable real function on a finite interval is integrable. -/
theorem Real.integrableOn_Ioc_of_aestronglyMeasurable_norm_le_const
    {f : ℝ → ℝ}
    {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, x ∈ Set.Ioc a b → ‖f x‖ ≤ C) :
    IntegrableOn f (Set.Ioc a b) := by
  have _ : 0 ≤ C := hC
  refine ⟨hmeas, ?_⟩
  exact
    hasFiniteIntegral_restrict_of_bounded
      (μ := volume)
      (s := Set.Ioc a b)
      (C := C)
      measure_Ioc_lt_top
      ((ae_restrict_mem measurableSet_Ioc).mono
        (fun x hx => hbound x hx))

/-- The Binet majorant is a.e.-measurable on the local interval `(0,1]`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_zero_one :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hmeas :
      Measurable
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    fun_prop
  exact hmeas.aestronglyMeasurable

/-- A bounded Binet majorant on `(0,1]` is integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_from_zero_cancellation :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  rcases
      Real.binetSecondFormula_kernel_majorant_bounded_zero_one with
    ⟨C, hC_pos, hC_bound⟩
  exact
    Real.integrableOn_Ioc_of_aestronglyMeasurable_norm_le_const
      Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_zero_one
      (le_of_lt hC_pos)
      hC_bound

/-- The Binet real majorant is integrable near zero. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_from_zero_cancellation

/-- On the Binet tail, `exp (2πt) - 1` is bounded below by
`(1/2) exp (2πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_denominator_lower
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    (Real.exp ((2 : ℝ) * Real.pi * t)) / 2 ≤
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  let x : ℝ := (2 : ℝ) * Real.pi * t
  have hx_ge_two_pi : (2 : ℝ) * Real.pi ≤ x := by
    have hcoeff_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
      le_of_lt (mul_pos two_pos Real.pi_pos)
    calc
      (2 : ℝ) * Real.pi = (2 : ℝ) * Real.pi * 1 := by ring
      _ ≤ (2 : ℝ) * Real.pi * t :=
        mul_le_mul_of_nonneg_left (le_of_lt ht) hcoeff_nonneg
      _ = x := rfl
  have hlog_two_le_two_pi : Real.log 2 ≤ (2 : ℝ) * Real.pi := by
    have hlog_two_lt_two : Real.log 2 < (2 : ℝ) := by
      calc
        Real.log 2 < 2 - 1 :=
          Real.log_lt_sub_one_of_pos
            (by norm_num : (0 : ℝ) < 2)
            (by norm_num : (2 : ℝ) ≠ 1)
        _ < 2 := by norm_num
    have htwo_lt_two_pi : (2 : ℝ) < 2 * Real.pi := by
      have hone_lt_pi : (1 : ℝ) < Real.pi :=
        lt_trans (by norm_num : (1 : ℝ) < 3) Real.pi_gt_three
      calc
        (2 : ℝ) = 2 * 1 := (mul_one 2).symm
        _ < 2 * Real.pi := mul_lt_mul_of_pos_left hone_lt_pi two_pos
    exact le_trans (le_of_lt hlog_two_lt_two) (le_of_lt htwo_lt_two_pi)
  have hlog_two_le_x : Real.log 2 ≤ x :=
    le_trans hlog_two_le_two_pi hx_ge_two_pi
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp x := by
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    exact (Real.log_le_iff_le_exp htwo_pos).mp hlog_two_le_x
  change Real.exp x / 2 ≤ Real.exp x - 1
  nlinarith [Real.exp_pos x]

/-- The linear factor on the Binet tail is absorbed by `exp (πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_linear_le_exp_pi
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    t ≤ Real.exp (Real.pi * t) := by
  have ht_nonneg : 0 ≤ t :=
    le_of_lt (lt_trans zero_lt_one ht)
  have hpi_t_ge_t : t ≤ Real.pi * t := by
    have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
      le_of_lt (lt_trans (by norm_num : (1 : ℝ) < 3) Real.pi_gt_three)
    calc
      t = 1 * t := by ring
      _ ≤ Real.pi * t :=
        mul_le_mul_of_nonneg_right hone_le_pi ht_nonneg
  have ht_le_add : t ≤ Real.pi * t + 1 :=
    le_trans hpi_t_ge_t (le_add_of_nonneg_right zero_le_one)
  have hadd_le_exp : Real.pi * t + 1 ≤ Real.exp (Real.pi * t) :=
    Real.add_one_le_exp (Real.pi * t)
  exact le_trans ht_le_add hadd_le_exp

/-- Pointwise tail domination after separating the denominator lower bound
and the linear/exponential absorption. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_two_exp_of_denominator_lower
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      2 * Real.exp (-Real.pi * t) := by
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t)
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hE_pos : 0 < E :=
    Real.exp_pos ((2 : ℝ) * Real.pi * t)
  have hd_pos : 0 < d :=
    Real.binetSecondFormula_kernel_majorant_denominator_pos
      (lt_trans zero_lt_one ht)
  have hd_lower : E / 2 ≤ d :=
    Real.binetSecondFormula_kernel_majorant_tail_denominator_lower ht
  have ht_le_exp : t ≤ Real.exp (Real.pi * t) :=
    Real.binetSecondFormula_kernel_majorant_tail_linear_le_exp_pi ht
  have hdiv_le : t / d ≤ t / (E / 2) :=
    div_le_div_of_nonneg_left
      (le_of_lt (lt_trans zero_lt_one ht))
      (div_pos hE_pos two_pos)
      hd_lower
  have hrewrite : t / (E / 2) = 2 * (t / E) := by
    have hE_ne : E ≠ 0 := ne_of_gt hE_pos
    calc
      t / (E / 2) = t * 2 / E := by
        exact div_div_eq_mul_div t E 2
      _ = (t * 2) / E := by
        rfl
      _ = (2 * t) / E := by
        exact congrArg (fun x : ℝ => x / E) (mul_comm t 2)
      _ = 2 * (t / E) := by
        exact (mul_div_assoc 2 t E)
  have ht_over_E_le :
      t / E ≤ Real.exp (-Real.pi * t) := by
    have hmul_le :
        t ≤ Real.exp (-Real.pi * t) * E := by
      have hmul :
          t ≤ E * Real.exp (-Real.pi * t) := by
        calc
          t ≤ Real.exp (Real.pi * t) := ht_le_exp
          _ = E * Real.exp (-Real.pi * t) := by
            dsimp [E]
            calc
              Real.exp (Real.pi * t) =
                  Real.exp (((2 : ℝ) * Real.pi * t) + (-Real.pi * t)) := by
                congr 1
                ring
              _ = Real.exp ((2 : ℝ) * Real.pi * t) *
                  Real.exp (-Real.pi * t) := by
                exact Real.exp_add ((2 : ℝ) * Real.pi * t) (-Real.pi * t)
      calc
        t ≤ E * Real.exp (-Real.pi * t) := hmul
        _ = Real.exp (-Real.pi * t) * E :=
          mul_comm E (Real.exp (-Real.pi * t))
    exact (div_le_iff₀ hE_pos).mpr hmul_le
  calc
    t / d ≤ t / (E / 2) := hdiv_le
    _ = 2 * (t / E) := hrewrite
    _ ≤ 2 * Real.exp (-Real.pi * t) :=
      mul_le_mul_of_nonneg_left ht_over_E_le (by norm_num : (0 : ℝ) ≤ 2)

/-- Pointwise exponential tail domination for the Binet majorant with the
concrete constant `2`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      2 * Real.exp (-Real.pi * t) := by
  have ht_pos : 0 < t :=
    lt_trans zero_lt_one ht
  have hnonneg :
      0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht_pos)
  have hle :
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        2 * Real.exp (-Real.pi * t) :=
    Real.binetSecondFormula_kernel_majorant_tail_le_two_exp_of_denominator_lower ht
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * Real.exp (-Real.pi * t))
      (Real.norm_of_nonneg hnonneg).symm
      hle

/-- The Binet real majorant has an exponentially decaying tail. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_exp :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (1 : ℝ) →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
            C * Real.exp (-Real.pi * t) := by
  refine ⟨2, two_pos, ?_⟩
  intro t ht
  exact
    Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp ht

/-- A real function dominated on a tail by a decaying exponential is integrable
on that tail. -/
theorem Real.integrableOn_Ioi_of_aestronglyMeasurable_norm_le_exp_tail
    {f : ℝ → ℝ}
    {a C b : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi a)))
    (hC : 0 ≤ C)
    (hb : 0 < b)
    (hbound :
      ∀ t : ℝ,
        t ∈ Set.Ioi a →
          ‖f t‖ ≤ C * Real.exp (-b * t)) :
    IntegrableOn f (Set.Ioi a) := by
  have _ : 0 ≤ C := hC
  have h_exp :
      IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi a) :=
    exp_neg_integrableOn_Ioi a hb
  have h_bound_integrable :
      Integrable (fun t : ℝ => C * Real.exp (-b * t))
        (volume.restrict (Set.Ioi a)) :=
    h_exp.integrable.const_mul C
  exact
    h_bound_integrable.mono'
      hmeas
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => hbound t ht))

/-- The Binet majorant is a.e.-measurable on the tail interval `(1,∞)`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_one_infty :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    fun_prop
  exact hmeas.aestronglyMeasurable

/-- Exponential tail domination implies tail integrability of the Binet
majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_from_exponential_tail :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  rcases
      Real.binetSecondFormula_kernel_majorant_tail_le_exp with
    ⟨C, hC_pos, hC_bound⟩
  exact
    Real.integrableOn_Ioi_of_aestronglyMeasurable_norm_le_exp_tail
      Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_one_infty
      (le_of_lt hC_pos)
      Real.pi_pos
      hC_bound

/-- The Binet real majorant is integrable at infinity. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_from_exponential_tail

/-- The positive half-line decomposes into the local Binet interval `(0,1]`
and the tail interval `(1,∞)`. -/
theorem Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one :
    Set.Ioi (0 : ℝ) =
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  exact
    Set.ext
      (fun x =>
        ⟨fun hx =>
            Or.elim (lt_or_ge (1 : ℝ) x)
              (fun hone_lt_x => Or.inr hone_lt_x)
              (fun hx_le_one => Or.inl ⟨hx, hx_le_one⟩),
          fun hx =>
            Or.elim hx
              (fun hx_local => hx_local.1)
              (fun hx_tail => lt_trans zero_lt_one hx_tail)⟩)

/-- A point of `(0,∞)` lies either in `(0,1]` or in `(1,∞)`. -/
theorem Real.Ioi_zero_subset_Ioc_zero_one_union_Ioi_one :
    Set.Ioi (0 : ℝ) ⊆
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
  fun x hx =>
    Or.elim (lt_or_ge (1 : ℝ) x)
      (fun hone_lt_x => Or.inr hone_lt_x)
      (fun hx_le_one => Or.inl ⟨hx, hx_le_one⟩)

/-- The union `(0,1] ∪ (1,∞)` is contained in `(0,∞)`. -/
theorem Real.Ioc_zero_one_union_Ioi_one_subset_Ioi_zero :
    Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) ⊆
      Set.Ioi (0 : ℝ) :=
  fun _ hx =>
    Or.elim hx
      (fun hx_local => hx_local.1)
      (fun hx_tail => lt_trans zero_lt_one hx_tail)

/-- Joining local integrability on `(0,1]` with tail integrability on `(1,∞)`
gives integrability on `(0,∞)`. -/
theorem Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
    {f : ℝ → ℝ}
    (hlocal : IntegrableOn f (Set.Ioc (0 : ℝ) 1))
    (htail : IntegrableOn f (Set.Ioi (1 : ℝ))) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  exact
    (hlocal.union htail).mono_set
      Real.Ioi_zero_subset_Ioc_zero_one_union_Ioi_one

/-- The real majorant for the Binet kernel is integrable on `(0,∞)` once its
local and tail pieces are integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
    (hlocal :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioc (0 : ℝ) 1))
    (htail :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi (1 : ℝ))) :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
      hlocal htail

/-- The Binet real majorant is integrable on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty

end

end LFunctions
end Boundary

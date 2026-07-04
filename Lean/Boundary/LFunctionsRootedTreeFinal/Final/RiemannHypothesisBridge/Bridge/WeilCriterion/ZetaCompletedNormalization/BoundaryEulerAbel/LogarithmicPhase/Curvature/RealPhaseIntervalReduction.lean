import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCore
import Mathlib.Order.Interval.Finset.Nat

/-!
# Real-phase interval reductions

This file owns finite interval-shape reductions used by the logarithmic
curvature block estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The endpoint-plus-square-root target is monotone in the natural right
endpoint. -/
theorem Real.logarithmicPhase_endpoint_sqrt_target_mono_right
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {r b : ℕ}
    (hrb : r ≤ b) :
    (((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
      (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  have hT_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hnum_le : ((r + 1 : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ hrb)
  have hdiv_le :
      ((r + 1 : ℕ) : ℝ) / ‖t‖ ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    (div_le_div_iff_of_pos_right hT_pos).mpr hnum_le
  exact add_le_add_right hdiv_le (Real.sqrt (1 + ‖t‖))

/-- Three subblock endpoint-plus-square-root targets are bounded by three
ambient targets. -/
theorem Real.logarithmicPhase_three_subblock_targets_le_three_ambient
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {r b : ℕ}
    (hrb : r ≤ b) :
    3 * (((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) ≤
      3 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
  exact
    mul_le_mul_of_nonneg_left
      (Real.logarithmicPhase_endpoint_sqrt_target_mono_right t ht hrb)
      (Nat.cast_nonneg 3)

/-- A closed logarithmic real-phase subblock estimate at its own right endpoint
widens to the ambient endpoint target. -/
theorem Complex.logarithmicPhaseRealPhase_Icc_subblock_bound_mono_right
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c r : ℕ}
    (hr_right : r ≤ b)
    (hlocal :
      ‖∑ n ∈ Finset.Icc c r,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        80 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc c r,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have htarget_mono :
      80 * ((((r + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_le_mul_of_nonneg_left
      (Real.logarithmicPhase_endpoint_sqrt_target_mono_right t ht hr_right)
      (Nat.cast_nonneg 80)
  exact le_trans hlocal htarget_mono

/-- A half-open logarithmic real-phase interval estimate follows from the
corresponding closed-interval estimates, with the empty interval handled
constructively. -/
theorem Complex.logarithmicPhaseRealPhase_Ico_bound_of_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c d : ℕ}
    (hd_right : d ≤ b + 1)
    (hIcc :
      ∀ {r : ℕ},
        c ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match Nat.lt_or_ge c d with
  | Or.inl hcd_strict =>
      let r : ℕ := d - 1
      have hd_pos : 0 < d :=
        lt_of_le_of_lt (Nat.zero_le c) hcd_strict
      have hd_pred_succ : r + 1 = d :=
        Nat.succ_pred_eq_of_pos hd_pos
      have hIco_succ : Finset.Ico c (r + 1) = Finset.Icc c r :=
        Nat.Ico_succ_right c r
      have hIco_eq : Finset.Ico c d = Finset.Icc c r :=
        Eq.subst
          (motive := fun right : ℕ => Finset.Ico c right = Finset.Icc c r)
          hd_pred_succ
          hIco_succ
      have hcr : c ≤ r :=
        Nat.le_pred_of_lt hcd_strict
      have hr_le_b : r ≤ b := by
        have hsucc_le : r + 1 ≤ b + 1 :=
          Eq.subst
            (motive := fun left : ℕ => left ≤ b + 1)
            hd_pred_succ.symm
            hd_right
        exact Nat.succ_le_succ_iff.mp hsucc_le
      have hlocal :
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        hIcc hcr hr_le_b
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hIco_eq.symm
          hlocal
  | Or.inr hdc =>
      have hIco_empty : Finset.Ico c d = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : c ≤ n ∧ n < d :=
              Finset.mem_Ico.mp hn
            have hd_le_n : d ≤ n :=
              Nat.le_trans hdc hn_bounds.1
            not_lt_of_ge hd_le_n hn_bounds.2)
      have hsum_zero :
          (∑ n ∈ Finset.Ico c d, Complex.exp (Complex.I * (φ n : ℂ))) = 0 :=
        Eq.trans
          (congrArg
            (fun S : Finset ℕ =>
              ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
            hIco_empty)
          Finset.sum_empty
      have htarget_nonneg :
          0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        mul_nonneg (Nat.cast_nonneg 80)
          (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
      have hzero_bound :
          ‖(0 : ℂ)‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Eq.subst
          (motive := fun left : ℝ =>
            left ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          (norm_zero : ‖(0 : ℂ)‖ = 0).symm
          htarget_nonneg
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤
              80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hsum_zero.symm
          hzero_bound

/-- Half-open logarithmic B-process interval reduction from closed subinterval
estimates.  This theorem owns only the finite interval-shape conversion; the
closed-interval analytic estimate is supplied as a local premise. -/
theorem Complex.logarithmicPhaseRealPhase_Ico_bProcess_of_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {b c d : ℕ}
    (hd_right : d ≤ b + 1)
    (hIcc :
      ∀ {r : ℕ},
        c ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
            80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Ico c d,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_Ico_bound_of_Icc_bounds
      t ht hd_right hIcc

end

end LFunctions
end Boundary

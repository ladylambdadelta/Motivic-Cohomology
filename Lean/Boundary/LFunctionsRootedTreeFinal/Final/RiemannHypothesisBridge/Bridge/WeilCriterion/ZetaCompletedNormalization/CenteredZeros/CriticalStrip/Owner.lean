import Mathlib.NumberTheory.LSeries.Dirichlet
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner

/-!
# Critical-strip localization for centered completed-zeta zeros

This child owner keeps the strict zeta nonvanishing dependency out of the core
centered-zero normalization owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Completed zeta has no zeros in the half-plane to the right of `1`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re
    (s : ℂ)
    (hsre : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hs0 : s ≠ 0 := by
    intro hs_zero
    have hre_zero : s.re = 0 := by
      exact congrArg Complex.re hs_zero
    have hone_lt_zero : (1 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hre_zero
        hsre
    exact (not_lt_of_ge zero_le_one) hone_lt_zero
  have hζ_eq :
      riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  have hζ_zero : riemannZeta s = 0 := by
    calc
      riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s := hζ_eq
      _ = 0 / Complex.Gammaℝ s := by
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ s) hs
      _ = 0 := by
        exact zero_div (Complex.Gammaℝ s)
  exact riemannZeta_ne_zero_of_one_lt_re hsre hζ_zero

/-- Completed zeta has no zeros in the left half-plane. -/
theorem completedRiemannZeta_ne_zero_of_re_lt_zero
    (s : ℂ)
    (hsre : s.re < 0) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hright_re :
      1 < ((1 : ℂ) - s).re := by
    have hre :
        ((1 : ℂ) - s).re = 1 - s.re := by
      exact Complex.sub_re (1 : ℂ) s
    have hlt : 1 < 1 - s.re := by
      have hsum : s.re + 1 < 0 + 1 :=
        add_lt_add_right hsre 1
      have hsum_one : s.re + 1 < 1 :=
        Eq.subst
          (motive := fun x : ℝ => s.re + 1 < x)
          (zero_add (1 : ℝ))
          hsum
      exact lt_sub_iff_add_lt'.2 hsum_one
    exact Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hre.symm
      hlt
  have hright_ne :
      completedRiemannZeta ((1 : ℂ) - s) ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re ((1 : ℂ) - s) hright_re
  have hsymm :
      completedRiemannZeta ((1 : ℂ) - s) =
        completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  exact hright_ne (hsymm.trans hs)

/-- Completed-zeta zeros lie in the ordinary critical strip.

This is the standard unconditional critical-strip theorem for zeros of the
completed Riemann zeta normalization. -/
theorem completedRiemannZeta_zero_re_mem_criticalStrip
    (s : ℂ)
    (hs : completedRiemannZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ (1 : ℝ) := by
  have hnot_left : ¬ s.re < 0 := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_re_lt_zero s hsre hs
  have hnot_right : ¬ (1 : ℝ) < s.re := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_one_lt_re s hsre hs
  exact ⟨le_of_not_gt hnot_left, le_of_not_gt hnot_right⟩

/-- The real coordinate of the uncentered argument is the centered real
coordinate shifted by `1/2`. -/
theorem centeredCompletedRiemannZeta_uncenter_re
    (s : ℂ) :
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re := by
  calc
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℂ).re + s.re := by
      exact Complex.add_re (1 / 2 : ℂ) s
    _ = (1 / 2 : ℝ) + s.re := by
      have hhalf_complex :
          (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        rfl
      have hhalf_coe_re :
          (((1 / 2 : ℝ) : ℂ).re) = (1 / 2 : ℝ) :=
        Complex.ofReal_re (1 / 2 : ℝ)
      have hhalf_re : (1 / 2 : ℂ).re = (1 / 2 : ℝ) :=
        Eq.trans
          (congrArg Complex.re hhalf_complex)
          hhalf_coe_re
      exact congrArg (fun x : ℝ => x + s.re) hhalf_re

/-- If the uncentered coordinate lies in `[0,1]`, the centered coordinate lies
in `[-1/2,1/2]`. -/
theorem centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    {x : ℝ}
    (hleft : 0 ≤ (1 / 2 : ℝ) + x)
    (hright : (1 / 2 : ℝ) + x ≤ 1) :
    -(1 / 2 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ) := by
  have hleft' :
      -(1 / 2 : ℝ) ≤ x :=
    (neg_le_iff_add_nonneg).2
      (Eq.subst
        (motive := fun y : ℝ => 0 ≤ y)
        (add_comm (1 / 2 : ℝ) x)
        hleft)
  have hright_comm :
      x + (1 / 2 : ℝ) ≤ 1 :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ 1)
      (add_comm (1 / 2 : ℝ) x)
      hright
  have hright_sub :
      x ≤ (1 : ℝ) - (1 / 2 : ℝ) :=
    (le_sub_iff_add_le).2 hright_comm
  have hhalf :
      (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) :=
    sub_half (1 : ℝ)
  have hright' :
      x ≤ (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun y : ℝ => x ≤ y)
      hhalf
      hright_sub
  exact ⟨hleft', hright'⟩

/-- Centered completed-zeta zeros lie in the centered critical strip.

This is the standard unconditional critical-strip theorem for nontrivial zeta
zeros, expressed in the centered completed-zeta normalization used by the
zero-side explicit formula. -/
theorem centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (s : ℂ)
    (hs : centeredCompletedRiemannZeta s = 0) :
    -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ (1 / 2 : ℝ) := by
  have huncentered_zero :
      completedRiemannZeta ((1 / 2 : ℂ) + s) = 0 := by
    exact hs
  have hstrip :
      0 ≤ ((1 / 2 : ℂ) + s).re ∧
        ((1 / 2 : ℂ) + s).re ≤ (1 : ℝ) :=
    completedRiemannZeta_zero_re_mem_criticalStrip
      ((1 / 2 : ℂ) + s)
      huncentered_zero
  have hre :
      ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re :=
    centeredCompletedRiemannZeta_uncenter_re s
  have hleft :
      0 ≤ (1 / 2 : ℝ) + s.re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre
      hstrip.1
  have hright :
      (1 / 2 : ℝ) + s.re ≤ 1 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 : ℝ))
      hre
      hstrip.2
  exact centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    hleft
    hright

end

end LFunctions
end Boundary

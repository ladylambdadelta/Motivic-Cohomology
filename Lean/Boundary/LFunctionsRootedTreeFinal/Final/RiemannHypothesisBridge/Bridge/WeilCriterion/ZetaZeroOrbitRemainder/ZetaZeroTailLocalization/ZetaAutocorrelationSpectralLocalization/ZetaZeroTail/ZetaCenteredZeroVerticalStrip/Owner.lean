import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.CriticalStrip.Owner

/-!
# Centered-zero vertical strip

This file owns the zero-geometry bridge needed to apply Paley-Wiener vertical-strip
decay to evaluations on the completed zero side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The real part of the spectral zero coordinate is the completed-zero real part shifted
by `1/2`. -/
theorem zetaCenteredZero_re_eq_completedZero_re_sub_half
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaCenteredZero (ρ : ℂ)).re = (ρ : ℂ).re - (1 / 2 : ℝ) := by
  calc
    (zetaCenteredZero (ρ : ℂ)).re =
        ((ρ : ℂ) - (1 / 2 : ℂ)).re := by
      rfl
    _ =
        (ρ : ℂ).re - (1 / 2 : ℂ).re := by
      exact Complex.sub_re (ρ : ℂ) (1 / 2 : ℂ)
    _ = (ρ : ℂ).re - (1 / 2 : ℝ) := by
      have hhalf_complex :
          (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
        exact Eq.symm (Complex.ofReal_div (1 : ℝ) (2 : ℝ))
      have hhalf_coe_re :
          (((1 / 2 : ℝ) : ℂ).re) = (1 / 2 : ℝ) :=
        Complex.ofReal_re (1 / 2 : ℝ)
      have hhalf_re : (1 / 2 : ℂ).re = (1 / 2 : ℝ) :=
        Eq.trans
          (congrArg Complex.re hhalf_complex)
          hhalf_coe_re
      exact congrArg (fun x : ℝ => (ρ : ℂ).re - x) hhalf_re

/-- Centered completed zeros lie in the centered critical strip. -/
theorem zetaCompletedZero_re_mem_centeredCriticalStrip
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    -(1 / 2 : ℝ) ≤ (ρ : ℂ).re ∧
      (ρ : ℂ).re ≤ (1 / 2 : ℝ) := by
  exact centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (ρ : ℂ)
    ((centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm.trans
      (zetaCompletedZero_zero ρ))

/-- Completed-zero coordinates lie in one fixed vertical strip.

This is the coarse critical-strip input for completed zeros after the normalizations used by
the zero-side transform. -/
theorem exists_zetaCompletedZero_fixed_vertical_strip :
    ∃ a : ℝ, ∃ b : ℝ,
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ b := by
  exact ⟨-(1 / 2 : ℝ), (1 / 2 : ℝ),
    zetaCompletedZero_re_mem_centeredCriticalStrip⟩

/-- Transport a completed-zero real-part strip through the centering map. -/
theorem zetaCenteredZero_mem_centered_transport_strip
    (a b : ℝ)
    (hstrip :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ b)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    a - (1 / 2 : ℝ) ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
      (zetaCenteredZero (ρ : ℂ)).re ≤ b - (1 / 2 : ℝ) := by
  have hρ : a ≤ (ρ : ℂ).re ∧ (ρ : ℂ).re ≤ b :=
    hstrip ρ
  have hleft : a - (1 / 2 : ℝ) ≤ (ρ : ℂ).re - (1 / 2 : ℝ) :=
    sub_le_sub_right hρ.1 (1 / 2 : ℝ)
  have hright : (ρ : ℂ).re - (1 / 2 : ℝ) ≤ b - (1 / 2 : ℝ) :=
    sub_le_sub_right hρ.2 (1 / 2 : ℝ)
  have hre :
      (zetaCenteredZero (ρ : ℂ)).re = (ρ : ℂ).re - (1 / 2 : ℝ) :=
    zetaCenteredZero_re_eq_completedZero_re_sub_half ρ
  exact
    ⟨Eq.subst
      (motive := fun x : ℝ => a - (1 / 2 : ℝ) ≤ x)
      hre.symm
      hleft,
    Eq.subst
      (motive := fun x : ℝ => x ≤ b - (1 / 2 : ℝ))
      hre.symm
      hright⟩

/-- The centered completed-zero spectral evaluation points lie in one fixed vertical
strip. -/
theorem exists_zetaCenteredZero_fixed_vertical_strip :
    ∃ a : ℝ, ∃ b : ℝ,
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        a ≤ (zetaCenteredZero (ρ : ℂ)).re ∧
          (zetaCenteredZero (ρ : ℂ)).re ≤ b := by
  exact
    match exists_zetaCompletedZero_fixed_vertical_strip with
    | ⟨a, b, hstrip⟩ =>
        ⟨a - (1 / 2 : ℝ), b - (1 / 2 : ℝ),
          fun ρ =>
            zetaCenteredZero_mem_centered_transport_strip a b hstrip ρ⟩

end

end LFunctions
end Boundary

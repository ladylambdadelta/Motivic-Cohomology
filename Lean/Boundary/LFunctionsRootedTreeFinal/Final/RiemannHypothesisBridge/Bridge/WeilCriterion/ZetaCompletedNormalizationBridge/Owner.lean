import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.ZetaCompletedLogDerivativeCore.Owner
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary completed normalization bridge

This file owns the direct factorization bridge between the completed zeta and
the ordinary zeta/Gamma product. It sits below the contour file so the
punctured-plane and contour owner files can consume it without importing the
full Weil-criterion surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The finite zeta-side factor obtained from the completed zeta by removing `Γℝ`. -/
def zetaSideFactor (s : ℂ) : ℂ :=
  completedRiemannZeta s * (Gammaℝ s)⁻¹

/-- The negative logarithmic derivative of the finite zeta-side factor. -/
def zetaSideNegLogDeriv (s : ℂ) : ℂ :=
  - deriv zetaSideFactor s / zetaSideFactor s

theorem zetaSideFactor_eq (s : ℂ) :
    zetaSideFactor s = completedRiemannZeta s * (Gammaℝ s)⁻¹ := by
  rfl

theorem zetaSideFactor_ne_zero {s : ℂ}
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideFactor s ≠ 0 := by
  exact mul_ne_zero hΛ (inv_ne_zero hΓ)

/-- Away from the singular point of the completed normalization, the zeta-side factor is
definitionally the ordinary Riemann zeta quotient. -/
theorem zetaSideFactor_eq_riemannZeta_of_ne_zero {s : ℂ}
    (hs : s ≠ 0) :
    zetaSideFactor s = riemannZeta s := by
  have h :
      riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs
  unfold zetaSideFactor
  exact h.symm

/-- Away from the singular point of the completed normalization, removing the Gamma factor
from the completed zeta recovers the ordinary Riemann zeta function. -/
theorem zetaSideFactor_eq_riemannZeta {s : ℂ}
    (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideFactor s = riemannZeta s := by
  have hcompleted :
      completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs
    exact (div_eq_iff hΓ).mp h.symm
  unfold zetaSideFactor
  calc
    completedRiemannZeta s * (Gammaℝ s)⁻¹ =
        (riemannZeta s * Gammaℝ s) * (Gammaℝ s)⁻¹ := by
      exact congrArg (fun x : ℂ => x * (Gammaℝ s)⁻¹) hcompleted
    _ = riemannZeta s * (Gammaℝ s * (Gammaℝ s)⁻¹) := by
      exact mul_assoc (riemannZeta s) (Gammaℝ s) (Gammaℝ s)⁻¹
    _ = riemannZeta s * 1 := by
      exact congrArg (fun x : ℂ => riemannZeta s * x) (mul_inv_cancel₀ hΓ)
    _ = riemannZeta s := by
      exact mul_one (riemannZeta s)

/-- Nonvanishing of the completed zeta and Gamma factor gives nonvanishing of the ordinary
Riemann zeta factor. -/
theorem riemannZeta_ne_zero_of_completed_ne_zero
    {s : ℂ} (hs : s ≠ 0)
    (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    riemannZeta s ≠ 0 := by
  intro hζ
  have hcompleted :
      completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs
    exact (div_eq_iff hΓ).mp h.symm
  have hzero :
      completedRiemannZeta s = 0 := by
    calc
      completedRiemannZeta s = riemannZeta s * Gammaℝ s := hcompleted
      _ = 0 * Gammaℝ s := by
        exact congrArg (fun x : ℂ => x * Gammaℝ s) hζ
      _ = 0 := by
        exact zero_mul (Gammaℝ s)
  exact hΛ hzero

/-- The zeta-side factor and ordinary Riemann zeta agree in a punctured neighborhood where
the completed normalization is valid. -/
theorem zetaSideFactor_eventually_eq_riemannZeta
    {s : ℂ} (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    ∀ᶠ w in 𝓝 s, zetaSideFactor w = riemannZeta w := by
  filter_upwards [eventually_ne_nhds hs] with w hw
  exact zetaSideFactor_eq_riemannZeta_of_ne_zero hw

/-- The derivative of the zeta-side factor is the derivative of the ordinary Riemann zeta
factor at every point where the completed normalization is valid. -/
theorem deriv_zetaSideFactor_eq_deriv_riemannZeta
    {s : ℂ} (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    deriv zetaSideFactor s = deriv riemannZeta s := by
  exact Filter.EventuallyEq.deriv_eq
    (zetaSideFactor_eventually_eq_riemannZeta hs hΓ)

theorem deriv_zetaSideFactor_at {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hΓ : Gammaℝ s ≠ 0) :
    deriv zetaSideFactor s =
      deriv completedRiemannZeta s * (Gammaℝ s)⁻¹ +
        completedRiemannZeta s * deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s := by
  unfold zetaSideFactor
  exact
    deriv_mul (differentiableAt_completedZeta hs0 hs1)
      differentiable_Gammaℝ_inv.differentiableAt

/-- Removing the Gamma factor adds the explicit archimedean correction to the negative
logarithmic derivative. This inverse-Gamma form is the owner-level statement available from
Mathlib's `Gammaℝ` API; it is equivalent to the usual `+ Γ'/Γ` correction once a direct
`Gammaℝ` differentiability theorem is imported. -/
theorem zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideNegLogDeriv s =
      completedZetaNegLogDeriv s -
        deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
  unfold zetaSideNegLogDeriv completedZetaNegLogDeriv
  rw [deriv_zetaSideFactor_at hs0 hs1 hΓ]
  unfold zetaSideFactor
  field_simp [hΛ, hΓ]
  ring

end ZetaAdmissibleFunction

/-- The completed Riemann zeta factors as `ζ · Γℝ` away from `0`. -/
theorem completedRiemannZeta_eq_riemannZeta_mul_gamma {s : ℂ}
    (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  have h := riemannZeta_def_of_ne_zero hs
  exact (div_eq_iff hΓ).mp h.symm

/-- The ordinary Riemann zeta function is nonzero at the normalization point `0`. -/
theorem riemannZeta_zero_eq_neg_half :
    riemannZeta (0 : ℂ) = (-1 / 2 : ℂ) := by
  exact _root_.riemannZeta_zero

/-- The value `-1/2` is nonzero in the complex normalization. -/
theorem complex_neg_half_ne_zero :
    (-1 / 2 : ℂ) ≠ 0 := by
  norm_num

/-- The ordinary Riemann zeta function is nonzero at the normalization point `0`. -/
theorem riemannZeta_zero_ne_zero :
    riemannZeta (0 : ℂ) ≠ 0 := by
  intro hz
  have hhalf : (-1 / 2 : ℂ) = 0 := by
    exact (riemannZeta_zero_eq_neg_half).symm.trans hz
  exact complex_neg_half_ne_zero hhalf

/-- Mathlib's `Γℝ` zero indexing splits into the normalization point and the negative
nonzero even locus used by the Weil criterion bridge. -/
theorem gammaReal_zeroIndex_iff_zero_or_negative_even
    {s : ℂ} :
    (∃ n : ℕ, s = -(2 * (n : ℂ))) ↔
      s = 0 ∨ ∃ n : ℕ, s = (-2 : ℂ) * ((n + 1 : ℕ) : ℂ) := by
  constructor
  · intro h
    rcases h with ⟨n, hn⟩
    cases n with
    | zero =>
        left
        calc
          s = -(2 * (0 : ℂ)) := hn
          _ = -0 := by
            exact congrArg Neg.neg (mul_zero (2 : ℂ))
          _ = 0 := by
            exact neg_zero
    | succ n =>
        right
        refine ⟨n, ?_⟩
        calc
          s = -(2 * (((n + 1 : ℕ) : ℂ))) := hn
          _ = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := by
            exact neg_mul_eq_neg_mul (2 : ℂ) (((n + 1 : ℕ) : ℂ))
  · intro h
    rcases h with hzero | hnegative
    · refine ⟨0, ?_⟩
      calc
        s = 0 := hzero
        _ = -0 := by
          exact neg_zero.symm
        _ = -(2 * (0 : ℂ)) := by
          exact congrArg Neg.neg (mul_zero (2 : ℂ)).symm
    · rcases hnegative with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      calc
        s = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ)) := hn
        _ = -(2 * (((n + 1 : ℕ) : ℂ))) := by
          exact (neg_mul_eq_neg_mul (2 : ℂ) (((n + 1 : ℕ) : ℂ))).symm

/-- The exact zero locus of the completed Gamma factor in the current normalization. -/
theorem Gammaℝ_eq_zero_iff_zero_or_negative_even
    {s : ℂ} :
    Gammaℝ s = 0 ↔ s = 0 ∨ ∃ n : ℕ, s = -2 * (n + 1) := by
  exact Complex.Gammaℝ_eq_zero_iff.trans gammaReal_zeroIndex_iff_zero_or_negative_even

/-- The completed Gamma factor is nonzero away from its centered nonpositive-even
singular locus. -/
theorem Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    {s : ℂ}
    (hs0 : s ≠ 0)
    (hneg : ¬ ∃ n : ℕ, s = -2 * (n + 1)) :
    Gammaℝ s ≠ 0 := by
  intro hΓ
  have hzero_or_negative :
      s = 0 ∨ ∃ n : ℕ, s = -2 * (n + 1) :=
    (Gammaℝ_eq_zero_iff_zero_or_negative_even).1 hΓ
  rcases hzero_or_negative with hzero | hnegative
  · exact hs0 hzero
  · exact hneg hnegative

/-- A zero of the ordinary Riemann zeta function is a zero of the completed zeta function
away from the normalization singularity, provided the Gamma factor is finite and nonzero. -/
theorem completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero
    {s : ℂ} (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0)
    (hζ : riemannZeta s = 0) :
    completedRiemannZeta s = 0 := by
  have hfactor :
      completedRiemannZeta s = riemannZeta s * Gammaℝ s :=
    completedRiemannZeta_eq_riemannZeta_mul_gamma hs hΓ
  calc
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := hfactor
    _ = 0 * Gammaℝ s := by
      exact congrArg (fun x : ℂ => x * Gammaℝ s) hζ
    _ = 0 := by
      exact zero_mul (Gammaℝ s)

/-- Centered form of forward zero transport from ordinary zeta to completed zeta. -/
theorem centeredCompletedRiemannZeta_eq_zero_of_riemannZeta_eq_zero
    {s : ℂ}
    (hs : (1 / 2 : ℂ) + s ≠ 0)
    (hΓ : Gammaℝ ((1 / 2 : ℂ) + s) ≠ 0)
    (hζ : riemannZeta ((1 / 2 : ℂ) + s) = 0) :
    centeredCompletedRiemannZeta s = 0 := by
  unfold centeredCompletedRiemannZeta
  exact completedRiemannZeta_eq_zero_of_riemannZeta_eq_zero hs hΓ hζ

end
end LFunctions
end Boundary

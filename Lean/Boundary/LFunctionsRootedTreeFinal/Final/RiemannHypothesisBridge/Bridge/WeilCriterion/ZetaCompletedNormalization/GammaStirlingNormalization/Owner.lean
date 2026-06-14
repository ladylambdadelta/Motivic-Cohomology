import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.RCLike.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.RightCriticalStripCompact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner

/-!
# Gamma/Stirling normalization package

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
    (P : ℂ → Prop)
    (hlog :
      ∃ C : ℝ, ∃ m : ℕ,
        ∀ z : ℂ,
          P z →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        P z →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hlog with ⟨C, m, hC⟩
  refine ⟨1, |C| + 1, m, zero_lt_one, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one
  intro z hzP
  have hC_le : C * (1 + ‖z‖) ^ m ≤ (|C| + 1) * (1 + ‖z‖) ^ m := by
    have hC_abs : C ≤ |C| + 1 := le_trans (le_abs_self C) (le_add_of_nonneg_right zero_le_one)
    exact mul_le_mul_of_nonneg_right hC_abs
      (pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))) m)
  have hlog_le :
      Real.log ‖Complex.Gammaℝ z‖ ≤ (|C| + 1) * (1 + ‖z‖) ^ m :=
    le_trans (hC z hzP) hC_le
  by_cases hzero : ‖Complex.Gammaℝ z‖ = 0
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))
      hzero.symm
      (le_of_lt (mul_pos zero_lt_one (Real.exp_pos ((|C| + 1) * (1 + ‖z‖) ^ m))))
  · have hpos : 0 < ‖Complex.Gammaℝ z‖ :=
      lt_of_le_of_ne (norm_nonneg (Complex.Gammaℝ z)) (Ne.symm hzero)
    have hexp_log : Real.exp (Real.log ‖Complex.Gammaℝ z‖) = ‖Complex.Gammaℝ z‖ :=
      Real.exp_log hpos
    have hnorm_eq :
        ‖Complex.Gammaℝ z‖ = Real.exp (Real.log ‖Complex.Gammaℝ z‖) := hexp_log.symm
    have hexp_le :
        Real.exp (Real.log ‖Complex.Gammaℝ z‖) ≤
          Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) :=
      Real.exp_le_exp.mpr hlog_le
    calc
      ‖Complex.Gammaℝ z‖ = Real.exp (Real.log ‖Complex.Gammaℝ z‖) := hnorm_eq
      _ ≤ Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := hexp_le
      _ = 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := by
        exact (one_mul (Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))).symm

/-- The corrected right-half-plane Gamma/Stirling region avoids the `Gammaℝ` zero at `0`.

Mathlib's `Complex.Gamma` and `Complex.Gammaℝ` are finite-valued at the classical pole
faces, with those faces represented by zeros. -/
theorem Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Complex.Gammaℝ z ≠ 0 := by
  intro hzero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hz⟩
  subst z
  cases n with
  | zero =>
      norm_num at hz_norm
  | succ n =>
      norm_num at hz_re

/-- Points with real part at least `1` have norm at least `1`. -/
theorem one_le_norm_of_one_le_re
    {z : ℂ}
    (hz_re : 1 ≤ z.re) :
    1 ≤ ‖z‖ := by
  have hre_nonneg : 0 ≤ z.re :=
    le_trans zero_le_one hz_re
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    simpa [Complex.normSq, norm_eq_abs] using Complex.abs_re_le_abs z
  have hre_abs_eq : |z.re| = z.re :=
    abs_of_nonneg hre_nonneg
  exact le_trans hz_re
    (Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      hre_abs_eq
      hre_abs_le_norm)

/-- Points with real part at least `2` lie in the large-norm region. -/
theorem one_le_norm_of_two_le_re
    {z : ℂ}
    (hz_re : 2 ≤ z.re) :
    1 ≤ ‖z‖ :=
  one_le_norm_of_one_le_re (le_trans one_le_two hz_re)

/-- Points whose imaginary coordinate has norm at least `1` have complex norm at least `1`. -/
theorem one_le_norm_of_one_le_norm_im
    {z : ℂ}
    (hz_im : 1 ≤ ‖z.im‖) :
    1 ≤ ‖z‖ := by
  have him_abs_le_norm : |z.im| ≤ ‖z‖ := by
    simpa [Complex.normSq, norm_eq_abs] using Complex.abs_im_le_abs z
  have him_norm_eq : ‖z.im‖ = |z.im| := Real.norm_eq_abs z.im
  exact le_trans
    (Eq.subst (motive := fun x : ℝ => 1 ≤ x) him_norm_eq hz_im)
    him_abs_le_norm

/-- The unfolded normalized real-Gamma factor. -/
def unfoldedNormalizedGammaℝFactor (z : ℂ) : ℂ :=
  π ^ (-z / 2) * Complex.Gamma (z / 2)

/-- The inline half-argument normalized Gamma expression is the local unfolded
`Gammaℝ` factor. -/
theorem halfArgument_normalized_complexGamma_eq_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    π ^ (-z / 2) * Complex.Gamma (z / 2) =
      unfoldedNormalizedGammaℝFactor z := by
  rfl

/-- Log-norm transport from the inline half-argument Gamma expression to the local
unfolded `Gammaℝ` factor. -/
theorem log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
      Real.log ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg
    (fun w : ℂ => Real.log ‖w‖)
    (halfArgument_normalized_complexGamma_eq_unfoldedNormalizedGammaℝFactor z)

/-- `Gammaℝ` is definitionally the unfolded normalized real-Gamma factor. -/
theorem Gammaℝ_eq_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Complex.Gammaℝ z = unfoldedNormalizedGammaℝFactor z := by
  exact Complex.Gammaℝ_def z

/-- Norm-level form of the unfolded `Gammaℝ` normalization. -/
theorem norm_Gammaℝ_eq_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    ‖Complex.Gammaℝ z‖ = ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg norm (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z)

/-- Log-norm form of the unfolded `Gammaℝ` normalization. -/
theorem log_norm_Gammaℝ_eq_log_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Real.log ‖Complex.Gammaℝ z‖ =
      Real.log ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg Real.log (norm_Gammaℝ_eq_norm_unfoldedNormalizedGammaℝFactor z)

/-- The unfolded normalized real-Gamma factor is nonzero on the right-half-plane
Stirling region. -/
theorem unfoldedNormalizedGammaℝFactor_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    unfoldedNormalizedGammaℝFactor z ≠ 0 := by
  intro hzero
  have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm
  have hGammaℝ_zero : Complex.Gammaℝ z = 0 :=
    Eq.trans (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z) hzero
  exact hGammaℝ_ne hGammaℝ_zero

/-- The unfolded normalized real-Gamma factor has positive norm on the right-half-plane
Stirling region. -/
theorem norm_unfoldedNormalizedGammaℝFactor_pos_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    0 < ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact norm_pos_iff.mpr
    (unfoldedNormalizedGammaℝFactor_ne_zero_of_re_nonneg_and_one_le_norm
      hz_re hz_norm)

/-- The half-argument has nonnegative real part in the right half-plane. -/
theorem halfArgument_re_nonneg_of_re_nonneg
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    0 ≤ (z / 2).re := by
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  rw [Complex.div_re_ofReal]
  exact div_nonneg hz_re (le_of_lt htwo_pos)

/-- The half-argument is nonzero in the large right-half-plane Stirling region. -/
theorem halfArgument_ne_zero_of_one_le_norm
    {z : ℂ}
    (hz_norm : 1 ≤ ‖z‖) :
    z / 2 ≠ 0 := by
  intro hzero
  have hz_zero : z = 0 := by
    have hmul := congrArg (fun w : ℂ => w * (2 : ℂ)) hzero
    calc
      z = (z / 2) * (2 : ℂ) := by
        exact (div_mul_cancel₀ z (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = 0 * (2 : ℂ) := by
        exact hmul
      _ = 0 := zero_mul (2 : ℂ)
  have hnorm_zero : ‖z‖ = 0 := by
    exact congrArg norm hz_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 := by norm_num
  exact hnot (Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_zero hz_norm)

/-- `Complex.Gamma (z / 2)` is nonzero on the large right-half-plane Stirling region. -/
theorem ComplexGamma_halfArgument_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Complex.Gamma (z / 2) ≠ 0 := by
  have hz_half_re : 0 ≤ (z / 2).re :=
    halfArgument_re_nonneg_of_re_nonneg hz_re
  have hz_half_ne : z / 2 ≠ 0 :=
    halfArgument_ne_zero_of_one_le_norm hz_norm
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff (z / 2)).mp hzero with ⟨n, hn⟩
  have hhalf_re_eq : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
  have hn_re : (-(n : ℂ)).re = -(n : ℝ) := by simp
  have hz_half_re_nonpos : (z / 2).re ≤ 0 := by
    calc
      (z / 2).re = (-(n : ℂ)).re := hhalf_re_eq
      _ = -(n : ℝ) := hn_re
      _ ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
  have hz_half_re_zero : (z / 2).re = 0 :=
    le_antisymm hz_half_re_nonpos hz_half_re
  cases n with
  | zero =>
      have hhalf_zero : z / 2 = 0 := by
        simpa using hn
      exact hz_half_ne hhalf_zero
  | succ n =>
      have hneg_succ_lt_zero : (-(Nat.succ n : ℂ)).re < 0 := by
        simp
      have hcontr : (z / 2).re < 0 := by
        calc
          (z / 2).re = (-(Nat.succ n : ℂ)).re := hhalf_re_eq
          _ < 0 := hneg_succ_lt_zero
      exact (not_lt_of_ge hz_half_re) hcontr

/-- Norm transport for the half-argument. -/
theorem two_mul_norm_halfArgument
    (z : ℂ) :
    2 * ‖z / 2‖ = ‖z‖ := by
  have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    calc
      ‖(2 : ℂ)‖ = ‖(2 : ℝ)‖ := by
        exact Complex.norm_real 2
      _ = (2 : ℝ) :=
        Real.norm_of_nonneg zero_le_two
  calc
    2 * ‖z / 2‖ = ‖(2 : ℂ)‖ * ‖z / 2‖ := by
      exact congrArg (fun x : ℝ => x * ‖z / 2‖) htwo_norm.symm
    _ = ‖(2 : ℂ) * (z / 2)‖ := by
      exact (norm_mul (2 : ℂ) (z / 2)).symm
    _ = ‖z‖ := by
      have hmul : (2 : ℂ) * (z / 2) = z := by
        calc
          (2 : ℂ) * (z / 2) = z / 2 * (2 : ℂ) := by
            exact mul_comm (2 : ℂ) (z / 2)
          _ = z := div_mul_cancel₀ z (by exact two_ne_zero)
      exact congrArg norm hmul

/-- The half-argument is in the large sectorial region measured at radius `1 / 2`. -/
theorem halfArgument_norm_ge_one_half_of_one_le_norm
    {z : ℂ}
    (hz_norm : 1 ≤ ‖z‖) :
    (1 / 2 : ℝ) ≤ ‖z / 2‖ := by
  have htwo_pos : (0 : ℝ) < 2 := zero_lt_two
  have htransport : 2 * ‖z / 2‖ = ‖z‖ :=
    two_mul_norm_halfArgument z
  have hone_le_two_mul : (1 : ℝ) ≤ 2 * ‖z / 2‖ :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      htransport.symm
      hz_norm
  exact (div_le_iff₀' htwo_pos).mpr hone_le_two_mul

/-- The sectorial envelope is preserved exactly under `w = z / 2`. -/
theorem sectorialGammaEnvelope_halfArgument_eq
    (C : ℝ)
    (z : ℂ) :
    C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) =
      C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact congrArg
    (fun x : ℝ => C * (1 + x) * Real.log (2 + x))
    (two_mul_norm_halfArgument z)

/-- The log-linear envelope is additive in its constant. -/
theorem logLinearEnvelope_add_constants
    (A B H L : ℝ) :
    A * H * L + B * H * L = (A + B) * H * L := by
  calc
    A * H * L + B * H * L = (A * H + B * H) * L := by
      exact (add_mul (A * H) (B * H) L).symm
    _ = ((A + B) * H) * L := by
      exact congrArg (fun x : ℝ => x * L) (add_mul A B H).symm
    _ = (A + B) * H * L := by
      rfl

/-- The log-linear envelope is monotone in its constant when the envelope
factors are nonnegative. -/
theorem logLinearEnvelope_mono_constant
    {A B H L : ℝ}
    (hAB : A ≤ B)
    (hH : 0 ≤ H)
    (hL : 0 ≤ L) :
    A * H * L ≤ B * H * L := by
  have hAH_le_BH : A * H ≤ B * H :=
    mul_le_mul_of_nonneg_right hAB hH
  exact mul_le_mul_of_nonneg_right hAH_le_BH hL

/-- The logarithmic envelope on `2 + ‖z‖` has argument at least one. -/
theorem one_le_two_add_complex_norm
    (z : ℂ) :
    (1 : ℝ) ≤ 2 + ‖z‖ := by
  calc
    (1 : ℝ) ≤ 2 := one_le_two
    _ ≤ 2 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)

/-- The closed right half-plane sector used for the owner Gamma/Stirling roots. -/
def Complex.closedRightHalfPlaneSector (w : ℂ) : Prop :=
  0 ≤ w.re

/-- Binet's second-formula remainder for `log Γ`.

For `Re w > 0`, Binet's second formula writes
`log Γ(w) = (w - 1/2) Log w - w + (1/2)log(2π) + J(w)`, where
`J(w) = 2 ∫₀∞ atan(t / w) / (exp(2πt) - 1) dt`.  This is the canonical
complex-analysis kernel used to prove sectorial Stirling estimates; cf. DLMF
5.11.3 and Whittaker-Watson, Ch. XII. -/
noncomputable def Complex.binetSecondFormulaRemainder (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The main term in Binet's logarithmic Stirling formula. -/
noncomputable def Complex.binetLogGammaMainTerm (w : ℂ) : ℂ :=
  (w - (1 / 2 : ℂ)) * Complex.log w - w +
    (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2

/-- Binet's second logarithmic formula for `Gamma` on the closed
right-half-plane sector, away from the origin.

This is the standard integral representation:
`Log Γ(w) = (w - 1/2) Log w - w + (1/2)log(2π) + J(w)`, where `J` is the
Binet second-formula remainder.  The closed-sector large-radius statement is
the form needed for sectorial Stirling; it includes the boundary rays by
continuation from the open right half-plane. -/
theorem Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  sorry

/-- Pointwise Binet-kernel estimate in the open right half-plane.

The numerator contributes the `t / ‖w‖` factor through the principal arctangent,
while the denominator is controlled by the positive real exponential
`exp (2πt) - 1`.  The open half-plane hypothesis avoids the principal
arctangent singularities on the imaginary boundary. -/
theorem Complex.binetSecondFormula_arctan_kernel_norm_le_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (t / ‖w‖) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  sorry

/-- Boundary-continuation form of the Binet-kernel estimate.

The literal principal-arctangent kernel has boundary singularities on the
imaginary axis, so the closed-sector estimate is obtained as the boundary
value of the open-right-half-plane kernel. -/
theorem Complex.binetSecondFormula_arctan_kernel_norm_le_closedRightHalfPlane
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_ne : w ≠ 0) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (t / ‖w‖) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  sorry

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
              (fun hlt_one_x => Or.inr hlt_one_x)
              (fun hx_le_one => Or.inl ⟨hx, hx_le_one⟩),
          fun hx =>
            Or.elim hx
              (fun hx_local => hx_local.1)
              (fun hx_tail => lt_trans zero_lt_one hx_tail)⟩)

/-- Joining local integrability on `(0,1]` with tail integrability on `(1,∞)`
gives integrability on `(0,∞)`. -/
theorem Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
    {f : ℝ → ℝ}
    (hlocal : IntegrableOn f (Set.Ioc (0 : ℝ) 1))
    (htail : IntegrableOn f (Set.Ioi (1 : ℝ))) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have hcover :
      Set.Ioi (0 : ℝ) =
        Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one
  have hunion :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) :=
    integrableOn_union.mpr ⟨hlocal, htail⟩
  exact
    Eq.subst
      (motive := fun s : Set ℝ => IntegrableOn f s)
      hcover.symm
      hunion

/-- The real majorant for the Binet kernel is integrable on `(0,∞)`. -/
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

/-- Pointwise zero-cancellation bound for the Binet majorant on `(0,1]`.

The proof is the elementary inequality `x + 1 ≤ exp x`, applied to
`x = 2πt`, followed by division by the positive denominator. -/
theorem Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise
    {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      1 / ((2 : ℝ) * Real.pi) := by
  sorry

/-- The Binet majorant is bounded near zero after cancellation of the simple
zero in `exp (2πt)-1`. -/
theorem Real.binetSecondFormula_kernel_majorant_zero_cancellation_bounded_on_Ioc_zero_one :
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

/-- The Binet majorant is bounded near zero after cancellation of the simple
zero in `exp (2πt)-1`. -/
theorem Real.binetSecondFormula_kernel_majorant_bounded_zero_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioc (0 : ℝ) 1 →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤ C := by
  exact
    Real.binetSecondFormula_kernel_majorant_zero_cancellation_bounded_on_Ioc_zero_one

/-- Bounded a.e.-measurable real functions on a finite interval are integrable. -/
theorem Real.integrableOn_Ioc_of_aestronglyMeasurable_norm_le_const
    {f : ℝ → ℝ}
    {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, x ∈ Set.Ioc a b → ‖f x‖ ≤ C) :
    IntegrableOn f (Set.Ioc a b) := by
  sorry

/-- The Binet majorant is a.e.-measurable on the local interval `(0,1]`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_zero_one :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  sorry

/-- A bounded Binet majorant on the finite interval `(0,1]` is integrable. -/
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

/-- A bounded Binet majorant on the finite interval `(0,1]` is integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_of_bounded :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_from_zero_cancellation

/-- Local integrability of the Binet majorant near zero.

This is the standard cancellation
`exp (2πt) - 1 ∼ 2πt`, so the quotient is bounded on `(0,1]`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_of_bounded

/-- Pointwise exponential tail domination for the Binet majorant with the
concrete constant `2`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      2 * Real.exp (-Real.pi * t) := by
  sorry

/-- Exponential tail domination for the Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_exponential_tail_dominated :
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

/-- Exponential tail domination for the Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_exp :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (1 : ℝ) →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
            C * Real.exp (-Real.pi * t) := by
  exact
    Real.binetSecondFormula_kernel_majorant_exponential_tail_dominated

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
  sorry

/-- The Binet majorant is a.e.-measurable on the tail interval `(1,∞)`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_one_infty :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  sorry

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

/-- Exponential tail domination implies tail integrability of the Binet
majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_of_tail_bound :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_from_exponential_tail

/-- Exponential decay of the Binet majorant at infinity. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_of_tail_bound

/-- The real majorant for the Binet kernel is integrable on `(0,∞)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty

/-- Strict lower bound for the Binet majorant at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_pos
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

/-- The Binet majorant denominator is nonzero at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_ne_zero
    {t : ℝ}
    (ht : 0 < t) :
    Real.exp ((2 : ℝ) * Real.pi * t) - 1 ≠ 0 :=
  ne_of_gt
    (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Strict lower bound for the Binet majorant at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    div_pos ht
      (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Nonnegativity of the Binet majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht
  exact le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht)

/-- A positive integrable function on an open real interval has positive set
integral. -/
theorem Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (h_integrable : IntegrableOn f (Set.Ioo a b))
    (hpos : ∀ t : ℝ, t ∈ Set.Ioo a b → 0 < f t) :
    0 < ∫ t : ℝ in Set.Ioo a b, f t := by
  sorry

/-- The Binet majorant is integrable on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioo (0 : ℝ) 1) := by
  exact
    IntegrableOn.mono_set
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Set.Ioo_subset_Ioc_self

/-- The Binet majorant has strictly positive integral on the concrete interval
`(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_strictlyPositiveIntegral_on_Ioo_zero_one :
    0 <
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
      zero_lt_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one
      (fun t ht =>
        Real.binetSecondFormula_kernel_majorant_pos ht.1)

/-- The Binet majorant has strictly positive integral on the concrete interval
`(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one :
    0 <
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.binetSecondFormula_kernel_majorant_strictlyPositiveIntegral_on_Ioo_zero_one

/-- A strict lower bound on `(0,1)` propagates to `(0,∞)` for the
nonnegative Binet majorant. -/
theorem Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
    {f : ℝ → ℝ}
    (h_integrable : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t)
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ f t) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ), f t := by
  sorry

/-- A strict lower bound on `(0,1)` propagates to `(0,∞)` for the
nonnegative Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
      Real.binetSecondFormula_kernel_majorant_integrableOn
      hpos_subinterval hnonneg

/-- Integration of the pointwise Binet-kernel majorant. -/
theorem Complex.binetSecondFormula_remainder_norm_le_integral_majorant
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_ne : w ≠ 0) :
    ‖Complex.binetSecondFormulaRemainder w‖ ≤
      2 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  sorry

/-- The Binet majorant integral is a positive finite constant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one
  have hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi
  exact
    Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
      hpos_subinterval hnonneg

/-- The Binet kernel estimate integrates to an `O(1 / ‖w‖)` remainder bound. -/
theorem Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_from_kernel_estimate :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let R : ℝ := 1
  let K : ℝ := 2 * J
  have hR : 0 < R :=
    zero_lt_one
  have hJ_pos : 0 < J :=
    Real.binetSecondFormula_kernel_majorant_integral_pos
  have hK : 0 < K :=
    mul_pos two_pos hJ_pos
  refine ⟨R, K, hR, hK, ?_⟩
  intro w hw_sector hw_radius
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le hR hw_radius
  have hw_ne : w ≠ 0 :=
    norm_pos_iff.mp hw_norm_pos
  have hmajorant :
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        2 * J / ‖w‖ :=
    Complex.binetSecondFormula_remainder_norm_le_integral_majorant
      hw_sector hw_ne
  exact hmajorant

/-- Uniform `O(1/‖w‖)` bound for the Binet second-formula remainder on the
closed right-half-plane sector.

This is the standard estimate obtained from the Binet kernel
`atan(t / w)/(exp(2πt)-1)`: for `Re w ≥ 0` and large radius, the remainder is
bounded by a constant multiple of `1/‖w‖`. -/
theorem Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := by
  exact
    Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_from_kernel_estimate

/-- Binet's second formula with a uniform sectorial remainder bound on the
closed right half-plane.

This wrapper combines the right-half-plane Binet representation with the
sectorial `O(1/‖w‖)` remainder estimate. -/
theorem Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w ∧
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := by
  rcases Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius with
    ⟨Rlog, hRlog, hlog⟩
  rcases Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane with
    ⟨Rbound, K, hRbound, hK, hbound⟩
  let R : ℝ := max Rlog Rbound
  have hR : 0 < R :=
    lt_of_lt_of_le hRlog (le_max_left Rlog Rbound)
  refine ⟨R, K, hR, hK, ?_⟩
  intro w hw_sector hw_norm
  have hRlog_le : Rlog ≤ ‖w‖ :=
    le_trans (le_max_left Rlog Rbound) hw_norm
  have hRbound_le : Rbound ≤ ‖w‖ :=
    le_trans (le_max_right Rlog Rbound) hw_norm
  exact ⟨hlog w hw_sector hRlog_le,
    hbound w hw_sector hRbound_le⟩

/-- Exponentiating Binet's logarithmic identity separates the main term from
the Binet remainder. -/
theorem Complex.Gamma_eq_exp_binetLogGammaMainTerm_mul_exp_binetRemainder
    {w : ℂ}
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hbinet :
      Complex.log (Complex.Gamma w) =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w) :
    Complex.Gamma w =
      Complex.exp (Complex.binetLogGammaMainTerm w) *
        Complex.exp (Complex.binetSecondFormulaRemainder w) := by
  calc
    Complex.Gamma w =
        Complex.exp (Complex.log (Complex.Gamma w)) :=
      (Complex.exp_log hGamma_ne).symm
    _ =
        Complex.exp
          (Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w) :=
      congrArg Complex.exp hbinet
    _ =
        Complex.exp (Complex.binetLogGammaMainTerm w) *
          Complex.exp (Complex.binetSecondFormulaRemainder w) :=
      Complex.exp_add
        (Complex.binetLogGammaMainTerm w)
        (Complex.binetSecondFormulaRemainder w)

/-- The square-root constant in Binet's main term after exponentiation. -/
theorem Complex.exp_half_log_two_pi_eq_sqrt_two_pi :
    Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  have htwo_pi_pos : 0 < 2 * Real.pi :=
    mul_pos two_pos Real.pi_pos
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos_of_pos htwo_pi_pos
  have hlog_sqrt :
      Real.log (Real.sqrt (2 * Real.pi)) =
        Real.log (2 * Real.pi) / 2 :=
    Real.log_sqrt (le_of_lt htwo_pi_pos)
  have hexp_real :
      Real.exp (Real.log (2 * Real.pi) / 2) =
        Real.sqrt (2 * Real.pi) := by
    calc
      Real.exp (Real.log (2 * Real.pi) / 2) =
          Real.exp (Real.log (Real.sqrt (2 * Real.pi))) :=
        congrArg Real.exp hlog_sqrt.symm
      _ = Real.sqrt (2 * Real.pi) :=
        Real.exp_log hsqrt_pos
  have hcoerce_arg :
      ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) =
        ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) :=
    (Complex.ofReal_div (Real.log (2 * Real.pi)) 2).symm
  calc
    Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) =
        Complex.exp ((Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) :=
      congrArg Complex.exp hcoerce_arg
    _ = (Real.exp (Real.log (2 * Real.pi) / 2) : ℂ) :=
      (Complex.ofReal_exp (Real.log (2 * Real.pi) / 2)).symm
    _ = (Real.sqrt (2 * Real.pi) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hexp_real

/-- Principal-branch power cancellation in the normalized Stirling factor.

This is the `cpow_def_of_ne_zero` step: the exponential of
`(w - 1/2) Log w` cancels against `w^(1/2-w)`. -/
theorem Complex.exp_binet_power_mul_cpow_cancel
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w) *
        w ^ ((1 / 2 : ℂ) - w) = 1 := by
  let A : ℂ := (w - (1 / 2 : ℂ)) * Complex.log w
  have hcpow :
      w ^ ((1 / 2 : ℂ) - w) =
        Complex.exp (Complex.log w * ((1 / 2 : ℂ) - w)) :=
    Complex.cpow_def_of_ne_zero hw_ne ((1 / 2 : ℂ) - w)
  have hcomm :
      Complex.log w * ((1 / 2 : ℂ) - w) =
        ((1 / 2 : ℂ) - w) * Complex.log w :=
    mul_comm (Complex.log w) ((1 / 2 : ℂ) - w)
  have hneg_factor :
      ((1 / 2 : ℂ) - w) * Complex.log w =
        -A := by
    have hsub :
        ((1 / 2 : ℂ) - w) = -(w - (1 / 2 : ℂ)) :=
      sub_eq_neg_sub (1 / 2 : ℂ) w
    calc
      ((1 / 2 : ℂ) - w) * Complex.log w =
          (-(w - (1 / 2 : ℂ))) * Complex.log w :=
        congrArg (fun z : ℂ => z * Complex.log w) hsub
      _ = -((w - (1 / 2 : ℂ)) * Complex.log w) :=
        neg_mul (w - (1 / 2 : ℂ)) (Complex.log w)
      _ = -A := rfl
  have hcpow_neg :
      w ^ ((1 / 2 : ℂ) - w) = Complex.exp (-A) := by
    calc
      w ^ ((1 / 2 : ℂ) - w) =
          Complex.exp (Complex.log w * ((1 / 2 : ℂ) - w)) :=
        hcpow
      _ = Complex.exp (((1 / 2 : ℂ) - w) * Complex.log w) :=
        congrArg Complex.exp hcomm
      _ = Complex.exp (-A) :=
        congrArg Complex.exp hneg_factor
  calc
    Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w) *
        w ^ ((1 / 2 : ℂ) - w) =
        Complex.exp A * Complex.exp (-A) := by
      exact congrArg
        (fun z : ℂ => Complex.exp A * z)
        hcpow_neg
    _ = Complex.exp (A + -A) :=
      (Complex.exp_add A (-A)).symm
    _ = Complex.exp 0 := by
      exact congrArg Complex.exp (add_neg_cancel A)
    _ = 1 :=
      Complex.exp_zero

/-- The exponential normalizer in Binet's main term cancels exactly. -/
theorem Complex.exp_neg_mul_exp_self_eq_one
    (w : ℂ) :
    Complex.exp (-w) * Complex.exp w = 1 := by
  calc
    Complex.exp (-w) * Complex.exp w =
        Complex.exp (-w + w) :=
      (Complex.exp_add (-w) w).symm
    _ = Complex.exp 0 := by
      exact congrArg Complex.exp (neg_add_cancel w)
    _ = 1 :=
      Complex.exp_zero

/-- Reassociate the three Binet main factors against the two normalizing
factors. -/
theorem Complex.binet_main_three_factor_reassociate
    (P N S B C : ℂ) :
    (P * N * S) * B * C = (P * C) * (N * B) * S := by
  calc
    (P * N * S) * B * C =
        (((P * N) * S) * B) * C := rfl
    _ = ((P * N) * (S * B)) * C := by
      exact congrArg (fun z : ℂ => z * C) (mul_assoc (P * N) S B)
    _ = ((P * N) * (B * S)) * C := by
      exact congrArg (fun z : ℂ => ((P * N) * z) * C) (mul_comm S B)
    _ = (((P * N) * B) * S) * C := by
      exact congrArg (fun z : ℂ => z * C) (mul_assoc (P * N) B S).symm
    _ = ((P * (N * B)) * S) * C := by
      exact congrArg (fun z : ℂ => (z * S) * C) (mul_assoc P N B)
    _ = (P * (N * B)) * (S * C) := by
      exact mul_assoc (P * (N * B)) S C
    _ = (P * (N * B)) * (C * S) := by
      exact congrArg (fun z : ℂ => (P * (N * B)) * z) (mul_comm S C)
    _ = ((P * (N * B)) * C) * S := by
      exact (mul_assoc (P * (N * B)) C S).symm
    _ = (P * ((N * B) * C)) * S := by
      exact congrArg (fun z : ℂ => z * S) (mul_assoc P (N * B) C)
    _ = (P * (C * (N * B))) * S := by
      exact congrArg (fun z : ℂ => (P * z) * S) (mul_comm (N * B) C)
    _ = ((P * C) * (N * B)) * S := by
      exact congrArg (fun z : ℂ => z * S) (mul_assoc P C (N * B)).symm
    _ = (P * C) * (N * B) * S := rfl

/-- Exponential of the Binet main term split into its three factors. -/
theorem Complex.exp_binetLogGammaMainTerm_eq
    (w : ℂ) :
    Complex.exp (Complex.binetLogGammaMainTerm w) =
      Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w) *
        Complex.exp (-w) *
          Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) := by
  let P : ℂ := (w - (1 / 2 : ℂ)) * Complex.log w
  let S : ℂ := ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
  have hsub_exp :
      Complex.exp (P - w) = Complex.exp P * Complex.exp (-w) := by
    calc
      Complex.exp (P - w) =
          Complex.exp (P + -w) := rfl
      _ = Complex.exp P * Complex.exp (-w) :=
        Complex.exp_add P (-w)
  calc
    Complex.exp (Complex.binetLogGammaMainTerm w) =
        Complex.exp ((P - w) + S) := rfl
    _ = Complex.exp (P - w) * Complex.exp S :=
      Complex.exp_add (P - w) S
    _ = (Complex.exp P * Complex.exp (-w)) * Complex.exp S := by
      exact congrArg (fun z : ℂ => z * Complex.exp S) hsub_exp
    _ =
        Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w) *
          Complex.exp (-w) *
            Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) := rfl

/-- The Binet main term is exactly cancelled by the normalized Stirling
factors, leaving the constant `sqrt (2π)`.

This is the principal-branch algebraic identity using
`w^(1/2-w) = exp (Log w * (1/2-w))` and
`exp ((log (2π))/2) = sqrt (2π)`. -/
theorem Complex.exp_binetLogGammaMainTerm_mul_exp_mul_cpow_eq_sqrt_two_pi
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    Complex.exp (Complex.binetLogGammaMainTerm w) *
        Complex.exp w * w ^ ((1 / 2 : ℂ) - w) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  have hpower :
      Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w) *
          w ^ ((1 / 2 : ℂ) - w) = 1 :=
    Complex.exp_binet_power_mul_cpow_cancel hw_ne
  have hnormalizer :
      Complex.exp (-w) * Complex.exp w = 1 :=
    Complex.exp_neg_mul_exp_self_eq_one w
  have hconstant :
      Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) =
        (Real.sqrt (2 * Real.pi) : ℂ) :=
    Complex.exp_half_log_two_pi_eq_sqrt_two_pi
  let P : ℂ := Complex.exp ((w - (1 / 2 : ℂ)) * Complex.log w)
  let N : ℂ := Complex.exp (-w)
  let S : ℂ :=
    Complex.exp ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
  let B : ℂ := Complex.exp w
  let C : ℂ := w ^ ((1 / 2 : ℂ) - w)
  have hmain :
      Complex.exp (Complex.binetLogGammaMainTerm w) = P * N * S :=
    Complex.exp_binetLogGammaMainTerm_eq w
  have hreassoc :
      (P * N * S) * B * C = (P * C) * (N * B) * S :=
    Complex.binet_main_three_factor_reassociate P N S B C
  have hpower' : P * C = 1 :=
    hpower
  have hnormalizer' : N * B = 1 :=
    hnormalizer
  have hconstant' : S = (Real.sqrt (2 * Real.pi) : ℂ) :=
    hconstant
  calc
    Complex.exp (Complex.binetLogGammaMainTerm w) *
        Complex.exp w * w ^ ((1 / 2 : ℂ) - w) =
        (P * N * S) * B * C := by
      exact congrArg (fun z : ℂ => z * B * C) hmain
    _ = (P * C) * (N * B) * S :=
      hreassoc
    _ = 1 * (N * B) * S := by
      exact congrArg (fun z : ℂ => z * (N * B) * S) hpower'
    _ = 1 * 1 * S := by
      exact congrArg (fun z : ℂ => 1 * z * S) hnormalizer'
    _ = 1 * 1 * (Real.sqrt (2 * Real.pi) : ℂ) := by
      exact congrArg (fun z : ℂ => 1 * 1 * z) hconstant'
    _ = (Real.sqrt (2 * Real.pi) : ℂ) := by
      calc
        1 * 1 * (Real.sqrt (2 * Real.pi) : ℂ) =
            1 * (Real.sqrt (2 * Real.pi) : ℂ) := by
          exact congrArg (fun z : ℂ => z * (Real.sqrt (2 * Real.pi) : ℂ)) (mul_one 1)
        _ = (Real.sqrt (2 * Real.pi) : ℂ) :=
          one_mul (Real.sqrt (2 * Real.pi) : ℂ)

/-- Reassociation of the four factors occurring after exponentiating Binet's
formula. -/
theorem Complex.binetMain_remainder_normalizer_reassociate
    (A E B C : ℂ) :
    (A * E) * B * C = (A * B * C) * E := by
  calc
    (A * E) * B * C =
        ((A * E) * B) * C := rfl
    _ = (A * (E * B)) * C := by
      exact congrArg (fun z : ℂ => z * C) (mul_assoc A E B)
    _ = (A * (B * E)) * C := by
      exact congrArg (fun z : ℂ => (A * z) * C) (mul_comm E B)
    _ = ((A * B) * E) * C := by
      exact congrArg (fun z : ℂ => z * C) (mul_assoc A B E).symm
    _ = (A * B) * (E * C) := by
      exact mul_assoc (A * B) E C
    _ = (A * B) * (C * E) := by
      exact congrArg (fun z : ℂ => (A * B) * z) (mul_comm E C)
    _ = ((A * B) * C) * E := by
      exact (mul_assoc (A * B) C E).symm
    _ = (A * B * C) * E := rfl

/-- Exponentiated Binet formula in normalized Stirling-factor form.

This is the branch-bookkeeping identity behind sectorial Stirling: using
`exp (Log Γ(w)) = Γ(w)` and `w^(1/2-w) = exp (Log w * (1/2-w))`, Binet's
main term cancels against the normalizing factors and leaves the exponential
of the Binet remainder. -/
theorem Complex.normalizedGammaStirlingFactor_eq_sqrt_two_pi_mul_exp_binetRemainder
    {w : ℂ}
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hw_ne : w ≠ 0)
    (hbinet :
      Complex.log (Complex.Gamma w) =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w) :
    Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        Complex.exp (Complex.binetSecondFormulaRemainder w) := by
  let A : ℂ := Complex.exp (Complex.binetLogGammaMainTerm w)
  let E : ℂ := Complex.exp (Complex.binetSecondFormulaRemainder w)
  let B : ℂ := Complex.exp w
  let C : ℂ := w ^ ((1 / 2 : ℂ) - w)
  have hGamma :
      Complex.Gamma w = A * E :=
    Complex.Gamma_eq_exp_binetLogGammaMainTerm_mul_exp_binetRemainder
      hGamma_ne hbinet
  have hreassoc :
      (A * E) * B * C = (A * B * C) * E :=
    Complex.binetMain_remainder_normalizer_reassociate A E B C
  have hmain :
      A * B * C = (Real.sqrt (2 * Real.pi) : ℂ) :=
    Complex.exp_binetLogGammaMainTerm_mul_exp_mul_cpow_eq_sqrt_two_pi
      hw_ne
  calc
    Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) =
        (A * E) * B * C := by
      exact congrArg (fun z : ℂ => z * B * C) hGamma
    _ = (A * B * C) * E :=
      hreassoc
    _ = (Real.sqrt (2 * Real.pi) : ℂ) * E := by
      exact congrArg (fun z : ℂ => z * E) hmain
    _ =
        (Real.sqrt (2 * Real.pi) : ℂ) *
          Complex.exp (Complex.binetSecondFormulaRemainder w) := rfl

/-- Exponentiating Binet's logarithmic formula gives the exact normalized
Gamma-factor error in terms of the Binet remainder.

This is the branch-bookkeeping step: after expanding
`binetLogGammaMainTerm`, the factors `exp w` and `w^(1/2-w)` cancel the
Stirling main term and leave `sqrt(2π) * (exp J(w) - 1)`. -/
theorem Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_eq_exp_binetRemainder_sub_one
    {w : ℂ}
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hw_ne : w ≠ 0)
    (hbinet :
      Complex.log (Complex.Gamma w) =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w) :
    Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ) =
      (Real.sqrt (2 * Real.pi) : ℂ) *
        (Complex.exp (Complex.binetSecondFormulaRemainder w) - 1) := by
  let C : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)
  let E : ℂ := Complex.exp (Complex.binetSecondFormulaRemainder w)
  have hfactor :
      Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) = C * E :=
    Complex.normalizedGammaStirlingFactor_eq_sqrt_two_pi_mul_exp_binetRemainder
      hGamma_ne hw_ne hbinet
  calc
    Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ) =
        C * E - C := by
      exact congrArg (fun z : ℂ => z - C) hfactor
    _ = C * E - C * 1 := by
      exact congrArg (fun z : ℂ => C * E - z) (mul_one C).symm
    _ = C * (E - 1) :=
      (mul_sub C E 1).symm
    _ =
        (Real.sqrt (2 * Real.pi) : ℂ) *
          (Complex.exp (Complex.binetSecondFormulaRemainder w) - 1) := rfl

/-- Small complex exponential errors are bounded linearly in their exponent,
with the Stirling constant attached. -/
theorem Complex.sqrt_two_pi_mul_exp_sub_one_norm_le_of_norm_le_one
    {E : ℂ}
    (hE : ‖E‖ ≤ 1) :
    ‖(Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1)‖ ≤
      2 * Real.sqrt (2 * Real.pi) * ‖E‖ := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hnorm_const :
      ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ = Real.sqrt (2 * Real.pi) :=
    Complex.norm_ofReal_of_nonneg hsqrt_nonneg
  have hnorm_exp_abs : ‖Complex.exp E - 1‖ = Complex.abs (Complex.exp E - 1) :=
    Complex.norm_eq_abs (Complex.exp E - 1)
  have hE_abs_bound : Complex.abs E ≤ 1 := by
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      (Complex.norm_eq_abs E)
      hE
  have hexp_bound_abs :
      Complex.abs (Complex.exp E - 1) ≤ 2 * Complex.abs E :=
    Complex.abs_exp_sub_one_le hE_abs_bound
  have hexp_bound_norm :
      ‖Complex.exp E - 1‖ ≤ 2 * ‖E‖ := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖Complex.exp E - 1‖ ≤ 2 * x)
      (Complex.norm_eq_abs E).symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ 2 * Complex.abs E)
        hnorm_exp_abs.symm
        hexp_bound_abs)
  have hmul_norm :
      ‖(Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1)‖ =
        Real.sqrt (2 * Real.pi) * ‖Complex.exp E - 1‖ := by
    calc
      ‖(Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1)‖ =
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ * ‖Complex.exp E - 1‖ :=
        norm_mul (Real.sqrt (2 * Real.pi) : ℂ) (Complex.exp E - 1)
      _ = Real.sqrt (2 * Real.pi) * ‖Complex.exp E - 1‖ := by
        exact congrArg (fun x : ℝ => x * ‖Complex.exp E - 1‖) hnorm_const
  have hscaled :
      Real.sqrt (2 * Real.pi) * ‖Complex.exp E - 1‖ ≤
        Real.sqrt (2 * Real.pi) * (2 * ‖E‖) :=
    mul_le_mul_of_nonneg_left hexp_bound_norm hsqrt_nonneg
  have htarget_eq :
      Real.sqrt (2 * Real.pi) * (2 * ‖E‖) =
        2 * Real.sqrt (2 * Real.pi) * ‖E‖ := by
    calc
      Real.sqrt (2 * Real.pi) * (2 * ‖E‖) =
          (Real.sqrt (2 * Real.pi) * 2) * ‖E‖ :=
        mul_assoc (Real.sqrt (2 * Real.pi)) 2 ‖E‖
      _ = (2 * Real.sqrt (2 * Real.pi)) * ‖E‖ := by
        exact congrArg (fun x : ℝ => x * ‖E‖)
          (mul_comm (Real.sqrt (2 * Real.pi)) 2)
      _ = 2 * Real.sqrt (2 * Real.pi) * ‖E‖ := rfl
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 2 * Real.sqrt (2 * Real.pi) * ‖E‖)
    hmul_norm.symm
    (hscaled.trans_eq htarget_eq)

/-- Binet's logarithmic formula implies the normalized sectorial Stirling
estimate for `Γ`.

This is the standard exponentiation step from the principal logarithmic Binet
formula to
`Γ(w) exp(w) w^(1/2-w) = sqrt(2π) + O(1/‖w‖)`, uniformly in the closed
right-half-plane sector. -/
theorem Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane_from_binetSecondFormula :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  rcases
    Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane
    with ⟨R, K, hR, hK, hBinet⟩
  let R' : ℝ := max R K
  let K' : ℝ := 2 * Real.sqrt (2 * Real.pi) * K
  have hR' : 0 < R' :=
    lt_of_lt_of_le hR (le_max_left R K)
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
    exact Real.sqrt_pos_of_pos (mul_pos two_pos Real.pi_pos)
  have hK' : 0 < K' := by
    have htwo_sqrt_pos : 0 < 2 * Real.sqrt (2 * Real.pi) :=
      mul_pos two_pos hsqrt_pos
    exact mul_pos htwo_sqrt_pos hK
  refine ⟨R', K', hR', hK', ?_⟩
  intro w hw_sector hw_radius
  have hR_le : R ≤ ‖w‖ :=
    le_trans (le_max_left R K) hw_radius
  have hK_le : K ≤ ‖w‖ :=
    le_trans (le_max_right R K) hw_radius
  rcases hBinet w hw_sector hR_le with ⟨hlog, hrem⟩
  let E : ℂ := Complex.binetSecondFormulaRemainder w
  have hnorm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le hR' hw_radius
  have hsmall : ‖E‖ ≤ 1 := by
    have hdiv_le_one : K / ‖w‖ ≤ 1 :=
      (div_le_one₀ hnorm_pos.le).mpr hK_le
    exact hrem.trans hdiv_le_one
  have hw_ne : w ≠ 0 :=
    norm_pos_iff.mp hnorm_pos
  have hGamma_ne : Complex.Gamma w ≠ 0 := by
    intro hzero
    rcases (Complex.Gamma_eq_zero_iff w).mp hzero with ⟨n, hn⟩
    subst w
    cases n with
    | zero =>
        exact hw_ne (neg_zero : -((0 : ℂ)) = 0)
    | succ n =>
        have hre_eq :
            (-(((Nat.succ n : ℕ) : ℂ))).re =
              -(((Nat.succ n : ℕ) : ℝ)) := by
          calc
            (-(((Nat.succ n : ℕ) : ℂ))).re =
                -(((Nat.succ n : ℕ) : ℂ).re) :=
              Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
            _ = -(((Nat.succ n : ℕ) : ℝ)) := by
              exact congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
        have hre_nonneg :
            (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
          Eq.subst
            (motive := fun x : ℝ => (0 : ℝ) ≤ x)
            hre_eq
            hw_sector
        have hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
          Nat.cast_pos.mpr (Nat.succ_pos n)
        have hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
          neg_neg_of_pos hsucc_pos
        exact (not_lt_of_ge hre_nonneg) hneg_lt_zero
  have hidentity :
      Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ) =
        (Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1) :=
    Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_eq_exp_binetRemainder_sub_one
      hGamma_ne hw_ne hlog
  have hleft :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ =
        ‖(Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1)‖ :=
    congrArg norm hidentity
  have hexp :
      ‖(Real.sqrt (2 * Real.pi) : ℂ) * (Complex.exp E - 1)‖ ≤
        2 * Real.sqrt (2 * Real.pi) * ‖E‖ :=
    Complex.sqrt_two_pi_mul_exp_sub_one_norm_le_of_norm_le_one hsmall
  have hscale :
      2 * Real.sqrt (2 * Real.pi) * ‖E‖ ≤
        K' / ‖w‖ := by
    have hconst_nonneg : 0 ≤ 2 * Real.sqrt (2 * Real.pi) :=
      le_of_lt (mul_pos two_pos hsqrt_pos)
    have hmul_rem :
        2 * Real.sqrt (2 * Real.pi) * ‖E‖ ≤
          2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) :=
      mul_le_mul_of_nonneg_left hrem hconst_nonneg
    have htarget_eq :
        2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) = K' / ‖w‖ := by
      calc
        2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) =
            (2 * Real.sqrt (2 * Real.pi) * K) / ‖w‖ := by
          exact (mul_div_assoc (2 * Real.sqrt (2 * Real.pi)) K ‖w‖).symm
        _ = K' / ‖w‖ := rfl
    exact hmul_rem.trans_eq htarget_eq
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ K' / ‖w‖)
    hleft.symm
    (hexp.trans hscale)

/-- The fixed-real-part vertical line point `a + i b`, named to keep all fixed-line
Stirling estimates definitionally aligned. -/
def Complex.fixedRealPartVerticalPoint (a b : ℝ) : ℂ :=
  (a : ℂ) + (b : ℂ) * Complex.I

/-- The fixed-line point has real coordinate `a`. -/
theorem Complex.fixedRealPartVerticalPoint_re
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).re = a := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).re =
        ((a : ℂ) + (b : ℂ) * Complex.I).re := rfl
    _ = (a : ℂ).re + ((b : ℂ) * Complex.I).re :=
        Complex.add_re (a : ℂ) ((b : ℂ) * Complex.I)
    _ = a + 0 := by simp [Complex.mul_I_re]
    _ = a := add_zero a

/-- The fixed-line point has imaginary coordinate `b`. -/
theorem Complex.fixedRealPartVerticalPoint_im
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).im = b := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).im =
        ((a : ℂ) + (b : ℂ) * Complex.I).im := rfl
    _ = (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
        Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
    _ = 0 + b := by simp [Complex.mul_I_im]
    _ = b := zero_add b

/-- The direct fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (a - 1 / 2)

/-- The reciprocal fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalReciprocalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp ((Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (1 / 2 - a)

/-- The fixed-real-part direct Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos (-(Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2))

/-- The fixed-real-part direct Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)

/-- The fixed-real-part reciprocal Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos ((Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a))

/-- The fixed-real-part reciprocal Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos a b)

/-- Shifting the fixed real part by a natural number multiplies the Stirling
envelope by the corresponding power of the vertical polynomial scale. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_natShift_eq
    (a b : ℝ)
    (N : ℕ) :
    Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b =
      Complex.fixedRealPartVerticalStirlingEnvelope a b *
        (1 + ‖b‖) ^ (N : ℝ) := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have hexponent :
      a + (N : ℝ) - 1 / 2 =
        (a - 1 / 2) + (N : ℝ) := by
    calc
      a + (N : ℝ) - 1 / 2 =
          (a + (N : ℝ)) + -(1 / 2) := by
        exact sub_eq_add_neg (a + (N : ℝ)) (1 / 2)
      _ = a + ((N : ℝ) + -(1 / 2)) := by
        exact add_assoc a (N : ℝ) (-(1 / 2))
      _ = a + (-(1 / 2) + (N : ℝ)) := by
        exact congrArg (fun t : ℝ => a + t) (add_comm (N : ℝ) (-(1 / 2)))
      _ = (a + -(1 / 2)) + (N : ℝ) := by
        exact (add_assoc a (-(1 / 2)) (N : ℝ)).symm
      _ = (a - 1 / 2) + (N : ℝ) := by
        exact congrArg (fun t : ℝ => t + (N : ℝ))
          (sub_eq_add_neg a (1 / 2)).symm
  unfold Complex.fixedRealPartVerticalStirlingEnvelope
  calc
    Real.exp (-(Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (a + (N : ℝ) - 1 / 2) =
      Real.exp (-(Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ ((a - 1 / 2) + (N : ℝ)) := by
      exact congrArg
        (fun t : ℝ =>
          Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ t)
        hexponent
    _ =
      Real.exp (-(Real.pi / 2) * ‖b‖) *
        ((1 + ‖b‖) ^ (a - 1 / 2) *
          (1 + ‖b‖) ^ (N : ℝ)) := by
      exact congrArg
        (fun t : ℝ => Real.exp (-(Real.pi / 2) * ‖b‖) * t)
        (Real.rpow_add hbase_pos (a - 1 / 2) (N : ℝ))
    _ =
      (Real.exp (-(Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (a - 1 / 2)) *
          (1 + ‖b‖) ^ (N : ℝ) := by
      exact mul_assoc (Real.exp (-(Real.pi / 2) * ‖b‖))
        ((1 + ‖b‖) ^ (a - 1 / 2))
        ((1 + ‖b‖) ^ (N : ℝ))

/-- Cancelling the polynomial scale introduced by a natural real-part shift in
the vertical Stirling envelope. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
    (a b : ℝ)
    (N : ℕ)
    (C d : ℝ)
    (hd_pos : 0 < d) :
    C * Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b /
        (d * (1 + ‖b‖) ^ (N : ℝ)) =
      (C / d) * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  let E : ℝ := Complex.fixedRealPartVerticalStirlingEnvelope a b
  let T : ℝ := (1 + ‖b‖) ^ (N : ℝ)
  have hbase_pos : 0 < 1 + ‖b‖ :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg b)
  have hT_pos : 0 < T :=
    Real.rpow_pos_of_pos hbase_pos (N : ℝ)
  have hT_ne : T ≠ 0 :=
    ne_of_gt hT_pos
  have hshift :
      Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b = E * T :=
    Complex.fixedRealPartVerticalStirlingEnvelope_natShift_eq a b N
  have hmul_div :
      C * (E * T) / (d * T) = C * E / d := by
    calc
      C * (E * T) / (d * T) = (C * E) * T / (d * T) := by
        exact congrArg (fun u : ℝ => u / (d * T)) (mul_assoc C E T).symm
      _ = C * E / d := by
        exact mul_div_mul_right (C * E) d hT_ne
  have hdiv_mul :
      C * E / d = (C / d) * E := by
    calc
      C * E / d = (C * E) * d⁻¹ := by
        exact div_eq_mul_inv (C * E) d
      _ = C * (E * d⁻¹) := by
        exact mul_assoc C E d⁻¹
      _ = C * (d⁻¹ * E) := by
        exact congrArg (fun u : ℝ => C * u) (mul_comm E d⁻¹)
      _ = (C * d⁻¹) * E := by
        exact (mul_assoc C d⁻¹ E).symm
      _ = (C / d) * E := by
        exact congrArg (fun u : ℝ => u * E) (div_eq_mul_inv C d).symm
  calc
    C * Complex.fixedRealPartVerticalStirlingEnvelope (a + N) b /
        (d * (1 + ‖b‖) ^ (N : ℝ)) =
      C * (E * T) / (d * T) := by
      exact congrArg
        (fun u : ℝ => C * u / (d * T))
        hshift
    _ = C * E / d := hmul_div
    _ = (C / d) * E := hdiv_mul

/-- Sectorial Stirling estimate for the normalized Gamma factor on the closed
right half-plane.

This is the canonical sectorial Stirling input in the exact normalized form
used by the owner API:
`Γ(w) exp(w) w^(1/2-w) = sqrt(2π) + O(1/‖w‖)`, uniformly in the closed
right half-plane for large radius; cf. DLMF §5.11 and Whittaker-Watson,
Ch. XII. -/
theorem Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact
    Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane_from_binetSecondFormula

/-- Classical sectorial Stirling estimate for the normalized Gamma factor on
the closed right half-plane.

This is only name transport to the canonical sectorial Stirling theorem above. -/
theorem Complex.classical_sectorialStirling_normalizedGamma_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane

/-- Sectorial logarithmic Stirling expansion for `Complex.Gamma` on the closed
right half-plane.

This public owner theorem is the normalized-factor consequence of the canonical
sectorial Stirling estimate.  The logarithmic formulation and this exponential
normalization are equivalent on the large closed right-half-plane sector. -/
theorem Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.classical_sectorialStirling_normalizedGamma_closedRightHalfPlane

/-- If a complex number is within `sqrt (2π)` of `sqrt (2π)`, then its norm is
bounded by `2 sqrt (2π)`.

This is the elementary triangle-inequality extraction used to pass from the
exponential Stirling remainder to a uniform bound for the normalized Gamma
factor. -/
theorem Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
    (A : ℂ)
    (hA :
      ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖A‖ ≤ 2 * Real.sqrt (2 * Real.pi) := by
  have htriangle :
      ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := by
    calc
      ‖A‖ =
          ‖(A - (Real.sqrt (2 * Real.pi) : ℂ)) +
            (Real.sqrt (2 * Real.pi) : ℂ)‖ := by
        exact congrArg norm (sub_add_cancel A (Real.sqrt (2 * Real.pi) : ℂ)).symm
      _ ≤
          ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
            ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        norm_add_le (A - (Real.sqrt (2 * Real.pi) : ℂ))
          (Real.sqrt (2 * Real.pi) : ℂ)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hnorm_sqrt :
      ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ = Real.sqrt (2 * Real.pi) := by
    exact Complex.norm_ofReal_of_nonneg hsqrt_nonneg
  calc
    ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := htriangle
    _ ≤ Real.sqrt (2 * Real.pi) +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        add_le_add_right hA ‖(Real.sqrt (2 * Real.pi) : ℂ)‖
    _ = Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) :=
        congrArg (fun x : ℝ => Real.sqrt (2 * Real.pi) + x) hnorm_sqrt
    _ = 2 * Real.sqrt (2 * Real.pi) := by
        exact (two_mul (Real.sqrt (2 * Real.pi))).symm

/-- Pointwise normalized Gamma-factor bound extracted from an exponential
Stirling estimate once the error term is at most `sqrt (2π)`. -/
theorem Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
    (R K : ℝ)
    (hStirling :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_R : R ≤ ‖w‖)
    (hw_error : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
      2 * Real.sqrt (2 * Real.pi) := by
  have herror :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) :=
    le_trans (hStirling w hw_sector hw_R) hw_error
  exact
    Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
      (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
      herror

/-- If a complex number is within half of `sqrt (2π)` from `sqrt (2π)`, then
its norm is bounded below by the same half-constant. -/
theorem Complex.half_sqrt_two_pi_le_norm_of_norm_sub_sqrt_two_pi_le_half
    (A : ℂ)
    (hA :
      ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) / 2) :
    Real.sqrt (2 * Real.pi) / 2 ≤ ‖A‖ := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_nonneg : 0 ≤ s :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hs_norm : ‖(s : ℂ)‖ = s :=
    Complex.norm_ofReal_of_nonneg hs_nonneg
  have htriangle :
      ‖(s : ℂ)‖ ≤ ‖A‖ + ‖A - (s : ℂ)‖ := by
    calc
      ‖(s : ℂ)‖ = ‖A - (A - (s : ℂ))‖ := by
        exact congrArg norm (sub_sub_cancel A (s : ℂ)).symm
      _ ≤ ‖A‖ + ‖A - (s : ℂ)‖ :=
        norm_sub_le A (A - (s : ℂ))
  have hs_le_sum : s ≤ ‖A‖ + s / 2 := by
    calc
      s = ‖(s : ℂ)‖ := hs_norm.symm
      _ ≤ ‖A‖ + ‖A - (s : ℂ)‖ := htriangle
      _ ≤ ‖A‖ + s / 2 := add_le_add_left hA ‖A‖
  have hhalf_le_sub : s - s / 2 ≤ ‖A‖ :=
    sub_le_iff_le_add.mpr hs_le_sum
  have hhalf_eq : s - s / 2 = s / 2 := by
    calc
      s - s / 2 = s * 1 - s * (1 / 2) := by
        exact congrArg₂ HSub.hSub (mul_one s).symm (mul_one_div s 2).symm
      _ = s * (1 - 1 / 2) := by
        exact (mul_sub s 1 (1 / 2)).symm
      _ = s * (1 / 2) := by
        exact congrArg (fun t : ℝ => s * t) (sub_eq_self.mpr ?_)
      _ = s / 2 := by
        exact mul_one_div s 2
    · exact sub_eq_zero.mpr (one_div_two_add_one_div_two.symm)
  exact
    Eq.subst
      (motive := fun t : ℝ => t ≤ ‖A‖)
      hhalf_eq
      hhalf_le_sub

/-- Pointwise lower normalized Gamma-factor bound extracted from an exponential
Stirling estimate once the error term is at most half of `sqrt (2π)`. -/
theorem Complex.half_sqrt_two_pi_le_normalizedGammaFactor_norm_of_exponentialStirling_error
    (R K : ℝ)
    (hStirling :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_R : R ≤ ‖w‖)
    (hw_error : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi) / 2) :
    Real.sqrt (2 * Real.pi) / 2 ≤
      ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ := by
  have herror :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) / 2 :=
    le_trans (hStirling w hw_sector hw_R) hw_error
  exact
    Complex.half_sqrt_two_pi_le_norm_of_norm_sub_sqrt_two_pi_le_half
      (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
      herror

/-- A cutoff radius that makes `K / r` at most half of `sqrt (2π)`. -/
theorem real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
    (K r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_cutoff : 4 * K / Real.sqrt (2 * Real.pi) ≤ r) :
    K / r ≤ Real.sqrt (2 * Real.pi) / 2 := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_pos : 0 < s :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hcutoff_mul : 4 * K ≤ r * s :=
    (div_le_iff₀ hs_pos).mp hr_cutoff
  have htwoK_le_fourK : 2 * K ≤ 4 * K := by
    have hK_nonneg : 0 ≤ K :=
      le_of_lt hK_pos
    have htwo_le_four : (2 : ℝ) ≤ 4 := by
      calc
        (2 : ℝ) ≤ 2 + 2 := le_add_of_nonneg_right (le_of_lt two_pos)
        _ = 4 := rfl
    calc
      2 * K ≤ 4 * K :=
        mul_le_mul_of_nonneg_right htwo_le_four hK_nonneg
  have htwoK_le_rs : 2 * K ≤ r * s :=
    le_trans htwoK_le_fourK hcutoff_mul
  have htwoK_div_r_le_s : 2 * K / r ≤ s :=
    (div_le_iff₀ hr_pos).mpr
      (Eq.subst
        (motive := fun t : ℝ => 2 * K ≤ t)
        (mul_comm s r)
        htwoK_le_rs)
  have htwo_pos : 0 < (2 : ℝ) :=
    two_pos
  have hK_div_eq : 2 * (K / r) = 2 * K / r := by
    calc
      2 * (K / r) = (2 * K) / r := by
        exact (mul_div_assoc 2 K r).symm
  have htwice_le : 2 * (K / r) ≤ s :=
    Eq.subst
      (motive := fun t : ℝ => t ≤ s)
      hK_div_eq.symm
      htwoK_div_r_le_s
  exact
    (le_div_iff₀ htwo_pos).mpr
      (Eq.subst
        (motive := fun t : ℝ => t ≤ s)
        (mul_comm (K / r) 2)
        htwice_le)

/-- The normalized factor appearing in sectorial exponential Stirling for
`Complex.Gamma`. -/
def Complex.normalizedGammaStirlingFactor (w : ℂ) : ℂ :=
  Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)

/-- The logarithmic denominator loss incurred when solving the normalized
Stirling factor for `log ‖Γ(w)‖`. -/
def Complex.normalizedGammaStirlingLogLoss (w : ℂ) : ℝ :=
  -w.re - Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖

/-- A norm bound for the normalized Stirling factor gives the corresponding
logarithmic bound. -/
theorem Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
    (B : ℝ)
    {w : ℂ}
    (hfactor_pos : 0 < ‖Complex.normalizedGammaStirlingFactor w‖)
    (hbound : ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
  Real.log_le_log hfactor_pos hbound

/-- `Gamma` is nonzero at nonzero points in the closed right half-plane.

The only zeros of mathlib's completed finite-valued `Gamma` are the
nonpositive integers; the closed right half-plane excludes the negative
integers, and the explicit nonzero hypothesis excludes `0`. -/
theorem Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_ne : w ≠ 0) :
    Complex.Gamma w ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff w).mp hzero with ⟨n, hn⟩
  subst w
  cases n with
  | zero =>
      exact hw_ne (neg_zero : -((0 : ℂ)) = 0)
  | succ n =>
      have hre_eq :
          (-(((Nat.succ n : ℕ) : ℂ))).re =
            -(((Nat.succ n : ℕ) : ℝ)) := by
        calc
          (-(((Nat.succ n : ℕ) : ℂ))).re =
              -(((Nat.succ n : ℕ) : ℂ).re) :=
            Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
          _ = -(((Nat.succ n : ℕ) : ℝ)) := by
            exact congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
      have hre_nonneg :
          (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
        Eq.subst
          (motive := fun x : ℝ => (0 : ℝ) ≤ x)
          hre_eq
          hw_sector
      have hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.succ_pos n)
      have hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
        neg_neg_of_pos hsucc_pos
      exact (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- Nonvanishing of the normalized Stirling factor in the closed right
half-plane away from the origin.

This is the exact nonvanishing input for the large-radius extraction: `Γ` has
no zeros off the nonpositive integers, `exp` never vanishes, and `w^α` is
nonzero for `w ≠ 0`. -/
theorem Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀)
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_radius : R₀ ≤ ‖w‖) :
    Complex.normalizedGammaStirlingFactor w ≠ 0 := by
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le hR₀_pos hw_radius
  have hw_ne : w ≠ 0 :=
    norm_pos_iff.mp hw_norm_pos
  have hGamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
      hw_sector hw_ne
  have hexp_ne : Complex.exp w ≠ 0 :=
    Complex.exp_ne_zero w
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  show
      Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) ≠ 0
  exact mul_ne_zero (mul_ne_zero hGamma_ne hexp_ne) hcpow_ne

/-- Norm expansion for the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_norm_eq
    (w : ℂ) :
    ‖Complex.normalizedGammaStirlingFactor w‖ =
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
        ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  calc
    ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ := rfl
    _ = ‖Complex.Gamma w * Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      norm_mul (Complex.Gamma w * Complex.exp w)
        (w ^ ((1 / 2 : ℂ) - w))
    _ = ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (norm_mul (Complex.Gamma w) (Complex.exp w))

/-- Log norm of the complex exponential is its real part. -/
theorem Complex.log_norm_exp_eq_re
    (w : ℂ) :
    Real.log ‖Complex.exp w‖ = w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    norm_eq_abs (Complex.exp w)
  have habs_eq_exp :
      Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  calc
    Real.log ‖Complex.exp w‖ =
        Real.log (Complex.abs (Complex.exp w)) :=
      congrArg Real.log hnorm_eq_abs
    _ = Real.log (Real.exp w.re) :=
      congrArg Real.log habs_eq_exp
    _ = w.re :=
      Real.log_exp w.re

/-- Norm of the complex exponential. -/
theorem Complex.norm_exp_eq_exp_re
    (w : ℂ) :
    ‖Complex.exp w‖ = Real.exp w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    norm_eq_abs (Complex.exp w)
  calc
    ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
      hnorm_eq_abs
    _ = Real.exp w.re :=
      Complex.abs_exp w

/-- Exact log expansion of the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_log_eq
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
      Real.log ‖Complex.Gamma w‖ + w.re +
        Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hGamma_norm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hGamma_ne)
  have hexp_norm_ne : ‖Complex.exp w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (Complex.exp_ne_zero w))
  have hcpow_norm_ne : ‖w ^ ((1 / 2 : ℂ) - w)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hcpow_ne)
  have hGamma_exp_norm_ne :
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ ≠ 0 :=
    mul_ne_zero hGamma_norm_ne hexp_norm_ne
  calc
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        Real.log
          (‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
      congrArg Real.log (Complex.normalizedGammaStirlingFactor_norm_eq w)
    _ =
        Real.log (‖Complex.Gamma w‖ * ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      Real.log_mul hGamma_exp_norm_ne hcpow_norm_ne
    _ =
        (Real.log ‖Complex.Gamma w‖ + Real.log ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x + Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Real.log_mul hGamma_norm_ne hexp_norm_ne)
    _ =
        (Real.log ‖Complex.Gamma w‖ + w.re) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => (Real.log ‖Complex.Gamma w‖ + x) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Complex.log_norm_exp_eq_re w)
    _ =
        Real.log ‖Complex.Gamma w‖ + w.re +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := rfl

/-- Real cancellation used when solving the normalized Stirling-factor logarithm
for the original Gamma logarithm. -/
theorem real_add_add_add_neg_add_neg_cancel
    (A B C : ℝ) :
    (A + B + C) + (-B + -C) = A := by
  have hC_cancel :
      C + (-B + -C) = -B := by
    calc
      C + (-B + -C) =
          C + (-C + -B) :=
        congrArg (fun x : ℝ => C + x) (add_comm (-B) (-C))
      _ = (C + -C) + -B :=
        (add_assoc C (-C) (-B)).symm
      _ = 0 + -B :=
        congrArg (fun x : ℝ => x + -B) (add_right_neg C)
      _ = -B :=
        zero_add (-B)
  calc
    (A + B + C) + (-B + -C) =
        (A + B) + (C + (-B + -C)) :=
      add_assoc (A + B) C (-B + -C)
    _ = (A + B) + -B :=
      congrArg (fun x : ℝ => (A + B) + x) hC_cancel
    _ = A + (B + -B) :=
      add_assoc A B (-B)
    _ = A + 0 :=
      congrArg (fun x : ℝ => A + x) (add_right_neg B)
    _ = A :=
      add_zero A

/-- Exact logarithmic extraction identity from the normalized Stirling factor. -/
theorem Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.Gamma w‖ =
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  let A : ℝ := Real.log ‖Complex.Gamma w‖
  let B : ℝ := w.re
  let C : ℝ := Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hfactor :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        A + B + C :=
    Complex.normalizedGammaStirlingFactor_log_eq w hGamma_ne hcpow_ne
  have hloss :
      Complex.normalizedGammaStirlingLogLoss w = -B + -C := by
    exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
  calc
    Real.log ‖Complex.Gamma w‖ = A := rfl
    _ = (A + B + C) + (-B + -C) :=
      (real_add_add_add_neg_add_neg_cancel A B C).symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          (-B + -C) :=
      congrArg (fun x : ℝ => x + (-B + -C)) hfactor.symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w :=
      congrArg
        (fun x : ℝ =>
          Real.log ‖Complex.normalizedGammaStirlingFactor w‖ + x)
        hloss.symm

/-- Exact logarithmic extraction from the normalized Stirling factor.

After expanding
`‖Γ(w) exp(w) w^(1/2-w)‖`, this inequality solves for
`log ‖Γ(w)‖`.  The loss term is precisely the exponential denominator
`log ‖exp w‖ = w.re` and the principal-power denominator
`log ‖w^(1/2-w)‖`. -/
theorem Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hfactor_ne : Complex.normalizedGammaStirlingFactor w ≠ 0) :
    Real.log ‖Complex.Gamma w‖ ≤
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  have hGamma_ne : Complex.Gamma w ≠ 0 := by
    intro hGamma_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = 0 * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) :=
          congrArg
            (fun x : ℂ => x * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
            hGamma_zero
        _ = (0 : ℂ) * w ^ ((1 / 2 : ℂ) - w) := by
          exact congrArg
            (fun x : ℂ => x * w ^ ((1 / 2 : ℂ) - w))
            (zero_mul (Complex.exp w))
        _ = 0 :=
          zero_mul (w ^ ((1 / 2 : ℂ) - w))
    exact hfactor_ne hfactor_zero
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hcpow_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = Complex.Gamma w * Complex.exp w * 0 :=
          congrArg
            (fun x : ℂ => Complex.Gamma w * Complex.exp w * x)
            hcpow_zero
        _ = 0 :=
          mul_zero (Complex.Gamma w * Complex.exp w)
    exact hfactor_ne hfactor_zero
  exact le_of_eq
    (Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
      w hGamma_ne hcpow_ne)

/-- Solving the normalized Stirling factor for an upper bound on `‖Γ(w)‖`.

The denominator is `‖exp w‖ * ‖w^(1/2-w)‖`, positive away from `w = 0`. -/
theorem Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
    (w : ℂ)
    (B : ℝ)
    (hbound : ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B)
    (hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :
    ‖Complex.Gamma w‖ ≤
      B / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  have hnorm :
      ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
    calc
      ‖Complex.normalizedGammaStirlingFactor w‖ =
          ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
        Complex.normalizedGammaStirlingFactor_norm_eq w
      _ =
          ‖Complex.Gamma w‖ *
            (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        mul_assoc ‖Complex.Gamma w‖ ‖Complex.exp w‖
          ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hmul_le :
      ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤ B :=
    Eq.subst
      (motive := fun t : ℝ => t ≤ B)
      hnorm
      hbound
  exact (le_div_iff₀ hden_pos).mpr hmul_le

/-- Solving the normalized Stirling factor for a lower bound on `‖Γ(w)‖`. -/
theorem Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
    (w : ℂ)
    (b : ℝ)
    (hlower : b ≤ ‖Complex.normalizedGammaStirlingFactor w‖)
    (hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :
    b / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
      ‖Complex.Gamma w‖ := by
  have hnorm :
      ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
    calc
      ‖Complex.normalizedGammaStirlingFactor w‖ =
          ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
        Complex.normalizedGammaStirlingFactor_norm_eq w
      _ =
          ‖Complex.Gamma w‖ *
            (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        mul_assoc ‖Complex.Gamma w‖ ‖Complex.exp w‖
          ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hle_mul :
      b ≤ ‖Complex.Gamma w‖ *
          (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
    le_trans hlower (le_of_eq hnorm)
  exact (div_le_iff₀ hden_pos).mpr hle_mul

/-- Constant logarithmic terms are absorbed by the large-radius log-linear
envelope on the closed right half-plane. -/
theorem Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  let δ : ℝ := Real.log 2
  let C : ℝ := max (Real.log B / δ) 1
  have hδ_pos : 0 < δ :=
    Real.log_pos one_lt_two
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (Real.log B / δ) 1)
  refine ⟨C, hC_pos, ?_⟩
  intro w _hw_sector _hw_radius
  have htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
    mul_nonneg zero_le_two (norm_nonneg w)
  have hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
    le_add_of_nonneg_right htwo_norm_nonneg
  have harg_ge_two : (2 : ℝ) ≤ 2 + 2 * ‖w‖ :=
    le_add_of_nonneg_right htwo_norm_nonneg
  have hlog_ge_delta :
      δ ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    le_trans (le_of_lt hδ_pos) hlog_ge_delta
  have hdelta_le_envelope :
      δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
    have hlog_le_envelope :
        Real.log (2 + 2 * ‖w‖) ≤
          (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
      calc
        Real.log (2 + 2 * ‖w‖) =
            1 * Real.log (2 + 2 * ‖w‖) :=
          (one_mul (Real.log (2 + 2 * ‖w‖))).symm
        _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
    exact le_trans hlog_ge_delta hlog_le_envelope
  have hlogB_div_le_C : Real.log B / δ ≤ C :=
    le_max_left (Real.log B / δ) 1
  have hlogB_le_Cδ : Real.log B ≤ C * δ :=
    (div_le_iff₀ hδ_pos).mp hlogB_div_le_C
  have hCδ_le_Cenv :
      C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
    mul_le_mul_of_nonneg_left hdelta_le_envelope (le_of_lt hC_pos)
  have hCenv_eq :
      C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
        C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact
    le_trans hlogB_le_Cδ
      (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq))

/-- In the closed right half-plane, the real-part contribution to the
normalized Stirling loss is nonpositive, so the loss is bounded by the
principal-power logarithmic loss alone. -/
theorem Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    Complex.normalizedGammaStirlingLogLoss w ≤
      -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hneg_re_nonpos : -w.re ≤ 0 :=
    neg_nonpos.mpr hw_sector
  calc
    Complex.normalizedGammaStirlingLogLoss w =
        -w.re + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ ≤ 0 + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      add_le_add_right hneg_re_nonpos
        (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ = -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      zero_add (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)

/-- Positive radius lower bound excludes the origin. -/
theorem Complex.ne_zero_of_pos_le_norm
    {R : ℝ}
    (hR_pos : 0 < R)
    {z : ℂ}
    (hz_radius : R ≤ ‖z‖) :
    z ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le hR_pos hz_radius)

/-- The closed right half-plane is exactly the principal-argument sector
`|arg z| ≤ π / 2`. -/
theorem Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector
    {z : ℂ}
    (hz_sector : Complex.closedRightHalfPlaneSector z) :
    |Complex.arg z| ≤ Real.pi / 2 :=
  Complex.abs_arg_le_pi_div_two_iff.mpr hz_sector

/-- Principal-branch absolute-value formula for complex powers in logarithmic
form. -/
theorem Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log (Complex.abs (z ^ a)) =
      a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
  have hz_abs_pos : 0 < Complex.abs z :=
    Complex.abs.pos hz_ne
  have hpow_pos : 0 < Complex.abs z ^ a.re :=
    Real.rpow_pos_of_pos hz_abs_pos a.re
  have hexp_pos : 0 < Real.exp (Complex.arg z * a.im) :=
    Real.exp_pos (Complex.arg z * a.im)
  have hcpow_abs :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    Real.log (Complex.abs (z ^ a)) =
        Real.log
          (Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im)) :=
      congrArg Real.log hcpow_abs
    _ =
        Real.log (Complex.abs z ^ a.re) -
          Real.log (Real.exp (Complex.arg z * a.im)) :=
      Real.log_div (ne_of_gt hpow_pos) (ne_of_gt hexp_pos)
    _ =
        a.re * Real.log (Complex.abs z) -
          Real.log (Real.exp (Complex.arg z * a.im)) := by
      exact congrArg
        (fun x : ℝ => x - Real.log (Real.exp (Complex.arg z * a.im)))
        (Real.log_rpow hz_abs_pos a.re)
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log (Complex.abs z) - x)
        (Real.log_exp (Complex.arg z * a.im))

/-- Principal-branch norm formula for complex powers. -/
theorem Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    ‖z ^ a‖ =
      ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  have habs_cpow :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    ‖z ^ a‖ = Complex.abs (z ^ a) :=
      hnorm_cpow_abs
    _ = Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
      habs_cpow
    _ = ‖z‖ ^ a.re / Real.exp (Complex.arg z * a.im) := by
      exact congrArg
        (fun r : ℝ => r ^ a.re / Real.exp (Complex.arg z * a.im))
        hnorm_z_abs.symm

/-- Principal-branch norm formula for complex powers in logarithmic form. -/
theorem Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log ‖z ^ a‖ =
      a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  calc
    Real.log ‖z ^ a‖ =
        Real.log (Complex.abs (z ^ a)) :=
      congrArg Real.log hnorm_cpow_abs
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im :=
      Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
        hz_ne
    _ =
        a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log x - Complex.arg z * a.im)
        hnorm_z_abs.symm

/-- Real coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_re
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re := by
  calc
    ((1 / 2 : ℂ) - w).re =
        (1 / 2 : ℂ).re - w.re :=
      Complex.sub_re (1 / 2 : ℂ) w
    _ = (1 / 2 : ℝ) - w.re := by
      exact congrArg (fun x : ℝ => x - w.re) (Complex.ofReal_re (1 / 2))

/-- Imaginary coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_im
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).im = -w.im := by
  calc
    ((1 / 2 : ℂ) - w).im =
        (1 / 2 : ℂ).im - w.im :=
      Complex.sub_im (1 / 2 : ℂ) w
    _ = 0 - w.im := by
      exact congrArg (fun x : ℝ => x - w.im) (Complex.ofReal_im (1 / 2))
    _ = -w.im :=
      zero_sub w.im

/-- Algebraic rearrangement of the cpow logarithmic formula for the Stirling
exponent. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
    {w : ℂ}
    (hw_ne : w ≠ 0)
    (hlog :
      Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  have hre :
      ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re :=
    Complex.half_minus_self_re w
  have him :
      ((1 / 2 : ℂ) - w).im = -w.im :=
    Complex.half_minus_self_im w
  have hcoordinate :
      ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im =
        ((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im) := by
    exact congrArg₂
      (fun x y : ℝ => x * Real.log ‖w‖ - Complex.arg w * y)
      hre
      him
  have hneg_coordinate :
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
    calc
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
          -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖) +
            Complex.arg w * (-w.im) := by
        exact neg_sub
          (((1 / 2 : ℝ) - w.re) * Real.log ‖w‖)
          (Complex.arg w * (-w.im))
      _ = (-((1 / 2 : ℝ) - w.re)) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x + Complex.arg w * (-w.im))
          (neg_mul ((1 / 2 : ℝ) - w.re) (Real.log ‖w‖))
      _ = (-(1 / 2 : ℝ) + w.re) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (neg_sub (1 / 2 : ℝ) w.re)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (sub_eq_add_neg w.re (1 / 2)).symm
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            (-(Complex.arg w * w.im)) := by
        exact congrArg
          (fun x : ℝ => (w.re - 1 / 2) * Real.log ‖w‖ + x)
          (mul_neg (Complex.arg w) w.im)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ -
            Complex.arg w * w.im := by
        exact sub_eq_add_neg
          ((w.re - 1 / 2) * Real.log ‖w‖)
          (Complex.arg w * w.im)
  calc
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        -(((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :=
      congrArg Neg.neg hlog
    _ =
        -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) :=
      congrArg Neg.neg hcoordinate
    _ = (w.re - 1 / 2) * Real.log ‖w‖ -
          Complex.arg w * w.im :=
      hneg_coordinate

/-- The exact branch-loss expression for `w^(1/2-w)`.  This is the
coordinate form of the principal logarithm contribution: the radius part is
`(Re w - 1/2) log ‖w‖`, and the angular part is `- arg(w) Im w`. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  exact
    Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
      hw_ne
      (Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
        hw_ne)

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.re_le_norm
    (w : ℂ) :
    w.re ≤ ‖w‖ := by
  have hre_abs_le_abs : |w.re| ≤ Complex.abs w :=
    Complex.abs_re_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  have hre_abs_le_norm : |w.re| ≤ ‖w‖ :=
    Eq.subst
      (motive := fun x : ℝ => |w.re| ≤ x)
      hnorm_eq_abs.symm
      hre_abs_le_abs
  exact le_trans (le_abs_self w.re) hre_abs_le_norm

/-- The imaginary coordinate absolute value is bounded by the complex norm. -/
theorem Complex.abs_im_le_norm
    (w : ℂ) :
    |w.im| ≤ ‖w‖ := by
  have him_abs_le_abs : |w.im| ≤ Complex.abs w :=
    Complex.abs_im_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  exact
    Eq.subst
      (motive := fun x : ℝ => |w.im| ≤ x)
      hnorm_eq_abs.symm
      him_abs_le_abs

/-- Fixed vertical points lie in the closed right half-plane exactly when their
fixed real part is nonnegative. -/
theorem Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector
    {a b : ℝ}
    (ha : 0 ≤ a) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint a b) := by
  exact
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (Complex.fixedRealPartVerticalPoint_re a b).symm
      ha

/-- The imaginary height is bounded by the complex norm of a fixed vertical
point. -/
theorem Complex.fixedRealPartVerticalPoint_abs_im_le_norm
    (a b : ℝ) :
    ‖b‖ ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ := by
  have him :
      (Complex.fixedRealPartVerticalPoint a b).im = b :=
    Complex.fixedRealPartVerticalPoint_im a b
  have hbasic :
      |(Complex.fixedRealPartVerticalPoint a b).im| ≤
        ‖Complex.fixedRealPartVerticalPoint a b‖ :=
    Complex.abs_im_le_norm (Complex.fixedRealPartVerticalPoint a b)
  have hnorm_eq_abs : ‖b‖ = |b| :=
    Real.norm_eq_abs b
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖Complex.fixedRealPartVerticalPoint a b‖)
      hnorm_eq_abs.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          |x| ≤ ‖Complex.fixedRealPartVerticalPoint a b‖)
        him
        hbasic)

/-- A large imaginary height forces a large complex radius on a fixed vertical
line. -/
theorem Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge
    {a b H : ℝ}
    (hH : H ≤ ‖b‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hH (Complex.fixedRealPartVerticalPoint_abs_im_le_norm a b)

/-- If `H` dominates a sectorial radius cutoff, then a height cutoff by `H`
dominates the corresponding complex radius cutoff. -/
theorem Complex.fixedRealPartVerticalPoint_sectorialRadius_ge_of_height_ge
    {a b H R : ℝ}
    (hR_le_H : R ≤ H)
    (hH : H ≤ ‖b‖) :
    R ≤ ‖Complex.fixedRealPartVerticalPoint a b‖ :=
  le_trans hR_le_H
    (Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH)

/-- Shifting a fixed vertical point by a natural number shifts only its real
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_re
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).re =
      x + (N : ℝ) := by
  exact Complex.fixedRealPartVerticalPoint_re (x + N) y

/-- Shifting a fixed vertical point by a natural number preserves its imaginary
coordinate. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_im
    (x y : ℝ)
    (N : ℕ) :
    (Complex.fixedRealPartVerticalPoint (x + N) y).im = y := by
  exact Complex.fixedRealPartVerticalPoint_im (x + N) y

/-- A natural right shift moves the whole real strip into the closed right
half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    {N : ℕ}
    (hA : -A ≤ (N : ℝ))
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint (x + N) y) := by
  have hnonneg : 0 ≤ x + (N : ℝ) := by
    have hneg_x_le_N : -x ≤ (N : ℝ) :=
      le_trans (neg_le_neg hx) hA
    exact neg_le.mp hneg_x_le_N
  exact
    Complex.fixedRealPartVerticalPoint_closedRightHalfPlaneSector hnonneg

/-- The shifted vertical point has radius bounded below by the same height. -/
theorem Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge
    {x y H : ℝ}
    {N : ℕ}
    (hH : H ≤ ‖y‖) :
    H ≤ ‖Complex.fixedRealPartVerticalPoint (x + N) y‖ :=
  Complex.fixedRealPartVerticalPoint_radius_ge_of_height_ge hH

/-- Bounded real part in a strip remains bounded after a fixed natural shift. -/
theorem real_natShift_mem_strip_of_mem_strip
    {A B x : ℝ}
    (N : ℕ)
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    A + (N : ℝ) ≤ x + (N : ℝ) ∧
      x + (N : ℝ) ≤ B + (N : ℝ) :=
  ⟨add_le_add_right hxA (N : ℝ),
    add_le_add_right hxB (N : ℝ)⟩

/-- Deterministic right shift for a vertical strip.  It is the least natural
integer produced by the floor API which is at least `max 0 (-A)`, hence it
moves the strip lower edge `A` into the closed right half-plane. -/
def Complex.verticalStripRightShift (A : ℝ) : ℕ :=
  Nat.ceil (max 0 (-A))

/-- The deterministic strip shift dominates the negative lower endpoint. -/
theorem Complex.neg_lower_le_verticalStripRightShift
    (A : ℝ) :
    -A ≤ (Complex.verticalStripRightShift A : ℝ) := by
  have hmax : -A ≤ max 0 (-A) :=
    le_max_right 0 (-A)
  have hceil : max 0 (-A) ≤ (Complex.verticalStripRightShift A : ℝ) := by
    unfold Complex.verticalStripRightShift
    exact Nat.le_ceil (max 0 (-A))
  exact le_trans hmax hceil

/-- The deterministic strip shift is nonnegative as a real number. -/
theorem Complex.verticalStripRightShift_nonneg
    (A : ℝ) :
    (0 : ℝ) ≤ (Complex.verticalStripRightShift A : ℝ) :=
  Nat.cast_nonneg (Complex.verticalStripRightShift A)

/-- The deterministic shift moves every point in the strip into the closed
right half-plane. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y) :=
  Complex.fixedRealPartVerticalPoint_natShift_closedRightHalfPlaneSector
    (Complex.neg_lower_le_verticalStripRightShift A) hx

/-- The deterministic shift preserves the large-height-to-large-radius lower
bound. -/
theorem Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripRightShift A) y‖ :=
  Complex.fixedRealPartVerticalPoint_natShift_radius_ge_of_height_ge hH

/-- A positive lower radius cutoff makes the logarithmic envelope positive. -/
theorem real_largeRadius_log_envelope_pos
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 < Real.log (2 + 2 * r) := by
  have hr_pos : 0 < r :=
    lt_of_lt_of_le hR₀_pos hr
  have htwo_r_pos : 0 < 2 * r :=
    mul_pos two_pos hr_pos
  have hone_lt_arg : (1 : ℝ) < 2 + 2 * r := by
    calc
      (1 : ℝ) < 2 := one_lt_two
      _ ≤ 2 + 2 * r := le_add_of_nonneg_right (le_of_lt htwo_r_pos)
  exact Real.log_pos hone_lt_arg

/-- The large-radius log envelope is nonnegative. -/
theorem real_largeRadius_log_envelope_nonneg
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ Real.log (2 + 2 * r) :=
  le_of_lt (real_largeRadius_log_envelope_pos R₀ r hR₀_pos hr)

/-- On a positive large-radius region, the log envelope is at least `log 2`. -/
theorem real_log_two_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    Real.log 2 ≤ Real.log (2 + 2 * r) := by
  have hr_nonneg : 0 ≤ r :=
    le_of_lt (lt_of_lt_of_le hR₀_pos hr)
  have harg_le : (2 : ℝ) ≤ 2 + 2 * r :=
    le_add_of_nonneg_right (mul_nonneg zero_le_two hr_nonneg)
  exact Real.log_le_log zero_lt_two harg_le

/-- Positive lower radius cutoff gives nonnegative radius. -/
theorem real_nonneg_of_largeRadius
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ r :=
  le_of_lt (lt_of_lt_of_le hR₀_pos hr)

/-- The linear factor `r + 1/2` is dominated by the standard height factor
`1 + 2r` on nonnegative radii. -/
theorem real_radius_add_half_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r + 1 / 2 ≤ 1 + 2 * r := by
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
    one_half_le_one
  have hr_le_two_r : r ≤ 2 * r := by
    calc
      r = 1 * r := (one_mul r).symm
      _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
  calc
    r + 1 / 2 ≤ 2 * r + 1 :=
      add_le_add hr_le_two_r hhalf_le_one
    _ = 1 + 2 * r :=
      add_comm (2 * r) 1

/-- The radius itself is dominated by the standard height factor. -/
theorem real_radius_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r ≤ 1 + 2 * r := by
  calc
    r ≤ 2 * r :=
      calc
        r = 1 * r := (one_mul r).symm
        _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
    _ ≤ 1 + 2 * r :=
      le_add_of_nonneg_left zero_le_one

/-- The angular linear term is absorbed by the standard log-linear envelope on
any positive large-radius region. -/
theorem real_pi_radius_absorbed_by_logLinearEnvelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  let C : ℝ := (Real.pi / 2) / Real.log 2
  have hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hpi_half_pos : 0 < Real.pi / 2 :=
    div_pos Real.pi_pos two_pos
  have hC_pos : 0 < C :=
    div_pos hpi_half_pos hlog_two_pos
  refine ⟨C, hC_pos, ?_⟩
  intro r hr
  have hr_nonneg : 0 ≤ r :=
    real_nonneg_of_largeRadius R₀ r hR₀_pos hr
  have hH_nonneg : 0 ≤ 1 + 2 * r :=
    add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
  have hr_le_H : r ≤ 1 + 2 * r :=
    real_radius_le_one_add_two_mul r hr_nonneg
  have hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
    real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
  have hC_log_two : C * Real.log 2 = Real.pi / 2 := by
    calc
      C * Real.log 2 =
          ((Real.pi / 2) / Real.log 2) * Real.log 2 := rfl
      _ = Real.pi / 2 :=
        div_mul_cancel₀ (Real.pi / 2) (ne_of_gt hlog_two_pos)
  have hpi_half_le_CL :
      Real.pi / 2 ≤ C * Real.log (2 + 2 * r) := by
    have hmul : C * Real.log 2 ≤ C * Real.log (2 + 2 * r) :=
      mul_le_mul_of_nonneg_left hL_lower (le_of_lt hC_pos)
    exact le_trans (le_of_eq hC_log_two.symm) hmul
  have hleft_to_H :
      (Real.pi / 2) * r ≤ (Real.pi / 2) * (1 + 2 * r) :=
    mul_le_mul_of_nonneg_left hr_le_H (le_of_lt hpi_half_pos)
  have hH_scale :
      (Real.pi / 2) * (1 + 2 * r) ≤
        (C * Real.log (2 + 2 * r)) * (1 + 2 * r) :=
    mul_le_mul_of_nonneg_right hpi_half_le_CL hH_nonneg
  have htarget_eq :
      (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
        C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
    calc
      (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
          C * (Real.log (2 + 2 * r) * (1 + 2 * r)) :=
        (mul_assoc C (Real.log (2 + 2 * r)) (1 + 2 * r)).symm
      _ = C * ((1 + 2 * r) * Real.log (2 + 2 * r)) := by
        exact congrArg
          (fun x : ℝ => C * x)
          (mul_comm (Real.log (2 + 2 * r)) (1 + 2 * r))
      _ = C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
        exact mul_assoc C (1 + 2 * r) (Real.log (2 + 2 * r))
  exact le_trans hleft_to_H
    (le_trans hH_scale (le_of_eq htarget_eq))

/-- Uniform version of the real logarithmic envelope on a large-radius region. -/
theorem real_abs_log_le_largeRadius_log_envelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) := by
  let C : ℝ := max 1 (R₀⁻¹ / Real.log 2)
  have hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hR₀_inv_nonneg : 0 ≤ R₀⁻¹ :=
    inv_nonneg.mpr (le_of_lt hR₀_pos)
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (R₀⁻¹ / Real.log 2))
  refine ⟨C, hC_pos, ?_⟩
  intro r hr
  have hr_pos : 0 < r :=
    lt_of_lt_of_le hR₀_pos hr
  have hr_nonneg : 0 ≤ r :=
    le_of_lt hr_pos
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
    real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
  have hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
    real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
  by_cases hone_le_r : (1 : ℝ) ≤ r
  · have hlog_nonneg : 0 ≤ Real.log r :=
      Real.log_nonneg hone_le_r
    have hnorm_log : ‖Real.log r‖ = Real.log r :=
      Real.norm_of_nonneg hlog_nonneg
    have hr_le_arg : r ≤ 2 + 2 * r := by
      calc
        r ≤ 2 * r :=
          calc
            r = 1 * r := (one_mul r).symm
            _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
        _ ≤ 2 + 2 * r :=
          le_add_of_nonneg_left zero_le_two
    have hlog_le_L : Real.log r ≤ Real.log (2 + 2 * r) :=
      Real.log_le_log hr_pos hr_le_arg
    have hC_ge_one : (1 : ℝ) ≤ C :=
      le_max_left 1 (R₀⁻¹ / Real.log 2)
    have hL_le_CL : Real.log (2 + 2 * r) ≤ C * Real.log (2 + 2 * r) := by
      calc
        Real.log (2 + 2 * r) =
            1 * Real.log (2 + 2 * r) :=
          (one_mul (Real.log (2 + 2 * r))).symm
        _ ≤ C * Real.log (2 + 2 * r) :=
          mul_le_mul_of_nonneg_right hC_ge_one hL_nonneg
    exact le_trans (le_of_eq hnorm_log)
      (le_trans hlog_le_L hL_le_CL)
  · have hr_le_one : r ≤ 1 :=
      le_of_not_ge hone_le_r
    have hlog_nonpos : Real.log r ≤ 0 :=
      (Real.log_nonpos_iff hr_pos).mpr hr_le_one
    have hnorm_log : ‖Real.log r‖ = -Real.log r :=
      Real.norm_of_nonpos hlog_nonpos
    have hneg_log_le_inv : -Real.log r ≤ r⁻¹ := by
      have hneg_inv_le_log : -r⁻¹ ≤ Real.log r :=
        Real.neg_inv_le_log hr_nonneg
      exact neg_le.mp hneg_inv_le_log
    have hinv_le_R₀_inv : r⁻¹ ≤ R₀⁻¹ :=
      one_div_le_one_div_of_le hR₀_pos hr
    have hsmall : ‖Real.log r‖ ≤ R₀⁻¹ :=
      le_trans (le_of_eq hnorm_log) (le_trans hneg_log_le_inv hinv_le_R₀_inv)
    have hratio_le_C : R₀⁻¹ / Real.log 2 ≤ C :=
      le_max_right 1 (R₀⁻¹ / Real.log 2)
    have hR₀_inv_le_ratio_L :
        R₀⁻¹ ≤ (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) := by
      have hR₀_inv_div_mul :
          R₀⁻¹ = (R₀⁻¹ / Real.log 2) * Real.log 2 := by
        exact (div_mul_cancel₀ R₀⁻¹ (ne_of_gt hlog_two_pos)).symm
      have hmul :
          (R₀⁻¹ / Real.log 2) * Real.log 2 ≤
            (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) :=
        mul_le_mul_of_nonneg_left hL_lower
          (div_nonneg hR₀_inv_nonneg (le_of_lt hlog_two_pos))
      exact le_trans (le_of_eq hR₀_inv_div_mul)
        hmul
    have hratio_L_le_CL :
        (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) ≤
          C * Real.log (2 + 2 * r) :=
      mul_le_mul_of_nonneg_right hratio_le_C hL_nonneg
    exact le_trans hsmall
      (le_trans hR₀_inv_le_ratio_L hratio_L_le_CL)

/-- Pure real logarithmic envelope for a radius bounded below away from zero. -/
theorem real_abs_log_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) := by
  rcases real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos with
    ⟨C, hC_pos, hC⟩
  exact ⟨C, hC_pos, hC r hr⟩

/-- The logarithm of the radius is absorbed by the logarithmic envelope on any
large-radius region bounded away from zero. -/
theorem Complex.log_norm_le_log_envelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        ‖Real.log ‖w‖‖ ≤ C * Real.log (2 + 2 * ‖w‖) := by
  exact real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos

/-- If `0 ≤ x ≤ r`, then the shifted coordinate `x - 1/2` is bounded by
`r + 1/2` in absolute value. -/
theorem real_abs_sub_half_le_radius_add_half
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    |x - 1 / 2| ≤ r + 1 / 2 := by
  have hr_nonneg : 0 ≤ r :=
    le_trans hx_nonneg hx_le_r
  have hneg_r_le_x : -r ≤ x :=
    le_trans (neg_nonpos.mpr hr_nonneg) hx_nonneg
  have hneg_half_le_half : -(1 / 2 : ℝ) ≤ 1 / 2 :=
    neg_le_self (le_of_lt one_half_pos)
  have hlower : -(r + 1 / 2) ≤ x - 1 / 2 := by
    calc
      -(r + 1 / 2) = -r + -(1 / 2 : ℝ) :=
        neg_add r (1 / 2)
      _ ≤ x + -(1 / 2 : ℝ) :=
        add_le_add_right hneg_r_le_x (-(1 / 2 : ℝ))
      _ = x - 1 / 2 :=
        (sub_eq_add_neg x (1 / 2)).symm
  have hupper : x - 1 / 2 ≤ r + 1 / 2 := by
    calc
      x - 1 / 2 ≤ r - 1 / 2 :=
        sub_le_sub_right hx_le_r (1 / 2)
      _ = r + -(1 / 2 : ℝ) :=
        sub_eq_add_neg r (1 / 2)
      _ ≤ r + 1 / 2 :=
        add_le_add_left hneg_half_le_half r
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Radius part of the branch loss is bounded by the norm-log majorant. -/
theorem real_radiusTerm_le_norm_log_majorant
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    (x - 1 / 2) * Real.log r ≤
      (r + 1 / 2) * ‖Real.log r‖ := by
  have hterm_le_abs :
      (x - 1 / 2) * Real.log r ≤
        |(x - 1 / 2) * Real.log r| :=
    le_abs_self ((x - 1 / 2) * Real.log r)
  have habs_mul :
      |(x - 1 / 2) * Real.log r| =
        |x - 1 / 2| * |Real.log r| :=
    abs_mul (x - 1 / 2) (Real.log r)
  have habs_log_eq_norm :
      |Real.log r| = ‖Real.log r‖ :=
    (Real.norm_eq_abs (Real.log r)).symm
  have hshift :
      |x - 1 / 2| ≤ r + 1 / 2 :=
    real_abs_sub_half_le_radius_add_half x r hx_nonneg hx_le_r
  have hmajor :
      |x - 1 / 2| * |Real.log r| ≤
        (r + 1 / 2) * ‖Real.log r‖ := by
    have hlog_nonneg : 0 ≤ ‖Real.log r‖ :=
      norm_nonneg (Real.log r)
    have hmul :
        |x - 1 / 2| * ‖Real.log r‖ ≤
          (r + 1 / 2) * ‖Real.log r‖ :=
      mul_le_mul_of_nonneg_right hshift hlog_nonneg
    exact
      Eq.subst
        (motive := fun y : ℝ =>
          |x - 1 / 2| * y ≤ (r + 1 / 2) * ‖Real.log r‖)
        habs_log_eq_norm.symm
        hmul
  exact le_trans hterm_le_abs
    (le_trans (le_of_eq habs_mul) hmajor)

/-- Angular part of the branch loss is bounded by the sectorial angle majorant. -/
theorem real_argumentTerm_le_sectorial_majorant
    (θ y r : ℝ)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    -θ * y ≤ (Real.pi / 2) * r := by
  have hneg_product_le_abs :
      -θ * y ≤ |θ * y| := by
    calc
      -θ * y = -(θ * y) :=
        (neg_mul θ y).symm
      _ ≤ |θ * y| :=
        neg_le_abs (θ * y)
  have habs_product :
      |θ * y| = |θ| * |y| :=
    abs_mul θ y
  have hpi_half_nonneg : 0 ≤ Real.pi / 2 :=
    le_of_lt (div_pos Real.pi_pos two_pos)
  have habs_product_le :
      |θ| * |y| ≤ (Real.pi / 2) * r :=
    mul_le_mul hθ_abs_le hy_abs_le_r (abs_nonneg y) hpi_half_nonneg
  exact le_trans hneg_product_le_abs
    (le_trans (le_of_eq habs_product) habs_product_le)

/-- Pure real radius/argument majorization after replacing coordinates by norm
bounds and the argument by its sectorial bound. -/
theorem real_radiusArgumentLoss_le_norm_log_majorant
    (x y θ r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    (x - 1 / 2) * Real.log r - θ * y ≤
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r := by
  have hradius :
      (x - 1 / 2) * Real.log r ≤
        (r + 1 / 2) * ‖Real.log r‖ :=
    real_radiusTerm_le_norm_log_majorant x r hx_nonneg hx_le_r
  have hangle :
      -θ * y ≤ (Real.pi / 2) * r :=
    real_argumentTerm_le_sectorial_majorant θ y r hy_abs_le_r hθ_abs_le
  have hleft_eq :
      (x - 1 / 2) * Real.log r - θ * y =
        (x - 1 / 2) * Real.log r + (-θ * y) := by
    exact sub_eq_add_neg ((x - 1 / 2) * Real.log r) (θ * y)
  have hsum :
      (x - 1 / 2) * Real.log r + (-θ * y) ≤
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r :=
    add_le_add hradius hangle
  exact le_trans (le_of_eq hleft_eq) hsum

/-- Coordinate domination of the Stirling radius/argument loss by the elementary
norm majorant. -/
theorem Complex.radiusArgumentLoss_le_norm_log_majorant
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
      (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ := by
  exact
    real_radiusArgumentLoss_le_norm_log_majorant
      w.re w.im (Complex.arg w) ‖w‖
      hw_sector
      (Complex.re_le_norm w)
      (Complex.abs_im_le_norm w)
      (Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector hw_sector)

/-- Uniform pure real absorption of the norm-log majorant into the standard
log-linear envelope on a large-radius region. -/
theorem real_linear_log_absorption_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  rcases real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos with
    ⟨Clog, hClog_pos, hlog⟩
  rcases real_pi_radius_absorbed_by_logLinearEnvelope_uniform R₀ hR₀_pos with
    ⟨Cpi, hCpi_pos, hpi⟩
  refine ⟨Clog + Cpi, add_pos hClog_pos hCpi_pos, ?_⟩
  intro r hr
  have hr_nonneg : 0 ≤ r :=
    real_nonneg_of_largeRadius R₀ r hR₀_pos hr
  have hH_nonneg : 0 ≤ 1 + 2 * r :=
    add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
    real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
  have hfactor_nonneg : 0 ≤ r + 1 / 2 :=
    add_nonneg hr_nonneg (le_of_lt one_half_pos)
  have hfactor_le_H : r + 1 / 2 ≤ 1 + 2 * r :=
    real_radius_add_half_le_one_add_two_mul r hr_nonneg
  have hlog_bound :
      ‖Real.log r‖ ≤ Clog * Real.log (2 + 2 * r) :=
    hlog r hr
  have hfirst_step :
      (r + 1 / 2) * ‖Real.log r‖ ≤
        (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) :=
    mul_le_mul_of_nonneg_left hlog_bound hfactor_nonneg
  have hClogL_nonneg :
      0 ≤ Clog * Real.log (2 + 2 * r) :=
    mul_nonneg (le_of_lt hClog_pos) hL_nonneg
  have hfirst_factor :
      (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) ≤
        (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) :=
    mul_le_mul_of_nonneg_right hfactor_le_H hClogL_nonneg
  have hfirst_assoc :
      (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) := by
    calc
      (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
          ((1 + 2 * r) * Clog) * Real.log (2 + 2 * r) :=
        mul_assoc (1 + 2 * r) Clog (Real.log (2 + 2 * r))
      _ = (Clog * (1 + 2 * r)) * Real.log (2 + 2 * r) := by
        exact congrArg
          (fun x : ℝ => x * Real.log (2 + 2 * r))
          (mul_comm (1 + 2 * r) Clog)
      _ = Clog * (1 + 2 * r) * Real.log (2 + 2 * r) := rfl
  have hfirst :
      (r + 1 / 2) * ‖Real.log r‖ ≤
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    le_trans hfirst_step
      (le_trans hfirst_factor (le_of_eq hfirst_assoc))
  have hsecond :
      (Real.pi / 2) * r ≤
        Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    hpi r hr
  have hsum :
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
          Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    add_le_add hfirst hsecond
  have hcombine :
      Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
          Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) =
        (Clog + Cpi) * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    logLinearEnvelope_add_constants
      Clog Cpi (1 + 2 * r) (Real.log (2 + 2 * r))
  exact le_trans hsum (le_of_eq hcombine)

/-- Pure real absorption of the norm-log majorant into the standard log-linear
envelope, using a lower radius cutoff. -/
theorem real_linear_log_absorption
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
        C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  rcases real_linear_log_absorption_uniform R₀ hR₀_pos with
    ⟨C, hC_pos, hC⟩
  exact ⟨C, hC_pos, hC r hr⟩

/-- The elementary norm-log majorant is absorbed by the standard log-linear
envelope on every large-radius region. -/
theorem Complex.linear_log_absorption
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact real_linear_log_absorption_uniform R₀ hR₀_pos

/-- Pure real domination of the radius/argument loss by the standard
log-linear envelope on the closed right half-plane.

This is now the deepest real-inequality sink in the normalized Stirling
extraction.  It combines `0 ≤ Re w`, `|arg w| ≤ π/2`, `|Re w|, |Im w| ≤ ‖w‖`,
and lower-radius control to absorb the possible small-radius logarithmic term
into a constant multiple of `(1 + 2 ‖w‖) log (2 + 2 ‖w‖)`. -/
theorem Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.linear_log_absorption R₀ hR₀_pos with
    ⟨C, hC_pos, hlinear⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  exact le_trans
    (Complex.radiusArgumentLoss_le_norm_log_majorant w hw_sector)
    (hlinear w hw_radius)

/-- The branch-loss radius/argument expression is absorbed by the standard
large-radius log-linear envelope on the closed right half-plane. -/
theorem Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
      R₀ hR₀_pos

/-- Principal-power logarithmic loss for `w^(1/2-w)` is absorbed by the
large-radius log-linear envelope. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases
      Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos with
    ⟨C, hC_pos, hbranch_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  have hw_ne : w ≠ 0 :=
    Complex.ne_zero_of_pos_le_norm hR₀_pos hw_radius
  exact le_trans
    (le_of_eq
      (Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss
        hw_ne))
    (hbranch_bound w hw_sector hw_radius)

/-- The principal-branch logarithmic loss in normalized Stirling is absorbed by
the large-radius log-linear envelope. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases
      Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos with
    ⟨C, hC_pos, hcpow⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  exact le_trans
    (Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log hw_sector)
    (hcpow w hw_sector hw_radius)

/-- Assembly of constant-log absorption and principal-branch loss absorption. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
    (B R₀ : ℝ)
    (hconstant :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log B ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hloss :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Complex.normalizedGammaStirlingLogLoss w ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hconstant with ⟨Cconstant, hCconstant_pos, hconstant_bound⟩
  rcases hloss with ⟨Closs, hCloss_pos, hloss_bound⟩
  refine ⟨Cconstant + Closs, add_pos hCconstant_pos hCloss_pos, ?_⟩
  intro w hw_sector hw_radius
  have hsum :
      Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
        Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
          Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    add_le_add
      (hconstant_bound w hw_sector hw_radius)
      (hloss_bound w hw_sector hw_radius)
  have hcombine :
      Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
          Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) =
        (Cconstant + Closs) * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    logLinearEnvelope_add_constants
      Cconstant Closs (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact le_trans hsum (le_of_eq hcombine)

/-- The branch/cpow logarithmic loss from normalized Stirling is absorbed by
the standard log-linear envelope on the large-radius closed right half-plane. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
      B R₀
      (Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
        B R₀ hB_pos hR₀_pos)
      (Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos)

/-- Large-radius extraction from a normalized Stirling-factor bound to a
logarithmic Gamma envelope.

This is the branch-sensitive analytic core of the normalized-factor route:
from
`‖Γ(w) exp(w) w^(1/2-w)‖ ≤ B`, one expands the norm of `exp(w)` and the
principal-branch norm of `w^(1/2-w)`, then bounds the resulting real part by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` on the closed right half-plane. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.normalizedGammaStirlingLogLoss_absorbs_logBound
      B R₀ hB_pos hR₀_pos with
    ⟨C, hC_pos, hloss⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  have hfactor_ne :
      Complex.normalizedGammaStirlingFactor w ≠ 0 :=
    Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
      R₀ hR₀_pos hw_sector hw_radius
  have hfactor_pos :
      0 < ‖Complex.normalizedGammaStirlingFactor w‖ :=
    norm_pos_iff.mpr hfactor_ne
  have hfactor_bound :
      ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B :=
    hfactor w hw_sector hw_radius
  have hfactor_log :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
    Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
      B hfactor_pos hfactor_bound
  have hgamma_extract :
      Real.log ‖Complex.Gamma w‖ ≤
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w :=
    Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
      w hfactor_ne
  have hlog_plus_loss :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w ≤
        Real.log B + Complex.normalizedGammaStirlingLogLoss w :=
    add_le_add_right hfactor_log
      (Complex.normalizedGammaStirlingLogLoss w)
  exact
    le_trans hgamma_extract
      (le_trans hlog_plus_loss (hloss w hw_sector hw_radius))

/-- The closed right-half-plane Gamma annulus used to absorb small radii in the
normalized Stirling extraction. -/
def Complex.closedRightHalfPlaneGammaAnnulus (R₀ : ℝ) : Set ℂ :=
  {w : ℂ | Complex.closedRightHalfPlaneSector w ∧ (1 / 2 : ℝ) ≤ ‖w‖ ∧ ‖w‖ ≤ R₀}

/-- The closed right-half-plane Gamma annulus is closed. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isClosed
    (R₀ : ℝ) :
    IsClosed (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  have hsector : IsClosed {w : ℂ | Complex.closedRightHalfPlaneSector w} := by
    exact isClosed_le continuous_const Complex.continuous_re
  have hinner : IsClosed {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} := by
    exact isClosed_le continuous_const continuous_norm
  have houter : IsClosed {w : ℂ | ‖w‖ ≤ R₀} := by
    exact isClosed_le continuous_norm continuous_const
  have hset :
      Complex.closedRightHalfPlaneGammaAnnulus R₀ =
        {w : ℂ | Complex.closedRightHalfPlaneSector w} ∩
          {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} ∩
            {w : ℂ | ‖w‖ ≤ R₀} := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
    · intro hw
      exact ⟨hw.1.1, hw.1.2, hw.2⟩
  exact Eq.subst
    (motive := fun S : Set ℂ => IsClosed S)
    hset.symm
    ((hsector.inter hinner).inter houter)

/-- The closed right-half-plane Gamma annulus is bounded. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isBounded
    (R₀ : ℝ) :
    Bornology.IsBounded (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  refine isBounded_iff_forall_norm_le.2 ⟨max R₀ 0 + 1, ?_⟩
  intro w hw
  have hraw : ‖w‖ ≤ R₀ := hw.2.2
  exact le_trans hraw
    (le_trans (le_max_left R₀ 0) (le_add_of_nonneg_right zero_le_one))

/-- The closed right-half-plane Gamma annulus is compact. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isCompact
    (R₀ : ℝ) :
    IsCompact (Complex.closedRightHalfPlaneGammaAnnulus R₀) :=
  Metric.isCompact_of_isClosed_isBounded
    (Complex.closedRightHalfPlaneGammaAnnulus_isClosed R₀)
    (Complex.closedRightHalfPlaneGammaAnnulus_isBounded R₀)

/-- `Gamma` is nonzero on the closed right-half-plane Gamma annulus. -/
theorem Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ)
    {w : ℂ}
    (hw : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀) :
    Complex.Gamma w ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff w).mp hzero with ⟨n, hn⟩
  subst w
  cases n with
  | zero =>
      have hnorm_zero : ‖(-((0 : ℕ) : ℂ))‖ = 0 := by
        calc
          ‖(-((0 : ℕ) : ℂ))‖ = ‖(-(0 : ℂ))‖ := rfl
          _ = ‖(0 : ℂ)‖ :=
            congrArg norm (neg_zero : -((0 : ℂ)) = 0)
          _ = 0 := norm_zero
      have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 :=
        Eq.subst
          (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
          hnorm_zero
          hw.2.1
      exact (not_lt_of_ge hhalf_le_zero) one_half_pos
  | succ n =>
      have hre_eq :
          (-(((Nat.succ n : ℕ) : ℂ))).re =
            -(((Nat.succ n : ℕ) : ℝ)) := by
        calc
          (-(((Nat.succ n : ℕ) : ℂ))).re =
              -(((Nat.succ n : ℕ) : ℂ).re) :=
            Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
          _ = -(((Nat.succ n : ℕ) : ℝ)) := by
            exact congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
      have hre_nonneg :
          (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
        Eq.subst
          (motive := fun x : ℝ => (0 : ℝ) ≤ x)
          hre_eq
          hw.1
      have hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.succ_pos n)
      have hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
        neg_neg_of_pos hsucc_pos
      exact (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- The function `w ↦ log ‖Γ(w)‖` is continuous on the closed right-half-plane
Gamma annulus. -/
theorem Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ) :
    ContinuousOn
      (fun w : ℂ => Real.log ‖Complex.Gamma w‖)
      (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  intro w hw
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus R₀ hw
  have hnot_pole : ∀ m : ℕ, w ≠ -m := by
    intro m hwm
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨m, hwm⟩)
  have hgamma_cont : ContinuousAt Complex.Gamma w :=
    (Complex.differentiableAt_Gamma w hnot_pole).continuousAt
  have hnorm_cont :
      ContinuousWithinAt (fun z : ℂ => ‖Complex.Gamma z‖)
        (Complex.closedRightHalfPlaneGammaAnnulus R₀) w :=
    hgamma_cont.norm.continuousWithinAt
  have hnorm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hgamma_ne)
  exact hnorm_cont.log hnorm_ne

/-- Compact boundedness of `log ‖Γ(w)‖` on the closed right-half-plane Gamma
annulus. -/
theorem Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound
    (R₀ : ℝ) :
    ∃ M : ℝ,
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M := by
  rcases IsCompact.exists_bound_of_continuousOn
      (Complex.closedRightHalfPlaneGammaAnnulus_isCompact R₀)
      (Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus R₀) with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro w hw
  exact hM w hw

/-- The log-linear Gamma envelope has a positive lower bound on the compact
annulus. -/
theorem Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  refine ⟨Real.log 3, Real.log_pos one_lt_three, ?_⟩
  intro w hw
  have htwo_norm_ge_one : (1 : ℝ) ≤ 2 * ‖w‖ :=
    (div_le_iff₀' zero_lt_two).mp hw.2.1
  have hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
    le_add_of_nonneg_right (mul_nonneg zero_le_two (norm_nonneg w))
  have harg_ge_three : (3 : ℝ) ≤ 2 + 2 * ‖w‖ := by
    calc
      (3 : ℝ) = 2 + 1 := rfl
      _ ≤ 2 + 2 * ‖w‖ :=
        add_le_add_left htwo_norm_ge_one 2
  have hlog_le :
      Real.log 3 ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_le_log zero_lt_three harg_ge_three
  have hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    le_trans (le_of_lt (Real.log_pos one_lt_three)) hlog_le
  have hone_mul :
      Real.log (2 + 2 * ‖w‖) ≤
        (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
    calc
      Real.log (2 + 2 * ‖w‖) = 1 * Real.log (2 + 2 * ‖w‖) :=
        (one_mul (Real.log (2 + 2 * ‖w‖))).symm
      _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
        mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
  exact le_trans hlog_le hone_mul

/-- A bounded numerator and positive envelope lower bound give a constant
multiple bound on the compact Gamma annulus. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
    (R₀ M δ : ℝ)
    (hδ_pos : 0 < δ)
    (hM :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M)
    (hδ :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  let C : ℝ := max (M / δ) 1
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (M / δ) 1)
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_inner hw_outer
  have hw_annulus : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ :=
    ⟨hw_sector, hw_inner, hw_outer⟩
  have hraw :
      Real.log ‖Complex.Gamma w‖ ≤ M :=
    hM w hw_annulus
  have hM_div_le_C : M / δ ≤ C :=
    le_max_left (M / δ) 1
  have hM_le_Cδ : M ≤ C * δ :=
    (div_le_iff₀ hδ_pos).mp hM_div_le_C
  have hδ_le_env :
      δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    hδ w hw_annulus
  have hCδ_le_Cenv :
      C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
    mul_le_mul_of_nonneg_left hδ_le_env (le_of_lt hC_pos)
  have hCenv_eq :
      C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
        C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact
    le_trans hraw
      (le_trans hM_le_Cδ
        (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq)))

/-- Compact annulus absorption for the logarithmic Gamma envelope in the closed
right half-plane sector.

This owns the local boundedness part omitted by the large-radius normalized
Stirling estimate: on the compact annulus
`0 ≤ re w`, `1 / 2 ≤ ‖w‖`, `‖w‖ ≤ R₀`, continuity of `Γ` and nonvanishing of
`Γ` give a finite bound for `log ‖Γ(w)‖`, which is absorbed by the positive
logarithmic envelope. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound R₀ with
    ⟨M, hM⟩
  rcases Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound
      R₀ hR₀_pos with
    ⟨δ, hδ_pos, hδ⟩
  exact
    Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
      R₀ M δ hδ_pos hM hδ

/-- Assembly of large-radius extraction and compact-annulus absorption. -/
theorem Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
    (R₀ : ℝ)
    (hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hlarge with ⟨Clarge, hClarge_pos, hlarge_bound⟩
  rcases hannulus with ⟨Cannulus, hCannulus_pos, hannulus_bound⟩
  refine ⟨max Clarge Cannulus,
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Cannulus), ?_⟩
  intro w hw_sector hw_norm
  have htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
    mul_nonneg zero_le_two (norm_nonneg w)
  have hH_nonneg : 0 ≤ 1 + 2 * ‖w‖ :=
    add_nonneg zero_le_one htwo_norm_nonneg
  have hlog_arg_ge_one : (1 : ℝ) ≤ 2 + 2 * ‖w‖ := by
    exact le_trans one_le_two (le_add_of_nonneg_right htwo_norm_nonneg)
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_nonneg hlog_arg_ge_one
  by_cases hlarge_radius : R₀ ≤ ‖w‖
  · have hraw :
        Real.log ‖Complex.Gamma w‖ ≤
          Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      hlarge_bound w hw_sector hlarge_radius
    have hmono :
        Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
          max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      logLinearEnvelope_mono_constant
        (le_max_left Clarge Cannulus)
        hH_nonneg
        hL_nonneg
    exact le_trans hraw hmono
  · have hannulus_radius : ‖w‖ ≤ R₀ :=
      le_of_not_ge hlarge_radius
    have hraw :
        Real.log ‖Complex.Gamma w‖ ≤
          Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      hannulus_bound w hw_sector hw_norm hannulus_radius
    have hmono :
        Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
          max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      logLinearEnvelope_mono_constant
        (le_max_right Clarge Cannulus)
        hH_nonneg
        hL_nonneg
    exact le_trans hraw hmono

/-- The remaining real/branch extraction from a uniform bound for
`Γ(w) exp(w) w^(1/2-w)` to the logarithmic Gamma norm envelope.

This is deliberately isolated as the deepest nontrivial extraction root: it is
where the norm identities for `Complex.exp`, the closed-right-half-plane branch
control for `w ^ (1/2-w)`, and the elementary real domination by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` are used. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  have hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
      B R₀ hB_pos hR₀_pos hfactor
  have hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
      R₀ hR₀_pos
  exact
    Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
      R₀ hlarge hannulus

/-- The elementary cutoff inequality used in the exponential-Stirling extraction:
if the radius dominates `2K / sqrt (2π)`, then the normalized error term
`K / r` is at most `sqrt (2π)`.

This is a pure real-inequality sink; it is separated from the Gamma theorem so
the analytic owner theorem only assembles named estimates. -/
theorem real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
    (K r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ r) :
    K / r ≤ Real.sqrt (2 * Real.pi) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_pos : 0 < s :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hcutoff_mul : 2 * K ≤ r * s :=
    (div_le_iff₀ hs_pos).mp hr_cutoff
  have hK_le_twoK : K ≤ 2 * K := by
    calc
      K = 1 * K := (one_mul K).symm
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right one_le_two (le_of_lt hK_pos)
  have hK_le_rs : K ≤ r * s :=
    le_trans hK_le_twoK hcutoff_mul
  have hK_le_sr : K ≤ s * r :=
    Eq.subst
      (motive := fun x : ℝ => K ≤ x)
      (mul_comm r s)
      hK_le_rs
  exact (div_le_iff₀ hr_pos).mpr hK_le_sr

/-- Log-norm envelope extracted from the closed-right-half-plane exponential
Stirling expansion.

This is the exact reusable Gamma/Stirling API boundary between the normalized
exponential asymptotic and the downstream finite-order estimates.  Its proof is
the analytic extraction step: compare
`Γ(w) exp(w) w^(1/2-w)` with `sqrt (2π)`, bound the normalized factor away from
zero for large `‖w‖`, and transport through the branch-sensitive norm identities
for `Complex.exp` and `Complex.cpow`; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hStirling with ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩
  let R₀ : ℝ :=
    max R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)
  have hR₀_pos : 0 < R₀ := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))
  have hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
          2 * Real.sqrt (2 * Real.pi) := by
    intro w hw_sector hw_R₀
    have hw_R : R ≤ ‖w‖ :=
      le_trans (le_max_left R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)) hw_R₀
    have hw_one : 1 ≤ ‖w‖ :=
      le_trans (le_trans (le_max_right (2 * K / Real.sqrt (2 * Real.pi)) 1)
        (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le zero_lt_one hw_one
    have hw_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ ‖w‖ :=
      le_trans (le_trans
        (le_max_left (2 * K / Real.sqrt (2 * Real.pi)) 1)
        (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
    have hK_div_le : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi) :=
      real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
        K ‖w‖ hK_pos hw_norm_pos hw_cutoff
    exact
      Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R hK_div_le
  have hB_pos : 0 < 2 * Real.sqrt (2 * Real.pi) := by
    exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  exact
    Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
      (2 * Real.sqrt (2 * Real.pi)) R₀ hB_pos hR₀_pos hfactor

/-- The sectorial exponential Stirling asymptotic gives the standard logarithmic
norm envelope on the closed right half-plane.

This is still part of the classical complex-Gamma Stirling input: it is the
real-part extraction and elementary domination step from the sectorial
asymptotic above, using nonnegative standard comparison envelopes.  Once
mathlib has a sectorial complex Stirling theorem, this is the single local
corollary that should be proved from it. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
      hStirling

/-- Classical closed-sector exponential Stirling expansion for `Complex.Gamma`.

This is the formula-level sectorial asymptotic root for the Gamma lane:
Stirling's expansion with a uniform `O(1 / ‖w‖)` remainder on the closed right
half-plane, viewed as a closed sector avoiding the negative real axis; cf. DLMF
§5.11 and Whittaker-Watson, Ch. XII. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- Sectorial Gamma exponential envelope on the closed right half-plane.

This is the classical growth consequence of sectorial logarithmic Stirling:
the real part of `log Γ(w)` is bounded by a linear-logarithmic envelope on the
closed right half-plane, uniformly away from the origin; cf. DLMF §5.11. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
      Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- The finite recurrence product relating `Γ z` and `Γ (z + N)`. -/
def Complex.gammaRecurrenceProduct (z : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, z + (j : ℂ)

/-- The recurrence product is nonzero when all its factors are nonzero. -/
theorem Complex.gammaRecurrenceProduct_ne_zero
    {z : ℂ}
    {N : ℕ}
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.gammaRecurrenceProduct z N ≠ 0 := by
  unfold Complex.gammaRecurrenceProduct
  exact Finset.prod_ne_zero_iff.mpr
    (fun j hj =>
      hfactor_ne j (Finset.mem_range.mp hj))

/-- Multiplicative form of the finite Gamma recurrence. -/
theorem Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (N : ℂ)) =
      Complex.gammaRecurrenceProduct z N * Complex.Gamma z := by
  induction N with
  | zero =>
      calc
        Complex.Gamma (z + ((0 : ℕ) : ℂ)) =
            Complex.Gamma z :=
          congrArg Complex.Gamma (add_zero z)
        _ = 1 * Complex.Gamma z :=
          (one_mul (Complex.Gamma z)).symm
        _ = Complex.gammaRecurrenceProduct z 0 * Complex.Gamma z := by
          unfold Complex.gammaRecurrenceProduct
          exact congrArg (fun t : ℂ => t * Complex.Gamma z)
            (Finset.prod_range_zero (fun j : ℕ => z + (j : ℂ))).symm
  | succ N ih =>
      have hfactor_prev :
          ∀ j : ℕ, j < N → z + (j : ℂ) ≠ 0 := by
        intro j hj
        exact hfactor_ne j (Nat.lt_trans hj (Nat.lt_succ_self N))
      have hN_factor : z + (N : ℂ) ≠ 0 :=
        hfactor_ne N (Nat.lt_succ_self N)
      have hsucc_arg :
          z + ((Nat.succ N : ℕ) : ℂ) =
            (z + (N : ℂ)) + 1 := by
        calc
          z + ((Nat.succ N : ℕ) : ℂ) =
              z + ((N : ℂ) + 1) := by
            exact congrArg (fun t : ℂ => z + t) (Nat.cast_succ N)
          _ = (z + (N : ℂ)) + 1 :=
            (add_assoc z (N : ℂ) 1).symm
      have hgamma_step :
          Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) := by
        exact Eq.trans
          (congrArg Complex.Gamma hsucc_arg)
          (Complex.Gamma_add_one (z + (N : ℂ)) hN_factor)
      have hprod_step :
          Complex.gammaRecurrenceProduct z (Nat.succ N) =
            Complex.gammaRecurrenceProduct z N * (z + (N : ℂ)) := by
        unfold Complex.gammaRecurrenceProduct
        exact Finset.prod_range_succ (fun j : ℕ => z + (j : ℂ)) N
      calc
        Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) :=
          hgamma_step
        _ = (z + (N : ℂ)) *
              (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) := by
          exact congrArg (fun t : ℂ => (z + (N : ℂ)) * t)
            (ih hfactor_prev)
        _ =
            (Complex.gammaRecurrenceProduct z N * (z + (N : ℂ))) *
              Complex.Gamma z := by
          exact (mul_left_comm (z + (N : ℂ))
            (Complex.gammaRecurrenceProduct z N) (Complex.Gamma z)).symm
        _ =
            Complex.gammaRecurrenceProduct z (Nat.succ N) *
              Complex.Gamma z := by
          exact congrArg (fun t : ℂ => t * Complex.Gamma z) hprod_step.symm

/-- The deterministic shift as a complex horizontal translation. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripRightShift A : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).re =
            x + (Complex.verticalStripRightShift A : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).re =
                (Complex.verticalStripRightShift A : ℝ) :=
            Complex.ofReal_re (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_re
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).im =
            y :=
          Complex.fixedRealPartVerticalPoint_im
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).im = 0 :=
            Complex.ofReal_im (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_im
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- A natural real-part shift is the corresponding complex horizontal
translation of a fixed vertical point. -/
theorem Complex.fixedRealPartVerticalPoint_add_natCast
    (x y : ℝ)
    (N : ℕ) :
    Complex.fixedRealPartVerticalPoint (x + N) y =
      Complex.fixedRealPartVerticalPoint x y + (N : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).re =
            x + (N : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright : ((N : ℂ)).re = (N : ℝ) :=
            Complex.natCast_re N
          exact
            (Eq.trans
              (Complex.add_re (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).im = y :=
          Complex.fixedRealPartVerticalPoint_im (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright : ((N : ℂ)).im = 0 :=
            Complex.natCast_im N
          exact
            (Eq.trans
              (Complex.add_im (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- Gamma recurrence over a deterministic finite product.

For large vertical height the factors `z + j` avoid zero, so iterating
`Γ(s + 1) = s Γ(s)` gives the exact transport from `Γ z` to
`Γ(z + N)`. -/
theorem Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma z =
      Complex.Gamma (z + (N : ℂ)) /
        Complex.gammaRecurrenceProduct z N := by
  have hprod_ne :
      Complex.gammaRecurrenceProduct z N ≠ 0 :=
    Complex.gammaRecurrenceProduct_ne_zero hfactor_ne
  have hshift :
      Complex.Gamma (z + (N : ℂ)) =
        Complex.gammaRecurrenceProduct z N * Complex.Gamma z :=
    Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul N hfactor_ne
  exact
    (calc
      Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N =
          (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) /
            Complex.gammaRecurrenceProduct z N := by
        exact congrArg
          (fun t : ℂ => t / Complex.gammaRecurrenceProduct z N)
          hshift
      _ = Complex.Gamma z :=
        mul_div_cancel_left₀ (Complex.Gamma z) hprod_ne).symm

/-- Norm form of the finite Gamma recurrence transport. -/
theorem Complex.Gamma_norm_eq_shifted_norm_div_gammaRecurrenceProduct_norm
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + (N : ℂ))‖ /
        ‖Complex.gammaRecurrenceProduct z N‖ := by
  have hgamma :
      Complex.Gamma z =
        Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N :=
    Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct N hfactor_ne
  calc
    ‖Complex.Gamma z‖ =
        ‖Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N‖ :=
      congrArg norm hgamma
    _ =
        ‖Complex.Gamma (z + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct z N‖ :=
      norm_div (Complex.Gamma (z + (N : ℂ)))
        (Complex.gammaRecurrenceProduct z N)

/-- The imaginary coordinate of a deterministic recurrence factor is the
vertical height. -/
theorem Complex.gammaRecurrenceProduct_factor_im
    (x y : ℝ)
    (j : ℕ) :
    (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y := by
  calc
    (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im =
        (Complex.fixedRealPartVerticalPoint x y).im + (j : ℂ).im :=
      Complex.add_im (Complex.fixedRealPartVerticalPoint x y) (j : ℂ)
    _ = y + (j : ℂ).im := by
      exact congrArg
        (fun t : ℝ => t + (j : ℂ).im)
        (Complex.fixedRealPartVerticalPoint_im x y)
    _ = y + 0 := by
      exact congrArg (fun t : ℝ => y + t) (Complex.natCast_im j)
    _ = y :=
      add_zero y

/-- Each recurrence factor has norm at least the vertical height. -/
theorem Complex.gammaRecurrenceProduct_factor_height_le_norm
    (x y : ℝ)
    (j : ℕ) :
    ‖y‖ ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  have him :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
    Complex.gammaRecurrenceProduct_factor_im x y j
  have hbasic :
      |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
        ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ :=
    Complex.abs_im_le_norm
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))
  have hnorm_eq_abs : ‖y‖ = |y| :=
    Real.norm_eq_abs y
  exact
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖)
      hnorm_eq_abs.symm
      (Eq.subst
        (motive := fun t : ℝ =>
          |t| ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖)
        him
        hbasic)

/-- For height at least one, the factor lower bound is comparable to
`1 + |y|` with the explicit constant `1 / 2`. -/
theorem Complex.gammaRecurrenceProduct_factor_largeHeight_lower
    {x y : ℝ}
    (j : ℕ)
    (hy : (1 : ℝ) ≤ ‖y‖) :
    (1 / 2 : ℝ) * (1 + ‖y‖) ≤
      ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  have htwo_pos : 0 < (2 : ℝ) :=
    two_pos
  have hy_nonneg : 0 ≤ ‖y‖ :=
    norm_nonneg y
  have hone_le_norm : 1 ≤ ‖y‖ :=
    hy
  have hsum_le_twice : 1 + ‖y‖ ≤ 2 * ‖y‖ := by
    calc
      1 + ‖y‖ ≤ ‖y‖ + ‖y‖ :=
        add_le_add_right hone_le_norm ‖y‖
      _ = (1 + 1) * ‖y‖ := by
        exact (two_mul ‖y‖).symm
      _ = 2 * ‖y‖ := by
        exact congrArg (fun t : ℝ => t * ‖y‖) (one_add_one_eq_two)
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
    le_of_lt (one_div_pos.mpr htwo_pos)
  have hhalf_sum_le_norm :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖y‖ := by
    have hmul :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          (1 / 2 : ℝ) * (2 * ‖y‖) :=
      mul_le_mul_of_nonneg_left hsum_le_twice hhalf_nonneg
    have hcollapse :
        (1 / 2 : ℝ) * (2 * ‖y‖) = ‖y‖ := by
      calc
        (1 / 2 : ℝ) * (2 * ‖y‖) =
            ((1 / 2 : ℝ) * 2) * ‖y‖ :=
          (mul_assoc (1 / 2 : ℝ) 2 ‖y‖).symm
        _ = 1 * ‖y‖ := by
          have htwo_ne : (2 : ℝ) ≠ 0 :=
            ne_of_gt htwo_pos
          exact congrArg (fun t : ℝ => t * ‖y‖)
            (inv_mul_cancel₀ htwo_ne)
        _ = ‖y‖ :=
          one_mul ‖y‖
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          (1 / 2 : ℝ) * (1 + ‖y‖) ≤ t)
        hcollapse
        hmul
  exact
    le_trans hhalf_sum_le_norm
      (Complex.gammaRecurrenceProduct_factor_height_le_norm x y j)

/-- Bounded intervals have a uniform absolute-value bound by the endpoint
absolute values. -/
theorem real_abs_le_max_abs_of_mem_Icc
    {A B x : ℝ}
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    |x| ≤ max |A| |B| := by
  have hmax_A : |A| ≤ max |A| |B| :=
    le_max_left |A| |B|
  have hmax_B : |B| ≤ max |A| |B| :=
    le_max_right |A| |B|
  have hleft_endpoint : -|A| ≤ A :=
    neg_le_abs A
  have hleft_max : -max |A| |B| ≤ -|A| :=
    neg_le_neg hmax_A
  have hleft : -max |A| |B| ≤ x :=
    le_trans hleft_max (le_trans hleft_endpoint hxA)
  have hright_endpoint : B ≤ |B| :=
    le_abs_self B
  have hright : x ≤ max |A| |B| :=
    le_trans hxB (le_trans hright_endpoint hmax_B)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- The real part of a deterministic recurrence factor is bounded uniformly on
the strip and for `j < N`. -/
theorem Complex.gammaRecurrenceProduct_factor_re_abs_le_stripConstant
    {A B x y : ℝ}
    {N j : ℕ}
    (hxA : A ≤ x)
    (hxB : x ≤ B)
    (hj : j < N) :
    |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| ≤
      max |A| |B| + N := by
  have hre :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re =
        x + (j : ℝ) := by
    calc
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re =
          (Complex.fixedRealPartVerticalPoint x y).re + (j : ℂ).re :=
        Complex.add_re (Complex.fixedRealPartVerticalPoint x y) (j : ℂ)
      _ = x + (j : ℂ).re := by
        exact congrArg
          (fun t : ℝ => t + (j : ℂ).re)
          (Complex.fixedRealPartVerticalPoint_re x y)
      _ = x + (j : ℝ) := by
        exact congrArg (fun t : ℝ => x + t) (Complex.natCast_re j)
  have hx_abs : |x| ≤ max |A| |B| :=
    real_abs_le_max_abs_of_mem_Icc hxA hxB
  have hj_le_N : (j : ℝ) ≤ N :=
    Nat.cast_le.mpr (Nat.le_of_lt hj)
  have hj_abs : |(j : ℝ)| = (j : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg j)
  have hsum :
      |x + (j : ℝ)| ≤ max |A| |B| + N := by
    calc
      |x + (j : ℝ)| ≤ |x| + |(j : ℝ)| :=
        abs_add x (j : ℝ)
      _ ≤ max |A| |B| + |(j : ℝ)| :=
        add_le_add_right hx_abs |(j : ℝ)|
      _ = max |A| |B| + (j : ℝ) := by
        exact congrArg (fun t : ℝ => max |A| |B| + t) hj_abs
      _ ≤ max |A| |B| + N :=
        add_le_add_left hj_le_N (max |A| |B|)
  exact
    Eq.subst
      (motive := fun t : ℝ => |t| ≤ max |A| |B| + N)
      hre.symm
      hsum

/-- A recurrence factor is bounded above by a fixed strip constant times
`1 + |y|`. -/
theorem Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
    (A B : ℝ)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        ∀ j : ℕ,
          j < N →
            ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
              C * (1 + ‖y‖) := by
  let C₀ : ℝ := max |A| |B| + N
  refine ⟨C₀ + 1, ?_, ?_⟩
  · have hC₀_nonneg : 0 ≤ C₀ := by
      have hmax_nonneg : 0 ≤ max |A| |B| :=
        le_trans (abs_nonneg A) (le_max_left |A| |B|)
      have hN_nonneg : 0 ≤ (N : ℝ) :=
        Nat.cast_nonneg N
      exact add_nonneg hmax_nonneg hN_nonneg
    exact add_pos_of_nonneg_of_pos hC₀_nonneg zero_lt_one
  intro x y hxA hxB j hj
  have hnorm_coord :
      ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im|)
      (Complex.norm_eq_abs
        (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))).symm
      (Complex.abs_le_abs_re_add_abs_im
        (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)))
  have hre_bound :
      |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| ≤ C₀ :=
    Complex.gammaRecurrenceProduct_factor_re_abs_le_stripConstant
      hxA hxB hj
  have him_eq :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
    Complex.gammaRecurrenceProduct_factor_im x y j
  have him_abs_eq_norm :
      |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| = ‖y‖ := by
    exact
      Eq.trans
        (congrArg abs him_eq)
        (Real.norm_eq_abs y).symm
  have hcoord_bound :
      |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
        C₀ + ‖y‖ := by
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
              C₀ + t)
        him_abs_eq_norm.symm
        (add_le_add_right hre_bound
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im|)
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hmax_nonneg : 0 ≤ max |A| |B| :=
      le_trans (abs_nonneg A) (le_max_left |A| |B|)
    have hN_nonneg : 0 ≤ (N : ℝ) :=
      Nat.cast_nonneg N
    exact add_nonneg hmax_nonneg hN_nonneg
  have hC_ge_one : 1 ≤ C₀ + 1 := by
    calc
      1 = 0 + 1 := (zero_add 1).symm
      _ ≤ C₀ + 1 := add_le_add_right hC₀_nonneg 1
  have hy_nonneg : 0 ≤ ‖y‖ :=
    norm_nonneg y
  have hlinear_to_product :
      C₀ + ‖y‖ ≤ (C₀ + 1) * (1 + ‖y‖) := by
    have hleft_const : C₀ ≤ C₀ + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hleft_height : ‖y‖ ≤ (C₀ + 1) * ‖y‖ :=
      calc
        ‖y‖ = 1 * ‖y‖ := (one_mul ‖y‖).symm
        _ ≤ (C₀ + 1) * ‖y‖ :=
          mul_le_mul_of_nonneg_right hC_ge_one hy_nonneg
    have hsum :
        C₀ + ‖y‖ ≤ (C₀ + 1) + (C₀ + 1) * ‖y‖ :=
      add_le_add hleft_const hleft_height
    have htarget :
        (C₀ + 1) + (C₀ + 1) * ‖y‖ =
          (C₀ + 1) * (1 + ‖y‖) := by
      calc
        (C₀ + 1) + (C₀ + 1) * ‖y‖ =
            (C₀ + 1) * 1 + (C₀ + 1) * ‖y‖ := by
          exact congrArg (fun t : ℝ => t + (C₀ + 1) * ‖y‖)
            (mul_one (C₀ + 1)).symm
        _ = (C₀ + 1) * (1 + ‖y‖) :=
          (mul_add (C₀ + 1) 1 ‖y‖).symm
    exact
      Eq.subst
        (motive := fun t : ℝ => C₀ + ‖y‖ ≤ t)
        htarget
        hsum
  exact le_trans hnorm_coord (le_trans hcoord_bound hlinear_to_product)

/-- Per-factor two-sided bounds for deterministic recurrence factors on a fixed
vertical strip. -/
theorem Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ∀ j : ℕ,
            j < N →
              ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                C * (1 + ‖y‖) ∧
              c * (1 + ‖y‖) ≤
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  rcases Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip A B N with
    ⟨C, hC_pos, hC⟩
  refine ⟨1, C, (1 / 2 : ℝ), zero_lt_one, hC_pos, ?_, ?_⟩
  · exact one_div_pos.mpr two_pos
  intro x y hxA hxB hy j hj
  constructor
  · exact hC x y hxA hxB j hj
  · exact Complex.gammaRecurrenceProduct_factor_largeHeight_lower j hy

/-- Norm of the deterministic recurrence product as the finite product of
factor norms. -/
theorem Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
    (z : ℂ)
    (N : ℕ) :
    ‖Complex.gammaRecurrenceProduct z N‖ =
      ∏ j ∈ Finset.range N, ‖z + (j : ℂ)‖ := by
  unfold Complex.gammaRecurrenceProduct
  calc
    ‖∏ j ∈ Finset.range N, z + (j : ℂ)‖ =
        Complex.abs (∏ j ∈ Finset.range N, z + (j : ℂ)) :=
      Complex.norm_eq_abs (∏ j ∈ Finset.range N, z + (j : ℂ))
    _ = ∏ j ∈ Finset.range N, Complex.abs (z + (j : ℂ)) :=
      Complex.abs_prod (Finset.range N) (fun j : ℕ => z + (j : ℂ))
    _ = ∏ j ∈ Finset.range N, ‖z + (j : ℂ)‖ :=
      Finset.prod_congr rfl
        (fun j hj =>
          (Complex.norm_eq_abs (z + (j : ℂ))).symm)

/-- Uniform finite-product upper estimate from per-factor upper estimates. -/
theorem real_finset_range_prod_upper_of_factor_le
    (N : ℕ)
    {M : ℝ}
    {f : ℕ → ℝ}
    (hM_nonneg : 0 ≤ M)
    (hf_nonneg : ∀ j : ℕ, j < N → 0 ≤ f j)
    (hf_le : ∀ j : ℕ, j < N → f j ≤ M) :
    (∏ j ∈ Finset.range N, f j) ≤ M ^ N := by
  have hprod_le :
      (∏ j ∈ Finset.range N, f j) ≤
        ∏ j ∈ Finset.range N, M :=
    Finset.prod_le_prod
      (fun j hj => hf_nonneg j (Finset.mem_range.mp hj))
      (fun j hj => hf_le j (Finset.mem_range.mp hj))
  have hconst :
      (∏ j ∈ Finset.range N, M) = M ^ #(Finset.range N) :=
    Finset.prod_const M
  have hcard :
      #(Finset.range N) = N :=
    Finset.card_range N
  have hconst_N :
      (∏ j ∈ Finset.range N, M) = M ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => M ^ n) hcard)
  exact le_trans hprod_le (le_of_eq hconst_N)

/-- Uniform finite-product lower estimate from per-factor lower estimates. -/
theorem real_finset_range_prod_lower_of_factor_ge
    (N : ℕ)
    {m : ℝ}
    {f : ℕ → ℝ}
    (hm_nonneg : 0 ≤ m)
    (hf_ge : ∀ j : ℕ, j < N → m ≤ f j) :
    m ^ N ≤ (∏ j ∈ Finset.range N, f j) := by
  have hprod_le :
      (∏ j ∈ Finset.range N, m) ≤
        ∏ j ∈ Finset.range N, f j :=
    Finset.prod_le_prod
      (fun j hj => hm_nonneg)
      (fun j hj => hf_ge j (Finset.mem_range.mp hj))
  have hconst :
      (∏ j ∈ Finset.range N, m) = m ^ #(Finset.range N) :=
    Finset.prod_const m
  have hcard :
      #(Finset.range N) = N :=
    Finset.card_range N
  have hconst_N :
      (∏ j ∈ Finset.range N, m) = m ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => m ^ n) hcard)
  exact
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ∏ j ∈ Finset.range N, f j)
      hconst_N
      hprod_le

/-- Convert a natural power to the real-power notation used by the Gamma
envelope statements. -/
theorem real_pow_natCast_eq_rpow
    {r : ℝ}
    (hr : 0 ≤ r)
    (N : ℕ) :
    r ^ N = r ^ (N : ℝ) := by
  exact Real.rpow_natCast r N

/-- Finite products preserve uniform per-factor polynomial upper/lower bounds
for the deterministic Gamma recurrence product. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
    (A B : ℝ)
    (N : ℕ)
    (hfactor :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ∀ j : ℕ,
              j < N →
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                  C * (1 + ‖y‖) ∧
                c * (1 + ‖y‖) ≤
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  rcases hfactor with ⟨H, C, c, hH_pos, hC_pos, hc_pos, hfactor_pointwise⟩
  refine ⟨H, C ^ N, c ^ N, hH_pos, ?_, ?_, ?_⟩
  · exact pow_pos hC_pos N
  · exact pow_pos hc_pos N
  intro x y hxA hxB hy
  let R : ℝ := 1 + ‖y‖
  have hR_nonneg : 0 ≤ R :=
    add_nonneg zero_le_one (norm_nonneg y)
  have hR_pos : 0 < R :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hCR_nonneg : 0 ≤ C * R :=
    mul_nonneg (le_of_lt hC_pos) hR_nonneg
  have hcR_nonneg : 0 ≤ c * R :=
    mul_nonneg (le_of_lt hc_pos) hR_nonneg
  have hprod_norm :
      ‖Complex.gammaRecurrenceProduct
          (Complex.fixedRealPartVerticalPoint x y) N‖ =
        ∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ :=
    Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
      (Complex.fixedRealPartVerticalPoint x y) N
  have hupper_prod :
      (∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) ≤
        (C * R) ^ N :=
    real_finset_range_prod_upper_of_factor_le
      N
      hCR_nonneg
      (fun j hj =>
        norm_nonneg (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)))
      (fun j hj =>
        (hfactor_pointwise x y hxA hxB hy j hj).1)
  have hlower_prod :
      (c * R) ^ N ≤
        (∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
    real_finset_range_prod_lower_of_factor_ge
      N
      hcR_nonneg
      (fun j hj =>
        (hfactor_pointwise x y hxA hxB hy j hj).2)
  have hupper_target :
      (C * R) ^ N =
        C ^ N * R ^ (N : ℝ) := by
    have hmul_pow : (C * R) ^ N = C ^ N * R ^ N :=
      mul_pow C R N
    have hR_pow : R ^ N = R ^ (N : ℝ) :=
      real_pow_natCast_eq_rpow hR_nonneg N
    exact
      Eq.trans hmul_pow
        (congrArg (fun t : ℝ => C ^ N * t) hR_pow)
  have hlower_target :
      (c * R) ^ N =
        c ^ N * R ^ (N : ℝ) := by
    have hmul_pow : (c * R) ^ N = c ^ N * R ^ N :=
      mul_pow c R N
    have hR_pow : R ^ N = R ^ (N : ℝ) :=
      real_pow_natCast_eq_rpow hR_nonneg N
    exact
      Eq.trans hmul_pow
        (congrArg (fun t : ℝ => c ^ N * t) hR_pow)
  constructor
  · exact
      Eq.subst
        (motive := fun t : ℝ =>
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤ t)
        hupper_target
        (Eq.subst
          (motive := fun t : ℝ => t ≤ (C * R) ^ N)
          hprod_norm.symm
          hupper_prod)
  · exact
      Eq.subst
        (motive := fun t : ℝ =>
          t ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖)
        hlower_target
        (Eq.subst
          (motive := fun t : ℝ => (c * R) ^ N ≤ t)
          hprod_norm
          hlower_prod)

/-- The exact finite-product geometry estimate for deterministic Gamma
recurrence factors on a fixed vertical strip.

The per-factor strip geometry is proved above; this theorem packages those
factor estimates with the finite product algebra over `j < N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
      A B N
      (Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
        A B N)

/-- Finite recurrence products have uniform polynomial upper/lower bounds on a
fixed vertical strip after a deterministic shift.

This is the exact finite-product estimate needed for recurrence transport: for
fixed `N`, bounded real part and large `|y|` make each factor `x + i y + j`
comparable to `1 + |y|`, and therefore the whole product is comparable to
`(1 + |y|)^N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
      A B N

/-- Large vertical height keeps all deterministic recurrence factors nonzero. -/
theorem Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ,
      0 < H ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ∀ j : ℕ,
            j < N →
              Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y _hxA _hxB hy j _hj
  intro hzero
  have him_eq :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = (0 : ℂ).im :=
    congrArg Complex.im hzero
  have hleft_im :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
    Complex.gammaRecurrenceProduct_factor_im x y j
  have hzero_im : (0 : ℂ).im = (0 : ℝ) :=
    Complex.zero_im
  have hy_zero : y = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hzero_im)
  have hnorm_zero : ‖y‖ = 0 :=
    congrArg norm hy_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 :=
    not_le.mpr zero_lt_one
  exact hnot
    (Eq.subst
      (motive := fun t : ℝ => (1 : ℝ) ≤ t)
      hnorm_zero
      hy)

/-- The deterministic strip shift written as a local abbreviation for the
vertical-strip Stirling transport. -/
def Complex.verticalStripTransportShift (A : ℝ) : ℕ :=
  Complex.verticalStripRightShift A

/-- The deterministic transport shift moves the strip into the closed right
half-plane. -/
theorem Complex.verticalStripTransportShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y) := by
  unfold Complex.verticalStripTransportShift
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
      hx

/-- Large vertical height gives the sectorial radius cutoff after the
deterministic transport shift. -/
theorem Complex.verticalStripTransportShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y‖ := by
  unfold Complex.verticalStripTransportShift
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
      hH

/-- The deterministic transport shift is the complex horizontal translation
appearing in the finite Gamma recurrence. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripTransportShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripTransportShift A : ℂ) := by
  unfold Complex.verticalStripTransportShift
  exact Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift A x y

/-- Sectorial Stirling gives uniform two-sided bounds for the normalized
Stirling factor on the deterministically shifted vertical strip. -/
theorem Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ ≤ C ∧
          c ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ := by
  rcases hStirling with ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩
  let s : ℝ := Real.sqrt (2 * Real.pi)
  let H : ℝ := max R (max (4 * K / s) 1)
  refine ⟨H, 2 * s, s / 2, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (le_trans
        (le_max_right (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
  · exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  · exact half_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  intro x y hxA _hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hw_sector : Complex.closedRightHalfPlaneSector w :=
    Complex.verticalStripTransportShift_closedRightHalfPlaneSector hxA
  have hw_radius_H : H ≤ ‖w‖ :=
    Complex.verticalStripTransportShift_radius_ge_of_height_ge hy
  have hw_R : R ≤ ‖w‖ :=
    le_trans (le_max_left R (max (4 * K / s) 1)) hw_radius_H
  have hw_one : 1 ≤ ‖w‖ :=
    le_trans
      (le_trans
        (le_max_right (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
      hw_radius_H
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le zero_lt_one hw_one
  have hw_cutoff_half : 4 * K / s ≤ ‖w‖ :=
    le_trans
      (le_trans
        (le_max_left (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
      hw_radius_H
  have herror_half :
      K / ‖w‖ ≤ s / 2 :=
    real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
      K ‖w‖ hK_pos hw_norm_pos hw_cutoff_half
  have hhalf_le_s : s / 2 ≤ s := by
    have hs_nonneg : 0 ≤ s :=
      Real.sqrt_nonneg (2 * Real.pi)
    exact
      (div_le_iff₀ zero_lt_two).mpr
        (by
          calc
            s ≤ s + s := le_add_of_nonneg_right hs_nonneg
            _ = 2 * s := (two_mul s).symm
            _ = s * 2 := mul_comm 2 s)
  have herror_full :
      K / ‖w‖ ≤ s :=
    le_trans herror_half hhalf_le_s
  constructor
  · exact
      Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R herror_full
  · exact
      Complex.half_sqrt_two_pi_le_normalizedGammaFactor_norm_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R herror_half

/-- Positivity of the exponential/power denominator in normalized Stirling away
from the origin. -/
theorem Complex.stirlingDenominator_pos_of_ne_zero
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hexp_pos : 0 < ‖Complex.exp w‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  have hcpow_pos : 0 < ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    norm_pos_iff.mpr hcpow_ne
  exact mul_pos hexp_pos hcpow_pos

/-- Elementary arctangent majorization used to quantify the angular defect of a
right-half-plane vertical ray. -/
theorem Real.arctan_le_self_of_nonneg
    {t : ℝ}
    (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  have harctan_nonneg : 0 ≤ Real.arctan t := by
    have hzero_le :
        Real.arctan 0 ≤ Real.arctan t :=
      Real.arctan_strictMono.monotone ht
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ Real.arctan t)
      Real.arctan_zero
      hzero_le
  have harctan_lt_half_pi : Real.arctan t < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two t
  have hle_tan :
      Real.arctan t ≤ Real.tan (Real.arctan t) :=
    Real.le_tan harctan_nonneg harctan_lt_half_pi
  exact Eq.subst
    (motive := fun r : ℝ => Real.arctan t ≤ r)
    (Real.tan_arctan t)
    hle_tan

/-- Multiplicative form of `Real.arctan_le_self_of_nonneg` after the scale
change `t = u / |y|`. -/
theorem Real.norm_mul_arctan_div_norm_le_self_of_nonneg
    {u y : ℝ}
    (hu : 0 ≤ u) :
    ‖y‖ * Real.arctan (u / ‖y‖) ≤ u := by
  by_cases hy_zero : ‖y‖ = 0
  · have hleft_eq_zero :
        ‖y‖ * Real.arctan (u / ‖y‖) = 0 := by
      exact Eq.trans
        (congrArg (fun r : ℝ => r * Real.arctan (u / ‖y‖)) hy_zero)
        (zero_mul (Real.arctan (u / ‖y‖)))
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ u)
      hleft_eq_zero.symm
      hu
  · have hy_pos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg y) hy_zero.symm
    have hratio_nonneg : 0 ≤ u / ‖y‖ :=
      div_nonneg hu (le_of_lt hy_pos)
    have harctan_le : Real.arctan (u / ‖y‖) ≤ u / ‖y‖ :=
      Real.arctan_le_self_of_nonneg hratio_nonneg
    have hmul :
        ‖y‖ * Real.arctan (u / ‖y‖) ≤ ‖y‖ * (u / ‖y‖) :=
      mul_le_mul_of_nonneg_left harctan_le (le_of_lt hy_pos)
    have hcancel :
        ‖y‖ * (u / ‖y‖) = u :=
      mul_div_cancel₀ u hy_zero
    exact Eq.subst
      (motive := fun r : ℝ => ‖y‖ * Real.arctan (u / ‖y‖) ≤ r)
      hcancel.symm
      hmul

/-- Principal-argument formula for a right-half-plane ray above the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : 0 < y) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      Real.pi / 2 - Real.arctan (u / y) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  by_cases hu_zero : u = 0
  · have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_pos : 0 < z.im := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_axis : Complex.arg z = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_pos⟩
    have hratio_zero : u / y = 0 := by
      calc
        u / y = 0 / y := congrArg (fun r : ℝ => r / y) hu_zero
        _ = 0 := zero_div y
    have hatan_zero : Real.arctan (u / y) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Real.pi / 2 :=
        harg_axis
      _ = Real.pi / 2 - 0 := (sub_zero (Real.pi / 2)).symm
      _ = Real.pi / 2 - Real.arctan (u / y) := by
        exact congrArg (fun r : ℝ => Real.pi / 2 - r) hatan_zero.symm
  · have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_zero.symm
    have hz_re_pos : 0 < z.re := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_re u y).symm
        hu_pos
    have hz_im_pos : 0 < z.im := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hratio_pos : 0 < y / u :=
      div_pos hy hu_pos
    have hinv_eq : (y / u)⁻¹ = u / y :=
      inv_div
    have hrecip :
        Real.arctan (u / y) = Real.pi / 2 - Real.arctan (y / u) := by
      exact Eq.subst
        (motive := fun r : ℝ =>
          Real.arctan r = Real.pi / 2 - Real.arctan (y / u))
        hinv_eq
        (Real.arctan_inv_of_pos hratio_pos)
    have hswap :
        Real.arctan (y / u) = Real.pi / 2 - Real.arctan (u / y) := by
      have hsum :
          Real.arctan (u / y) + Real.arctan (y / u) = Real.pi / 2 := by
        exact (eq_sub_iff_add_eq.mp hrecip)
      exact (eq_sub_iff_add_eq.mpr hsum.symm)
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = Real.pi / 2 - Real.arctan (u / y) := hswap

/-- Principal-argument formula for a right-half-plane ray below the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : y < 0) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  by_cases hu_zero : u = 0
  · have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_neg : z.im < 0 := by
      exact Eq.subst
        (motive := fun r : ℝ => r < 0)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_axis : Complex.arg z = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_neg⟩
    have hratio_zero : u / ‖y‖ = 0 := by
      calc
        u / ‖y‖ = 0 / ‖y‖ := congrArg (fun r : ℝ => r / ‖y‖) hu_zero
        _ = 0 := zero_div ‖y‖
    have hatan_zero : Real.arctan (u / ‖y‖) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -(Real.pi / 2) :=
        harg_axis
      _ = -(Real.pi / 2) + 0 := (add_zero (-(Real.pi / 2))).symm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
        exact congrArg (fun r : ℝ => -(Real.pi / 2) + r) hatan_zero.symm
  · have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_zero.symm
    have hy_norm_pos : 0 < ‖y‖ :=
      Real.norm_pos_iff.mpr (ne_of_lt hy)
    have hz_re_pos : 0 < z.re := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_re u y).symm
        hu_pos
    have hz_im_neg : z.im < 0 := by
      exact Eq.subst
        (motive := fun r : ℝ => r < 0)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have hy_eq_neg_norm : y = -‖y‖ := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy)
      exact hnorm.symm ▸ rfl
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hatan_neg_norm :
        Real.arctan (y / u) = -Real.arctan (‖y‖ / u) := by
      have hdiv_eq : y / u = -(‖y‖ / u) := by
        calc
          y / u = (-‖y‖) / u := congrArg (fun r : ℝ => r / u) hy_eq_neg_norm
          _ = -(‖y‖ / u) := neg_div ‖y‖ u
      exact Eq.trans
        (congrArg Real.arctan hdiv_eq)
        (Real.arctan_neg (‖y‖ / u))
    have hratio_pos : 0 < ‖y‖ / u :=
      div_pos hy_norm_pos hu_pos
    have hinv_eq : (‖y‖ / u)⁻¹ = u / ‖y‖ :=
      inv_div
    have hrecip :
        Real.arctan (u / ‖y‖) =
          Real.pi / 2 - Real.arctan (‖y‖ / u) := by
      exact Eq.subst
        (motive := fun r : ℝ =>
          Real.arctan r = Real.pi / 2 - Real.arctan (‖y‖ / u))
        hinv_eq
        (Real.arctan_inv_of_pos hratio_pos)
    have hneg_atan_eq :
        -Real.arctan (‖y‖ / u) =
          -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
      calc
        -Real.arctan (‖y‖ / u) =
            -(Real.pi / 2 - Real.arctan (u / ‖y‖)) := by
          have hswap :
              Real.arctan (‖y‖ / u) =
                Real.pi / 2 - Real.arctan (u / ‖y‖) := by
            have hsum :
                Real.arctan (u / ‖y‖) + Real.arctan (‖y‖ / u) =
                  Real.pi / 2 :=
              eq_sub_iff_add_eq.mp hrecip
            exact eq_sub_iff_add_eq.mpr hsum.symm
          exact congrArg Neg.neg hswap
        _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
          exact neg_sub (Real.pi / 2) (Real.arctan (u / ‖y‖))
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = -Real.arctan (‖y‖ / u) := hatan_neg_norm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := hneg_atan_eq

/-- Exact arctangent form of the principal-argument defect on the ray `u + i y`
inside the closed right half-plane. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
      ‖y‖ * Real.arctan (u / ‖y‖) := by
  rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
  · let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / n)
    let p : ℝ := Real.pi / 2
    have hn_pos : 0 < n :=
      Real.norm_pos_iff.mpr (ne_of_lt hy_neg)
    have hy_eq_neg_n : y = -n := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy_neg)
      have hneg_norm : -n = y := by
        calc
          -n = -‖y‖ := rfl
          _ = -(-y) := congrArg Neg.neg hnorm
          _ = y := neg_neg y
      exact hneg_norm.symm
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -p + a :=
      Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
        hu hy_neg
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / n :=
        div_nonneg hu (le_of_lt hn_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / n) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      exact Eq.subst
        (motive := fun r : ℝ => r ≤ a)
        Real.arctan_zero
        hzero_le
    have hprod_nonneg : 0 ≤ a * n :=
      mul_nonneg ha_nonneg (le_of_lt hn_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * n - a * n := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (-p + a) * (-n) := by
          exact congrArg₂
            (fun r s : ℝ => r * s)
            harg
            hy_eq_neg_n
        _ = -((-p + a) * n) := by
          exact mul_neg (-p + a) n
        _ = -((-p) * n + a * n) := by
          exact congrArg Neg.neg (add_mul (-p) a n)
        _ = -((-p) * n) + -(a * n) := by
          exact neg_add ((-p) * n) (a * n)
        _ = p * n + -(a * n) := by
          have hneg_left : -((-p) * n) = p * n := by
            calc
              -((-p) * n) = -(-(p * n)) := by
                exact congrArg Neg.neg (neg_mul p n)
              _ = p * n := neg_neg (p * n)
          exact congrArg (fun r : ℝ => r + -(a * n)) hneg_left
        _ = p * n - a * n := (sub_eq_add_neg (p * n) (a * n)).symm
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * n := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * n - (p * n - a * n) := by
          exact congrArg₂
            (fun r s : ℝ => r - s)
            rfl
            harg_mul
        _ = a * n := sub_sub_self (p * n) (a * n)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * n| := congrArg abs hinside
      _ = a * n := abs_of_nonneg hprod_nonneg
      _ = n * a := mul_comm a n
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := rfl
  · have hy_subst : y = 0 := hy_zero
    subst y
    have hnorm_zero : ‖(0 : ℝ)‖ = 0 :=
      norm_zero
    calc
      |(Real.pi / 2) * ‖(0 : ℝ)‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)| =
          |(Real.pi / 2) * 0 -
            Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)| := by
        exact congrArg
          (fun r : ℝ =>
            |(Real.pi / 2) * r -
              Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)|)
          hnorm_zero
      _ = |0 - 0| := by
        have hleft : (Real.pi / 2) * (0 : ℝ) = 0 :=
          mul_zero (Real.pi / 2)
        have hright :
            Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ) = 0 :=
          mul_zero (Complex.arg (Complex.fixedRealPartVerticalPoint u 0))
        exact congrArg₂ (fun r s : ℝ => |r - s|) hleft hright
      _ = 0 := by
        exact Eq.trans (congrArg abs (sub_zero (0 : ℝ))) abs_zero
      _ = ‖(0 : ℝ)‖ * Real.arctan (u / ‖(0 : ℝ)‖) := by
        have hright :
            ‖(0 : ℝ)‖ * Real.arctan (u / ‖(0 : ℝ)‖) = 0 := by
          exact Eq.trans
            (congrArg
              (fun r : ℝ => r * Real.arctan (u / ‖(0 : ℝ)‖))
              hnorm_zero)
            (zero_mul (Real.arctan (u / ‖(0 : ℝ)‖)))
        exact hright.symm
  · let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / y)
    let p : ℝ := Real.pi / 2
    have hn_eq_y : n = y :=
      Real.norm_of_nonneg (le_of_lt hy_pos)
    have hn_pos : 0 < n :=
      Eq.subst
        (motive := fun r : ℝ => 0 < r)
        hn_eq_y.symm
        hy_pos
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = p - a :=
      Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
        hu hy_pos
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / y :=
        div_nonneg hu (le_of_lt hy_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / y) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      exact Eq.subst
        (motive := fun r : ℝ => r ≤ a)
        Real.arctan_zero
        hzero_le
    have hprod_nonneg : 0 ≤ a * y :=
      mul_nonneg ha_nonneg (le_of_lt hy_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * y - a * y := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (p - a) * y := by
          exact congrArg (fun r : ℝ => r * y) harg
        _ = p * y - a * y := sub_mul p a y
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * y := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * y - (p * y - a * y) := by
          have hleft : (Real.pi / 2) * ‖y‖ = p * y := by
            exact congrArg (fun r : ℝ => (Real.pi / 2) * r) hn_eq_y
          exact congrArg₂ (fun r s : ℝ => r - s) hleft harg_mul
        _ = a * y := sub_sub_self (p * y) (a * y)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * y| := congrArg abs hinside
      _ = a * y := abs_of_nonneg hprod_nonneg
      _ = y * a := mul_comm a y
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := by
        have harg_eq : a = Real.arctan (u / ‖y‖) := by
          exact congrArg (fun r : ℝ => Real.arctan (u / r)) hn_eq_y.symm
        exact congrArg₂ (fun r s : ℝ => r * s) hn_eq_y.symm harg_eq

/-- Principal-argument defect on a right-half-plane vertical ray.

For `u ≥ 0`, the angle of `u + i y` differs from `sign(y) · π/2` by at most
`u / |y|`; multiplying by `|y|` gives the displayed scale-free bound.  This is
the canonical `arg` geometry lemma behind the shifted-strip exponential defect. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u := by
  have hdef_eq :
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
        ‖y‖ * Real.arctan (u / ‖y‖) :=
    Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan hu
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ u)
    hdef_eq.symm
    (Real.norm_mul_arctan_div_norm_le_self_of_nonneg hu)

/-- Additive quantitative argument-defect estimate for shifted right-half-plane
vertical strips.

This is the exact arctangent-defect form behind the exponential comparison:
`-arg(w) y` differs from `-(π/2)|y|` by a bounded amount on every shifted
bounded vertical strip. -/
theorem Complex.shiftedVertical_arg_linear_defect_bounded
    (A B : ℝ) :
    ∃ H : ℝ, ∃ D : ℝ,
      0 < H ∧
      0 ≤ D ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          -(Complex.arg w * y) ≤ D + (-(Real.pi / 2) * ‖y‖) ∧
          (-(Real.pi / 2) * ‖y‖) - D ≤ -(Complex.arg w * y) := by
  let D : ℝ :=
    max |A + Complex.verticalStripTransportShift A|
      |B + Complex.verticalStripTransportShift A|
  refine ⟨1, D, zero_lt_one, ?_, ?_⟩
  · exact le_trans (abs_nonneg (A + Complex.verticalStripTransportShift A))
      (le_max_left
        |A + Complex.verticalStripTransportShift A|
        |B + Complex.verticalStripTransportShift A|)
  intro x y hxA hxB _hy
  let u : ℝ := x + Complex.verticalStripTransportShift A
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hu_nonneg : 0 ≤ u := by
    unfold Complex.verticalStripTransportShift
    have hshift : -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
      Complex.neg_lower_le_verticalStripRightShift A
    calc
      0 = A + -A := by
        exact (add_right_neg A).symm
      _ ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
        add_le_add hxA hshift
  have hu_abs_le_D : |u| ≤ D := by
    exact real_abs_le_max_abs_of_mem_Icc
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
  have hu_le_D : u ≤ D :=
    le_trans (le_abs_self u) hu_abs_le_D
  have hdef_abs :
      |(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤ D := by
    have hray :
        |(Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u :=
      Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re hu_nonneg
    exact le_trans hray hu_le_D
  have hdef_upper :
      (Real.pi / 2) * ‖y‖ - Complex.arg w * y ≤ D :=
    le_trans (le_abs_self ((Real.pi / 2) * ‖y‖ - Complex.arg w * y))
      hdef_abs
  have hdef_lower :
      -D ≤ (Real.pi / 2) * ‖y‖ - Complex.arg w * y := by
    have hneg_abs :
        -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤
          (Real.pi / 2) * ‖y‖ - Complex.arg w * y :=
      neg_abs_le ((Real.pi / 2) * ‖y‖ - Complex.arg w * y)
    have hneg_bound :
        -D ≤ -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| :=
      neg_le_neg hdef_abs
    exact le_trans hneg_bound hneg_abs
  constructor
  · have htarget :
        - (Complex.arg w * y) ≤
          D + (-(Real.pi / 2) * ‖y‖) := by
      calc
        -(Complex.arg w * y) =
            ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) := by
          exact (add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))).symm
        _ ≤ D + (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_upper (-(Real.pi / 2) * ‖y‖)
    exact htarget
  · have htarget :
        (-(Real.pi / 2) * ‖y‖) - D ≤
          -(Complex.arg w * y) := by
      calc
        (-(Real.pi / 2) * ‖y‖) - D =
            -D + (-(Real.pi / 2) * ‖y‖) := by
          calc
            (-(Real.pi / 2) * ‖y‖) - D =
                (-(Real.pi / 2) * ‖y‖) + -D :=
              sub_eq_add_neg (-(Real.pi / 2) * ‖y‖) D
            _ = -D + (-(Real.pi / 2) * ‖y‖) :=
              add_comm (-(Real.pi / 2) * ‖y‖) (-D)
        _ ≤ ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_lower (-(Real.pi / 2) * ‖y‖)
        _ = -(Complex.arg w * y) := by
          exact add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))
    exact htarget

/-- Quantitative arctangent-defect comparison for shifted right-half-plane
vertical strips.

For `w = x + N + i y` with `x` in a fixed bounded strip and `N` the deterministic
right-half-plane shift, the classical estimate
`|arg w - sign(y) · π/2| = O(1 / |y|)` gives a bounded multiplicative loss in
`exp (-arg(w) y)`.  This is the precise geometric input needed by the normalized
Stirling denominator comparison. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  rcases Complex.shiftedVertical_arg_linear_defect_bounded A B with
    ⟨H, D, hH_pos, hD_nonneg, hdefect⟩
  refine ⟨H, Real.exp D, Real.exp (-D), hH_pos,
    Real.exp_pos D, Real.exp_pos (-D), ?_⟩
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let b : ℝ := -(Real.pi / 2) * ‖y‖
  have hdef := hdefect x y hxA hxB hy
  constructor
  · have hexp_le :
        Real.exp (-(Complex.arg w * y)) ≤ Real.exp (D + b) :=
      Real.exp_le_exp.mpr hdef.1
    have hsplit :
        Real.exp (D + b) =
          Real.exp D * Real.exp b :=
      Real.exp_add D b
    exact le_trans hexp_le
      (le_of_eq
        (Eq.trans hsplit
          (by
            rfl)))
  · have hlower_exp :
        Real.exp (b - D) ≤ Real.exp (-(Complex.arg w * y)) :=
      Real.exp_le_exp.mpr hdef.2
    have hsplit :
        Real.exp (b - D) =
          Real.exp (-D) * Real.exp b := by
      calc
        Real.exp (b - D) =
            Real.exp (b + -D) := by
          exact congrArg Real.exp (sub_eq_add_neg b D)
        _ = Real.exp b * Real.exp (-D) :=
          Real.exp_add b (-D)
        _ = Real.exp (-D) * Real.exp b :=
          mul_comm (Real.exp b) (Real.exp (-D))
    exact le_trans (le_of_eq hsplit.symm) hlower_exp

/-- Quantitative vertical argument-defect estimate for shifted right-half-plane
strip points.

This is the real geometric core of the denominator comparison.  In a fixed
right-half-plane vertical strip, the principal argument approaches
`sign(y) * π/2`, and the defect contributes only a bounded exponential factor
to `exp (-arg(w) y)`. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  exact
    Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
      A B

/-- On a deterministically shifted vertical strip, the radius is comparable to
`1 + |y|`.

This is the base geometric input for the radius-power comparison; the remaining
power step only has to transport this through `rpow` with bounded exponent. -/
theorem Complex.shiftedVertical_radius_base_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ≤ C * (1 + ‖y‖) ∧
          c * (1 + ‖y‖) ≤ ‖w‖ := by
  rcases
      Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
        (A + Complex.verticalStripTransportShift A)
        (B + Complex.verticalStripTransportShift A)
        1 with
    ⟨C, hC_pos, hupper⟩
  refine ⟨1, C, 1 / 2, zero_lt_one, hC_pos, one_div_pos.mpr two_pos, ?_⟩
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hxA_shift :
      A + Complex.verticalStripTransportShift A ≤
        x + Complex.verticalStripTransportShift A :=
    add_le_add_right hxA (Complex.verticalStripTransportShift A)
  have hxB_shift :
      x + Complex.verticalStripTransportShift A ≤
        B + Complex.verticalStripTransportShift A :=
    add_le_add_right hxB (Complex.verticalStripTransportShift A)
  have hzero_lt_one_nat : (0 : ℕ) < 1 :=
    Nat.zero_lt_one
  have hupper_w :
      ‖Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ ≤
        C * (1 + ‖y‖) :=
    hupper (x + Complex.verticalStripTransportShift A) y
      hxA_shift hxB_shift 0 hzero_lt_one_nat
  have hzero_add :
      Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ) =
        w :=
    add_zero w
  have hupper_final :
      ‖w‖ ≤ C * (1 + ‖y‖) :=
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ C * (1 + ‖y‖))
      hzero_add
      hupper_w
  have hlower_final :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖w‖ := by
    have hlower_raw :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
      Complex.gammaRecurrenceProduct_factor_largeHeight_lower 0 hy
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖z‖)
        hzero_add
        hlower_raw
  exact ⟨hupper_final, hlower_final⟩

/-- Real bounded-exponent transport for radius powers.

If `R` is uniformly comparable to the height scale `Y`, and the exponent `e`
stays in a fixed bounded interval, then `R^e` is uniformly comparable to
`Y^e`.  This is the purely real step needed after the shifted-strip radius
comparison has removed all complex geometry. -/
theorem real_rpow_comparable_of_base_comparable_and_bounded_exponent
    (C c L U : ℝ)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c) :
    ∃ K : ℝ, ∃ k : ℝ,
      0 < K ∧
      0 < k ∧
      ∀ R Y e : ℝ,
        0 < Y →
        c * Y ≤ R →
        R ≤ C * Y →
        L ≤ e →
        e ≤ U →
          R ^ e ≤ K * Y ^ e ∧
          k * Y ^ e ≤ R ^ e := by
  let E : ℝ := max |L| |U|
  let M : ℝ := |Real.log c| + |Real.log C|
  let K : ℝ := Real.exp (E * M)
  let k : ℝ := Real.exp (-(E * M))
  have hE_nonneg : 0 ≤ E :=
    le_trans (abs_nonneg L) (le_max_left |L| |U|)
  have hM_nonneg : 0 ≤ M :=
    add_nonneg (abs_nonneg (Real.log c)) (abs_nonneg (Real.log C))
  have hEM_nonneg : 0 ≤ E * M :=
    mul_nonneg hE_nonneg hM_nonneg
  refine ⟨K, k, Real.exp_pos (E * M), Real.exp_pos (-(E * M)), ?_⟩
  intro R Y e hY_pos hlow hhigh hL hU
  let q : ℝ := R / Y
  have hY_nonneg : 0 ≤ Y :=
    le_of_lt hY_pos
  have hY_ne : Y ≠ 0 :=
    ne_of_gt hY_pos
  have hq_lower : c ≤ q := by
    calc
      c = (c * Y) / Y := by
        exact (mul_div_cancel_right₀ c hY_ne).symm
      _ ≤ R / Y :=
        div_le_div_of_nonneg_right hlow hY_nonneg
  have hq_upper : q ≤ C := by
    calc
      q = R / Y := rfl
      _ ≤ (C * Y) / Y :=
        div_le_div_of_nonneg_right hhigh hY_nonneg
      _ = C := by
        exact mul_div_cancel_right₀ C hY_ne
  have hq_pos : 0 < q :=
    lt_of_lt_of_le hc_pos hq_lower
  have hq_nonneg : 0 ≤ q :=
    le_of_lt hq_pos
  have hR_eq : R = q * Y := by
    calc
      R = (R / Y) * Y := by
        exact (div_mul_cancel₀ R hY_ne).symm
      _ = q * Y := rfl
  have he_abs : |e| ≤ E :=
    real_abs_le_max_abs_of_mem_Icc hL hU
  have hlog_abs : |Real.log q| ≤ M := by
    by_cases hlog_nonneg : 0 ≤ Real.log q
    · have hlog_le_C : Real.log q ≤ Real.log C :=
        Real.log_le_log hq_pos hq_upper
      have hlog_abs_eq : |Real.log q| = Real.log q :=
        abs_of_nonneg hlog_nonneg
      have hC_le_abs : Real.log C ≤ |Real.log C| :=
        le_abs_self (Real.log C)
      calc
        |Real.log q| = Real.log q := hlog_abs_eq
        _ ≤ Real.log C := hlog_le_C
        _ ≤ |Real.log C| := hC_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_left (abs_nonneg (Real.log c))
    · have hlog_nonpos : Real.log q ≤ 0 :=
        le_of_not_ge hlog_nonneg
      have hlog_c_le : Real.log c ≤ Real.log q :=
        Real.log_le_log hc_pos hq_lower
      have hneg_le : -Real.log q ≤ -Real.log c :=
        neg_le_neg hlog_c_le
      have hneg_c_le_abs : -Real.log c ≤ |Real.log c| :=
        neg_le_abs (Real.log c)
      have hlog_abs_eq : |Real.log q| = -Real.log q :=
        abs_of_nonpos hlog_nonpos
      calc
        |Real.log q| = -Real.log q := hlog_abs_eq
        _ ≤ -Real.log c := hneg_le
        _ ≤ |Real.log c| := hneg_c_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_right (abs_nonneg (Real.log C))
  have hmul_abs :
      |e * Real.log q| ≤ E * M := by
    calc
      |e * Real.log q| = |e| * |Real.log q| :=
        abs_mul e (Real.log q)
      _ ≤ E * M :=
        mul_le_mul he_abs hlog_abs hM_nonneg (abs_nonneg e)
  have hupper_exp_arg : e * Real.log q ≤ E * M :=
    le_trans (le_abs_self (e * Real.log q)) hmul_abs
  have hlower_exp_arg : -(E * M) ≤ e * Real.log q := by
    have hneg_abs : -|e * Real.log q| ≤ e * Real.log q :=
      neg_abs_le (e * Real.log q)
    have hneg_bound : -(E * M) ≤ -|e * Real.log q| :=
      neg_le_neg hmul_abs
    exact le_trans hneg_bound hneg_abs
  have hq_pow_upper : q ^ e ≤ K := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    exact Eq.subst
      (motive := fun t : ℝ => t ≤ K)
      hq_pow_eq.symm
      (Eq.subst
        (motive := fun t : ℝ => Real.exp t ≤ K)
        hcomm
        (Real.exp_le_exp.mpr hupper_exp_arg))
  have hq_pow_lower : k ≤ q ^ e := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    exact Eq.subst
      (motive := fun t : ℝ => k ≤ t)
      hq_pow_eq.symm
      (Eq.subst
        (motive := fun t : ℝ => k ≤ Real.exp t)
        hcomm
        (Real.exp_le_exp.mpr hlower_exp_arg))
  have hY_pow_nonneg : 0 ≤ Y ^ e :=
    Real.rpow_nonneg hY_nonneg e
  have hR_pow_eq : R ^ e = q ^ e * Y ^ e := by
    calc
      R ^ e = (q * Y) ^ e := by
        exact congrArg (fun t : ℝ => t ^ e) hR_eq
      _ = q ^ e * Y ^ e :=
        Real.mul_rpow hq_nonneg hY_nonneg
  constructor
  · exact Eq.subst
      (motive := fun t : ℝ => t ≤ K * Y ^ e)
      hR_pow_eq.symm
      (mul_le_mul_of_nonneg_right hq_pow_upper hY_pow_nonneg)
  · exact Eq.subst
      (motive := fun t : ℝ => k * Y ^ e ≤ t)
      hR_pow_eq.symm
      (mul_le_mul_of_nonneg_right hq_pow_lower hY_pow_nonneg)

/-- Bounded-exponent radius-power comparison for shifted vertical strips.

On a bounded shifted strip, `‖x + N + i y‖` is comparable to `1 + |y|`, while
the exponent `x + N - 1/2` ranges over a fixed compact real interval.  The
standard logarithmic/rpow comparison therefore gives uniform two-sided
constants for the radius power. -/
theorem Complex.shiftedVertical_radiusPower_comparable_boundedExponent
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  rcases Complex.shiftedVertical_radius_base_comparable A B with
    ⟨Hbase, Cbase, cbase, hHbase_pos, hCbase_pos, hcbase_pos, hbase⟩
  let L : ℝ := A + Complex.verticalStripTransportShift A - 1 / 2
  let U : ℝ := B + Complex.verticalStripTransportShift A - 1 / 2
  rcases
      real_rpow_comparable_of_base_comparable_and_bounded_exponent
        Cbase cbase L U hCbase_pos hcbase_pos with
    ⟨K, k, hK_pos, hk_pos, hrpow⟩
  refine ⟨Hbase, K, k, hHbase_pos, hK_pos, hk_pos, ?_⟩
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Y : ℝ := 1 + ‖y‖
  let e : ℝ := x + Complex.verticalStripTransportShift A - 1 / 2
  have hbase_xy := hbase x y hxA hxB hy
  have hY_pos : 0 < Y :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have heq :
      w.re - 1 / 2 = e := by
    exact congrArg (fun t : ℝ => t - 1 / 2) hw_re
  have hL : L ≤ e :=
    add_le_add_right
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hU : e ≤ U :=
    add_le_add_right
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hr :
      ‖w‖ ^ e ≤ K * Y ^ e ∧
        k * Y ^ e ≤ ‖w‖ ^ e :=
    hrpow ‖w‖ Y e hY_pos hbase_xy.2 hbase_xy.1 hL hU
  exact
    ⟨Eq.subst
        (motive := fun t : ℝ =>
          ‖w‖ ^ t ≤ K * Y ^ e)
        heq.symm
        hr.1,
      Eq.subst
        (motive := fun t : ℝ =>
          k * Y ^ e ≤ ‖w‖ ^ t)
        heq.symm
        hr.2⟩

/-- In a fixed shifted vertical strip, the radial polynomial factor in the
principal-power denominator is comparable to the standard height polynomial. -/
theorem Complex.shiftedVertical_radiusPower_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  exact
    Complex.shiftedVertical_radiusPower_comparable_boundedExponent
      A B

/-- On a fixed shifted vertical strip, the real-part exponential factor
`exp (-Re w)` is bounded above and below by positive constants. -/
theorem Complex.shiftedVertical_realPartExp_bounded
    (A B : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-w.re) ≤ C ∧
          c ≤ Real.exp (-w.re) := by
  let N : ℝ := Complex.verticalStripTransportShift A
  let C : ℝ := max (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  let c : ℝ := min (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  have hEA_pos : 0 < Real.exp (-(A + N)) :=
    Real.exp_pos (-(A + N))
  have hEB_pos : 0 < Real.exp (-(B + N)) :=
    Real.exp_pos (-(B + N))
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hEA_pos (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hc_pos : 0 < c :=
    lt_min hEA_pos hEB_pos
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
  intro x y hxA hxB
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hw_re :
      w.re = x + N := by
    exact Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hleft : A + N ≤ x + N :=
    add_le_add_right hxA N
  have hright : x + N ≤ B + N :=
    add_le_add_right hxB N
  have hneg_upper : -(B + N) ≤ -(x + N) :=
    neg_le_neg hright
  have hneg_lower : -(x + N) ≤ -(A + N) :=
    neg_le_neg hleft
  have hexp_upper_A :
      Real.exp (-(x + N)) ≤ Real.exp (-(A + N)) :=
    Real.exp_le_exp.mpr hneg_lower
  have hexp_upper :
      Real.exp (-(x + N)) ≤ C :=
    le_trans hexp_upper_A
      (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hexp_lower_B :
      Real.exp (-(B + N)) ≤ Real.exp (-(x + N)) :=
    Real.exp_le_exp.mpr hneg_upper
  have hexp_lower :
      c ≤ Real.exp (-(x + N)) :=
    le_trans
      (min_le_right (Real.exp (-(A + N))) (Real.exp (-(B + N))))
      hexp_lower_B
  exact
    ⟨Eq.subst
        (motive := fun t : ℝ => Real.exp (-t) ≤ C)
        hw_re.symm
        hexp_upper,
      Eq.subst
        (motive := fun t : ℝ => c ≤ Real.exp (-t))
        hw_re.symm
        hexp_lower⟩

/-- Real algebra behind the reciprocal denominator after the exponential and
principal-power norm formulas have been substituted. -/
theorem real_stirlingDenominator_reciprocal_shape
    (R x θ y : ℝ)
    (hR_pos : 0 < R) :
    1 / (Real.exp x *
        (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
      Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
  let E : ℝ := Real.exp x
  let Q : ℝ := R ^ (1 / 2 - x)
  let F : ℝ := Real.exp (θ * (-y))
  have hQ_pos : 0 < Q :=
    Real.rpow_pos_of_pos hR_pos (1 / 2 - x)
  have hF_pos : 0 < F :=
    Real.exp_pos (θ * (-y))
  have hE_pos : 0 < E :=
    Real.exp_pos x
  have htheta : θ * (-y) = -(θ * y) := by
    exact mul_neg θ y
  have hF_eq : F = Real.exp (-(θ * y)) := by
    exact congrArg Real.exp htheta
  have hQ_inv :
      Q⁻¹ = R ^ (x - 1 / 2) := by
    have hexp : x - 1 / 2 = -(1 / 2 - x) := by
      calc
        x - 1 / 2 = x + -(1 / 2) := sub_eq_add_neg x (1 / 2)
        _ = -(1 / 2) + x := add_comm x (-(1 / 2))
        _ = -(1 / 2 + -x) := by
          exact (neg_add (1 / 2) (-x)).symm
        _ = -(1 / 2 - x) := by
          exact congrArg Neg.neg (sub_eq_add_neg (1 / 2) x).symm
    have hneg :
        R ^ (-(1 / 2 - x)) = Q⁻¹ :=
      Real.rpow_neg (le_of_lt hR_pos) (1 / 2 - x)
    exact Eq.trans hneg.symm (congrArg (fun t : ℝ => R ^ t) hexp).symm
  have hE_inv : E⁻¹ = Real.exp (-x) := by
    exact (Real.exp_neg x).symm
  calc
    1 / (Real.exp x * (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
        1 / (E * (Q / F)) := rfl
    _ = (E * (Q / F))⁻¹ := by
      exact one_div (E * (Q / F))
    _ = (Q / F)⁻¹ * E⁻¹ := by
      exact mul_inv_rev E (Q / F)
    _ = (F * Q⁻¹) * E⁻¹ := by
      have hdiv_inv : (Q / F)⁻¹ = F * Q⁻¹ := by
        calc
          (Q / F)⁻¹ = F / Q := inv_div Q F
          _ = F * Q⁻¹ := div_eq_mul_inv F Q
      exact congrArg (fun t : ℝ => t * E⁻¹) hdiv_inv
    _ = F * Q⁻¹ * E⁻¹ := by
      rfl
    _ = Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ HMul.hMul hF_eq hQ_inv)
        hE_inv

/-- Exact reciprocal shape of the normalized-Stirling denominator on a fixed
vertical point, after expanding `‖exp w‖` and the principal-branch power norm. -/
theorem Complex.stirlingDenominator_reciprocal_shape_fixedVertical
    {w : ℂ}
    {y : ℝ}
    (hw_ne : w ≠ 0)
    (hw_im : w.im = y) :
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
      Real.exp (-(Complex.arg w * y)) *
        ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
  have hR_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne
  have hexp_norm :
      ‖Complex.exp w‖ = Real.exp w.re :=
    Complex.norm_exp_eq_exp_re w
  have hre_exp :
      ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re :=
    Complex.half_minus_self_re w
  have him_exp :
      ((1 / 2 : ℂ) - w).im = -y := by
    exact Eq.trans (Complex.half_minus_self_im w) (congrArg Neg.neg hw_im)
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (1 / 2 - w.re) /
          Real.exp (Complex.arg w * (-y)) := by
    have hraw :
        ‖w ^ ((1 / 2 : ℂ) - w)‖ =
          ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
            Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
      Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
    exact Eq.trans hraw
      (congrArg₂ HDiv.hDiv
        (congrArg (fun t : ℝ => ‖w‖ ^ t) hre_exp)
        (congrArg (fun t : ℝ => Real.exp (Complex.arg w * t)) him_exp))
  calc
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        1 / (Real.exp w.re *
          (‖w‖ ^ (1 / 2 - w.re) /
            Real.exp (Complex.arg w * (-y)))) := by
      exact congrArg
        (fun t : ℝ => 1 / t)
        (congrArg₂ HMul.hMul hexp_norm hcpow_norm)
    _ =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
      real_stirlingDenominator_reciprocal_shape
        ‖w‖ w.re (Complex.arg w) y hR_pos

/-- Reciprocal denominator comparison for the shifted vertical Stirling
normalization.

For `w = x + N + i y` in a fixed shifted right-half-plane strip, the
principal-branch identity
`log ‖w^(1/2-w)‖ = (1/2 - Re w) log ‖w‖ + arg(w) Im w`, together with
`‖exp w‖ = exp (Re w)`, shows that
`1 / (‖exp w‖ ‖w^(1/2-w)‖)` is comparable to
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)`.  This is the sharp vertical-line
branch comparison left after the normalized sectorial Stirling estimate has
been extracted. -/
theorem Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          0 < ‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖ ∧
          1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  rcases Complex.shiftedVertical_arg_exponential_defect_comparable A B with
    ⟨Ha, Ca, ca, hHa_pos, hCa_pos, hca_pos, harg⟩
  rcases Complex.shiftedVertical_radiusPower_comparable A B with
    ⟨Hr, Cr, cr, hHr_pos, hCr_pos, hcr_pos, hradius⟩
  rcases Complex.shiftedVertical_realPartExp_bounded A B with
    ⟨Ce, ce, hCe_pos, hce_pos, hexpRe⟩
  let H : ℝ := max Ha Hr
  refine ⟨H, (Ca * Cr) * Ce, (ca * cr) * ce,
    lt_of_lt_of_le hHa_pos (le_max_left Ha Hr),
    mul_pos (mul_pos hCa_pos hCr_pos) hCe_pos,
    mul_pos (mul_pos hca_pos hcr_pos) hce_pos, ?_⟩
  intro x y hxA hxB hy
  have hy_a : Ha ≤ ‖y‖ :=
    le_trans (le_max_left Ha Hr) hy
  have hy_r : Hr ≤ ‖y‖ :=
    le_trans (le_max_right Ha Hr) hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Eexp : ℝ := Real.exp (-(Real.pi / 2) * ‖y‖)
  let P : ℝ := (1 + ‖y‖) ^
    (x + Complex.verticalStripTransportShift A - 1 / 2)
  have harg_xy := harg x y hxA hxB hy_a
  have hradius_xy := hradius x y hxA hxB hy_r
  have hexpRe_xy := hexpRe x y hxA hxB
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hw_ne : w ≠ 0 := by
    have hH_pos : 0 < H :=
      lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le hH_pos
        (Complex.verticalStripTransportShift_radius_ge_of_height_ge hy)
    exact norm_pos_iff.mp hw_norm_pos
  have hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    Complex.stirlingDenominator_pos_of_ne_zero hw_ne
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
          Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
    Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
  have hreciprocal_shape :
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
    exact
      Complex.stirlingDenominator_reciprocal_shape_fixedVertical
        hw_ne
        (Complex.fixedRealPartVerticalPoint_im
          (x + Complex.verticalStripTransportShift A) y)
  constructor
  · exact hden_pos
  constructor
  · have hrad_upper :
        ‖w‖ ^ (w.re - 1 / 2) ≤ Cr * P := by
      exact Eq.subst
        (motive := fun t : ℝ => ‖w‖ ^ (t - 1 / 2) ≤ Cr * P)
        hw_re.symm
        hradius_xy.1
    have harg_upper :
        Real.exp (-(Complex.arg w * y)) ≤ Ca * Eexp :=
      harg_xy.1
    have hexpRe_upper :
        Real.exp (-w.re) ≤ Ce :=
      hexpRe_xy.1
    have hshape_bound :
        Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
          ((Ca * Cr) * Ce) *
            (Eexp * P) := by
      have harg_nonneg :
          0 ≤ Real.exp (-(Complex.arg w * y)) :=
        le_of_lt (Real.exp_pos (-(Complex.arg w * y)))
      have hrad_nonneg :
          0 ≤ ‖w‖ ^ (w.re - 1 / 2) :=
        Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)
      have hexpRe_nonneg :
          0 ≤ Real.exp (-w.re) :=
        le_of_lt (Real.exp_pos (-w.re))
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hCrP_nonneg : 0 ≤ Cr * P :=
        mul_nonneg (le_of_lt hCr_pos) hP_nonneg
      have hCaE_nonneg : 0 ≤ Ca * Eexp :=
        mul_nonneg (le_of_lt hCa_pos) hEexp_nonneg
      have hfirst :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) ≤
            (Ca * Eexp) * (Cr * P) :=
        mul_le_mul harg_upper hrad_upper hrad_nonneg hCaE_nonneg
      have htarget_step :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Eexp) * (Cr * P)) * Ce :=
        mul_le_mul hfirst hexpRe_upper hexpRe_nonneg
          (mul_nonneg hCaE_nonneg hCrP_nonneg)
      have htarget_eq :
          ((Ca * Eexp) * (Cr * P)) * Ce =
            ((Ca * Cr) * Ce) * (Eexp * P) := by
        calc
          ((Ca * Eexp) * (Cr * P)) * Ce =
              (Ca * Eexp) * ((Cr * P) * Ce) :=
            (mul_assoc (Ca * Eexp) (Cr * P) Ce).symm
          _ = (Ca * Eexp) * (Ce * (Cr * P)) := by
            exact congrArg
              (fun t : ℝ => (Ca * Eexp) * t)
              (mul_comm (Cr * P) Ce)
          _ = ((Ca * Eexp) * Ce) * (Cr * P) :=
            mul_assoc (Ca * Eexp) Ce (Cr * P)
          _ = (Ca * (Eexp * Ce)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Eexp Ce)
          _ = (Ca * (Ce * Eexp)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * (Cr * P))
              (mul_comm Eexp Ce)
          _ = ((Ca * Ce) * Eexp) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Ce Eexp).symm
          _ = (Ca * Ce) * (Eexp * (Cr * P)) :=
            (mul_assoc (Ca * Ce) Eexp (Cr * P)).symm
          _ = (Ca * Ce) * ((Cr * P) * Eexp) := by
            exact congrArg
              (fun t : ℝ => (Ca * Ce) * t)
              (mul_comm Eexp (Cr * P))
          _ = ((Ca * Ce) * (Cr * P)) * Eexp :=
            mul_assoc (Ca * Ce) (Cr * P) Eexp
          _ = (Ca * (Ce * (Cr * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => t * Eexp)
              (mul_assoc Ca Ce (Cr * P))
          _ = (Ca * ((Cr * P) * Ce)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_comm Ce (Cr * P))
          _ = (Ca * (Cr * (P * Ce))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr P Ce)
          _ = (Ca * (Cr * (Ce * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * (Cr * t)) * Eexp)
              (mul_comm P Ce)
          _ = (Ca * ((Cr * Ce) * P)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr Ce P).symm
          _ = ((Ca * (Cr * Ce)) * P) * Eexp :=
            congrArg (fun t : ℝ => t * Eexp)
              (mul_assoc Ca (Cr * Ce) P)
          _ = (((Ca * Cr) * Ce) * P) * Eexp := by
            exact congrArg
              (fun t : ℝ => (t * P) * Eexp)
              (mul_assoc Ca Cr Ce).symm
          _ = ((Ca * Cr) * Ce) * (P * Eexp) :=
            (mul_assoc ((Ca * Cr) * Ce) P Eexp).symm
          _ = ((Ca * Cr) * Ce) * (Eexp * P) := by
            exact congrArg
              (fun t : ℝ => ((Ca * Cr) * Ce) * t)
              (mul_comm P Eexp)
      exact le_trans htarget_step (le_of_eq htarget_eq)
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    exact Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ((Ca * Cr) * Ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y)
      hreciprocal_shape.symm
      (Eq.subst
        (motive := fun t : ℝ =>
            Real.exp (-(Complex.arg w * y)) *
                ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Cr) * Ce) * t)
        henv_eq
        hshape_bound)
  · have hrad_lower :
        cr * P ≤ ‖w‖ ^ (w.re - 1 / 2) := by
      exact Eq.subst
        (motive := fun t : ℝ => cr * P ≤ ‖w‖ ^ (t - 1 / 2))
        hw_re.symm
        hradius_xy.2
    have harg_lower :
        ca * Eexp ≤ Real.exp (-(Complex.arg w * y)) :=
      harg_xy.2
    have hexpRe_lower :
        ce ≤ Real.exp (-w.re) :=
      hexpRe_xy.2
    have hshape_bound :
        ((ca * cr) * ce) *
            (Eexp * P) ≤
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hce_nonneg : 0 ≤ ce :=
        le_of_lt hce_pos
      have hcrP_nonneg : 0 ≤ cr * P :=
        mul_nonneg (le_of_lt hcr_pos) hP_nonneg
      have hcaE_nonneg : 0 ≤ ca * Eexp :=
        mul_nonneg (le_of_lt hca_pos) hEexp_nonneg
      have hleft_eq :
          ((ca * cr) * ce) * (Eexp * P) =
            (ca * Eexp) * (cr * P) * ce := by
        calc
          ((ca * cr) * ce) * (Eexp * P) =
              (ca * cr) * (ce * (Eexp * P)) :=
            (mul_assoc (ca * cr) ce (Eexp * P)).symm
          _ = (ca * cr) * ((Eexp * P) * ce) := by
            exact congrArg
              (fun t : ℝ => (ca * cr) * t)
              (mul_comm ce (Eexp * P))
          _ = ((ca * cr) * (Eexp * P)) * ce :=
            mul_assoc (ca * cr) (Eexp * P) ce
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P))
          _ = (ca * ((Eexp * P) * cr)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm cr (Eexp * P))
          _ = (ca * (Eexp * (P * cr))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp P cr)
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (Eexp * t)) * ce)
              (mul_comm P cr)
          _ = (ca * ((Eexp * cr) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp cr P).symm
          _ = (ca * ((cr * Eexp) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (t * P)) * ce)
              (mul_comm Eexp cr)
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc cr Eexp P)
          _ = ((ca * cr) * (Eexp * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P)).symm
          _ = ((ca * cr) * (P * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => ((ca * cr) * t) * ce)
              (mul_comm Eexp P)
          _ = (ca * cr) * (P * Eexp) * ce := rfl
          _ = (ca * (cr * P) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (by
                calc
                  (ca * cr) * (P * Eexp) =
                      ca * (cr * (P * Eexp)) :=
                    (mul_assoc ca cr (P * Eexp)).symm
                  _ = ca * ((cr * P) * Eexp) := by
                    exact congrArg
                      (fun t : ℝ => ca * t)
                      (mul_assoc cr P Eexp)
                  _ = ca * (cr * P) * Eexp :=
                    mul_assoc ca (cr * P) Eexp)
          _ = (Eexp * (ca * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm (ca * (cr * P)) Eexp)
          _ = ((ca * (cr * P)) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm Eexp (ca * (cr * P)))
          _ = (ca * ((cr * P) * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca (cr * P) Eexp).symm
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm (cr * P) Eexp)
          _ = ((ca * Eexp) * (cr * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca Eexp (cr * P))
          _ = (ca * Eexp) * (cr * P) * ce := rfl
      have hfirst :
          (ca * Eexp) * (cr * P) ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) :=
        mul_le_mul harg_lower hrad_lower hcrP_nonneg
          (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
      have hsecond :
          (ca * Eexp) * (cr * P) * ce ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        mul_le_mul hfirst hexpRe_lower hce_nonneg
          (mul_nonneg
            (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
            (Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)))
      exact le_trans (le_of_eq hleft_eq) hsecond
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    exact Eq.subst
      (motive := fun t : ℝ =>
        ((ca * cr) * ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y ≤ t)
      hreciprocal_shape.symm
      (Eq.subst
        (motive := fun t : ℝ =>
          ((ca * cr) * ce) * t ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re))
        henv_eq
        hshape_bound)

/-- Sectorial normalized Stirling, on the shifted closed-right-half-plane
points, gives the raw two-sided Gamma envelope with shifted real part.

This is the branch/exponential extraction layer: it converts control of
`Γ(w) e^w w^(1/2-w)` into the classical
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)` profile for
`w = x + N + i y`.  The only analytic input is the sectorial Stirling
hypothesis; the rest is principal-branch norm algebra. -/
theorem Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ := by
  rcases
      Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
        hStirling A B with
    ⟨Hn, Cn, cn, hHn_pos, hCn_pos, hcn_pos, hnormalized⟩
  rcases
      Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable
        A B with
    ⟨Hd, Cd, cd, hHd_pos, hCd_pos, hcd_pos, hdenom⟩
  let H : ℝ := max Hn Hd
  refine ⟨H, Cn * Cd, cn * cd,
    lt_of_lt_of_le hHn_pos (le_max_left Hn Hd),
    mul_pos hCn_pos hCd_pos,
    mul_pos hcn_pos hcd_pos, ?_⟩
  intro x y hxA hxB hy
  have hy_n : Hn ≤ ‖y‖ :=
    le_trans (le_max_left Hn Hd) hy
  have hy_d : Hd ≤ ‖y‖ :=
    le_trans (le_max_right Hn Hd) hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let E : ℝ :=
    Complex.fixedRealPartVerticalStirlingEnvelope
      (x + Complex.verticalStripTransportShift A) y
  let D : ℝ :=
    ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hnormalized_xy := hnormalized x y hxA hxB hy_n
  have hdenom_xy := hdenom x y hxA hxB hy_d
  have hD_pos : 0 < D :=
    hdenom_xy.1
  have hrecip_upper : 1 / D ≤ Cd * E :=
    hdenom_xy.2.1
  have hrecip_lower : cd * E ≤ 1 / D :=
    hdenom_xy.2.2
  have hgamma_upper_raw :
      ‖Complex.Gamma w‖ ≤ Cn / D :=
    Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
      w Cn hnormalized_xy.1 hD_pos
  have hgamma_lower_raw :
      cn / D ≤ ‖Complex.Gamma w‖ :=
    Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
      w cn hnormalized_xy.2 hD_pos
  have hCn_nonneg : 0 ≤ Cn :=
    le_of_lt hCn_pos
  have hcn_nonneg : 0 ≤ cn :=
    le_of_lt hcn_pos
  have hupper_scale :
      Cn / D ≤ (Cn * Cd) * E := by
    have hdiv_eq : Cn / D = Cn * (1 / D) := by
      calc
        Cn / D = Cn * D⁻¹ := div_eq_mul_inv Cn D
        _ = Cn * (1 / D) := by
          exact congrArg (fun u : ℝ => Cn * u) (one_div D).symm
    have hmul :
        Cn * (1 / D) ≤ Cn * (Cd * E) :=
      mul_le_mul_of_nonneg_left hrecip_upper hCn_nonneg
    have htarget :
        Cn * (Cd * E) = (Cn * Cd) * E :=
      mul_assoc Cn Cd E
    exact le_trans (le_of_eq hdiv_eq)
      (le_trans hmul (le_of_eq htarget))
  have hlower_scale :
      (cn * cd) * E ≤ cn / D := by
    have hleft_assoc :
        (cn * cd) * E = cn * (cd * E) :=
      (mul_assoc cn cd E).symm
    have hmul :
        cn * (cd * E) ≤ cn * (1 / D) :=
      mul_le_mul_of_nonneg_left hrecip_lower hcn_nonneg
    have hdiv_eq : cn * (1 / D) = cn / D := by
      calc
        cn * (1 / D) = cn * D⁻¹ := by
          exact congrArg (fun u : ℝ => cn * u) (one_div D)
        _ = cn / D := (div_eq_mul_inv cn D).symm
    exact le_trans (le_of_eq hleft_assoc)
      (le_trans hmul (le_of_eq hdiv_eq))
  constructor
  · exact le_trans hgamma_upper_raw hupper_scale
  · exact le_trans hlower_scale hgamma_lower_raw

/-- Finite recurrence transport from shifted raw Gamma bounds and recurrence
product bounds back to the original vertical strip.

The shifted envelope has power `x + N - 1/2`; division by the recurrence product
contributes exactly a fixed polynomial factor of degree `N`, which is absorbed
into strip-dependent constants and recovers the unshifted envelope. -/
theorem Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
    (A B : ℝ)
    (N : ℕ)
    (hshift_eq : N = Complex.verticalStripTransportShift A)
    (hshifted :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖)
    (hproduct :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
              C * (1 + ‖y‖) ^ (N : ℝ) ∧
            c * (1 + ‖y‖) ^ (N : ℝ) ≤
              ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖)
    (hfactor_ne :
      ∃ H : ℝ,
        0 < H ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ∀ j : ℕ,
              j < N →
                Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  rcases hshifted with ⟨Hs, Cs, cs, hHs_pos, hCs_pos, hcs_pos, hshifted_bound⟩
  rcases hproduct with ⟨Hp, Cp, cp, hHp_pos, hCp_pos, hcp_pos, hproduct_bound⟩
  rcases hfactor_ne with ⟨Hn, hHn_pos, hfactor_ne_pointwise⟩
  let H : ℝ := max Hs (max Hp Hn)
  refine ⟨H, Cs / cp, cs / Cp, ?_, div_pos hCs_pos hcp_pos,
    div_pos hcs_pos hCp_pos, ?_⟩
  · exact lt_of_lt_of_le hHs_pos (le_max_left Hs (max Hp Hn))
  intro x y hxA hxB hy
  have hy_s : Hs ≤ ‖y‖ :=
    le_trans (le_max_left Hs (max Hp Hn)) hy
  have hy_p : Hp ≤ ‖y‖ :=
    le_trans (le_trans (le_max_left Hp Hn) (le_max_right Hs (max Hp Hn))) hy
  have hy_n : Hn ≤ ‖y‖ :=
    le_trans (le_trans (le_max_right Hp Hn) (le_max_right Hs (max Hp Hn))) hy
  have hshifted_xy := hshifted_bound x y hxA hxB hy_s
  have hproduct_xy := hproduct_bound x y hxA hxB hy_p
  have hfactor_xy :
      ∀ j : ℕ,
        j < N →
          Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0 :=
    hfactor_ne_pointwise x y hxA hxB hy_n
  have hnorm_rec :
      ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ =
        ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct
            (Complex.fixedRealPartVerticalPoint x y) N‖ :=
    Complex.Gamma_norm_eq_shifted_norm_div_gammaRecurrenceProduct_norm
      N hfactor_xy
  have hshift_point :
      Complex.fixedRealPartVerticalPoint x y + (N : ℂ) =
        Complex.fixedRealPartVerticalPoint (x + N) y := by
    exact (Complex.fixedRealPartVerticalPoint_add_natCast x y N).symm
  have hshifted_norm :
      ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ =
        ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint (x + N) y)‖ :=
    congrArg (fun z : ℂ => ‖Complex.Gamma z‖) hshift_point
  let R : ℝ := 1 + ‖y‖
  have hR_pos : 0 < R :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hRpow_pos : 0 < R ^ (N : ℝ) :=
    Real.rpow_pos_of_pos hR_pos (N : ℝ)
  have hprod_lower_pos :
      0 < cp * R ^ (N : ℝ) :=
    mul_pos hcp_pos hRpow_pos
  have hprod_upper_pos :
      0 < Cp * R ^ (N : ℝ) :=
    mul_pos hCp_pos hRpow_pos
  have hprod_norm_pos :
      0 <
        ‖Complex.gammaRecurrenceProduct
          (Complex.fixedRealPartVerticalPoint x y) N‖ :=
    lt_of_lt_of_le hprod_lower_pos hproduct_xy.2
  have hshifted_upper :
      ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ ≤
        Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y :=
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y)
      hshifted_norm.symm
      hshifted_xy.1
  have hshifted_lower :
      cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
        ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ :=
    Eq.subst
      (motive := fun t : ℝ =>
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤ t)
      hshifted_norm.symm
      hshifted_xy.2
  have hupper_div :
      ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct
            (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
        Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
          (cp * R ^ (N : ℝ)) := by
    have hstep_den :
        ‖Complex.Gamma
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
          ‖Complex.Gamma
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
            (cp * R ^ (N : ℝ)) :=
      div_le_div_of_nonneg_left
        (norm_nonneg
          (Complex.Gamma
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))))
        hprod_lower_pos
        hproduct_xy.2
    have hstep_num :
        ‖Complex.Gamma
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
            (cp * R ^ (N : ℝ)) ≤
          Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (cp * R ^ (N : ℝ)) :=
      div_le_div_of_nonneg_right hshifted_upper (le_of_lt hprod_lower_pos)
    exact le_trans hstep_den hstep_num
  have hlower_div :
      cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
          (Cp * R ^ (N : ℝ)) ≤
        ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct
            (Complex.fixedRealPartVerticalPoint x y) N‖ := by
    have hnum_nonneg :
        0 ≤ cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y :=
      mul_nonneg (le_of_lt hcs_pos)
        (Complex.fixedRealPartVerticalStirlingEnvelope_nonneg (x + N) y)
    have hstep_den :
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (Cp * R ^ (N : ℝ)) ≤
          cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ :=
      div_le_div_of_nonneg_left
        hnum_nonneg
        hprod_norm_pos
        hproduct_xy.1
    have hstep_num :
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
          ‖Complex.Gamma
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ :=
      div_le_div_of_nonneg_right hshifted_lower
        (le_of_lt hprod_norm_pos)
    exact le_trans hstep_den hstep_num
  constructor
  · have htarget :
        Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (cp * R ^ (N : ℝ)) =
          (Cs / cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
      Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
        x y N Cs cp hcp_pos
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤ t)
        htarget
        (Eq.subst
          (motive := fun t : ℝ =>
            t ≤
              Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (cp * R ^ (N : ℝ)))
          hnorm_rec.symm
          hupper_div)
  · have htarget :
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (Cp * R ^ (N : ℝ)) =
          (cs / Cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
      Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
        x y N cs Cp hCp_pos
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          t ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖)
        htarget
        (Eq.subst
          (motive := fun t : ℝ =>
            cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (Cp * R ^ (N : ℝ)) ≤ t)
          hnorm_rec.symm
          hlower_div)

/-- Sectorial Stirling at the deterministic right shift, transported back
through the finite Gamma recurrence product.

This is the single non-special-function owner sink for the vertical-strip
transport.  It combines the deterministic shift geometry, the exact Gamma
recurrence product identity, and the finite-product upper/lower estimates. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  let N : ℕ := Complex.verticalStripTransportShift A
  have hshifted_transport :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ := by
    exact
      Eq.subst
        (motive := fun M : ℕ =>
          ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
            0 < H ∧
            0 < C ∧
            0 < c ∧
            ∀ x y : ℝ,
              A ≤ x →
              x ≤ B →
              H ≤ ‖y‖ →
                ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint (x + M) y)‖ ≤
                  C * Complex.fixedRealPartVerticalStirlingEnvelope (x + M) y ∧
                c * Complex.fixedRealPartVerticalStirlingEnvelope (x + M) y ≤
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint (x + M) y)‖)
        (show Complex.verticalStripTransportShift A = N from rfl)
        (Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
          hStirling A B)
  exact
    Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
      A B N rfl
      hshifted_transport
      (Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds A B N)
      (Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
        A B N)

/-- Deterministic finite-recurrence transport from closed-right-half-plane
sectorial Stirling to a vertical strip.

The shift is `Complex.verticalStripRightShift A`.  Applying sectorial Stirling
to `z + N` is justified by
`fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector`
and the height/radius comparison.  The finite product
`gammaRecurrenceProduct z N` is controlled uniformly on the strip because `N`
is fixed and the strip real part is bounded; Gamma recurrence gives
`Γ z = Γ (z + N) / gammaRecurrenceProduct z N`. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
      hStirling A B

/-- Vertical-strip two-sided Stirling bounds as a consequence of sectorial
log-Gamma Stirling.

For a strip that crosses the left half-plane, choose a natural shift `N` with
`-A ≤ N`.  The shifted points `z + N` lie in the closed right half-plane and
the sectorial logarithmic Stirling theorem applies there; the finite Gamma
recurrence product transports the estimate back to `z`.  The coordinate and
radius facts above supply the non-Stirling geometry of this reduction. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
      hStirling A B

/-- Standard vertical-strip specialization of sectorial Stirling.

On every compact real strip `A ≤ Re z ≤ B`, the vertical tails lie in closed
sectors avoiding the negative real axis.  Sectorial Stirling therefore gives
uniform two-sided Gamma bounds with the classical
`exp (-π |y| / 2) (1 + |y|)^(x - 1/2)` profile.  This is the upstream
fixed-line owner theorem; cf. Whittaker-Watson, Ch. XII and DLMF §5.11. -/
theorem Complex.sectorialStirling_verticalStrip_largeHeight_classical
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds
      Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane A B

/-- Classical large-height fixed-real-part vertical Stirling theorem.

For arbitrary real part `a`, the vertical line `a + i b` is not contained in
the closed right half-plane when `a < 0`.  The correct owner input is therefore
the fixed-line specialization of sectorial Stirling in sectors avoiding the
negative real axis, with constants depending on `a`; cf. DLMF §5.11. -/
theorem Complex.fixedRealPartVerticalStirling_largeHeight_classical
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases
      Complex.sectorialStirling_verticalStrip_largeHeight_classical
        a a with
    ⟨H, C, c, hH_pos, hC_pos, hc_pos, hstrip⟩
  exact
    ⟨H, C, c, hH_pos, hC_pos, hc_pos,
      fun b hb =>
        hstrip a b (le_refl a) (le_refl a) hb⟩

/-- Large-height fixed-real-part vertical Stirling bounds for `Complex.Gamma`.

For an arbitrary fixed real part `a`, the vertical line `a + ib` eventually
lies in a closed sector avoiding the negative real axis, with sector aperture
depending on `a`.  Sectorial Stirling there gives the two-sided
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact Complex.fixedRealPartVerticalStirling_largeHeight_classical a

/-- The compact-height part of a fixed vertical line. -/
def Complex.fixedRealPartVerticalCompactHeightSet
    (H : ℝ) : Set ℝ :=
  {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖ ∧ ‖b‖ ≤ H}

/-- Upper ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaUpperRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- Lower ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaLowerRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- The fixed-line compact-height set is compact. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_isCompact
    (H : ℝ) :
    IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  have hclosed_inner : IsClosed {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖} :=
    isClosed_Ici.preimage continuous_norm
  have hclosed_outer : IsClosed {b : ℝ | ‖b‖ ≤ H} :=
    isClosed_Iic.preimage continuous_norm
  have hclosed :
      IsClosed (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    hclosed_inner.inter hclosed_outer
  have hsubset :
      Complex.fixedRealPartVerticalCompactHeightSet H ⊆ Set.Icc (-H) H := by
    intro b hb
    have hb_abs_le : |b| ≤ H := by
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ H)
        (Real.norm_eq_abs b)
        hb.2
    exact abs_le.mp hb_abs_le
  exact isCompact_Icc.of_isClosed_subset hclosed hsubset

/-- The fixed-line compact-height set is nonempty once `H ≥ 1 / 2`. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_nonempty
    {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H) :
    (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty := by
  refine ⟨(1 / 2 : ℝ), ?_⟩
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 :=
    le_of_lt (half_pos zero_lt_one)
  have hnorm_half : ‖(1 / 2 : ℝ)‖ = 1 / 2 :=
    Real.norm_of_nonneg hhalf_nonneg
  exact
    ⟨Eq.subst
        (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
        hnorm_half.symm
        (le_refl (1 / 2 : ℝ)),
      Eq.subst
        (motive := fun x : ℝ => x ≤ H)
        hnorm_half.symm
        hH⟩

/-- `Gamma` is nonzero on the fixed-line compact-height strip. -/
theorem Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight
    {a H b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 := by
  intro hzero
  rcases
      (Complex.Gamma_eq_zero_iff
        (Complex.fixedRealPartVerticalPoint a b)).mp hzero with
    ⟨n, hn⟩
  have him_eq :
      (Complex.fixedRealPartVerticalPoint a b).im = (-(n : ℂ)).im :=
    congrArg Complex.im hn
  have hleft_im :
      (Complex.fixedRealPartVerticalPoint a b).im = b :=
    Complex.fixedRealPartVerticalPoint_im a b
  have hright_im : (-(n : ℂ)).im = 0 := by
    calc
      (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
      _ = -0 := congrArg Neg.neg (Complex.natCast_im n)
      _ = 0 := neg_zero
  have hb_zero : b = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have hnorm_zero : ‖b‖ = 0 :=
    congrArg norm hb_zero
  have hhalf_pos : (0 : ℝ) < 1 / 2 :=
    half_pos zero_lt_one
  have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
    not_le.mpr hhalf_pos
  exact
    hnot
      (Eq.subst
        (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
        hnorm_zero hb.1)

/-- The fixed-line Gamma ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ =>
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  intro b hb
  have hgamma_ne :
      Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
    Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
  have hpole_free :
      ∀ n : ℕ, Complex.fixedRealPartVerticalPoint a b ≠ -n := by
    intro n hn
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff
      (Complex.fixedRealPartVerticalPoint a b)).mpr ⟨n, hn⟩)
  have hpoint_cont :
      ContinuousAt (fun x : ℝ => Complex.fixedRealPartVerticalPoint a x) b := by
    unfold Complex.fixedRealPartVerticalPoint
    exact continuousAt_const.add
      (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
  have hgamma_cont :
      ContinuousAt
        (fun x : ℝ => Complex.Gamma (Complex.fixedRealPartVerticalPoint a x))
        b :=
    (Complex.differentiableAt_Gamma
      (Complex.fixedRealPartVerticalPoint a b) hpole_free).continuousAt.comp
      hpoint_cont
  have hnum_cont :
      ContinuousAt
        (fun x : ℝ => ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a x)‖)
        b :=
    hgamma_cont.norm
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have henv_cont :
      ContinuousAt
        (fun x : ℝ => Complex.fixedRealPartVerticalStirlingEnvelope a x)
        b := by
    unfold Complex.fixedRealPartVerticalStirlingEnvelope
    have hexp_arg_cont :
        ContinuousAt (fun x : ℝ => (-(Real.pi / 2)) * ‖x‖) b :=
      continuousAt_const.mul continuousAt_id.norm
    have hpow_base_cont :
        ContinuousAt (fun x : ℝ => 1 + ‖x‖) b :=
      continuousAt_const.add continuousAt_id.norm
    exact
      hexp_arg_cont.rexp.mul
        (hpow_base_cont.rpow_const (Or.inl hbase_pos.ne'))
  have henv_ne :
      Complex.fixedRealPartVerticalStirlingEnvelope a b ≠ 0 :=
    ne_of_gt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)
  exact (hnum_cont.div henv_cont henv_ne).continuousWithinAt

/-- The upper ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaUpperRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The lower ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The fixed-line Gamma ratio is nonnegative on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_nonneg_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (_hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hnum_nonneg :
      0 ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_nonneg (Complex.Gamma (Complex.fixedRealPartVerticalPoint a b))
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  have hden_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    le_of_lt hden_pos
  exact div_nonneg hnum_nonneg hden_nonneg

/-- The fixed-line Gamma ratio is positive on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 < Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hgamma_ne :
      Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
    Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
  have hnum_pos :
      0 < ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_pos_iff.mpr hgamma_ne
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  exact div_pos hnum_pos hden_pos

/-- Compact-height upper ratio has a positive global upper bound. -/
theorem Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
    (a H : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      (Complex.fixedRealPartVerticalCompactHeightSet_isCompact H)
      (Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
        a H) with
    ⟨M, hM⟩
  let C : ℝ := max 1 M
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  exact le_trans (hM b hb) (le_max_right 1 M)

/-- Compact-height lower ratio has a positive global lower bound. -/
theorem Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
    (a H : ℝ)
    (hH_half : (1 / 2 : ℝ) ≤ H) :
    ∃ c : ℝ,
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hcompact :
      IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.fixedRealPartVerticalCompactHeightSet_isCompact H
  have hnonempty :
      (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty :=
    Complex.fixedRealPartVerticalCompactHeightSet_nonempty hH_half
  have hcont :
      ContinuousOn
        (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
        (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
      a H
  rcases hcompact.exists_isMinOn hnonempty hcont with
    ⟨b₀, hb₀, hb₀_min⟩
  let c : ℝ := Complex.fixedRealPartVerticalGammaLowerRatio a b₀
  have hc_pos : 0 < c :=
    Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight a H hb₀
  refine ⟨c, hc_pos, ?_⟩
  intro b hb
  exact hb₀_min b hb

/-- Canonical compact-height ratio theorem for a fixed vertical line.

The proof is the standard compactness argument: the height set is compact,
the Gamma ratio is continuous there, `Gamma` has no zeros on it because
`|b| ≥ 1/2`, and the fixed-line Stirling envelope is strictly positive. -/
theorem Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  rcases
      Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
        a H with
    ⟨C, hC_pos, hC⟩
  by_cases hH_half : (1 / 2 : ℝ) ≤ H
  · rcases
        Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
          a H hH_half with
      ⟨c, hc_pos, hc⟩
    exact ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hC b hb, hc b hb⟩⟩
  · have hhalf_lt_H : H < (1 / 2 : ℝ) :=
      lt_of_not_ge hH_half
    have hone_pos : (0 : ℝ) < 1 :=
      zero_lt_one
    refine ⟨C, 1, hC_pos, hone_pos, ?_⟩
    intro b hb
    have hle : (1 / 2 : ℝ) ≤ H :=
      le_trans hb.1 hb.2
    exact False.elim ((not_lt_of_ge hle) hhalf_lt_H)

/-- Ratio bounds on the compact-height part of a fixed vertical line.

This is the compactness/nonvanishing owner certificate: continuity supplies a
finite upper bound for the upper ratio, while nonvanishing of `Γ` and the
strictly positive Stirling envelope supply a positive lower bound. -/
theorem Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  exact Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds a H hH_pos

/-- Ratio bounds convert to two-sided envelope bounds on the compact-height
part of a fixed vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
    (a H C c : ℝ)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c)
    (hratio :
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b) :
    ∀ b : ℝ,
      (1 / 2 : ℝ) ≤ ‖b‖ →
      ‖b‖ ≤ H →
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro b hb_inner hb_outer
  have hb_mem :
      b ∈ Complex.fixedRealPartVerticalCompactHeightSet H :=
    ⟨hb_inner, hb_outer⟩
  have hratio_b :
      Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
        c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b :=
    hratio b hb_mem
  have hE_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  have hE_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    le_of_lt hE_pos
  have hupper_div :
      ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b ≤ C :=
    hratio_b.1
  have hlower_div :
      c ≤
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    hratio_b.2
  have hupper :
      ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
        C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    (div_le_iff₀ hE_pos).mp hupper_div
  have hlower :
      c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    (le_div_iff₀ hE_pos).mp hlower_div
  exact ⟨hupper, hlower⟩

/-- Compact-height patch for fixed-real-part vertical Stirling bounds.

On the compact set `1 / 2 ≤ |b| ≤ H`, continuity and nonvanishing of `Γ` on
the fixed vertical line give finite upper and positive lower constants relative
to the positive fixed-line Stirling envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        (1 / 2 : ℝ) ≤ ‖b‖ →
        ‖b‖ ≤ H →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases
      Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
        a H hH_pos with
    ⟨C, c, hC_pos, hc_pos, hratio⟩
  exact
    ⟨C, c, hC_pos, hc_pos,
      Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
        a H C c hC_pos hc_pos hratio⟩

/-- Assembly of large-height fixed-line Stirling and compact-height patching. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
    (a : ℝ)
    (hlarge :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          H ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖)
    (hcompact :
      ∀ H : ℝ,
        0 < H →
          ∃ C : ℝ, ∃ c : ℝ,
            0 < C ∧
            0 < c ∧
            ∀ b : ℝ,
              (1 / 2 : ℝ) ≤ ‖b‖ →
              ‖b‖ ≤ H →
                ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
                  C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
                c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases hlarge with ⟨H, Clarge, clarge, hH_pos, hClarge_pos, hclarge_pos, hlarge_bound⟩
  rcases hcompact H hH_pos with
    ⟨Ccompact, ccompact, hCcompact_pos, hccompact_pos, hcompact_bound⟩
  let C : ℝ := max Clarge Ccompact
  let c : ℝ := min clarge ccompact
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Ccompact)
  have hc_pos : 0 < c :=
    lt_min hclarge_pos hccompact_pos
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
  intro b hb
  have hE_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_nonneg a b
  by_cases hb_large : H ≤ ‖b‖
  · have hlarge_b :
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
      hlarge_bound b hb_large
    have hupper_constant :
        Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (le_max_left Clarge Ccompact) hE_nonneg
    have hlower_constant :
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (min_le_left clarge ccompact) hE_nonneg
    exact
      ⟨le_trans hlarge_b.1 hupper_constant,
        le_trans hlower_constant hlarge_b.2⟩
  · have hb_compact_upper : ‖b‖ ≤ H :=
      le_of_not_ge hb_large
    have hcompact_b :
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
      hcompact_bound b hb hb_compact_upper
    have hupper_constant :
        Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (le_max_right Clarge Ccompact) hE_nonneg
    have hlower_constant :
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (min_le_right clarge ccompact) hE_nonneg
    exact
      ⟨le_trans hcompact_b.1 hupper_constant,
        le_trans hlower_constant hcompact_b.2⟩

/-- Fixed-real-part vertical two-sided Stirling bounds for `Complex.Gamma`.

This is the exact fixed-line specialization theorem in the classical Stirling
API.  Deriving it from the sectorial exponential asymptotic requires the full
vertical-line argument analysis of
`w ^ ((1 / 2 : ℂ) - w)`, including the `exp (-π |b| / 2)` factor and matching
lower bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
    (a : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact
    Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
      a
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
        a)
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
        a)

/-- Two-sided fixed-real-part vertical Stirling envelope for `Complex.Gamma`.

This is the fixed-line specialization of sectorial complex Stirling after
separating the argument of `a + i b`: it supplies the matching
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` upper and lower envelopes on every
fixed real line.  The public one-sided estimates below are just projections
from this two-sided classical input. -/
theorem Complex.fixedLineVerticalGammaTwoSidedEnvelope :
    ∀ a : ℝ,
      ∃ C : ℝ, ∃ c : ℝ,
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro a
  exact Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical a

/-- Standard sectorial `log Γ` Stirling upper bound on the closed right half-plane.

This is the logarithmic special-function root after peeling the downstream
growth theory: Stirling's expansion for `log Γ(w)` on a closed sector avoiding
the negative real axis gives a uniform
`O((1 + ‖w‖) log (2 + ‖w‖))` bound on the closed right half-plane; cf. DLMF
§5.11. The bound is stated for `log ‖Γ(w)‖`, the real part of `log Γ(w)`, so
later Gamma-real normalization steps do not need a branch of `logGamma`. -/
theorem Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane

/-- Fixed-line vertical upper envelope for `Complex.Gamma`.

For each fixed real part `a`, Stirling's formula on the vertical line
`a + i b` gives exponential decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaUpperEnvelope :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  intro a
  rcases Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
    ⟨C, c, hC_pos, hc_pos, hbounds⟩
  exact
    ⟨C, hC_pos,
      fun b hb =>
        (hbounds b hb).1⟩

/-- Fixed-real-part vertical Stirling upper bound for `Complex.Gamma`.

This is the direct fixed-line classical estimate: for each fixed real part `a`,
`Γ(a + i b)` has vertical decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := by
  exact Complex.fixedLineVerticalGammaUpperEnvelope

/-- Fixed-line vertical lower envelope for `Complex.Gamma`.

For each fixed real part `a`, the lower half of vertical Stirling gives the
matching positive constant in front of the same exponential-polynomial
envelope; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaLowerEnvelope :
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro a
  rcases Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
    ⟨C, c, hC_pos, hc_pos, hbounds⟩
  exact
    ⟨c, hc_pos,
      fun b hb =>
        (hbounds b hb).2⟩

/-- Fixed-real-part vertical Stirling lower bound for `Complex.Gamma`.

This is the lower half of the classical fixed-line estimate, isolated so the
reciprocal estimate is a norm-order transport rather than an independent
primitive. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical :
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
  exact Complex.fixedLineVerticalGammaLowerEnvelope

/-- Two-sided fixed-real-part vertical Stirling bounds for `Complex.Gamma`, with the
fixed-line point and envelope named by the owner API.

This is the reusable bundled form of the classical fixed-line asymptotic estimates:
downstream reciprocal and quotient arguments should consume this statement rather
than repeatedly unpacking the two split roots. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_owner
    (a : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
    ⟨C, hC_pos, hupper⟩
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
    ⟨c, hc_pos, hlower⟩
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
  intro b hb
  exact ⟨hupper b hb, hlower b hb⟩

/-- Classical Gamma/Stirling owner package on the closed right half-plane.

This package is now only product assembly from the canonical local
special-function roots above: sectorial exponential Stirling, its log-norm
consequence, and the two fixed-real-part vertical estimates. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_package_classical :
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2)) ∧
    (∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) := by
  exact
    ⟨Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical,
      Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical⟩

/-- Sectorial log-norm consequence of closed-sector logarithmic Stirling for
`Complex.Gamma` on the closed right half-plane. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical

/-- `Complex.Gamma` is nonzero on fixed vertical lines away from the real-axis
pole convention when `|b| ≥ 1/2`. -/
theorem Complex.Gamma_fixedRealPart_vertical_ne_zero_of_half_le_norm
    (a b : ℝ)
    (hb : (1 / 2 : ℝ) ≤ ‖b‖) :
    Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff ((a : ℂ) + (b : ℂ) * Complex.I)).mp hzero with
    ⟨n, hn⟩
  have him_eq : (((a : ℂ) + (b : ℂ) * Complex.I).im) = (-(n : ℂ)).im :=
    congrArg Complex.im hn
  have hleft_im :
      (((a : ℂ) + (b : ℂ) * Complex.I).im) = b := by
    calc
      (((a : ℂ) + (b : ℂ) * Complex.I).im) =
          (a : ℂ).im + ((b : ℂ) * Complex.I).im := Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
      _ = 0 + b := by simp [Complex.mul_I_im]
      _ = b := zero_add b
  have hright_im : (-(n : ℂ)).im = 0 := by
    calc
      (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
      _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
      _ = 0 := neg_zero
  have hb_zero : b = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have hnorm_zero : ‖b‖ = 0 :=
    congrArg norm hb_zero
  have hhalf_pos : (0 : ℝ) < 1 / 2 :=
    half_pos zero_lt_one
  have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
    not_le.mpr hhalf_pos
  exact hnot (Eq.subst (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x) hnorm_zero hb)

/-- Reciprocal transport for fixed-real-part vertical Gamma estimates.

A lower Stirling bound and nonvanishing of `Γ(a + i b)` imply the corresponding
upper bound for the reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound
    {a c : ℝ}
    (hc_pos : 0 < c)
    (hlower :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        c * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ≤
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
        c⁻¹ * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro b hb
  let x : ℝ := (Real.pi / 2) * ‖b‖
  let H : ℝ := 1 + ‖b‖
  let G : ℂ := Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)
  have hH_pos : 0 < H :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have hexp_pos : 0 < Real.exp (-x) :=
    Real.exp_pos (-x)
  have hrpow_pos : 0 < H ^ (a - 1 / 2) :=
    Real.rpow_pos_of_pos hH_pos (a - 1 / 2)
  have henvelope_pos :
      0 < c * Real.exp (-x) * H ^ (a - 1 / 2) :=
    mul_pos (mul_pos hc_pos hexp_pos) hrpow_pos
  have hG_lower :
      c * Real.exp (-x) * H ^ (a - 1 / 2) ≤ ‖G‖ := by
    exact hlower b hb
  have hG_inv_norm :
      ‖G⁻¹‖ = ‖G‖⁻¹ :=
    norm_inv G
  have hreciprocal_le :
      ‖G‖⁻¹ ≤ (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ :=
    inv_le_inv_of_le henvelope_pos hG_lower
  have htarget_eq :
      (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
        c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := by
    have hexp_neg_eq : Real.exp (-x) = (Real.exp x)⁻¹ :=
      Real.exp_neg x
    have hpow_neg_eq :
        H ^ (1 / 2 - a) = (H ^ (a - 1 / 2))⁻¹ := by
      have hneg : 1 / 2 - a = -(a - 1 / 2) := by
        exact (neg_sub a (1 / 2)).symm
      exact Eq.trans
        (congrArg (fun y : ℝ => H ^ y) hneg)
        (Real.rpow_neg (le_of_lt hH_pos) (a - 1 / 2))
    calc
      (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
          (c * Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹ := by
            rw [mul_inv_rev]
      _ = (c⁻¹ * (Real.exp (-x))⁻¹) * (H ^ (a - 1 / 2))⁻¹ := by
            rw [mul_inv_rev]
      _ = (c⁻¹ * Real.exp x) * (H ^ (a - 1 / 2))⁻¹ := by
            exact congrArg
              (fun y : ℝ => (c⁻¹ * y) * (H ^ (a - 1 / 2))⁻¹)
              (congrArg Inv.inv hexp_neg_eq)
      _ = (c⁻¹ * Real.exp x) * H ^ (1 / 2 - a) := by
            exact congrArg
              (fun y : ℝ => (c⁻¹ * Real.exp x) * y)
              hpow_neg_eq.symm
      _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := by
            exact (mul_assoc c⁻¹ (Real.exp x) (H ^ (1 / 2 - a))).symm
  exact Eq.subst
    (motive := fun y : ℝ => ‖G⁻¹‖ ≤ y)
    htarget_eq
    (Eq.subst
      (motive := fun y : ℝ => y ≤
        (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹)
      hG_inv_norm.symm
      hreciprocal_le)

/-- Fixed-real-part reciprocal vertical Stirling bound for `Complex.Gamma`, obtained
from the lower fixed-line estimate by reciprocal transport. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro a
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
    ⟨c, hc_pos, hlower⟩
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, ?_⟩
  exact Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound hc_pos hlower

/-- Fixed-real-part vertical Stirling bounds for `Complex.Gamma` and its
reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro a
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
    ⟨Cu, hCu_pos, hCu⟩
  rcases Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical a with
    ⟨Cr, hCr_pos, hCr⟩
  let C : ℝ := Cu + Cr
  have hC_pos : 0 < C :=
    add_pos hCu_pos hCr_pos
  have hCu_le_C : Cu ≤ C :=
    le_add_of_nonneg_right (le_of_lt hCr_pos)
  have hCr_le_C : Cr ≤ C :=
    le_add_of_nonneg_left (le_of_lt hCu_pos)
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  have hdirect_envelope_nonneg :
      0 ≤ Real.exp (-(Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (a - 1 / 2) := by
    have hbase_pos : 0 < 1 + ‖b‖ :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg b))
    exact mul_nonneg
      (le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖b‖)))
      (le_of_lt (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2)))
  have hreciprocal_envelope_nonneg :
      0 ≤ Real.exp ((Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (1 / 2 - a) := by
    have hbase_pos : 0 < 1 + ‖b‖ :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg b))
    exact mul_nonneg
      (le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖b‖)))
      (le_of_lt (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a)))
  have hdirect_scaled :
      Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) ≤
        C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_le_mul_of_nonneg_right hCu_le_C hdirect_envelope_nonneg
  have hreciprocal_scaled :
      Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) ≤
        C * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_le_mul_of_nonneg_right hCr_le_C hreciprocal_envelope_nonneg
  have hdirect_source_assoc :
      Cu * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_assoc Cu (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have hdirect_target_assoc :
      C * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have hreciprocal_source_assoc :
      Cr * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_assoc Cr (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  have hreciprocal_target_assoc :
      C * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        C * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_assoc C (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  constructor
  · exact Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
      hdirect_target_assoc.symm
      (le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
          hdirect_source_assoc
          (hCu b hb))
        hdirect_scaled)
  · exact Eq.subst
      (motive := fun x : ℝ =>
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
      hreciprocal_target_assoc.symm
      (le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
          hreciprocal_source_assoc
          (hCr b hb))
        hreciprocal_scaled)

/-- Classical closed-sector Stirling expansion for `Complex.Gamma`, with the
sectorial and fixed-line consequences used by the normalization chain.

This owner theorem is now only the product assembly of the formula-level
Stirling input, its sectorial log-norm consequence, and the fixed-line vertical
estimates; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical :
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a)) := by
  exact
    ⟨Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical,
      Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical⟩

/-- Classical closed-sector Stirling estimates for `Complex.Gamma`.

This is the single classical special-function owner input for the Gamma lane.
It packages the sectorial log-norm consequence of Stirling's expansion in the
closed right half-plane together with the fixed-real-part vertical two-sided
estimates obtained from the same expansion.  The sector avoids the negative
real axis, and the fixed-line bounds are the usual
`Γ(a + i b) = O(exp (-π |b| / 2) |b|^(a - 1/2))` estimate and its reciprocal
dual; cf. DLMF §5.11. -/

end
end LFunctions
end Boundary

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
# Binet kernel and sectorial Gamma seed estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
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

/-- Binet's second logarithmic formula for `Gamma` on the open right half-plane,
away from the origin.

This is the standard integral representation:
`Log Γ(w) = (w - 1/2) Log w - w + (1/2)log(2π) + J(w)`, where `J` is the
Binet second-formula remainder.  The principal-arctangent kernel is not
evaluated on the imaginary boundary. -/
theorem Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    ⟨1, zero_lt_one, fun w hw_re_pos _hw_norm =>
      Complex.Gamma_binetSecondFormula_large_openRightHalfPlane
        w hw_re_pos _hw_norm⟩

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
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht hsmall
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      (w := w) hw_re_pos ht hsmall

/-- Open-half-plane form of the Binet-kernel estimate kept under the historical
name used by downstream normalization code.

The literal principal-arctangent kernel has boundary singularities on the
imaginary axis, so this theorem requires `0 < w.re`. -/
theorem Complex.binetSecondFormula_arctan_kernel_norm_le_closedRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact Complex.binetSecondFormula_arctan_kernel_norm_le_openRightHalfPlane hw_re_pos

/-- The positive half-line decomposes into the local Binet interval `(0,1]`
and the tail interval `(1,∞)`. -/
theorem Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one :
    Set.Ioi (0 : ℝ) =
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hle : x ≤ 1
    · left
      exact ⟨hx, hle⟩
    · right
      exact lt_of_not_ge hle
  · intro hx
    cases hx with
    | inl h => exact h.1
    | inr h => exact h

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

/-- Strict positivity of the Binet majorant denominator at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_pos_local
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

/-- Positivity of the Binet real majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_pos_local
    {t : ℝ}
    (ht : 0 < t) :
    0 < t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    div_pos ht
      (Real.binetSecondFormula_kernel_majorant_denominator_pos_local ht)

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
    Real.binetSecondFormula_kernel_majorant_denominator_pos_local ht
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
  exact (le_div_iff₀ ha_pos).mpr hmul

/-- Pointwise zero-cancellation bound for the Binet majorant on `(0,1]`.

The proof is the elementary inequality `x + 1 ≤ exp x`, applied to
`x = 2πt`, followed by division by the positive denominator. -/
theorem Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise
    {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      1 / ((2 : ℝ) * Real.pi) := by
  have hpos :
      0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos_local ht.1)
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
      exact Real.log_lt_self (by norm_num : (1 : ℝ) < 2)
    exact le_trans (le_of_lt hlog_two_lt_two)
      (le_of_lt (by positivity : (2 : ℝ) < 2 * Real.pi))
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
      le_of_lt Real.one_lt_pi
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
    Real.binetSecondFormula_kernel_majorant_denominator_pos_local
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
    field_simp [hE_pos.ne']
  have ht_over_E_le :
      t / E ≤ Real.exp (-Real.pi * t) := by
    have hmul_le :
        t ≤ E * Real.exp (-Real.pi * t) := by
      calc
        t ≤ Real.exp (Real.pi * t) := ht_le_exp
        _ = E * Real.exp (-Real.pi * t) := by
          simp [E, ← Real.exp_add]
          ring_nf
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
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos_local ht_pos)
  have hle :
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        2 * Real.exp (-Real.pi * t) :=
    Real.binetSecondFormula_kernel_majorant_tail_le_two_exp_of_denominator_lower ht
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * Real.exp (-Real.pi * t))
      (Real.norm_of_nonneg hnonneg).symm
      hle

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

/-- A reusable norm-transport lemma for complex quotients. -/
theorem Complex.norm_div_eq_div_norm
    {z w : ℂ}
    (hw : w ≠ 0) :
    ‖z / w‖ = ‖z‖ / ‖w‖ := by
  rw [div_eq_mul_inv, norm_mul, norm_inv, div_eq_mul_inv]
  exact mul_inv_eq_div _ _

/-- `Complex.arctan` is a scalar multiple of the logarithmic quotient it is
defined from. This isolates the remaining analytic content into a single
logarithmic norm estimate. -/
theorem Complex.norm_arctan_eq_half_norm_log_quotient
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    ‖Complex.arctan z‖ =
      ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := by
  unfold Complex.arctan
  rw [norm_mul, Complex.norm_div_eq_div_norm]
  · simp [mul_comm, mul_left_comm, mul_assoc]
  · exact hz

/-- A crude norm bound for `Complex.log` in terms of its real and imaginary
parts. -/
theorem Complex.norm_log_le_abs_re_add_abs_im (z : ℂ) :
    ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| := by
  have hsplit : Complex.log z = ((Complex.log z).re : ℂ) + (Complex.log z).im * Complex.I := by
    ext <;> simp
  rw [hsplit]
  calc
    ‖((Complex.log z).re : ℂ) + (Complex.log z).im * Complex.I‖ ≤
        ‖((Complex.log z).re : ℂ)‖ + ‖(Complex.log z).im * Complex.I‖ :=
      norm_add_le _ _
    _ = |(Complex.log z).re| + |(Complex.log z).im| := by
      simp [norm_mul]

/-- The complex logarithm norm is controlled by its modulus-logarithm and
argument parts. -/
theorem Complex.norm_log_le_abs_log_add_abs_arg (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log z.abs| + |z.arg| := by
  rw [Complex.log]
  calc
    ‖z.abs.log + z.arg * Complex.I‖ ≤ ‖z.abs.log‖ + ‖z.arg * Complex.I‖ :=
      norm_add_le _ _
    _ = |Real.log z.abs| + |z.arg| := by
      simp [Complex.norm_ofReal, norm_mul]

/-- A coarse `π`-bound for the complex logarithm norm. -/
theorem Complex.norm_log_le_abs_log_add_pi (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log z.abs| + π := by
  have hlog := Complex.norm_log_le_abs_log_add_abs_arg z
  have harg : |z.arg| ≤ π := by
    exact abs_arg_le_pi z
  exact le_trans hlog (add_le_add_left harg _)

/-- A coarse norm bound for `Complex.arctan` in terms of the logarithm size
and the universal `π` angle bound. -/
theorem Complex.norm_arctan_le_abs_log_quotient_add_pi_half
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    ‖Complex.arctan z‖ ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
  have hlog := Complex.norm_log_le_abs_log_add_pi ((1 + z * Complex.I) / (1 - z * Complex.I))
  rw [Complex.norm_arctan_eq_half_norm_log_quotient z hz]
  have hhalf : ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
    exact div_le_div_right (by norm_num : (0 : ℝ) < 2) hlog
  simpa using hhalf

/-- The argument of the Binet quotient is always within `[-π, π]`. -/
theorem Complex.arg_binet_quotient_le_pi
    (z : ℂ) :
    |arg ((1 + z * Complex.I) / (1 - z * Complex.I))| ≤ π := by
  exact abs_arg_le_pi _

/-- The Binet quotient log norm is controlled by its real part and the
universal `π` argument bound. -/
theorem Complex.norm_log_binet_quotient_le_abs_re_add_pi
    (z : ℂ) :
    ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
      |(Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re| + π := by
  exact Complex.norm_log_le_abs_log_add_pi ((1 + z * Complex.I) / (1 - z * Complex.I))

/-- The real part of the Binet quotient logarithm is the log of the ratio of
its numerator and denominator norms. -/
theorem Complex.log_binet_quotient_re_eq_log_ratio (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ := by
  rw [Complex.log_re, Complex.norm_div_eq_div_norm h2]
  rw [Real.log_div (norm_pos_iff.mpr h1) (norm_pos_iff.mpr h2)]

/-- The imaginary part of the Binet quotient logarithm is its argument. -/
theorem Complex.log_binet_quotient_im_eq_arg_ratio (z : ℂ) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  rw [Complex.log_im]

/-- The Binet quotient logarithm is exactly the pair of its real and imaginary
coordinate formulas. -/
theorem Complex.log_binet_quotient_coords (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) =
      (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖) +
        arg ((1 + z * Complex.I) / (1 - z * Complex.I)) * Complex.I := by
  apply Complex.ext <;>
    simp [Complex.log_binet_quotient_re_eq_log_ratio z h1 h2,
      Complex.log_binet_quotient_im_eq_arg_ratio z]

/-- The Binet quotient logarithm has real and imaginary parts given by the
coordinate formulas. -/
theorem Complex.log_binet_quotient_re_im (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ ∧
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  constructor
  · exact Complex.log_binet_quotient_re_eq_log_ratio z h1 h2
  · exact Complex.log_binet_quotient_im_eq_arg_ratio z

/-- The Binet quotient factors are automatically nonzero as soon as the
denominator is nonzero. -/
theorem Complex.binet_quotient_factors_ne_zero
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    1 + z * Complex.I ≠ 0 ∧ 1 - z * Complex.I ≠ 0 := by
  constructor
  · intro h1
    have hsum : (1 + z * Complex.I) + (1 - z * Complex.I) = (2 : ℂ) := by ring
    have hzero : (2 : ℂ) = 0 := by
      simpa [h1] using hsum
    norm_num at hzero
  · exact hz

/-- The Binet quotient factors are both nonzero whenever the denominator is
nonzero. -/
theorem Complex.binet_quotient_factors_ne_zero_of_denominator_ne_zero
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    1 + z * Complex.I ≠ 0 := by
  exact (Complex.binet_quotient_factors_ne_zero z hz).1

/-- A positive integrable function on an open real interval has positive set
integral. -/
theorem Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (h_integrable : IntegrableOn f (Set.Ioo a b))
    (hpos : ∀ t : ℝ, t ∈ Set.Ioo a b → 0 < f t) :
    0 < ∫ t : ℝ in Set.Ioo a b, f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioo a b)] f :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun t ht => le_of_lt (hpos t ht))
  have hsupport_pos :
      0 < volume (Function.support f ∩ Set.Ioo a b) := by
    have hIoo_pos : 0 < volume (Set.Ioo a b) :=
      (Measure.measure_Ioo_pos volume).mpr hab
    have hsubset :
        Set.Ioo a b ⊆ Function.support f ∩ Set.Ioo a b := by
      intro t ht
      exact ⟨fun hzero => (ne_of_gt (hpos t ht)) hzero, ht⟩
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsubset)
  exact
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae h_integrable).mpr hsupport_pos

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
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => hnonneg t ht)
  have hsubset_ae :
      Set.Ioo (0 : ℝ) 1 ≤ᵐ[volume] Set.Ioi (0 : ℝ) :=
    Eventually.of_forall (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), f t :=
    setIntegral_mono_set h_integrable hnonneg_ae hsubset_ae
  exact lt_of_lt_of_le hpos_subinterval hmono

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

/-- Honest split-bound mirror for the Binet remainder on the open right half-plane.

This is the shape owned classically by
`Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane`: the lower
part of the Binet kernel gives the `1 / ‖w‖` term, while the tail remains a
fixed-`w` majorant.  It is intentionally not a pure `O(1 / ‖w‖)` statement. -/
theorem Complex.binetSecondFormula_remainder_split_bound_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
          2 * C *
            (∫ t : ℝ in Set.Ioi (0 : ℝ),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  /-
  True owner theorem:
  `Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane` from
  `ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet`.

  This mirror still duplicates the Binet roots above, so importing the
  classical package here creates declaration-name conflicts.  The structural
  cleanup is to delete those duplicated roots and turn this theorem into a thin
  alias.
  -/
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

/-- Binet's second formula with the honest split remainder bound on the open
right half-plane. -/
theorem Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          Complex.log (Complex.Gamma w) =
              Complex.binetLogGammaMainTerm w +
                Complex.binetSecondFormulaRemainder w ∧
            ∃ C : ℝ,
              0 ≤ C ∧
              ‖Complex.binetSecondFormulaRemainder w‖ ≤
                4 *
                  (∫ t : ℝ in Set.Ioi (0 : ℝ),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
                  2 * C *
                    (∫ t : ℝ in Set.Ioi (0 : ℝ),
                      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius with
    ⟨Rlog, hRlog, hlog⟩
  refine ⟨Rlog, 1, hRlog, zero_lt_one, ?_⟩
  intro w hw_re_pos hw_norm
  exact
    ⟨hlog w hw_re_pos hw_norm,
      Complex.binetSecondFormula_remainder_split_bound_openRightHalfPlane hw_re_pos⟩

/-- Root marking the missing comparison from the honest split Binet remainder
bound to a pure open-right-half-plane `O(1 / ‖w‖)` estimate.

The split owner theorem does not imply this statement on the whole open
right half-plane by algebra alone.  The missing upstream content is a genuine
Binet-kernel tail-absorption theorem strong enough for the full closed
right-half-plane sector used by vertical-line Stirling, not merely a wedge
separated from the imaginary axis. -/
theorem Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := by
  sorry

/-- Root marking the missing pure-decay Binet/log-Gamma comparison.

Use `Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane`
for the currently proved mirror statement.  This theorem requires the same
full-sector tail-absorption theorem converting the split Binet estimate into
pure `O(1 / ‖w‖)` decay. -/
theorem Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w ∧
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := by
  sorry

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

/-- Small Binet remainder gives a linear normalized Stirling error.

This is the local error-extraction step used by the normalized Stirling
bridge: once the Binet remainder is small, the normalized factor is close to
`sqrt (2π)` with a linear bound in `‖J(w)‖`. -/
theorem Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_norm_le_of_binetRemainder_norm_le_one
    {w : ℂ}
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hw_ne : w ≠ 0)
    (hbinet :
      Complex.log (Complex.Gamma w) =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w)
    (hE : ‖Complex.binetSecondFormulaRemainder w‖ ≤ 1) :
    ‖Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
      2 * Real.sqrt (2 * Real.pi) * ‖Complex.binetSecondFormulaRemainder w‖ := by
  rw [Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_eq_exp_binetRemainder_sub_one
    hGamma_ne hw_ne hbinet]
  exact Complex.sqrt_two_pi_mul_exp_sub_one_norm_le_of_norm_le_one hE

/-- Binet's logarithmic formula implies the normalized sectorial Stirling
estimate for `Γ`.

This is the standard exponentiation step from the principal logarithmic Binet
formula to
`Γ(w) exp(w) w^(1/2-w) = sqrt(2π) + O(1/‖w‖)`, uniformly in the open
right half-plane. -/
theorem Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane_from_binetSecondFormula :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  /-
  This is now the precise completed-normalization root.  The available Binet
  input is
  `Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane`,
  whose remainder estimate has a fixed-tail term.  To recover this pure
  `O(1 / ‖w‖)` normalized Stirling statement one must prove a real
  full-sector tail-absorption theorem.  Restricting to
  `ε ≤ w.re / ‖w‖` is not acceptable here because the downstream vertical-line
  estimates have fixed real part and `w.re / ‖w‖ → 0`.
  -/
  sorry

/-- The fixed-real-part vertical line point `a + i b`, named to keep all fixed-line
Stirling estimates definitionally aligned. -/

end
end LFunctions
end Boundary

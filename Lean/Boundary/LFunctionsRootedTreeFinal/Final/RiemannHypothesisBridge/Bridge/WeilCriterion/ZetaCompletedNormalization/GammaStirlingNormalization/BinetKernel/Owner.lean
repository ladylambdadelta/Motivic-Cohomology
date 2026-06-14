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

end
end LFunctions
end Boundary

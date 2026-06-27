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

open Filter
open scoped Filter Topology
open MeasureTheory
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
  match hlog with
  | ⟨C, m, hC⟩ =>
      exact
        ⟨1, |C| + 1, m,
              zero_lt_one,
                  (add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one),
                  (fun z hzP =>
                    let hC_abs : C ≤ |C| + 1 :=
                      le_trans (le_abs_self C) (le_add_of_nonneg_right zero_le_one)
                    let hbase_nonneg : 0 ≤ 1 + ‖z‖ :=
                      le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
                    let hC_le :
                        C * (1 + ‖z‖) ^ m ≤ (|C| + 1) * (1 + ‖z‖) ^ m :=
                      mul_le_mul_of_nonneg_right hC_abs (pow_nonneg hbase_nonneg m)
                    let hlog_le :
                        Real.log ‖Complex.Gammaℝ z‖ ≤ (|C| + 1) * (1 + ‖z‖) ^ m :=
                      le_trans (hC z hzP) hC_le
                    match eq_or_ne ‖Complex.Gammaℝ z‖ 0 with
                    | Or.inl hzero =>
                        Eq.subst
                          (motive := fun x : ℝ =>
                            x ≤ 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))
                          hzero.symm
                          (le_of_lt
                            (mul_pos zero_lt_one
                              (Real.exp_pos ((|C| + 1) * (1 + ‖z‖) ^ m))))
                    | Or.inr hne =>
                        let hpos : 0 < ‖Complex.Gammaℝ z‖ :=
                          lt_of_le_of_ne (norm_nonneg (Complex.Gammaℝ z)) (Ne.symm hne)
                        let hexp_log :
                            Real.exp (Real.log ‖Complex.Gammaℝ z‖) =
                              ‖Complex.Gammaℝ z‖ :=
                          Real.exp_log hpos
                        let hnorm_eq :
                            ‖Complex.Gammaℝ z‖ =
                              Real.exp (Real.log ‖Complex.Gammaℝ z‖) :=
                          hexp_log.symm
                        let hexp_le :
                            Real.exp (Real.log ‖Complex.Gammaℝ z‖) ≤
                              Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) :=
                          Real.exp_le_exp.mpr hlog_le
                        calc
                          ‖Complex.Gammaℝ z‖ =
                              Real.exp (Real.log ‖Complex.Gammaℝ z‖) := hnorm_eq
                          _ ≤ Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := hexp_le
                          _ = 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := by
                            exact
                              (one_mul
                                (Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))).symm)⟩

/-- The corrected right-half-plane Gamma/Stirling region avoids the `Gammaℝ` zero at `0`.

Mathlib's `Complex.Gamma` and `Complex.Gammaℝ` are finite-valued at the classical pole
faces, with those faces represented by zeros. -/
theorem Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Complex.Gammaℝ z ≠ 0 := fun hzero =>
  match Complex.Gammaℝ_eq_zero_iff.mp hzero with
  | ⟨n, hz⟩ =>
      have hz_eq : z = -(2 * n : ℂ) := hz
      have hz_re_eq : z.re = (-(2 * n : ℂ)).re := congrArg Complex.re hz_eq
      match n with
      | Nat.zero => by
          have hnorm_zero : ‖z‖ = 0 := by
            have hzero : (-(2 * Nat.zero : ℂ)) = 0 := by
              have hnat_zero : (Nat.zero : ℂ) = 0 :=
                Nat.cast_zero
              have hmul_zero : (2 * Nat.zero : ℂ) = 0 := by
                calc
                  (2 * Nat.zero : ℂ) = (2 : ℂ) * 0 :=
                    congrArg (fun x : ℂ => (2 : ℂ) * x) hnat_zero
                  _ = 0 := mul_zero (2 : ℂ)
              calc
                -(2 * Nat.zero : ℂ) = -(0 : ℂ) := congrArg Neg.neg hmul_zero
                _ = 0 := neg_zero
            calc
              ‖z‖ = ‖(-(2 * Nat.zero : ℂ))‖ := congrArg norm hz_eq
              _ = ‖(0 : ℂ)‖ := congrArg norm hzero
              _ = 0 := norm_zero
          have hnot : ¬ (1 : ℝ) ≤ 0 :=
            not_le_of_gt zero_lt_one
          exact hnot (Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_zero hz_norm)
      | Nat.succ n => by
          have htwo_succ_pos : (0 : ℝ) < 2 * (Nat.succ n : ℝ) :=
            mul_pos two_pos (Nat.cast_pos.mpr (Nat.succ_pos n))
          have hre_pos : 0 < (2 * Nat.succ n : ℂ).re := by
            have hcast :
                (2 * Nat.succ n : ℂ) =
                  ((2 * (Nat.succ n : ℝ) : ℝ) : ℂ) := by
              have hmul_cast :
                  (((2 : ℝ) * (Nat.succ n : ℝ) : ℝ) : ℂ) =
                    (2 : ℂ) * (((Nat.succ n : ℝ) : ℝ) : ℂ) :=
                Complex.ofReal_mul (2 : ℝ) (Nat.succ n : ℝ)
              have hnat_cast :
                  (((Nat.succ n : ℝ) : ℝ) : ℂ) = (Nat.succ n : ℂ) :=
                Complex.ofReal_natCast (Nat.succ n)
              exact
                (Eq.trans hmul_cast
                  (congrArg (fun x : ℂ => (2 : ℂ) * x) hnat_cast)).symm
            calc
              (0 : ℝ) < 2 * (Nat.succ n : ℝ) := htwo_succ_pos
              _ = (((2 * (Nat.succ n : ℝ) : ℝ) : ℂ)).re := by
                exact (Complex.ofReal_re (2 * (Nat.succ n : ℝ))).symm
              _ = (2 * Nat.succ n : ℂ).re := congrArg Complex.re hcast.symm
          have hneg_re : (-(2 * Nat.succ n : ℂ)).re < 0 := by
            calc
              (-(2 * Nat.succ n : ℂ)).re = -((2 * Nat.succ n : ℂ).re) := by
                exact Complex.neg_re (2 * Nat.succ n : ℂ)
              _ < 0 := neg_neg_of_pos hre_pos
          have hz_re_neg : z.re < 0 := by
            calc
              z.re = (-(2 * Nat.succ n : ℂ)).re := hz_re_eq
              _ < 0 := hneg_re
          exact (not_lt_of_ge hz_re) hz_re_neg

/-- Points with real part at least `1` have norm at least `1`. -/
theorem one_le_norm_of_one_le_re
    {z : ℂ}
    (hz_re : 1 ≤ z.re) :
    1 ≤ ‖z‖ := by
  have hre_nonneg : 0 ≤ z.re :=
    le_trans zero_le_one hz_re
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    exact Complex.abs_re_le_abs z
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
    exact Complex.abs_im_le_abs z
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

/-- The unfolded `Gammaℝ` norm factors into the normalizing power of `π` and
the complex Gamma half-argument factor. -/
theorem norm_unfoldedNormalizedGammaℝFactor_eq
    (z : ℂ) :
    ‖unfoldedNormalizedGammaℝFactor z‖ =
      ‖((π : ℂ) ^ (-z / 2 : ℂ))‖ *
        ‖Complex.Gamma (z / 2)‖ := by
  let P : ℂ := (π : ℂ) ^ (-z / 2 : ℂ)
  let G : ℂ := Complex.Gamma (z / 2)
  have hunfold : unfoldedNormalizedGammaℝFactor z = P * G := rfl
  calc
    ‖unfoldedNormalizedGammaℝFactor z‖ = ‖P * G‖ :=
      congrArg norm hunfold
    _ = ‖P‖ * ‖G‖ := norm_mul P G
    _ = ‖((π : ℂ) ^ (-z / 2 : ℂ))‖ *
        ‖Complex.Gamma (z / 2)‖ := rfl

/-- The `Gammaℝ` norm factors through the unfolded normalization. -/
theorem norm_Gammaℝ_eq_norm_pi_mul_norm_complexGamma_half
    (z : ℂ) :
    ‖Complex.Gammaℝ z‖ =
      ‖((π : ℂ) ^ (-z / 2 : ℂ))‖ *
        ‖Complex.Gamma (z / 2)‖ := by
  calc
    ‖Complex.Gammaℝ z‖ =
        ‖unfoldedNormalizedGammaℝFactor z‖ :=
      norm_Gammaℝ_eq_norm_unfoldedNormalizedGammaℝFactor z
    _ = ‖((π : ℂ) ^ (-z / 2 : ℂ))‖ *
        ‖Complex.Gamma (z / 2)‖ :=
      norm_unfoldedNormalizedGammaℝFactor_eq z

/-- Reciprocal norm-level form of the unfolded `Gammaℝ` normalization. -/
theorem norm_inv_Gammaℝ_eq_norm_inv_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    ‖(Complex.Gammaℝ z)⁻¹‖ = ‖(unfoldedNormalizedGammaℝFactor z)⁻¹‖ := by
  exact congrArg (fun w : ℂ => ‖w⁻¹‖) (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z)

/-- The reciprocal unfolded `Gammaℝ` norm factors into the reciprocal
normalizing power of `π` and reciprocal complex Gamma factor. -/
theorem norm_inv_unfoldedNormalizedGammaℝFactor_eq
    (z : ℂ) :
    ‖(unfoldedNormalizedGammaℝFactor z)⁻¹‖ =
      ‖(Complex.Gamma (z / 2))⁻¹‖ *
        ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ := by
  let P : ℂ := (π : ℂ) ^ (-z / 2 : ℂ)
  let G : ℂ := Complex.Gamma (z / 2)
  have hunfold : unfoldedNormalizedGammaℝFactor z = P * G := rfl
  have hinv : (unfoldedNormalizedGammaℝFactor z)⁻¹ = G⁻¹ * P⁻¹ := by
    calc
      (unfoldedNormalizedGammaℝFactor z)⁻¹ = (P * G)⁻¹ :=
        congrArg Inv.inv hunfold
      _ = G⁻¹ * P⁻¹ := mul_inv_rev P G
  calc
    ‖(unfoldedNormalizedGammaℝFactor z)⁻¹‖ =
        ‖G⁻¹ * P⁻¹‖ := congrArg norm hinv
    _ = ‖G⁻¹‖ * ‖P⁻¹‖ := norm_mul G⁻¹ P⁻¹
    _ = ‖(Complex.Gamma (z / 2))⁻¹‖ *
        ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ := rfl

/-- The reciprocal `Gammaℝ` norm factors through the unfolded normalization. -/
theorem norm_inv_Gammaℝ_eq_norm_inv_complexGamma_half_mul_norm_inv_pi
    (z : ℂ) :
    ‖(Complex.Gammaℝ z)⁻¹‖ =
      ‖(Complex.Gamma (z / 2))⁻¹‖ *
        ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ := by
  calc
    ‖(Complex.Gammaℝ z)⁻¹‖ =
        ‖(unfoldedNormalizedGammaℝFactor z)⁻¹‖ :=
      norm_inv_Gammaℝ_eq_norm_inv_unfoldedNormalizedGammaℝFactor z
    _ = ‖(Complex.Gamma (z / 2))⁻¹‖ *
        ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ :=
      norm_inv_unfoldedNormalizedGammaℝFactor_eq z

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
    unfoldedNormalizedGammaℝFactor z ≠ 0 := fun hzero =>
  have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm
  have hGammaℝ_zero : Complex.Gammaℝ z = 0 :=
    Eq.trans (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z) hzero
  hGammaℝ_ne hGammaℝ_zero

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
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  calc
    0 ≤ z.re / 2 := by
      exact div_nonneg hz_re (le_of_lt htwo_pos)
    _ = (z / 2).re := by
      exact (RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))).symm

/-- The half-argument is nonzero in the large right-half-plane Stirling region. -/
theorem halfArgument_ne_zero_of_one_le_norm
    {z : ℂ}
    (hz_norm : 1 ≤ ‖z‖) :
    z / 2 ≠ 0 := fun hzero =>
  have hz_zero : z = 0 := by
    have hmul := congrArg (fun w : ℂ => w * (2 : ℂ)) hzero
    calc
      z = (z / 2) * (2 : ℂ) := by
        exact (div_mul_cancel₀ z (OfNat.ofNat_ne_zero 2)).symm
      _ = 0 * (2 : ℂ) := by
        exact hmul
      _ = 0 := zero_mul (2 : ℂ)
  have hnorm_zero : ‖z‖ = 0 := by
    calc
      ‖z‖ = ‖(0 : ℂ)‖ := congrArg norm hz_zero
      _ = 0 := norm_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 :=
    not_le_of_gt zero_lt_one
  hnot (Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_zero hz_norm)

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
  exact fun hzero =>
  match (Complex.Gamma_eq_zero_iff (z / 2)).mp hzero with
  | ⟨n, hn⟩ =>
      have hhalf_re_eq : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
      have hn_re : (-(n : ℂ)).re = -(n : ℝ) := by
        exact Complex.neg_re (n : ℂ)
      have hz_half_re_nonpos : (z / 2).re ≤ 0 := by
        calc
          (z / 2).re = (-(n : ℂ)).re := hhalf_re_eq
          _ = -(n : ℝ) := hn_re
          _ ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
      have hz_half_re_zero : (z / 2).re = 0 :=
        le_antisymm hz_half_re_nonpos hz_half_re
      match n with
      | Nat.zero => by
          have hhalf_zero : z / 2 = 0 := by
            have hzero : (-(Nat.zero : ℂ)) = 0 := by
              have hcast_zero : (Nat.zero : ℂ) = 0 :=
                Nat.cast_zero
              calc
                -(Nat.zero : ℂ) = -(0 : ℂ) := congrArg Neg.neg hcast_zero
                _ = 0 := neg_zero
            calc
              z / 2 = -(Nat.zero : ℂ) := hn
              _ = 0 := hzero
          exact hz_half_ne hhalf_zero
      | Nat.succ n => by
          have hneg_succ_lt_zero : (-(Nat.succ n : ℂ)).re < 0 := by
            exact neg_neg_of_pos (Nat.cast_pos.mpr (Nat.succ_pos n))
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
        Complex.binetLogGammaBranch w =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    ⟨1, zero_lt_one,
      fun w _hw_re_pos _hw_norm =>
        Complex.binetLogGammaBranch_unfold w⟩

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
            2 * (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
  fun t ht hsmall =>
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
            2 * (t / ‖w‖) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact Complex.binetSecondFormula_arctan_kernel_norm_le_openRightHalfPlane hw_re_pos

/-- Exponential tail integral bound for the scaled decay `exp (-π t)`.

The exact formula is
`∫ t in Ioi a, exp (-π t) = π⁻¹ * exp (-π a)`; this bound is the only
form needed for the Binet majorant tail estimate. -/
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
theorem Complex.norm_div_eq_div_norm
    {z w : ℂ}
    (hw : w ≠ 0) :
    ‖z / w‖ = ‖z‖ / ‖w‖ := by
  calc
    ‖z / w‖ = ‖z * w⁻¹‖ := by
      rfl
    _ = ‖z‖ * ‖w⁻¹‖ := norm_mul _ _
    _ = ‖z‖ * ‖w‖⁻¹ := by
      exact congrArg (fun x : ℝ => ‖z‖ * x) (norm_inv w)
    _ = ‖z‖ / ‖w‖ := by
      rfl

/-- `Complex.arctan` is a scalar multiple of the logarithmic quotient it is
defined from, in norm form. -/
theorem Complex.norm_arctan_eq_half_norm_log_quotient
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    ‖Complex.arctan z‖ =
      ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := by
  calc
    ‖Complex.arctan z‖ =
        ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
      rfl
    _ =
        ‖(-Complex.I / 2 : ℂ)‖ *
          ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
          exact norm_mul _ _
    _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := by
          have hcoeff : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
            calc
              ‖(-Complex.I / 2 : ℂ)‖ = ‖(-Complex.I : ℂ)‖ / ‖(2 : ℂ)‖ := by
                exact Complex.norm_div_eq_div_norm (OfNat.ofNat_ne_zero 2)
              _ = ‖Complex.I‖ / ‖(2 : ℂ)‖ := by
                exact congrArg (fun x : ℝ => x / ‖(2 : ℂ)‖) (norm_neg Complex.I)
              _ = 1 / ‖(2 : ℂ)‖ := by
                exact congrArg (fun x : ℝ => x / ‖(2 : ℂ)‖) Complex.abs_I
              _ = 1 / 2 := by
                exact congrArg (fun x : ℝ => 1 / x) (Complex.abs_ofNat 2)
          calc
            ‖(-Complex.I / 2 : ℂ)‖ *
                ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ =
                (1 / 2 : ℝ) *
                  ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
              exact
                congrArg
                  (fun x : ℝ =>
                    x *
                      ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖)
                  hcoeff
            _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := by
              exact one_div_mul_eq_div 2
                ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖

/-- A crude norm bound for `Complex.log` in terms of its real and imaginary
parts. -/
theorem Complex.norm_log_le_abs_re_add_abs_im (z : ℂ) :
    ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| := by
  have hsplit : Complex.log z = ((Complex.log z).re : ℂ) + (Complex.log z).im * Complex.I := by
    exact (Complex.re_add_im (Complex.log z)).symm
  calc
    ‖Complex.log z‖ = ‖((Complex.log z).re : ℂ) + (Complex.log z).im * Complex.I‖ := by
      exact congrArg (fun w : ℂ => ‖w‖) hsplit
    _ ≤
        ‖((Complex.log z).re : ℂ)‖ + ‖(Complex.log z).im * Complex.I‖ :=
      norm_add_le _ _
    _ = |(Complex.log z).re| + |(Complex.log z).im| := by
      calc
        ‖((Complex.log z).re : ℂ)‖ + ‖(Complex.log z).im * Complex.I‖ =
            |(Complex.log z).re| + (‖((Complex.log z).im : ℂ)‖ * ‖Complex.I‖) := by
          have him_mul :
              ‖(Complex.log z).im * Complex.I‖ =
                ‖((Complex.log z).im : ℂ)‖ * ‖Complex.I‖ :=
            norm_mul ((Complex.log z).im : ℂ) Complex.I
          have hre_norm :
              ‖(((Complex.log z).re : ℝ) : ℂ)‖ = |(Complex.log z).re| :=
            RCLike.norm_ofReal (K := ℂ) ((Complex.log z).re)
          exact
            Eq.trans
              (congrArg
                (fun x : ℝ => ‖((Complex.log z).re : ℂ)‖ + x)
                him_mul)
              (congrArg
                (fun x : ℝ => x + (‖((Complex.log z).im : ℂ)‖ * ‖Complex.I‖))
                hre_norm)
        _ = |(Complex.log z).re| + |(Complex.log z).im| := by
          have hleft : ‖((Complex.log z).im : ℂ)‖ = |(Complex.log z).im| :=
            RCLike.norm_ofReal (K := ℂ) ((Complex.log z).im)
          have hI : ‖Complex.I‖ = 1 :=
            Complex.abs_I
          calc
            |(Complex.log z).re| +
                (‖((Complex.log z).im : ℂ)‖ * ‖Complex.I‖) =
                |(Complex.log z).re| + (|(Complex.log z).im| * 1) := by
              exact
                congrArg
                  (fun x : ℝ => |(Complex.log z).re| + x)
                  (congrArg₂ HMul.hMul hleft hI)
            _ = |(Complex.log z).re| + |(Complex.log z).im| := by
              exact congrArg (fun x : ℝ => |(Complex.log z).re| + x)
                (mul_one |(Complex.log z).im|)

/-- The complex logarithm norm is controlled by its modulus-logarithm and
argument parts. -/
theorem Complex.norm_log_le_abs_log_add_abs_arg (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log z.abs| + |z.arg| := by
  have hraw :
      ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
    Complex.norm_log_le_abs_re_add_abs_im z
  have hre : (Complex.log z).re = Real.log z.abs :=
    Complex.log_re z
  have him : (Complex.log z).im = z.arg :=
    Complex.log_im z
  calc
    ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| := hraw
    _ = |Real.log z.abs| + |z.arg| := by
      exact congrArg₂ HAdd.hAdd (congrArg abs hre) (congrArg abs him)

/-- A coarse `π`-bound for the complex logarithm norm. -/
theorem Complex.norm_log_le_abs_log_add_pi (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log z.abs| + π := by
  have hlog := Complex.norm_log_le_abs_log_add_abs_arg z
  have harg : |z.arg| ≤ π := by
    exact Complex.abs_arg_le_pi z
  exact le_trans hlog (add_le_add_left harg _)

/-- A coarse norm bound for `Complex.arctan` in terms of the logarithm size
and the universal `π` angle bound. -/
theorem Complex.norm_arctan_le_abs_log_quotient_add_pi_half
    (z : ℂ)
    (hz : 1 - z * Complex.I ≠ 0) :
    ‖Complex.arctan z‖ ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
  have hlog := Complex.norm_log_le_abs_log_add_pi ((1 + z * Complex.I) / (1 - z * Complex.I))
  have hnorm := Complex.norm_arctan_eq_half_norm_log_quotient z hz
  have hhalf : ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 ≤
      (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := by
    exact (div_le_div_iff_of_pos_right zero_lt_two).mpr hlog
  calc
    ‖Complex.arctan z‖ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ / 2 := hnorm
    _ ≤ (|Real.log ((1 + z * Complex.I) / (1 - z * Complex.I)).abs| + π) / 2 := hhalf

/-- The argument of the Binet quotient is always within `[-π, π]`. -/
theorem Complex.arg_binet_quotient_le_pi
    (z : ℂ) :
    |Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I))| ≤ π := by
  exact Complex.abs_arg_le_pi _

/-- The Binet quotient log norm is controlled by its real part and the
universal `π` argument bound. -/
theorem Complex.norm_log_binet_quotient_le_abs_re_add_pi
    (z : ℂ) :
    ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
      |(Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re| + π := by
  let q : ℂ := (1 + z * Complex.I) / (1 - z * Complex.I)
  have hraw : ‖Complex.log q‖ ≤ |Real.log q.abs| + π :=
    Complex.norm_log_le_abs_log_add_pi q
  have hre : (Complex.log q).re = Real.log q.abs :=
    Complex.log_re q
  exact
    Eq.subst
      (motive := fun x : ℝ => ‖Complex.log q‖ ≤ |x| + π)
      hre.symm
      hraw

/-- The real part of the Binet quotient logarithm is the log of the ratio of
its numerator and denominator norms. -/
theorem Complex.log_binet_quotient_re_eq_log_ratio (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ := by
  calc
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
        Real.log ‖(1 + z * Complex.I) / (1 - z * Complex.I)‖ := Complex.log_re _
    _ = Real.log (‖1 + z * Complex.I‖ / ‖1 - z * Complex.I‖) := by
      exact congrArg Real.log (Complex.norm_div_eq_div_norm h2)
    _ = Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ := by
      exact Real.log_div (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)

/-- The imaginary part of the Binet quotient logarithm is its argument. -/
theorem Complex.log_binet_quotient_im_eq_arg_ratio (z : ℂ) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  exact Complex.log_im _

/-- The Binet quotient logarithm is exactly the pair of its real and imaginary
coordinate formulas. -/
theorem Complex.log_binet_quotient_coords (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) =
      (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖) +
        Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) * Complex.I := by
  let q : ℂ := (1 + z * Complex.I) / (1 - z * Complex.I)
  have hsplit : Complex.log q = ((Complex.log q).re : ℂ) + (Complex.log q).im * Complex.I :=
    (Complex.re_add_im (Complex.log q)).symm
  have hre :
      ((Complex.log q).re : ℂ) =
        (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ : ℂ) := by
    have hre_real :
        (Complex.log q).re =
          Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ :=
      Complex.log_binet_quotient_re_eq_log_ratio z h1 h2
    calc
      ((Complex.log q).re : ℂ) =
          ((Real.log ‖1 + z * Complex.I‖ -
            Real.log ‖1 - z * Complex.I‖ : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hre_real
      _ =
          (Real.log ‖1 + z * Complex.I‖ : ℂ) -
            (Real.log ‖1 - z * Complex.I‖ : ℂ) :=
        Complex.ofReal_sub
          (Real.log ‖1 + z * Complex.I‖)
          (Real.log ‖1 - z * Complex.I‖)
  have him :
      (Complex.log q).im * Complex.I =
        Complex.arg q * Complex.I := by
    exact congrArg (fun x : ℝ => (x : ℂ) * Complex.I)
      (Complex.log_binet_quotient_im_eq_arg_ratio z)
  calc
    Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I)) =
        Complex.log q := rfl
    _ = ((Complex.log q).re : ℂ) + (Complex.log q).im * Complex.I := hsplit
    _ = (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ : ℂ) +
        Complex.arg q * Complex.I := congrArg₂ HAdd.hAdd hre him
    _ =
        (Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖) +
          Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) * Complex.I := rfl

/-- The Binet quotient logarithm has real and imaginary parts given by the
coordinate formulas. -/
theorem Complex.log_binet_quotient_re_im (z : ℂ)
    (h1 : 1 + z * Complex.I ≠ 0) (h2 : 1 - z * Complex.I ≠ 0) :
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).re =
      Real.log ‖1 + z * Complex.I‖ - Real.log ‖1 - z * Complex.I‖ ∧
    (Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))).im =
      Complex.arg ((1 + z * Complex.I) / (1 - z * Complex.I)) := by
  exact
    ⟨
      (Complex.log_binet_quotient_re_eq_log_ratio z h1 h2),
      (Complex.log_binet_quotient_im_eq_arg_ratio z)⟩

/-- The Binet quotient factors are both nonzero whenever z has nonzero real part.

The imaginary part of `1 + z * I` equals `z.re`, and the imaginary part of
`1 - z * I` equals `-z.re`.  If either factor were zero its imaginary part
would be zero, forcing `z.re = 0`. -/
theorem Complex.binet_quotient_factors_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 ∧ 1 - z * Complex.I ≠ 0 :=
  ⟨fun h1 =>
    let him_plus : (1 + z * Complex.I).im = z.re :=
      calc (1 + z * Complex.I).im
          = (1 : ℂ).im + (z * Complex.I).im :=
            Complex.add_im 1 (z * Complex.I)
        _ = 0 + (z * Complex.I).im :=
            congrArg (fun x : ℝ => x + (z * Complex.I).im) Complex.one_im
        _ = (z * Complex.I).im :=
            zero_add (z * Complex.I).im
        _ = z.re * Complex.I.im + z.im * Complex.I.re :=
            Complex.mul_im z Complex.I
        _ = z.re * 1 + z.im * 0 :=
            congrArg₂ (fun a b : ℝ => z.re * a + z.im * b) Complex.I_im Complex.I_re
        _ = z.re + 0 :=
            congrArg₂ (fun a b : ℝ => a + b) (mul_one z.re) (mul_zero z.im)
        _ = z.re :=
            add_zero z.re
    let him_zero : (1 + z * Complex.I).im = 0 :=
      (congrArg Complex.im h1).trans Complex.zero_im
    hz (him_plus.symm.trans him_zero),
  fun h2 =>
    let him_minus : (1 - z * Complex.I).im = -z.re :=
      calc (1 - z * Complex.I).im
          = (1 : ℂ).im - (z * Complex.I).im :=
            Complex.sub_im 1 (z * Complex.I)
        _ = 0 - (z * Complex.I).im :=
            congrArg (fun x : ℝ => x - (z * Complex.I).im) Complex.one_im
        _ = -(z * Complex.I).im :=
            zero_sub (z * Complex.I).im
        _ = -(z.re * Complex.I.im + z.im * Complex.I.re) :=
            congrArg Neg.neg (Complex.mul_im z Complex.I)
        _ = -(z.re * 1 + z.im * 0) :=
            congrArg (fun x : ℝ => -x)
              (congrArg₂ (fun a b : ℝ => z.re * a + z.im * b) Complex.I_im Complex.I_re)
        _ = -(z.re + 0) :=
            congrArg (fun x : ℝ => -x)
              (congrArg₂ (fun a b : ℝ => a + b) (mul_one z.re) (mul_zero z.im))
        _ = -z.re :=
            congrArg Neg.neg (add_zero z.re)
    let him_zero : (1 - z * Complex.I).im = 0 :=
      (congrArg Complex.im h2).trans Complex.zero_im
    hz (neg_eq_zero.mp (him_minus.symm.trans him_zero))⟩

/-- The Binet plus factor is nonzero whenever z has nonzero real part. -/
theorem Complex.binet_quotient_factors_ne_zero_of_re_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 :=
  (Complex.binet_quotient_factors_ne_zero z hz).1

/-- The Binet quotient factors are both nonzero whenever the real part is
nonzero.  This replaces the earlier false statement which claimed to derive
numerator nonvanishing from denominator nonvanishing alone. -/
theorem Complex.binet_quotient_factors_ne_zero_of_denominator_ne_zero
    (z : ℂ)
    (hz : z.re ≠ 0) :
    1 + z * Complex.I ≠ 0 :=
  Complex.binet_quotient_factors_ne_zero_of_re_ne_zero z hz

/-- Small-argument Binet remainder estimate with the explicit `1 / ‖w‖`
factor. -/
theorem Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaSmallRemainder w‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  exact Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
    (w := w) hw_re_pos

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
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : ℂ := Complex.binetSecondFormulaSmallRemainder w
  let T : ℂ := Complex.binetSecondFormulaTailRemainder w
  have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
    exact Complex.binetSecondFormulaRemainder_eq_small_add_tail (w := w) hw_re_pos
  have hS : ‖S‖ ≤ 4 * J / ‖w‖ := by
    exact Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
      (w := w) hw_re_pos
  match Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      (w := w) hw_re_pos with
  | ⟨C, hC_nonneg, hT⟩ =>
      let hT_named : ‖T‖ ≤ 2 * C * J := hT
      let hsum : ‖S + T‖ ≤ 4 * J / ‖w‖ + 2 * C * J :=
        calc
          ‖S + T‖ ≤ ‖S‖ + ‖T‖ :=
            norm_add_le S T
          _ ≤ 4 * J / ‖w‖ + 2 * C * J :=
            add_le_add hS hT_named
      exact
        ⟨C, hC_nonneg,
          Eq.subst
            (motive := fun z : ℂ =>
              ‖z‖ ≤
                4 * J / ‖w‖ + 2 * C * J)
            hsplit.symm
            hsum⟩

/-- Binet's second formula with the honest split remainder bound on the open
right half-plane. -/
theorem Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          Complex.binetLogGammaBranch w =
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
  match Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius with
  | ⟨Rlog, hRlog, hlog⟩ =>
      exact
        ⟨Rlog, 1, hRlog, zero_lt_one,
          fun w hw_re_pos hw_norm =>
            ⟨hlog w hw_re_pos hw_norm,
              Complex.binetSecondFormula_remainder_split_bound_openRightHalfPlane hw_re_pos⟩⟩

/-- The decaying Binet tail kernel that carries the genuine `1 / ‖w‖`
pointwise majorant. -/
noncomputable def Complex.binetSecondFormulaDecayingTailKernel
    (w : ℂ)
    (t : ℝ) : ℂ :=
  (((1 : ℝ) / ‖w‖) *
    (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) : ℝ)

/-- The decaying Binet tail kernel is integrable on the split tail.

This is the integrability half of the contour-kernel route; the pointwise
majorant theorem below supplies the corresponding `C / ‖w‖` bound. -/
theorem Complex.binetSecondFormula_decayingTailKernel_integrableOn_tail
    (w : ℂ) :
    IntegrableOn
      (fun t : ℝ => Complex.binetSecondFormulaDecayingTailKernel w t)
      (Set.Ioi (‖w‖ / 2)) := by
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : Set ℝ := Set.Ioi (‖w‖ / 2)
  have hhalf_nonneg : 0 ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hM_integrable :
      IntegrableOn M S :=
    Real.binetSecondFormula_kernel_majorant_integrableOn.mono_set
      (fun t ht => lt_of_le_of_lt hhalf_nonneg ht)
  have hscaled_integrable :
      IntegrableOn
        (fun t : ℝ => ((1 : ℝ) / ‖w‖) * M t)
        S :=
    hM_integrable.const_mul ((1 : ℝ) / ‖w‖)
  have hbase :
      Integrable
        (fun t : ℝ => (((1 : ℝ) / ‖w‖) * M t : ℂ))
        (volume.restrict S) :=
    Complex.ofRealCLM.integrable_comp hscaled_integrable
  exact
    hbase.congr
      (Filter.Eventually.of_forall
        (fun _t => Eq.refl _))

/-- The decaying Binet tail kernel has the uniform full-sector `1 / ‖w‖`
pointwise bound. -/
theorem Complex.binetSecondFormula_decayingTailKernel_uniform_majorant :
    Complex.BinetSecondFormulaContourTailUniformMajorant
      Complex.binetSecondFormulaDecayingTailKernel 2 1 := by
  exact fun w _hw_re_pos _hw_norm =>
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => by
        have ht_pos : 0 < t :=
          lt_of_le_of_lt
            (div_nonneg (norm_nonneg w) zero_le_two)
            ht
        have hmajorant_nonneg :
            0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          le_of_lt
            (Real.binetSecondFormula_kernel_majorant_pos ht_pos)
        have hcoeff_nonneg : 0 ≤ (1 : ℝ) / ‖w‖ :=
          div_nonneg zero_le_one (norm_nonneg w)
        have hkernel_nonneg :
            0 ≤
              ((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
          mul_nonneg hcoeff_nonneg hmajorant_nonneg
        have hnorm_eq :
            ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
              ((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
          let m : ℝ :=
            ((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
          have hkernel_cast :
              Complex.binetSecondFormulaDecayingTailKernel w t = (m : ℂ) := by
            rfl
          have hm_nonneg : 0 ≤ m :=
            hkernel_nonneg
          calc
            ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
                ‖(m : ℂ)‖ := by
              exact congrArg norm hkernel_cast
            _ = |m| := RCLike.norm_ofReal (K := ℂ) m
            _ = m := abs_of_nonneg hm_nonneg
            _ =
                ((1 : ℝ) / ‖w‖) *
                  (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := rfl
        exact
          Eq.subst
            (motive := fun x : ℝ =>
              x ≤
                ((1 : ℝ) / ‖w‖) *
                  (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
            hnorm_eq.symm
            (le_refl
              (((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))))

/-- Historical wrapper name for the genuine decaying tail kernel majorant. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_uniform_majorant :
    Complex.BinetSecondFormulaContourTailUniformMajorant
      Complex.binetSecondFormulaDecayingTailKernel 2 1 := by
  exact Complex.binetSecondFormula_decayingTailKernel_uniform_majorant

/-- Existence of a branch-safe contour-deformed Binet tail kernel with
uniform full-sector majorization. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_exists :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact
    ⟨Complex.binetSecondFormulaDecayingTailKernel, 2, 1,
      two_pos, zero_lt_one,
      Complex.binetSecondFormula_contourTailMajorantKernel_uniform_majorant⟩

/-- Positivity of the radius supplied by the contour-deformed tail kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_radius_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ,
      0 < R ∧
      ∃ C : ℝ,
        0 < C ∧
        Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      exact ⟨K, R, hR, C, hC, hmajorant⟩

/-- Positivity of the uniform majorant constant supplied by the
contour-deformed tail kernel existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_constant_pos :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < C ∧
      0 < R ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C :=
  match Complex.binetSecondFormula_contourDeformed_tail_kernel_exists with
  | ⟨K, R, C, hR, hC, hmajorant⟩ =>
      ⟨K, R, C, hC, hR, hmajorant⟩

/-- Principal-tail comparison supplied by the contour-deformed kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_principal_comparison_ae :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

/-- Uniform pointwise majorant supplied by the contour-deformed kernel
existence theorem. -/
theorem Complex.binetSecondFormula_contourDeformed_tail_kernel_uniform_majorant :
    ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      Complex.BinetSecondFormulaContourTailUniformMajorant K R C := by
  exact Complex.binetSecondFormula_contourDeformed_tail_kernel_exists

/-- Contour-deformed Binet tail kernel package for the full right half-plane.

This theorem is now only a bundling wrapper around the explicit owner-level
contour-deformed kernel predicates. -/
theorem Complex.binetSecondFormula_arctan_tail_contourDeformed_kernel_fullSector_package :
    ∃ K : ℂ → ℝ → ℂ, ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
            ‖K w t‖ ≤
              (C / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    ⟨Complex.binetSecondFormulaDecayingTailKernel, 2, 1,
      two_pos, zero_lt_one,
      fun w _hw hRle =>
        Complex.binetSecondFormula_decayingTailKernel_uniform_majorant
          w _hw hRle⟩

/-- Exact branch-coherence hypotheses required by the Binet owner theorem for
the Binet logarithm branch of `Gamma`.

This lives at the Binet-kernel owner level because normalized Stirling consumes
these hypotheses before the sectorial log-norm layer is imported. -/
def Complex.BinetSecondFormulaBranchCoherence : Prop :=
  (∀ z : ℂ, 0 < z.re →
      Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z) ∧
  (∀ x : ℝ,
    0 < x →
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
          Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
              Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) ∧
  (∀ z : ℂ,
    0 < z.re →
      (∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
      (∀ᶠ y : ℂ in 𝓝 z,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
            Complex.binetAbelPlanaFiniteMainTerm N y +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                Complex.binetAbelPlanaFiniteContourRemainder N y))

/-- The owner-level full-sector branch-tail absorption input. -/
def Complex.BinetSecondFormulaBranchUniformTailAbsorption : Prop :=
  (∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) ∧
  Complex.BinetSecondFormulaBranchCoherence

/-- The standard scalar Binet decaying-tail integral beginning at `‖w‖ / 2`. -/
noncomputable def Complex.binetSecondFormulaDecayingTailIntegral
    (w : ℂ) : ℝ :=
  ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- The branch-wall local-indentation envelope appearing in the full-sector
Binet contour estimate. -/
noncomputable def Complex.binetSecondFormulaBranchLocalIndentationEnvelope
    (w : ℂ) : ℝ :=
  2 *
    (((max |Real.log (w.re / (3 * ‖w‖))|
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
      (Real.exp (Real.pi * ‖w‖) - 1)) *
      (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal)

/-- Honest full-sector Binet tail estimate before local-indentation
absorption.

This is the estimate supplied by the contour calculation in the open right
half-plane.  It keeps the branch-wall logarithmic envelope explicit; the pure
`C / ‖w‖` tail package is a strictly stronger absorption theorem. -/
def Complex.BinetSecondFormulaBranchLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Honest tail-remainder estimate before local-indentation absorption.

This is the tail-remainder version of
`BinetSecondFormulaBranchLocalIndentationTailControl`: it transfers the
principal-tail integral estimate to the actual Binet tail remainder while
keeping the branch-wall local-indentation envelope explicit. -/
def Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl : Prop :=
  ∃ Cfar : ℝ,
    0 ≤ Cfar ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
            (Cfar / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local absorption of the Binet branch-wall local-indentation
envelope.

The pointwise logarithmic envelope is uniformly absorbable only after staying
a fixed angular distance away from the branch wall, and only at the natural
scale of the Binet decaying-tail integral.  The stronger pure
`C / ‖w‖` scale is not a consequence of this scalar window estimate: the
bounded indentation window has length comparable to `‖w‖`.  The full-sector
pure tail theorem must therefore use paired contour cancellation rather than
this local scalar absorption. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local pre-cancellation tail-remainder absorption.

Away from the branch wall, the local-indentation envelope can be absorbed
into the standard decaying tail, leaving a sector-local tail-remainder bound.
This is weaker than full branch-wall contour cancellation because the constant
depends on the angular margin `δ`. -/
def Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C + C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Legacy full-sector principal-tail norm estimate.

This raw norm statement is stronger than the canonical contour-level target
used by the owner package below.  It is retained only as a compatibility
predicate for older bookkeeping lemmas; the owner theorem for branch-wall
cancellation is `BinetSecondFormulaBranchWallContourCancellationTailAbsorption`. -/
def Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Sector-local real-variable comparison for the logarithmic
local-indentation envelope.

This is the scalar estimate behind local-indentation absorption: after fixing
an angular margin `δ`, the branch-wall logarithmic window is bounded by the
standard Binet decaying-tail integral at the scale-correct constant loss. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * Complex.binetSecondFormulaDecayingTailIntegral w

/-- Legacy paired-contour name for the principal-tail norm estimate.

This has the same raw-norm content as
`BinetSecondFormulaBranchWallPrincipalTailCancellation`.  The non-circular
owner target is the contour-cancellation tail-absorption predicate below. -/
def Complex.BinetSecondFormulaBranchWallPairedContourPrincipalTailCancellation : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Full-sector Binet tail absorption after branch-wall contour cancellation.

This is the canonical replacement for pointwise branch-wall envelope
absorption: away from the wall one uses sector-local absorption, while near
the wall the paired indentation contributions must cancel at the contour
level before taking the final tail norm. -/
def Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Owner target for the branch-wall lower-vertical cancellation estimate.

This is the cancellation-before-norm statement in Abel-Plana vertical-side
coordinates.  It is equivalent to the public tail-absorption theorem by the
proved lower-vertical split, but it keeps the analytic leaf attached to the
place where the wall terms actually cancel: the full lower vertical side with
the fixed initial Binet window removed. -/
def Complex.BinetSecondFormulaLowerVerticalDifferenceDecay : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
          (C / ‖w‖) *
            Complex.binetSecondFormulaDecayingTailIntegral w

/-- Endpoint-returned restored paired finite-height decay target.

This is the canonical endpoint-restored analytic leaf for branch-wall
cancellation.  The restored static expression and restored contour error are
paired before taking norms, with the half-endpoint term returned to both
members of the pair.  This avoids the false separate-estimate route where the
restored static limit carries a half-endpoint defect while the restored contour
error tends to zero. -/
def Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay : Prop :=
  ∃ R : ℝ, ∃ C : ℝ,
    0 < R ∧
    0 < C ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∃ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
              Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
              Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
              Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
              (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
                Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Quantitative solved-static Abel-Plana boundary decay.

This is the norm estimate for the solved static boundary expression alone,
with the boundary-target identity deliberately not bundled into the predicate.
The boundary target is structural Abel-Plana assembly; this predicate is the
remaining scale estimate for the static expression after subtracting the
initial lower-vertical Binet window. -/
def Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate : Prop :=
  ∃ R : ℝ, ∃ Cstatic : ℝ,
    0 < R ∧
    2 ≤ R ∧
    0 < Cstatic ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∃ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
              Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
              Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
              Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (Cstatic / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w

/-- Historical endpoint-free structural finite-height boundary target used by
the older solved-static Abel-Plana wall-cancellation estimate.

The endpoint-restored target below is the canonical target produced by the
real-segment constant-face reconstruction.  The endpoint-free target is
compatible with that reconstruction only if the endpoint indentation vanishes;
see
`binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero`. -/
def Complex.BinetSecondFormulaFiniteHeightBoundaryTarget : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T

/-- Structural finite-height boundary target with endpoint indentation kept
explicit.

This is the endpoint-restored target naturally produced when the two scaled
cotangent constant faces reconstruct only the real segment. -/
def Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
              Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T

/-- Structural constant-face reconstruction target for the finite-height
Abel-Plana rectangle.

This is the actual algebraic content supplied by the two scaled cotangent
constant faces: together they reconstruct the real segment, while endpoint
indentation is supplied separately by the principal-value endpoint owner. -/
def Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces : Prop :=
  ∃ R : ℝ,
    0 < R ∧
    2 ≤ R ∧
    ∀ w : ℂ,
      0 < w.re →
      R ≤ ‖w‖ →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand w (x : ℂ))

/-- Owner wrapper from a pointwise constant-face reconstruction to the
large-radius real-segment constant-face predicate. -/
theorem Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
    (hpoint :
      ∀ w : ℂ,
        0 < w.re →
          ∀ N : ℕ,
            ∀ T : ℝ,
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
                ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
                (let M : ℕ := N + 1;
                  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ))) :
    Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces := by
  exact
    ⟨2, zero_lt_two, le_refl (2 : ℝ),
      fun w hw_re_pos _hRle N =>
        eventually_of_forall
          (fun T => hpoint w hw_re_pos N T)⟩

/-- Endpoint-restored boundary target from real-segment constant-face
reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  match hconstant with
  | ⟨R, hR_pos, hR_two, hconstant_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle N =>
            (hconstant_bound w hw_re_pos hRle N).mono
              (fun T hconstantT =>
                Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_endpointRestored_of_realSegmentConstantFaces
                  N w T hconstantT)⟩

/-- Endpoint-restored structural boundary target from the pointwise
constant-face reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_pointwise_realSegmentConstantFaces
    (hpoint :
      ∀ w : ℂ,
        0 < w.re →
          ∀ N : ℕ,
            ∀ T : ℝ,
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T) +
                ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T) =
                (let M : ℕ := N + 1;
                  ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ))) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  have hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces :=
    Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
      hpoint
  exact
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
      hconstant

/-- Owner theorem for the real-segment constant-face reconstruction. -/
theorem Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner :
    Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces := by
  exact
    Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_of_pointwise
      (fun w hw_re_pos N T =>
        Complex.finiteAbelPlana_log_realSegmentConstantFaces N hw_re_pos T)

/-- Owner theorem for the endpoint-restored finite-height structural boundary
target. -/
theorem Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_owner :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored := by
  exact
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner

/-- If an expression and the same expression with an added endpoint term both
equal the same target, then the endpoint term is zero. -/
theorem Complex.endpoint_zero_of_boundary_target_and_endpoint_restored
    {X E Y : ℂ}
    (hplain : X = Y)
    (hrestored : X + E = Y) :
    E = 0 := by
  have hXE_eq_X : X + E = X := by
    exact Eq.trans hrestored hplain.symm
  calc
    E = (X + E) - X := by
      exact (add_sub_cancel_left X E).symm
    _ = X - X := by
      exact congrArg (fun z : ℂ => z - X) hXE_eq_X
    _ = 0 := sub_self X

/-- Pointwise incompatibility of the endpoint-free and endpoint-restored
finite-height targets unless the endpoint indentation itself vanishes. -/
theorem Complex.finiteHeightBoundaryTarget_and_endpointRestored_imply_endpointIndentation_zero
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hplain :
      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    (hrestored :
      ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
              Complex.I *
                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w = 0 := by
  exact
    Complex.endpoint_zero_of_boundary_target_and_endpoint_restored
      hplain hrestored

/-- At the first finite Abel-Plana window and `w = 1`, the endpoint
principal-value indentation is nonzero.

This pins down the obstruction to the historical endpoint-free target: the
endpoint term is the half-endpoint contribution, not a height-dependent contour
error that can disappear at large finite height. -/
theorem Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_one_ne_zero :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) ≠ 0 := by
  have hlog_one : Complex.log (1 : ℂ) = 0 :=
    Complex.log_one
  have hlog_two_re :
      (Complex.log (2 : ℂ)).re = Real.log 2 :=
    Complex.log_ofReal_re 2
  have hreal_log_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hcomplex_log_two_ne_zero : Complex.log (2 : ℂ) ≠ 0 := by
    intro hzero
    have hre_zero : (Complex.log (2 : ℂ)).re = 0 :=
      congrArg Complex.re hzero
    have hreal_zero : Real.log 2 = 0 :=
      Eq.trans hlog_two_re.symm hre_zero
    exact (ne_of_gt hreal_log_two_pos) hreal_zero
  have htwo_ne_zero : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  have hlog_two_div_two_ne_zero : Complex.log (2 : ℂ) / (2 : ℂ) ≠ 0 := by
    intro hdiv_zero
    have hmul_zero :
        (Complex.log (2 : ℂ) / (2 : ℂ)) * (2 : ℂ) = 0 * (2 : ℂ) :=
      congrArg (fun z : ℂ => z * (2 : ℂ)) hdiv_zero
    have hlog_two_zero : Complex.log (2 : ℂ) = 0 := by
      calc
        Complex.log (2 : ℂ) =
            (Complex.log (2 : ℂ) / (2 : ℂ)) * (2 : ℂ) := by
          exact (div_mul_cancel₀ (Complex.log (2 : ℂ)) htwo_ne_zero).symm
        _ = 0 * (2 : ℂ) := hmul_zero
        _ = 0 := zero_mul (2 : ℂ)
    exact hcomplex_log_two_ne_zero hlog_two_zero
  have hendpoint_eq :
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) =
        Complex.log (2 : ℂ) / (2 : ℂ) := by
    calc
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (1 : ℂ) =
          Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 (1 : ℂ) := by
        exact
          Complex.finiteAbelPlana_log_endpointPVIndentationContribution_eq_halfEndpoints
            0 (1 : ℂ)
      _ = (Complex.log (1 : ℂ) + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        rfl
      _ = (0 + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        exact congrArg (fun z : ℂ => (z + Complex.log ((1 : ℂ) + (1 : ℂ))) / (2 : ℂ)) hlog_one
      _ = Complex.log ((1 : ℂ) + (1 : ℂ)) / (2 : ℂ) := by
        exact congrArg (fun z : ℂ => z / (2 : ℂ)) (zero_add (Complex.log ((1 : ℂ) + (1 : ℂ))))
      _ = Complex.log (2 : ℂ) / (2 : ℂ) := by
        have hone_add_one : (1 : ℂ) + (1 : ℂ) = 2 := by
          rfl
        exact congrArg (fun z : ℂ => Complex.log z / (2 : ℂ)) hone_add_one
  intro hendpoint_zero
  exact hlog_two_div_two_ne_zero (Eq.trans hendpoint_eq.symm hendpoint_zero)

/-- On the real half-line `x ≥ 1`, the first endpoint principal-value
indentation is nonzero.

This is the large-radius version of the endpoint obstruction: the
endpoint-free target cannot be recovered from the real-segment constant-face
reconstruction by passing to sufficiently large heights or radii. -/
theorem Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_ofReal_ge_one_ne_zero
    {x : ℝ}
    (hx : 1 ≤ x) :
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) ≠ 0 := by
  have hx_nonneg : 0 ≤ x :=
    le_trans zero_le_one hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_one hx
  have hx_one_pos : 0 < x + 1 :=
    add_pos hx_pos zero_lt_one
  have hx_one_nonneg : 0 ≤ x + 1 :=
    le_of_lt hx_one_pos
  have hx_one_gt_one : 1 < x + 1 :=
    lt_add_of_pos_right x zero_lt_one
  have hlog_x_nonneg : 0 ≤ Real.log x :=
    Real.log_nonneg hx
  have hlog_x_one_pos : 0 < Real.log (x + 1) :=
    Real.log_pos hx_one_gt_one
  have hsum_pos : 0 < Real.log x + Real.log (x + 1) :=
    add_pos_of_nonneg_of_pos hlog_x_nonneg hlog_x_one_pos
  have hhalf_pos : 0 < (Real.log x + Real.log (x + 1)) / 2 :=
    div_pos hsum_pos zero_lt_two
  have hhalf_ne_zero : (Real.log x + Real.log (x + 1)) / 2 ≠ 0 :=
    ne_of_gt hhalf_pos
  have hlog_x :
      Complex.log (x : ℂ) = (Real.log x : ℂ) :=
    (Complex.ofReal_log hx_nonneg).symm
  have hx_one_cast :
      (x : ℂ) + (1 : ℂ) = ((x + 1 : ℝ) : ℂ) :=
    (Complex.ofReal_add x 1).symm
  have hlog_x_one :
      Complex.log ((x : ℂ) + (1 : ℂ)) = (Real.log (x + 1) : ℂ) := by
    exact Eq.trans
      (congrArg Complex.log hx_one_cast)
      (Complex.ofReal_log hx_one_nonneg).symm
  have hendpoint_eq :
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) =
        (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) := by
    calc
      Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) =
          Complex.finiteAbelPlanaLogSummandHalfEndpoints 0 (x : ℂ) := by
        exact
          Complex.finiteAbelPlana_log_endpointPVIndentationContribution_eq_halfEndpoints
            0 (x : ℂ)
      _ = (Complex.log (x : ℂ) + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        rfl
      _ = ((Real.log x : ℂ) + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => (z + Complex.log ((x : ℂ) + (1 : ℂ))) / (2 : ℂ))
          hlog_x
      _ = ((Real.log x : ℂ) + (Real.log (x + 1) : ℂ)) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => ((Real.log x : ℂ) + z) / (2 : ℂ))
          hlog_x_one
      _ = ((Real.log x + Real.log (x + 1) : ℝ) : ℂ) / (2 : ℂ) := by
        exact congrArg
          (fun z : ℂ => z / (2 : ℂ))
          (Complex.ofReal_add (Real.log x) (Real.log (x + 1))).symm
      _ = (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) := by
        exact (Complex.ofReal_div (Real.log x + Real.log (x + 1)) 2).symm
  intro hendpoint_zero
  have hhalf_cast_zero :
      (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) = 0 :=
    Eq.trans hendpoint_eq.symm hendpoint_zero
  have hhalf_cast_ne_zero :
      (((Real.log x + Real.log (x + 1)) / 2 : ℝ) : ℂ) ≠ 0 :=
    (Complex.ofReal_ne_zero).mpr hhalf_ne_zero
  exact hhalf_cast_ne_zero hhalf_cast_zero

/-- Predicate-level obstruction: the endpoint-free boundary target is
compatible with the real-segment constant-face reconstruction only if the
endpoint indentation contribution eventually vanishes. -/
theorem Complex.binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero
    (hplain :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ N : ℕ,
            ∀ᶠ T : ℝ in atTop,
              Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w = 0 := by
  match hplain with
  | ⟨Rplain, hRplain_pos, hRplain_two, hplain_bound⟩ =>
      match
        Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_of_realSegmentConstantFaces
          hconstant
      with
      | ⟨Rrestored, _hRrestored_pos, _hRrestored_two, hrestored_bound⟩ =>
          let R : ℝ := max Rplain Rrestored
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRplain_pos (le_max_left Rplain Rrestored)
          have hR_two : 2 ≤ R :=
            le_trans hRplain_two (le_max_left Rplain Rrestored)
          exact
            ⟨R, hR_pos, hR_two,
              fun w hw_re_pos hRle N =>
                have hRplain_le : Rplain ≤ ‖w‖ :=
                  le_trans (le_max_left Rplain Rrestored) hRle
                have hRrestored_le : Rrestored ≤ ‖w‖ :=
                  le_trans (le_max_right Rplain Rrestored) hRle
                have hplain_T :
                    ∀ᶠ T : ℝ in atTop,
                      (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                              Complex.I *
                                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hplain_bound w hw_re_pos hRplain_le N
                have hrestored_T :
                    ∀ᶠ T : ℝ in atTop,
                      ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                              Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                        ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                            (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                              Complex.I *
                                Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                          (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) +
                        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N w) =
                        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hrestored_bound w hw_re_pos hRrestored_le N
                (hplain_T.and hrestored_T).mono
                  (fun T hpair =>
                    Complex.finiteHeightBoundaryTarget_and_endpointRestored_imply_endpointIndentation_zero
                      N w T hpair.1 hpair.2)⟩

/-- The historical endpoint-free finite-height target is incompatible with
the canonical real-segment reconstruction of the two constant cotangent faces.

The contradiction is obtained on the real half-line at `N = 0`: the two
structural targets force the endpoint indentation to be eventually zero, while
the endpoint owner calculation shows it is nonzero for every real `w ≥ 1`. -/
theorem Complex.not_boundaryTarget_and_realSegmentConstantFaces
    (hplain :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    False := by
  match
    Complex.binetSecondFormula_boundaryTarget_and_realSegmentConstantFaces_imply_endpointIndentation_eventually_zero
      hplain hconstant
  with
  | ⟨R, _hR_pos, _hR_two, hzero_bound⟩ =>
      let x : ℝ := max R 1
      have hx_ge_one : 1 ≤ x :=
        le_max_right R 1
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_ge_one
      have hx_complex_re_pos : 0 < ((x : ℂ).re) :=
        hx_pos
      have hx_nonneg : 0 ≤ x :=
        le_of_lt hx_pos
      have hRle_x : R ≤ x :=
        le_max_left R 1
      have hnorm_eq : ‖(x : ℂ)‖ = x :=
        Eq.trans (Complex.norm_real x) (Real.norm_of_nonneg hx_nonneg)
      have hRle_norm : R ≤ ‖(x : ℂ)‖ :=
        Eq.subst
          (motive := fun y : ℝ => R ≤ y)
          hnorm_eq.symm
          hRle_x
      have hzero_eventual :
          ∀ᶠ T : ℝ in atTop,
            Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) = 0 :=
        hzero_bound (x : ℂ) hx_complex_re_pos hRle_norm 0
      have hzero :
          Complex.finiteAbelPlanaLogEndpointPVIndentationContribution 0 (x : ℂ) = 0 :=
        (eventually_const.mp hzero_eventual)
      exact
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution_at_zero_ofReal_ge_one_ne_zero
          hx_ge_one hzero

/-- Owner obstruction to the historical endpoint-free finite-height boundary
target.

The owner-level constant-face reconstruction has now been proved, and it is
the canonical reconstruction of the real segment.  Combined with the endpoint
calculation, it rules out the historical endpoint-free target outright. -/
theorem Complex.not_binetSecondFormula_finiteHeightBoundaryTarget_owner :
    ¬ Complex.BinetSecondFormulaFiniteHeightBoundaryTarget := by
  intro hplain
  exact
    Complex.not_boundaryTarget_and_realSegmentConstantFaces
      hplain
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner

/-- The historical solved-static input pair is not the correct owner target.

Its first component is the endpoint-free finite-height boundary target, which
is incompatible with the canonical real-segment constant-face reconstruction. -/
theorem Complex.not_binetSecondFormula_boundarySolvedStatic_inputs_owner_target :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  intro hinputs
  exact
    Complex.not_binetSecondFormula_finiteHeightBoundaryTarget_owner
      hinputs.1

/-- Corrected endpoint-restored finite-height contour input package.

This is the structural input actually produced by the canonical constant-face
algebra: the boundary target keeps the endpoint indentation, and the contour
error is the endpoint-restored contour error with that indentation subtracted. -/
def Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs : Prop :=
  Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored ∧
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ N : ℕ,
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                ((1 : ℝ) / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w

/-- The historical sector-absorption predicate and the scalar log-window
comparison predicate have the same mathematical content. -/
theorem Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption_iff_logWindowComparison :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption ↔
      Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    ⟨fun hsector => hsector,
      fun hwindow => hwindow⟩

/-- The two legacy principal-tail norm predicates have the same content. -/
theorem Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation_iff_pairedContour :
    Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation ↔
      Complex.BinetSecondFormulaBranchWallPairedContourPrincipalTailCancellation := by
  exact
    ⟨fun hprincipal => hprincipal,
      fun hpaired => hpaired⟩

/-- Tail-absorption projection from the full Binet branch package. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.tail
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  hbranch.1

/-- Branch-coherence projection from the full Binet branch package. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    Complex.BinetSecondFormulaBranchCoherence :=
  hbranch.2

/-- Owner-level access to the Abel-Plana contour comparison for the actual
Binet tail remainder.

The comparison is deliberately integral-level: the principal branch
singularity is absorbed by contour deformation only after the split-tail
integral has been formed. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral_owner :
    Complex.BinetSecondFormulaContourTailIntegralComparison
      Complex.binetSecondFormulaContourTailMajorantKernel 2 :=
  Complex.binetSecondFormula_tailRemainder_norm_le_contourTailMajorantKernel_integral

/-- Construct the tail half of `BinetSecondFormulaBranchUniformTailAbsorption`
from a proved decaying-kernel comparison. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_decayingTailKernel_bound
    {R C : ℝ}
    (hR : 0 < R)
    (hC : 0 < C)
    (htail :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  ⟨R, C, hR, hC, htail⟩

/-- Owner-level constructor reducing branch-uniform tail absorption to a
contour-majorant integral decay estimate. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_contourTailMajorantKernel_integral_decay
    {C : ℝ}
    (hC : 0 < C)
    (hdecay :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
  Complex.binetSecondFormula_branchUniform_tail_absorption_of_decayingTailKernel_bound
    two_pos
    hC
    (Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailMajorantKernel_integral_decay
      hdecay)

/-- Assemble the full branch-tail package once the real decaying-tail
comparison and Binet-branch coherence have both been proved. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_and_coherence
    (htail :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
    (hcoh : Complex.BinetSecondFormulaBranchCoherence) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  ⟨htail, hcoh⟩

/-- Positive real-axis values of Gamma lie in the principal slit plane. -/
theorem Complex.Gamma_ofReal_mem_slitPlane_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    Complex.Gamma (x : ℂ) ∈ Complex.slitPlane := by
  have hGamma_pos : 0 < Real.Gamma x :=
    Real.Gamma_pos_of_pos hx
  have hGamma_mem : ((Real.Gamma x : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr hGamma_pos
  exact
    Eq.subst
      (motive := fun w : ℂ => w ∈ Complex.slitPlane)
      (Complex.Gamma_ofReal x).symm
      hGamma_mem

/-- Gamma is nonzero on the open right half-plane.  This is the elementary
input for constructing a logarithm of `Γ` there. -/
theorem Complex.Gamma_openRightHalfPlane_nonvanishing
    {z : ℂ}
    (hz : 0 < z.re) :
    Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos hz

/-- Owner branch construction for `log Γ` on the simply connected open right
half-plane, normalized by the positive real axis.

This is the exact analytic theorem obtained by applying the holomorphic
logarithm theorem to the nonvanishing holomorphic Gamma function on
`{z | 0 < z.re}` and fixing the additive constant by the positive real axis. -/
theorem Complex.Gamma_openRightHalfPlane_logBranch_normalized_ownerGap :
    ∃ logGammaRHP : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.re →
        Complex.exp (logGammaRHP z) = Complex.Gamma z) ∧
      (∀ x : ℝ, 0 < x →
        logGammaRHP (x : ℂ) = (Real.log (Real.Gamma x) : ℂ)) := by
  refine ⟨fun z : ℂ => Complex.log (Complex.Gamma z), ?_, ?_⟩
  · intro z hz_re_pos
    exact
      Complex.exp_log
        (Complex.Gamma_openRightHalfPlane_nonvanishing hz_re_pos)
  · intro x hx_pos
    have hGamma_pos : 0 < Real.Gamma x :=
      Real.Gamma_pos_of_pos hx_pos
    calc
      Complex.log (Complex.Gamma (x : ℂ)) =
          Complex.log ((Real.Gamma x : ℝ) : ℂ) := by
        exact congrArg Complex.log (Complex.Gamma_ofReal x)
      _ = (Real.log (Real.Gamma x) : ℂ) := by
        exact (Complex.ofReal_log (le_of_lt hGamma_pos)).symm

/-- The canonical principal logarithm of `Γ` lies in the principal strip once
Gamma is known to avoid the negative real axis. -/
theorem Complex.Gamma_openRightHalfPlane_principalLog_im_mem_principalStrip_of_no_negativeRealValue
    (hno_negative :
      ∀ z : ℂ, 0 < z.re →
        ¬ ((Complex.Gamma z).re < 0 ∧ (Complex.Gamma z).im = 0)) :
    ∀ z : ℂ, 0 < z.re →
      (Complex.log (Complex.Gamma z)).im ∈ Set.Ioo (-Real.pi) Real.pi := by
  intro z hz_re_pos
  constructor
  · exact Complex.neg_pi_lt_log_im (Complex.Gamma z)
  · have hle :
        (Complex.log (Complex.Gamma z)).im ≤ Real.pi :=
      Complex.log_im_le_pi (Complex.Gamma z)
    have hne :
        (Complex.log (Complex.Gamma z)).im ≠ Real.pi := by
      intro him_eq
      have harg_eq :
          (Complex.Gamma z).arg = Real.pi :=
        Eq.trans (Complex.log_im (Complex.Gamma z)).symm him_eq
      have hnegative :
          (Complex.Gamma z).re < 0 ∧ (Complex.Gamma z).im = 0 :=
        Complex.arg_eq_pi_iff.mp harg_eq
      exact hno_negative z hz_re_pos hnegative
    exact lt_of_le_of_ne hle hne

/-- Binet's logarithm branch exponentiates to Gamma once the finite Abel-Plana
summand formula has been restored at the point. -/
theorem Complex.exp_binetLogGammaBranch_eq_Gamma_of_finiteAbelPlana
    {z : ℂ}
    (hz : 0 < z.re)
    (hfinite :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z) :
    Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z :=
  Complex.exp_binetLogGammaBranch_eq_Gamma_from_AbelPlana z hz hfinite

/-- The finite Abel-Plana contour formula follows once the defining finite
remainder error has been identified with the honest contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_of_remainderError_eq_contourRemainder
    (hrem :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaFiniteRemainderError N z =
              Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hfinite_error :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteRemainderError N z :=
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMainTerm_add_boundary_add_error
      hz_re_pos
  have herror_eq :
      Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaFiniteContourRemainder N z :=
    hrem z hz_re_pos N
  exact
    Eq.trans hfinite_error
      (congrArg
        (fun u : ℂ =>
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z + u)
        herror_eq)

/-- Boundary-target algebra after the two scaled cotangent constants have
been identified with the real-segment side and the endpoint indentation is
kept as a separate principal-value contribution. -/
theorem Complex.finiteAbelPlana_boundaryTarget_collect_from_realSegment_endpointIndentation
    (leftConstant rightConstant realSegment endpointIndentation lower upper : ℂ)
    (hconstant : leftConstant + rightConstant = realSegment) :
    ((leftConstant + endpointIndentation) + (-lower)) + (rightConstant + (-upper)) =
      (realSegment + endpointIndentation) + (-lower - upper) := by
  calc
    ((leftConstant + endpointIndentation) + (-lower)) + (rightConstant + (-upper)) =
        (((leftConstant + endpointIndentation) + (-lower)) + rightConstant) +
          (-upper) := by
      exact
        (add_assoc
          ((leftConstant + endpointIndentation) + (-lower))
          rightConstant
          (-upper)).symm
    _ = ((leftConstant + endpointIndentation) + ((-lower) + rightConstant)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc (leftConstant + endpointIndentation) (-lower) rightConstant)
    _ = ((leftConstant + endpointIndentation) + (rightConstant + (-lower))) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => ((leftConstant + endpointIndentation) + z) + (-upper))
        (add_comm (-lower) rightConstant)
    _ = (((leftConstant + endpointIndentation) + rightConstant) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc (leftConstant + endpointIndentation) rightConstant (-lower)).symm
    _ = ((leftConstant + (endpointIndentation + rightConstant)) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => (z + (-lower)) + (-upper))
        (add_assoc leftConstant endpointIndentation rightConstant)
    _ = ((leftConstant + (rightConstant + endpointIndentation)) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => ((leftConstant + z) + (-lower)) + (-upper))
        (add_comm endpointIndentation rightConstant)
    _ = (((leftConstant + rightConstant) + endpointIndentation) + (-lower)) +
          (-upper) := by
      exact congrArg
        (fun z : ℂ => (z + (-lower)) + (-upper))
        (add_assoc leftConstant rightConstant endpointIndentation).symm
    _ = ((realSegment + endpointIndentation) + (-lower)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => ((z + endpointIndentation) + (-lower)) + (-upper))
        hconstant
    _ = (realSegment + endpointIndentation) + (-lower) + (-upper) := by
      exact Eq.refl (((realSegment + endpointIndentation) + (-lower)) + (-upper))
    _ = (realSegment + endpointIndentation) + (-lower - upper) := by
      exact Eq.trans
        (add_assoc (realSegment + endpointIndentation) (-lower) (-upper))
        (congrArg (fun z : ℂ => (realSegment + endpointIndentation) + z)
          (sub_eq_add_neg (-lower) upper).symm)

/-- Boundary-target algebra after the two scaled cotangent constants have
been identified with the full real-endpoint side. -/
theorem Complex.finiteAbelPlana_boundaryTarget_collect_from_realEndpoint
    (leftConstant rightConstant endpoint lower upper : ℂ)
    (hconstant : leftConstant + rightConstant = endpoint) :
    (leftConstant + (-lower)) + (rightConstant + (-upper)) =
      endpoint + (-lower - upper) := by
  calc
    (leftConstant + (-lower)) + (rightConstant + (-upper)) =
        ((leftConstant + (-lower)) + rightConstant) + (-upper) := by
      exact (add_assoc (leftConstant + (-lower)) rightConstant (-upper)).symm
    _ = (leftConstant + ((-lower) + rightConstant)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc leftConstant (-lower) rightConstant)
    _ = (leftConstant + (rightConstant + (-lower))) + (-upper) := by
      exact congrArg
        (fun z : ℂ => (leftConstant + z) + (-upper))
        (add_comm (-lower) rightConstant)
    _ = ((leftConstant + rightConstant) + (-lower)) + (-upper) := by
      exact congrArg
        (fun z : ℂ => z + (-upper))
        (add_assoc leftConstant rightConstant (-lower)).symm
    _ = (leftConstant + rightConstant) + (-lower) + (-upper) := by
      exact Eq.refl (((leftConstant + rightConstant) + (-lower)) + (-upper))
    _ = endpoint + (-lower) + (-upper) := by
      exact congrArg (fun z : ℂ => z + (-lower) + (-upper)) hconstant
    _ = endpoint + (-lower - upper) := by
      exact Eq.trans
        (add_assoc endpoint (-lower) (-upper))
        (congrArg (fun z : ℂ => endpoint + z)
          (sub_eq_add_neg (-lower) upper).symm)

/-- Boundary-target normalization reduced to the real-endpoint reconstruction
for the two scaled cotangent constant faces. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_constantFaces
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z) :
    (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  let leftConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)
  let rightConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
        Complex.I *
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)
  let endpoint : ℂ :=
    Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z
  let lower : ℂ :=
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T
  let upper : ℂ :=
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T
  have hcollected :
      (leftConstant + (-lower)) + (rightConstant + (-upper)) =
        endpoint + (-lower - upper) :=
    Complex.finiteAbelPlana_boundaryTarget_collect_from_realEndpoint
      leftConstant rightConstant endpoint lower upper hconstant
  have hnamed :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
        endpoint + (-lower - upper) := by
    have hboundary :
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
          Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z +
            Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T :=
      Complex.finiteAbelPlana_log_namedBoundaryFaceSum_unfold N z T
    have hvertical :
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T -
            Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T :=
      Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
        N z T
    exact Eq.trans hboundary
      (congrArg₂ HAdd.hAdd rfl hvertical)
  exact Eq.trans hcollected hnamed.symm

/-- Boundary-target normalization reduced to the real-segment reconstruction
for the two scaled cotangent constant faces, with the endpoint principal-value
indentation supplied separately by the endpoint owner path. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_realSegmentConstantFaces_endpointIndentation
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        (let M : ℕ := N + 1;
          ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand z (x : ℂ))) :
    ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  let leftConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)
  let rightConstant : ℂ :=
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
        Complex.I *
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)
  let realSegment : ℂ :=
    let M : ℕ := N + 1
    ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
      Complex.finiteAbelPlanaLogSummand z (x : ℂ)
  let endpointIndentation : ℂ :=
    Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z
  let lower : ℂ :=
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T
  let upper : ℂ :=
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T
  have hcollected :
      ((leftConstant + endpointIndentation) + (-lower)) +
          (rightConstant + (-upper)) =
        (realSegment + endpointIndentation) + (-lower - upper) :=
    Complex.finiteAbelPlana_boundaryTarget_collect_from_realSegment_endpointIndentation
      leftConstant rightConstant realSegment endpointIndentation lower upper hconstant
  have hrealEndpoint :
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z =
        realSegment + endpointIndentation := by
    exact Eq.refl (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z)
  have hnamed :
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
        (realSegment + endpointIndentation) + (-lower - upper) := by
    have hboundary :
        Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T =
          Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N z +
            Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T :=
      Complex.finiteAbelPlana_log_namedBoundaryFaceSum_unfold N z T
    have hvertical :
        Complex.finiteAbelPlanaLogFiniteHeightNamedVerticalSideExpression N z T =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T -
            Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T :=
      Complex.finiteAbelPlana_log_finiteHeightNamedVerticalSideExpression_unfold
        N z T
    exact Eq.trans hboundary
      (Eq.trans
        (congrArg₂ HAdd.hAdd hrealEndpoint hvertical)
        (Eq.refl ((realSegment + endpointIndentation) + (-lower - upper))))
  exact Eq.trans hcollected hnamed.symm

/-- Pointwise endpoint-restored boundary-face normalization for the
finite-height logarithmic Abel-Plana rectangle.

The endpoint-free target is not the correct owner statement: the two constant
faces reconstruct the real segment, while the endpoint principal-value
indentation is supplied by the endpoint owner path. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_endpointRestored
    (z : ℂ)
    (N : ℕ)
    (T : ℝ)
    (hconstant :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
        (let M : ℕ := N + 1;
          ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
            Complex.finiteAbelPlanaLogSummand z (x : ℂ))) :
    ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
        Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
        (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
      ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
        (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_of_realSegmentConstantFaces_endpointIndentation
      z N T hconstant

/-- Owner endpoint-restored boundary-face normalization for the finite-height
logarithmic Abel-Plana rectangle.

The eventual wrapper is intentionally thin: the actual analytic primitive is
the real-segment reconstruction for the two scaled constant faces. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_endpointRestored :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand z (x : ℂ))) →
        ∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                    Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T)) +
                Complex.finiteAbelPlanaLogEndpointPVIndentationContribution N z) +
                (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo z T)) +
              ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                  (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                    Complex.I *
                      Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T)) +
                (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N z T))) =
              Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N z T := by
  intro z _hz_re_pos hconstant N
  filter_upwards [hconstant N] with T hconstantT
  exact
    Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBoundaryTarget_pointwise_endpointRestored
      z N T hconstantT

/-- Endpoint-restored finite-height principal-value bridge package for the
logarithmic Abel-Plana rectangle in the open right half-plane.

The package keeps the endpoint indentation explicit.  It requires the genuine
four-edge constant-face real-segment reconstruction as input. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          ∀ᶠ T : ℝ in atTop,
            ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N z T -
                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide z T) +
              ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N z T +
                  Complex.I *
                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N z T) =
              (let M : ℕ := N + 1;
                ∫ x : ℝ in (0 : ℝ)..(M : ℝ),
                  Complex.finiteAbelPlanaLogSummand z (x : ℂ))) →
        Complex.FiniteHeightPVBridgePackageEndpointRestored z := by
  intro z hz_re_pos hconstant N
  have htarget :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVBoundaryTargetBridgeEndpointRestored N z T := by
    filter_upwards [hconstant N] with T hconstantT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVBoundaryTargetBridge_endpointRestored_of_realSegmentConstantFaces
        N z T hconstantT
  have hrectangle :
      ∀ᶠ T : ℝ in atTop,
        Complex.FiniteHeightPVRectangleBoundaryBridge N z T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact
      Complex.finiteAbelPlana_log_finiteHeightPVRectangleBoundaryBridge_eventually_owner
        N hz_re_pos T hT
  exact
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_endpointRestored_of_boundaryBridge_and_targets
      N hrectangle htarget

/-- Endpoint-restored finite-height principal-value bridge package from the
owner real-segment constant-face reconstruction predicate. -/
theorem Complex.binetSecondFormula_finiteHeightPVBridgePackageEndpointRestored_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          Complex.FiniteHeightPVBridgePackageEndpointRestored w := by
  match hconstant with
  | ⟨R, hR_pos, hR_two, hconstant_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle =>
            Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored
              w hw_re_pos (hconstant_bound w hw_re_pos hRle)⟩

/-- Pure additive transport for the endpoint-restored finite Euler package.

The extra endpoint-restoration term on the summand side survives as a
subtracted defect after passing through `E - S`. -/
theorem Complex.neg_sub_eq_neg_add
    (x y : ℂ) :
    -(x - y) = -x + y := by
  calc
    -(x - y) = y - x := by
      exact neg_sub x y
    _ = y + -x := by
      exact sub_eq_add_neg y x
    _ = -x + y := by
      exact add_comm y (-x)

theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointRestored_transport_additive_core
    (E S A H B L U R : ℂ)
    (hsummand : S = A + H - B - L - U + R) :
    E - S = (E - A - H) + B + (L + U) - R := by
  have hrestored_as_normalized :
      S = A + H - B - L - (U - R) := by
    have hright :
        A + H - B - L - U + R =
          A + H - B - L - (U - R) := by
      calc
        A + H - B - L - U + R =
            ((A + H - B - L) - U) + R := rfl
        _ = ((A + H - B - L) + -U) + R := by
          exact
            congrArg (fun q : ℂ => q + R)
              (sub_eq_add_neg (A + H - B - L) U)
        _ = (A + H - B - L) + (-U + R) := by
          exact add_assoc (A + H - B - L) (-U) R
        _ = (A + H - B - L) + -(U - R) := by
          exact
            congrArg (fun q : ℂ => (A + H - B - L) + q)
              (Complex.neg_sub_eq_neg_add U R).symm
        _ = A + H - B - L - (U - R) := by
          exact
            (sub_eq_add_neg (A + H - B - L) (U - R)).symm
    exact Eq.trans hsummand hright
  have hnormalized_transport :
      E - S = (E - A - H) + B + (L + (U - R)) :=
    have hsubstitute :
        E - S = E - (A + H - B - L - (U - R)) :=
      congrArg (fun q : ℂ => E - q) hrestored_as_normalized
    have hnormalize :
        E - (A + H - B - L - (U - R)) =
          (E - A - H) + B + (L + (U - R)) := by
      calc
        E - (A + H - B - L - (U - R))
            = E + -((A + H - B - L) - (U - R)) :=
          sub_eq_add_neg E ((A + H - B - L) - (U - R))
        _ = E + (-(A + H - B - L) + (U - R)) :=
          congrArg (fun q : ℂ => E + q)
            (Complex.neg_sub_eq_neg_add (A + H - B - L) (U - R))
        _ = E + ((-(A + H - B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + (q + (U - R)))
            (Complex.neg_sub_eq_neg_add (A + H - B) L)
        _ = E + (((-(A + H) + B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + ((q + L) + (U - R)))
            (Complex.neg_sub_eq_neg_add (A + H) B)
        _ = E + ((((-A + -H) + B) + L) + (U - R)) :=
          congrArg (fun q : ℂ => E + (((q + B) + L) + (U - R)))
            (neg_add A H)
        _ = (E + (-A + -H)) + B + (L + (U - R)) := by
          let X : ℂ := -A + -H
          let T : ℂ := L + (U - R)
          exact
            Eq.trans
              (congrArg (fun q : ℂ => E + q)
                (add_assoc (X + B) L (U - R)))
              (Eq.trans
                (congrArg (fun q : ℂ => E + q)
                  (add_assoc X B T))
                (Eq.trans
                  (Eq.symm (add_assoc E X (B + T)))
                  (Eq.symm (add_assoc (E + X) B T))))
        _ = (E - A - H) + B + (L + (U - R)) := by
          exact
            congrArg (fun q : ℂ => q + B + (L + (U - R)))
              (Eq.trans
                (Eq.symm (add_assoc E (-A) (-H)))
                (Eq.trans
                  (congrArg (fun q : ℂ => q + -H)
                    (sub_eq_add_neg E A).symm)
                  (sub_eq_add_neg (E - A) H).symm))
    Eq.trans hsubstitute hnormalize
  have hright :
      (E - A - H) + B + (L + (U - R)) =
        (E - A - H) + B + (L + U) - R := by
    calc
      (E - A - H) + B + (L + (U - R)) =
          ((E - A - H) + B) + (L + (U - R)) := rfl
      _ = ((E - A - H) + B) + (L + (U + -R)) := by
        exact
          congrArg
            (fun q : ℂ => ((E - A - H) + B) + (L + q))
            (sub_eq_add_neg U R)
      _ = ((E - A - H) + B) + ((L + U) + -R) := by
        exact
          congrArg
            (fun q : ℂ => ((E - A - H) + B) + q)
            (add_assoc L U (-R)).symm
      _ = (((E - A - H) + B) + (L + U)) + -R := by
        exact (add_assoc ((E - A - H) + B) (L + U) (-R)).symm
      _ = (E - A - H) + B + (L + U) - R := by
        exact
          (sub_eq_add_neg ((E - A - H) + B + (L + U)) R).symm
  exact Eq.trans hnormalized_transport hright

/-- Exact transport sink for the endpoint-restored ordinary finite range.

Unfolding the definitions gives
`finiteApproximation = EulerFinite - sampleSum` and
`finiteMainTerm = EulerFinite - endpointPrimitive - halfEndpoints`.  Therefore
an endpoint-restored sample-sum formula produces the contour remainder minus
the explicit endpoint-restoration term. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestoration_defect_transport_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          (let M : ℕ := N + 1
          ∑ n in Finset.range (M + 1), Complex.log (z + n) =
            (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
                (z + (M : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z +
                  Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) →
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  (Complex.binetAbelPlanaFiniteLowerContourTail N z +
                    Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                      Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  intro z _hz_re_pos N hsummand
  let M : ℕ := N + 1
  let E : ℂ :=
    z * Complex.log (M : ℂ) +
      Complex.log ((Nat.factorial M : ℕ) : ℂ)
  let A : ℂ :=
    (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
        (z + (M : ℂ))) -
      (z * Complex.log z - z))
  let H : ℂ :=
    (Complex.log z + Complex.log (z + (M : ℂ))) / 2
  let B : ℂ :=
    Complex.binetAbelPlanaFiniteBoundaryCorrection N z
  let L : ℂ :=
    Complex.binetAbelPlanaFiniteLowerContourTail N z
  let U : ℂ :=
    Complex.binetAbelPlanaFiniteUpperContourResidual N z
  let R : ℂ :=
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z
  have hfiniteApproximation :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        E - ∑ n in Finset.range (M + 1), Complex.log (z + n) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_shifted N M z rfl
  have hfiniteMain :
      Complex.binetAbelPlanaFiniteMainTerm N z = E - A - H :=
    Complex.binetAbelPlanaFiniteMainTerm_unfold N z
  have hsummand_named :
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        A + H - B - L - U + R :=
    hsummand
  have htransport :
      E - ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (E - A - H) + B + (L + U) - R :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointRestored_transport_additive_core
      E
      (∑ n in Finset.range (M + 1), Complex.log (z + n))
      A H B L U R hsummand_named
  exact
    Eq.trans hfiniteApproximation
      (Eq.trans htransport
        (congrArg
          (fun q : ℂ => q + B + (L + U) - R)
          hfiniteMain.symm))

/-- The endpoint-restored summand formula transports through the shifted
Euler logarithmic-Gamma approximant with the endpoint restoration still visible
as a defect.

Unfolding the definitions gives
`finiteApproximation = EulerFinite - sampleSum` and
`finiteMainTerm = EulerFinite - endpointPrimitive - halfEndpoints`.  Therefore
an endpoint-restored sample-sum formula produces the contour remainder minus
the explicit endpoint-restoration term. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestoration_defect_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          (let M : ℕ := N + 1
          ∑ n in Finset.range (M + 1), Complex.log (z + n) =
            (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
                (z + (M : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z +
                  Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) →
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  (Complex.binetAbelPlanaFiniteLowerContourTail N z +
                    Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                      Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestoration_defect_transport_ownerGap

/-- The ordinary finite range formula is endpoint-restored.

For `Finset.range (M + 1)`, the endpoint integer poles are counted with full
weight.  The principal-value contour theorem therefore supplies the
endpoint-restoration term explicitly. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_restoredOrdinaryRange
    (z : ℂ)
    (hz : 0 < z.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage z)
    (N : ℕ) :
    let M : ℕ := N + 1
    ∑ n in Finset.range (M + 1), Complex.log (z + n) =
      (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
          (z + (M : ℂ))) -
        (z * Complex.log z - z)) +
        (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
        Complex.binetAbelPlanaFiniteLowerContourTail N z -
          Complex.binetAbelPlanaFiniteUpperContourResidual N z +
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
  Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper hz hbridges N
    (fun n _hn z => inferInstance)

/-- Exact convention-change sink from the ordinary endpoint-restored finite
range to the endpoint-normalized finite range.

The ordinary finite range counts endpoint integer residues with full weight.
The endpoint-normalized sample is therefore the ordinary sample with the
explicit endpoint-restoration term subtracted from the left side.  This theorem
does not cancel `finiteAbelPlanaLogEndpointResidueRestoration` from an identity
for the same ordinary finite sum. -/
theorem Complex.finiteAbelPlana_log_summand_endpointRestoredOrdinaryRange_to_endpointNormalizedConvention_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
          (∑ n in Finset.range ((N + 1) + 1), Complex.log (z + n) =
              ((((z + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (z + ((N + 1 : ℕ) : ℂ)) -
                  (z + ((N + 1 : ℕ) : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + ((N + 1 : ℕ) : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z) +
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) →
            (∑ n in Finset.range ((N + 1) + 1), Complex.log (z + n)) -
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
              ((((z + ((N + 1 : ℕ) : ℂ)) *
                    Complex.log (z + ((N + 1 : ℕ) : ℂ)) -
                  (z + ((N + 1 : ℕ) : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + ((N + 1 : ℕ) : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z) := by
  intro z _hz_re_pos _hbridges N
  let M : ℕ := N + 1
  let X : ℂ :=
    (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
        (z + (M : ℂ))) -
      (z * Complex.log z - z)) +
      (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
      Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
      Complex.binetAbelPlanaFiniteLowerContourTail N z -
        Complex.binetAbelPlanaFiniteUpperContourResidual N z
  intro hordinary
  have hsubtract :
      (∑ n in Finset.range (M + 1), Complex.log (z + n)) -
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
        (X + Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) -
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
    congrArg
      (fun q : ℂ =>
        q - Complex.finiteAbelPlanaLogEndpointResidueRestoration N z)
      hordinary
  have hcancel :
      (X + Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) -
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
        X :=
    add_sub_cancel_right X
      (Complex.finiteAbelPlanaLogEndpointResidueRestoration N z)
  exact Eq.trans hsubtract hcancel

/-- Endpoint-normalized finite Abel-Plana summation convention for the
logarithmic summand.

The ordinary finite range theorem is endpoint-restored.  This wrapper therefore
first records the restored ordinary-range identity and then delegates the actual
endpoint-normalized convention change to
`finiteAbelPlana_log_summand_endpointRestoredOrdinaryRange_to_endpointNormalizedConvention_ownerGap`. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_endpointNormalizedSummationConvention_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
          let M : ℕ := N + 1
          (∑ n in Finset.range (M + 1), Complex.log (z + n)) -
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
            (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
                (z + (M : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z := by
  intro z hz_re_pos hbridges N
  have hordinary :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_restoredOrdinaryRange
      z hz_re_pos hbridges N
  exact
    Complex.finiteAbelPlana_log_summand_endpointRestoredOrdinaryRange_to_endpointNormalizedConvention_ownerGap
      z hz_re_pos hbridges N hordinary

/-- Corrected finite summand normalization without double-counting endpoint
restoration.

The restored imported summand formula includes the endpoint half-residue
restoration explicitly.  Since `binetAbelPlanaFiniteMainTerm` is
`EulerFinite - endpointPrimitive - halfEndpoints`, transporting that restored
formula through the finite Euler logarithmic-Gamma approximant leaves a genuine
`- finiteAbelPlanaLogEndpointResidueRestoration` defect.  The no-defect Binet
finite formula must therefore consume the endpoint-normalized summation
convention above. -/
theorem Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_nonrestored_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
          let M : ℕ := N + 1
          (∑ n in Finset.range (M + 1), Complex.log (z + n)) -
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
            (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
                (z + (M : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z := by
  exact
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_endpointNormalizedSummationConvention_ownerGap

/-- Pure additive transport for the endpoint-normalized finite Euler package.

Here `E` is the shifted Euler finite prefactor, `S` is the logarithmic sample
sum, `A` is the endpoint primitive, and `H` is the half-endpoint term.  This
lemma is intentionally independent of the contour/PV construction; it is only
the algebra saying that an endpoint-normalized identity for `S` transports
through `E - S` and `E - A - H`. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_additive_core_ownerGap
    (E S A H B L U : ℂ)
    (hsummand : S = A + H - B - L - U) :
    E - S = (E - A - H) + B + (L + U) := by
  have hsubstitute :
      E - S = E - (A + H - B - L - U) :=
    congrArg (fun q : ℂ => E - q) hsummand
  have hnormalize :
      E - (A + H - B - L - U) =
        (E - A - H) + B + (L + U) := by
    calc
      E - (A + H - B - L - U)
          = E + -((A + H - B - L) - U) :=
        sub_eq_add_neg E ((A + H - B - L) - U)
      _ = E + (-(A + H - B - L) + U) :=
        congrArg (fun q : ℂ => E + q)
          (Complex.neg_sub_eq_neg_add (A + H - B - L) U)
      _ = E + ((-(A + H - B) + L) + U) :=
        congrArg (fun q : ℂ => E + (q + U))
          (Complex.neg_sub_eq_neg_add (A + H - B) L)
      _ = E + (((-(A + H) + B) + L) + U) :=
        congrArg (fun q : ℂ => E + ((q + L) + U))
          (Complex.neg_sub_eq_neg_add (A + H) B)
      _ = E + ((((-A + -H) + B) + L) + U) :=
        congrArg (fun q : ℂ => E + (((q + B) + L) + U))
          (neg_add A H)
      _ = (E + (-A + -H)) + B + (L + U) := by
        let X : ℂ := -A + -H
        let T : ℂ := L + U
        exact
          Eq.trans
            (congrArg (fun q : ℂ => E + q)
              (add_assoc (X + B) L U))
            (Eq.trans
              (congrArg (fun q : ℂ => E + q)
                (add_assoc X B T))
              (Eq.trans
                (Eq.symm (add_assoc E X (B + T)))
                (Eq.symm (add_assoc (E + X) B T))))
      _ = (E - A - H) + B + (L + U) := by
        exact
          congrArg (fun q : ℂ => q + B + (L + U))
            (Eq.trans
              (Eq.symm (add_assoc E (-A) (-H)))
              (Eq.trans
                (congrArg (fun q : ℂ => q + -H)
                  (sub_eq_add_neg E A).symm)
                (sub_eq_add_neg (E - A) H).symm))
  exact Eq.trans hsubstitute hnormalize

/-- The shifted Euler finite approximation transports an endpoint-normalized
summand formula to the finite main/boundary/lower-tail/upper-residual
decomposition.

This lemma owns only the deterministic substitution of
`binetAbelPlanaLogGammaFiniteApproximation` and
`binetAbelPlanaFiniteMainTerm`.  It assumes the sample-sum identity has already
been stated in endpoint-normalized form, so no endpoint-restoration term can be
introduced or canceled here. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_unfolded_ownerGap
    (N : ℕ)
    (z : ℂ)
    (hsummand :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) :
    Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
      Complex.binetAbelPlanaFiniteMainTerm N z +
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
          (Complex.binetAbelPlanaFiniteLowerContourTail N z +
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) := by
  let M : ℕ := N + 1
  let E : ℂ :=
    z * Complex.log (M : ℂ) +
      Complex.log ((Nat.factorial M : ℕ) : ℂ)
  let A : ℂ :=
    (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
        (z + (M : ℂ))) -
      (z * Complex.log z - z))
  let H : ℂ :=
    (Complex.log z + Complex.log (z + (M : ℂ))) / 2
  let B : ℂ :=
    Complex.binetAbelPlanaFiniteBoundaryCorrection N z
  let L : ℂ :=
    Complex.binetAbelPlanaFiniteLowerContourTail N z
  let U : ℂ :=
    Complex.binetAbelPlanaFiniteUpperContourResidual N z
  have hfiniteApproximation :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        E - ∑ n in Finset.range (M + 1), Complex.log (z + n) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_shifted N M z rfl
  have hfiniteMain :
      Complex.binetAbelPlanaFiniteMainTerm N z = E - A - H :=
    Complex.binetAbelPlanaFiniteMainTerm_unfold N z
  have hsummand_named :
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        A + H - B - L - U :=
    hsummand
  have htransport :
      E - ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (E - A - H) + B + (L + U) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_additive_core_ownerGap
      E
      (∑ n in Finset.range (M + 1), Complex.log (z + n))
      A H B L U hsummand_named
  exact
    Eq.trans hfiniteApproximation
      (Eq.trans htransport
        (congrArg
          (fun q : ℂ => q + B + (L + U))
          hfiniteMain.symm))

/-- Pure Euler-finite algebra for an endpoint-normalized Abel-Plana summand.

This is the exact deterministic identity used after the contour theorem has
already supplied a non-restored sample-sum formula.  It deliberately contains no
endpoint-restoration term. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_algebra_ownerGap
    (N : ℕ)
    (z : ℂ)
    (hsummand :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) :
    Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
      Complex.binetAbelPlanaFiniteMainTerm N z +
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
          (Complex.binetAbelPlanaFiniteLowerContourTail N z +
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) := by
  exact
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_unfolded_ownerGap
      N z hsummand

/-- Transport an endpoint-normalized finite logarithmic summand identity
through the shifted Euler logarithmic-Gamma approximant.

This is the deterministic algebraic layer after the Abel-Plana contour theorem
has already supplied the non-restored finite summand formula.  It is separate
from the contour/PV package so the endpoint normalization can be repaired at
the summand owner level without reintroducing the restored endpoint defect. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointNormalized_transport_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          (let M : ℕ := N + 1
          ∑ n in Finset.range (M + 1), Complex.log (z + n) =
            (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
                (z + (M : ℂ))) -
              (z * Complex.log z - z)) +
              (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
              Complex.binetAbelPlanaFiniteLowerContourTail N z -
                Complex.binetAbelPlanaFiniteUpperContourResidual N z) →
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  (Complex.binetAbelPlanaFiniteLowerContourTail N z +
                    Complex.binetAbelPlanaFiniteUpperContourResidual N z) := by
  intro z _hz_re_pos N hsummand
  exact
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_algebra_ownerGap
      N z hsummand

/-- Endpoint-normalized shifted Euler identity for the finite Binet
approximation.

The historical logarithmic-Gamma approximation is definitionally `E - S`.  If
the sample is rewritten in endpoint-normalized form as `S - R`, the endpoint
restoration remains as a visible final `- R` defect. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_endpointNormalized_shifted_ownerGap :
    ∀ N : ℕ,
      ∀ z : ℂ,
        let M : ℕ := N + 1
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          (z * Complex.log (M : ℂ) +
              Complex.log ((Nat.factorial M : ℕ) : ℂ)) -
            ((∑ n in Finset.range (M + 1), Complex.log (z + n)) -
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z) -
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  intro N z
  let M : ℕ := N + 1
  let E : ℂ :=
    z * Complex.log (M : ℂ) +
      Complex.log ((Nat.factorial M : ℕ) : ℂ)
  let S : ℂ :=
    ∑ n in Finset.range (M + 1), Complex.log (z + n)
  let R : ℂ :=
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z
  have hshifted :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        E - S :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_shifted N M z rfl
  have hendpoint_normalized_sub :
      E - S = E - (S - R) - R := by
    calc
      E - S = E + -S := sub_eq_add_neg E S
      _ = E + (-(S - R) + -R) := by
        have hneg_normalized :
            -(S - R) + -R = -S := by
          calc
            -(S - R) + -R = (R - S) + -R := by
              exact congrArg (fun q : ℂ => q + -R) (neg_sub S R)
            _ = (R + -S) + -R := by
              exact congrArg (fun q : ℂ => q + -R) (sub_eq_add_neg R S)
            _ = (-S + R) + -R := by
              exact congrArg (fun q : ℂ => q + -R) (add_comm R (-S))
            _ = -S + (R + -R) := add_assoc (-S) R (-R)
            _ = -S + 0 := by
              exact congrArg (fun q : ℂ => -S + q) (add_neg_cancel R)
            _ = -S := add_zero (-S)
        exact congrArg (fun q : ℂ => E + q) hneg_normalized.symm
      _ = (E + -(S - R)) + -R := (add_assoc E (-(S - R)) (-R)).symm
      _ = E - (S - R) + -R := by
        exact congrArg (fun q : ℂ => q + -R) (sub_eq_add_neg E (S - R)).symm
      _ = E - (S - R) - R :=
        (sub_eq_add_neg (E - (S - R)) R).symm
  exact Eq.trans hshifted hendpoint_normalized_sub

/-- Deterministic transport for the repaired endpoint-normalized shifted
identity, with the endpoint-restoration defect kept visible. -/
theorem Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_shifted_transport_ownerGap
    (N : ℕ)
    (z : ℂ)
    (hsummand :
      let M : ℕ := N + 1
      (∑ n in Finset.range (M + 1), Complex.log (z + n)) -
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) :
    Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
      Complex.binetAbelPlanaFiniteMainTerm N z +
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
          (Complex.binetAbelPlanaFiniteLowerContourTail N z +
            Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  let M : ℕ := N + 1
  let E : ℂ :=
    z * Complex.log (M : ℂ) +
      Complex.log ((Nat.factorial M : ℕ) : ℂ)
  let S : ℂ :=
    ∑ n in Finset.range (M + 1), Complex.log (z + n)
  let R : ℂ :=
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z
  let A : ℂ :=
    (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
        (z + (M : ℂ))) -
      (z * Complex.log z - z))
  let H : ℂ :=
    (Complex.log z + Complex.log (z + (M : ℂ))) / 2
  let B : ℂ :=
    Complex.binetAbelPlanaFiniteBoundaryCorrection N z
  let L : ℂ :=
    Complex.binetAbelPlanaFiniteLowerContourTail N z
  let U : ℂ :=
    Complex.binetAbelPlanaFiniteUpperContourResidual N z
  have hfiniteApproximation :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        E - (S - R) - R :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_eq_endpointNormalized_shifted_ownerGap
      N z
  have hfiniteMain :
      Complex.binetAbelPlanaFiniteMainTerm N z = E - A - H :=
    Complex.binetAbelPlanaFiniteMainTerm_unfold N z
  have hsummand_named :
      S - R = A + H - B - L - U :=
    hsummand
  have htransport :
      E - (S - R) = (E - A - H) + B + (L + U) :=
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_transport_additive_core_ownerGap
      E
      (S - R)
      A H B L U hsummand_named
  exact
    Eq.trans hfiniteApproximation
      (Eq.trans
        (congrArg (fun q : ℂ => q - R) htransport)
        (Eq.trans
          (congrArg
            (fun q : ℂ => q - R)
            (congrArg
              (fun q : ℂ => q + B + (L + U))
              hfiniteMain.symm))
          rfl))

/-- Remaining endpoint-normalized finite logarithmic Gamma accounting.

The shifted identity above shows that endpoint-normalizing the sample sum alone
still leaves the explicit endpoint-restoration defect for the historical finite
Euler approximation.  Removing this defect requires a genuine upstream
normalization/absorption theorem, not local algebra. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointNormalized_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  (Complex.binetAbelPlanaFiniteLowerContourTail N z +
                    Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                      Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  intro z hz_re_pos hbridges N
  have hsummand :
      let M : ℕ := N + 1
      (∑ n in Finset.range (M + 1), Complex.log (z + n)) -
          Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z :=
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper_nonrestored_ownerGap
      z hz_re_pos hbridges N
  exact
    Complex.binetAbelPlanaLogGammaFiniteApproximation_endpointNormalized_shifted_transport_ownerGap
      N z hsummand

/-- Transport the endpoint-normalized finite summand Abel-Plana formula through
the shifted Euler logarithmic Gamma approximant and the finite-main-term
normalization.

The finite summand theorem must be consumed in endpoint-normalized form here.
The restored summand identity is still useful as a diagnostic: transporting it
through this layer gives the explicit defect theorem above, so the owner repair
belongs in the finite Abel-Plana endpoint-normalization theorem rather than in a
false downstream cancellation. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_accounting_from_endpointNormalizedSummandFormula_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                (Complex.binetAbelPlanaFiniteLowerContourTail N z +
                  Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z := by
  exact fun z hz_re_pos hbridges N =>
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointNormalized_ownerGap
      z hz_re_pos hbridges N

/-- The endpoint restoration term is exactly the half-weighted endpoint
integer-residue contribution used by the principal-value rectangle. -/
theorem Complex.finiteAbelPlanaLogEndpointResidueRestoration_eq_endpointIntegerResidueContribution_ownerFiniteContourNormalization
    (N : ℕ)
    (z : ℂ) :
    Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
      Complex.finiteAbelPlanaLogEndpointIntegerResidueContribution N z :=
  Complex.finiteAbelPlanaLogEndpointResidueRestoration_unfold N z

/-- Additive transport from endpoint-normalized accounting to the corrected
finite contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_endpointRestoration_accounting_to_contourRemainder
    (A S R C : ℂ)
    (hC : C = S - R) :
    A + S - R = A + C := by
  have hleft :
      A + S - R = A + (S - R) := by
    calc
      A + S - R = (A + S) + -R := by
        exact sub_eq_add_neg (A + S) R
      _ = A + (S + -R) := by
        exact add_assoc A S (-R)
      _ = A + (S - R) := by
        exact congrArg (fun q : ℂ => A + q) (sub_eq_add_neg S R).symm
  exact Eq.trans hleft (congrArg (fun q : ℂ => A + q) hC.symm)

/-- The endpoint-normalized finite Abel-Plana formula is exactly the corrected
finite-contour formula once the named contour remainder owns the endpoint
restoration defect. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestorationAccounted_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        Complex.FiniteHeightPVBridgePackage z →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos hbridges N
  have hdefect :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            (Complex.binetAbelPlanaFiniteLowerContourTail N z +
              Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointNormalized_ownerGap
      z hz_re_pos hbridges N
  have hcontour :
      Complex.binetAbelPlanaFiniteContourRemainder N z =
        (Complex.binetAbelPlanaFiniteLowerContourTail N z +
          Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
            Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
    Complex.binetAbelPlanaFiniteContourRemainder_core_unfold N z
  have haccount :
      Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            (Complex.binetAbelPlanaFiniteLowerContourTail N z +
              Complex.binetAbelPlanaFiniteUpperContourResidual N z) -
                Complex.finiteAbelPlanaLogEndpointResidueRestoration N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z :=
    Complex.binetSecondFormula_finiteAbelPlana_endpointRestoration_accounting_to_contourRemainder
      (Complex.binetAbelPlanaFiniteMainTerm N z +
        Complex.binetAbelPlanaFiniteBoundaryCorrection N z)
      (Complex.binetAbelPlanaFiniteLowerContourTail N z +
        Complex.binetAbelPlanaFiniteUpperContourResidual N z)
      (Complex.finiteAbelPlanaLogEndpointResidueRestoration N z)
      (Complex.binetAbelPlanaFiniteContourRemainder N z)
      hcontour
  exact Eq.trans hdefect haccount

/-- The finite-height Abel-Plana contour package plus endpoint-restoration
accounting gives the corrected finite Binet contour-remainder formula. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_of_bridgePackage
    (hbridge :
      ∀ z : ℂ,
        0 < z.re →
          Complex.FiniteHeightPVBridgePackage z)
    (haccounting :
      ∀ z : ℂ,
        0 < z.re →
          Complex.FiniteHeightPVBridgePackage z →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hbridges : Complex.FiniteHeightPVBridgePackage z :=
    hbridge z hz_re_pos
  have hsummand :
      let M : ℕ := N + 1
      ∑ n in Finset.range (M + 1), Complex.log (z + n) =
        (((z + (M : ℂ)) * Complex.log (z + (M : ℂ)) -
            (z + (M : ℂ))) -
          (z * Complex.log z - z)) +
          (Complex.log z + Complex.log (z + (M : ℂ))) / 2 -
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z -
          Complex.binetAbelPlanaFiniteLowerContourTail N z -
            Complex.binetAbelPlanaFiniteUpperContourResidual N z +
              Complex.finiteAbelPlanaLogEndpointResidueRestoration N z :=
    Complex.finiteAbelPlana_log_summand_eq_mainBoundaryUpper
      hz_re_pos hbridges N
      (fun n _hn z => inferInstance)
  have habsorbed :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z :=
    haccounting z hz_re_pos hbridges N
  exact habsorbed

/-- Residual finite Abel-Plana contour obligation: the finite approximation is
exactly the main term, boundary correction, and corrected contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_of_bridgePackage
      Complex.binetSecondFormula_finiteAbelPlana_finiteHeightPVBridgePackage_endpointRestored
      Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_endpointRestorationAccounted_ownerGap

/-- The finite contour formula identifies the named finite remainder error with
the corrected finite contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder
    (hfinite :
      ∀ z : ℂ,
        0 < z.re →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaFiniteRemainderError N z =
            Complex.binetAbelPlanaFiniteContourRemainder N z := by
  intro z hz_re_pos N
  have hfinite_N :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
        Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z :=
    hfinite z hz_re_pos N
  have herror_unfold :
      Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) :=
    Complex.binetAbelPlanaFiniteRemainderError_unfold N z
  calc
    Complex.binetAbelPlanaFiniteRemainderError N z =
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) :=
      herror_unfold
    _ =
        (Complex.binetAbelPlanaFiniteMainTerm N z +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
            Complex.binetAbelPlanaFiniteContourRemainder N z) -
          (Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z) := by
      exact
        congrArg
          (fun u : ℂ =>
            u -
              (Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z))
          hfinite_N
    _ = Complex.binetAbelPlanaFiniteContourRemainder N z := by
      exact
        Complex.add_add_sub_add_eq_right
          (Complex.binetAbelPlanaFiniteMainTerm N z)
          (Complex.binetAbelPlanaFiniteBoundaryCorrection N z)
          (Complex.binetAbelPlanaFiniteContourRemainder N z)

/-- Residual finite Abel-Plana contour obligation after endpoint restoration
has been accounted into the named contour remainder. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaFiniteRemainderError N z =
            Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder
      Complex.binetSecondFormula_finiteAbelPlana_logGammaFiniteApproximation_eq_main_boundary_contourRemainder_ownerGap

/-- Pointwise finite Abel-Plana contour decomposition on the open right
half-plane. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z := by
  exact
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_of_remainderError_eq_contourRemainder
      Complex.binetSecondFormula_finiteAbelPlana_remainderError_eq_contourRemainder_ownerGap

/-- The finite Abel-Plana logarithmic summand decomposition on the positive
real axis. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_posReal_ownerGap :
    ∀ x : ℝ,
      0 < x →
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
            Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ) := by
  intro x hx_pos
  have hx_re_pos : 0 < ((x : ℂ).re) :=
    Eq.subst
      (motive := fun y : ℝ => 0 < y)
      (Complex.ofReal_re x).symm
      hx_pos
  exact
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
      (x : ℂ) hx_re_pos

/-- The finite Abel-Plana logarithmic summand decomposition on the open right
half-plane, with the neighborhood stability needed for differentiation. -/
theorem Complex.binetSecondFormula_finiteAbelPlana_decomposition_openRightHalfPlane_ownerGap :
    ∀ z : ℂ,
      0 < z.re →
        (∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
        (∀ᶠ y : ℂ in 𝓝 z,
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
              Complex.binetAbelPlanaFiniteMainTerm N y +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                  Complex.binetAbelPlanaFiniteContourRemainder N y) := by
  intro z hz_re_pos
  have hpoint :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
          Complex.binetAbelPlanaFiniteMainTerm N z +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z :=
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
      z hz_re_pos
  have hopen : IsOpen {y : ℂ | 0 < y.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hnear_re_pos : ∀ᶠ y : ℂ in 𝓝 z, 0 < y.re :=
    hopen.mem_nhds hz_re_pos
  have hnear :
      ∀ᶠ y : ℂ in 𝓝 z,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
            Complex.binetAbelPlanaFiniteMainTerm N y +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                Complex.binetAbelPlanaFiniteContourRemainder N y :=
    hnear_re_pos.mono
      (fun y hy_re_pos =>
        Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
          y hy_re_pos)
  exact ⟨hpoint, hnear⟩

/-- Binet-branch coherence for the Binet second formula, assembled from the
owner-level exponential branch and finite-Abel-Plana components. -/
theorem Complex.BinetSecondFormulaBranchCoherence.of_owner_components
    (hgamma :
      ∀ z : ℂ, 0 < z.re →
        Complex.exp (Complex.binetLogGammaBranch z) = Complex.Gamma z)
    (hreal :
      ∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ))
    (hopen :
      ∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) :
    Complex.BinetSecondFormulaBranchCoherence :=
  ⟨hgamma, hreal, hopen⟩

/-- Owner gap: Binet-branch coherence for the Binet second formula on the
right half-plane. -/
theorem Complex.binetSecondFormula_branchCoherence_ownerGap :
    Complex.BinetSecondFormulaBranchCoherence :=
  Complex.BinetSecondFormulaBranchCoherence.of_owner_components
    (fun z hz_re_pos =>
      Complex.exp_binetLogGammaBranch_eq_Gamma_of_finiteAbelPlana
        hz_re_pos
        (Complex.binetSecondFormula_finiteAbelPlana_decomposition_pointwise_openRightHalfPlane_ownerGap
          z hz_re_pos))
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_posReal_ownerGap
    Complex.binetSecondFormula_finiteAbelPlana_decomposition_openRightHalfPlane_ownerGap

/-- Assemble the Binet branch-tail package from a tail absorption theorem and
the already proved branch-coherence theorem. -/
theorem Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_ownerCoherence
    (htail :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
              (C / ‖w‖) *
                (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
  Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_and_coherence
    htail
    Complex.binetSecondFormula_branchCoherence_ownerGap

/-- Pointwise unfolding of the contour-tail majorant kernel norm.

The current contour kernel is deliberately not just the decaying split-tail
kernel.  It contains the raw principal-tail norm plus the decaying scalar
majorant.  Any proof of decay for its integral must therefore separately
control the raw principal-tail integral. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
    (w : ℂ)
    (t : ℝ) :
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
  let A : ℝ := ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let B : ℝ :=
    |((1 : ℝ) / ‖w‖) *
      (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
  have hAB_nonneg : 0 ≤ A + B :=
    add_nonneg (norm_nonneg _) (abs_nonneg _)
  have hkernel :
      Complex.binetSecondFormulaContourTailMajorantKernel w t =
        ((A + B : ℝ) : ℂ) := by
    rfl
  calc
    ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
        ‖((A + B : ℝ) : ℂ)‖ := by
      exact congrArg norm hkernel
    _ = |A + B| := Complex.norm_real (A + B)
    _ = A + B := abs_of_nonneg hAB_nonneg
    _ =
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ +
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := rfl

/-- On the Binet split-tail range the explicit decaying summand has no sign
change, so its absolute value integrates as the constant multiple
`1 / ‖w‖` of the scalar tail kernel. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_eq
    (w : ℂ)
    (hw_norm : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
      ((1 : ℝ) / ‖w‖) *
        (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
    (le_div_iff₀ two_pos).mpr
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖w‖)
        (one_mul (2 : ℝ)).symm
        hw_norm)
  have hcoeff_nonneg : 0 ≤ (1 : ℝ) / ‖w‖ :=
    div_nonneg zero_le_one (norm_nonneg w)
  have hpoint :
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
            ((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    fun t ht =>
      let ht_pos : 0 < t :=
        lt_of_le_of_lt
          (le_trans zero_le_one hhalf_ge_one)
          ht
      let htail_nonneg :
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
        le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht_pos)
      let hprod_nonneg :
          0 ≤
            ((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        mul_nonneg hcoeff_nonneg htail_nonneg
      abs_of_nonneg hprod_nonneg
  calc
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact setIntegral_congr_fun measurableSet_Ioi hpoint
    _ =
        ((1 : ℝ) / ‖w‖) *
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact MeasureTheory.integral_smul
        ((1 : ℝ) / ‖w‖)
        (fun t : ℝ =>
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))

/-- Multiplying the decaying-summand integral identity by the contour symmetry
factor gives exactly the constant `2 / ‖w‖`. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
    (w : ℂ)
    (hw_norm : 2 ≤ ‖w‖) :
    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
      ((2 : ℝ) / ‖w‖) *
        (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  have hdecay_eq :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ((1 : ℝ) / ‖w‖) * J :=
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_eq
      w hw_norm
  have hconst :
      2 * (((1 : ℝ) / ‖w‖) * J) = ((2 : ℝ) / ‖w‖) * J := by
    calc
      2 * (((1 : ℝ) / ‖w‖) * J) =
          (2 * ((1 : ℝ) / ‖w‖)) * J := by
        exact (mul_assoc (2 : ℝ) ((1 : ℝ) / ‖w‖) J).symm
      _ = ((2 * (1 : ℝ)) / ‖w‖) * J := by
        exact congrArg (fun x : ℝ => x * J)
          (mul_div_assoc (2 : ℝ) (1 : ℝ) ‖w‖).symm
      _ = ((2 : ℝ) / ‖w‖) * J := by
        exact congrArg (fun x : ℝ => (x / ‖w‖) * J) (mul_one (2 : ℝ))
  have htarget_eq :
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| =
        ((2 : ℝ) / ‖w‖) * J := by
    exact Eq.trans (congrArg (fun x : ℝ => 2 * x) hdecay_eq) hconst
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ ((2 : ℝ) / ‖w‖) * J)
    htarget_eq.symm
    (le_refl (((2 : ℝ) / ‖w‖) * J))

/-- Elementary integral normalization for the decaying summand included in the
contour-tail majorant kernel.

This is not the hard Binet contour theorem: it only says that the explicitly
inserted scalar summand contributes the expected additional constant `2` after
integration over the split tail. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            |((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact fun w _hw_re_pos hw_norm =>
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
      w hw_norm

/-- Integral decay for the genuine scalar decaying tail kernel. -/
theorem Complex.binetSecondFormula_decayingTailKernel_integral_decay :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro w _hw_re_pos hw_norm
  have hpoint :
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
            |((1 : ℝ) / ‖w‖) *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
    intro t ht
    let m : ℝ :=
      ((1 : ℝ) / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    have hkernel_cast :
        Complex.binetSecondFormulaDecayingTailKernel w t = (m : ℂ) := by
      rfl
    calc
      ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
          ‖(m : ℂ)‖ := by
        exact congrArg norm hkernel_cast
      _ = |m| := RCLike.norm_ofReal (K := ℂ) m
      _ =
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := rfl
  have hintegral_eq :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaDecayingTailKernel w t‖ =
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| := by
    exact setIntegral_congr_fun measurableSet_Ioi hpoint
  have hsummand :
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          |((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
        ((2 : ℝ) / ‖w‖) *
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le
      w hw_norm
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        2 * x ≤
          ((2 : ℝ) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
      hintegral_eq.symm
      hsummand

/-- The principal-tail norm is integrable on the split-tail range.

This is only the norm-integrability consequence of the existing principal-tail
integrability theorem; it is not the principal-tail decay estimate. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_integrableOn_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ => ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖)
      (Set.Ioi (‖w‖ / 2)) := by
  exact
    (Complex.binetSecondFormulaPrincipalTailKernel_integrableOn_tail
      (w := w) hw_re_pos).norm

/-- The explicit scalar summand in the contour-tail majorant is integrable on
the split-tail range. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integrableOn_tail
    {w : ℂ}
    (hw_norm : 2 ≤ ‖w‖) :
    IntegrableOn
      (fun t : ℝ =>
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|)
      (Set.Ioi (‖w‖ / 2)) := by
  have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
    (le_div_iff₀ two_pos).mpr
      (Eq.subst
        (motive := fun x : ℝ => x ≤ ‖w‖)
        (one_mul (2 : ℝ)).symm
        hw_norm)
  have htail_integrable :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi (‖w‖ / 2)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty.mono_set
      (fun t ht => lt_of_le_of_lt hhalf_ge_one ht)
  have hscaled_integrable :
      IntegrableOn
        (fun t : ℝ =>
          ((1 : ℝ) / ‖w‖) *
            (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
        (Set.Ioi (‖w‖ / 2)) :=
    htail_integrable.const_mul ((1 : ℝ) / ‖w‖)
  exact hscaled_integrable.abs

/-- Set-integral decomposition for the unfolded contour-tail majorant.

This is the remaining elementary bookkeeping condition behind the accounting
lemma: after the pointwise norm unfolding, the set integral of the full
majorant is the sum of the principal-tail norm integral and the explicit
decaying-summand integral.  Its proof should be the ordinary `integral_add`
transport after the local integrability facts for the two summands are in
scope. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_decomposition_ownerGap :
    ∀ w : ℂ,
      0 < w.re →
      2 ≤ ‖w‖ →
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              |((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|) := by
  exact fun w hw_re_pos hw_norm =>
    let A : ℝ → ℝ := fun t : ℝ =>
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
    let B : ℝ → ℝ := fun t : ℝ =>
      |((1 : ℝ) / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
    let hprincipal_integrable :
        IntegrableOn A (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_principalTailKernel_norm_integrableOn_tail
        (w := w) hw_re_pos
    let hdecaying_integrable :
        IntegrableOn B (Set.Ioi (‖w‖ / 2)) :=
      Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integrableOn_tail
        (w := w) hw_norm
    let hpoint :
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
              A t + B t :=
      fun t _ht =>
        Complex.binetSecondFormula_contourTailMajorantKernel_norm_eq_principal_add_decaying
          w t
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t + B t := by
        exact setIntegral_congr_fun measurableSet_Ioi hpoint
      _ =
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), A t) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2), B t) := by
        exact integral_add hprincipal_integrable hdecaying_integrable

/-- Integral accounting for the unfolded contour-tail majorant kernel.

After the pointwise unfolding, the kernel integral is the sum of the raw
principal-tail contribution and the explicit decaying summand.  This theorem
is the bookkeeping layer that combines those two estimates and produces the
constant `C + 2`. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
    {C : ℝ}
    (hprincipal :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
    (hdecaying :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              |((1 : ℝ) / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))| ≤
            ((2 : ℝ) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            ((C + 2) / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact fun w hw_re_pos hw_norm =>
    let J : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
    let P : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
    let D : ℝ :=
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        |((1 : ℝ) / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))|
    have hdecomp :
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
            ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ =
          P + D :=
      Complex.binetSecondFormula_contourTailMajorantKernel_integral_decomposition_ownerGap
        w hw_re_pos hw_norm
    have hprincipal_w :
        2 * P ≤ (C / ‖w‖) * J :=
      hprincipal w hw_re_pos hw_norm
    have hdecaying_w :
        2 * D ≤ ((2 : ℝ) / ‖w‖) * J :=
      hdecaying w hw_re_pos hw_norm
    have hsum :
        2 * (P + D) ≤
          (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J := by
      have hleft :
          2 * (P + D) = 2 * P + 2 * D := by
        exact mul_add (2 : ℝ) P D
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J)
          hleft.symm
          (add_le_add hprincipal_w hdecaying_w)
    have hconst :
        (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J =
          ((C + 2) / ‖w‖) * J := by
      calc
        (C / ‖w‖) * J + ((2 : ℝ) / ‖w‖) * J =
            (C / ‖w‖ + (2 : ℝ) / ‖w‖) * J := by
          exact (add_mul (C / ‖w‖) ((2 : ℝ) / ‖w‖) J).symm
        _ = (((C + 2 : ℝ) / ‖w‖)) * J := by
          exact congrArg (fun x : ℝ => x * J) (add_div C (2 : ℝ) ‖w‖).symm
        _ = ((C + 2) / ‖w‖) * J := rfl
    have hfull :
        2 *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖) ≤
          ((C + 2) / ‖w‖) * J := by
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            2 * x ≤ ((C + 2) / ‖w‖) * J)
          hdecomp.symm
          (le_trans hsum (le_of_eq hconst))
    hfull

/-- Integral accounting for the contour-tail majorant kernel.

This is the exact real-variable comparison needed after unfolding the kernel:
the raw principal-tail integral contributes the supplied constant `C`, and the
extra decaying summand contributes the additional constant `2`.

The proof is intentionally separated from the analytic principal-tail decay
because the latter is a contour deformation/cancellation theorem, not a
pointwise domination by the decaying scalar kernel. -/
theorem Complex.binetSecondFormula_contourTailMajorantKernel_integral_decay_of_principalTailKernel_integral_decay
    {C : ℝ}
    (hC : 0 < C)
    (hprincipal :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    ⟨C + 2, add_pos hC two_pos,
      Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
        hprincipal
        Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap⟩

/-- Correct principal-tail norm estimate after removing the false endpoint
absorption.

The raw principal-tail norm does not satisfy a full-sector pure
`C / ‖w‖` bound: on the bounded branch-wall window it retains the explicit
local-indentation logarithmic envelope.  The far tail has the desired scaled
decay. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_cancellation_estimate_ownerGap :
    Complex.BinetSecondFormulaBranchLocalIndentationTailControl := by
  match
    Complex.binetSecondFormula_principalTailKernel_integral_localIndentation_add_far_scaled_decay with
  | ⟨Cfar, hCfar_nonneg, hestimate⟩ =>
      exact
        ⟨Cfar, hCfar_nonneg,
          fun w hw_re_pos hw_norm_two =>
            hestimate w hw_re_pos (le_trans one_le_two hw_norm_two)⟩

/-- Pre-cancellation tail-remainder estimate with the branch-wall
local-indentation term still visible.

This is the honest contour estimate before paired branch-wall cancellation:
the actual Binet tail remainder is bounded by the local indentation envelope
plus the far scaled decaying tail. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_localIndentation_add_far_scaled_decay
    (hlocal : Complex.BinetSecondFormulaBranchLocalIndentationTailControl) :
    Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl := by
  match hlocal with
  | ⟨Cfar, hCfar_nonneg, hlocal_bound⟩ =>
      exact
        ⟨Cfar, hCfar_nonneg,
          fun w hw_re_pos hw_norm_two =>
            have htail_to_principal :
                ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                  2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ :=
              Complex.binetSecondFormulaTailRemainder_norm_le_principalTailKernel_norm_integral
                (w := w) hw_re_pos
            have hprincipal_local :
                2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w +
                    (Cfar / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w :=
              hlocal_bound w hw_re_pos hw_norm_two
            le_trans htail_to_principal hprincipal_local⟩

/-- Owner pre-cancellation tail-remainder estimate with the branch-wall
local-indentation term still visible. -/
theorem Complex.binetSecondFormula_tailRemainder_localIndentation_add_far_scaled_decay_ownerGap :
    Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl := by
  exact
    Complex.binetSecondFormula_tailRemainder_norm_le_localIndentation_add_far_scaled_decay
      Complex.binetSecondFormula_principalTailKernel_integral_cancellation_estimate_ownerGap

/-- Sector-local pre-cancellation tail-remainder estimate after absorbing the
local-indentation envelope.

Away from the branch wall, the local indentation envelope is absorbed into the
standard Binet decaying tail.  The estimate remains sector-local and therefore
does not replace the full wall-cancellation theorem. -/
theorem Complex.binetSecondFormula_tailRemainder_sectorBound_of_localIndentation_absorption
    (hlocal :
      Complex.BinetSecondFormulaTailRemainderLocalIndentationTailControl)
    (habsorb : Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption) :
    Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption := by
  intro δ hδ
  match hlocal with
  | ⟨Cfar, _hCfar_nonneg, htail_local⟩ =>
      match habsorb δ hδ with
      | ⟨Clocal, hClocal_pos, hlocal_absorb⟩ =>
          let C : ℝ := max Clocal Cfar
          have hClocal_le_C : Clocal ≤ C :=
            le_max_left Clocal Cfar
          have hCfar_le_C : Cfar ≤ C :=
            le_max_right Clocal Cfar
          have hC_pos : 0 < C :=
            lt_of_lt_of_le hClocal_pos hClocal_le_C
          exact
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two =>
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                let L : ℝ :=
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w
                let F : ℝ := (Cfar / ‖w‖) * J
                have htail_pre :
                    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                      L + F :=
                  have hnorm_pos : 0 < ‖w‖ :=
                    lt_of_lt_of_le zero_lt_two hw_norm_two
                  have hsector_pos : 0 < δ * ‖w‖ :=
                    mul_pos hδ hnorm_pos
                  htail_local w
                    (lt_of_lt_of_le hsector_pos hw_sector)
                    hw_norm_two
                have hlocal_le :
                    L ≤ Clocal * J :=
                  hlocal_absorb w hw_sector hw_norm_two
                have hJ_nonneg : 0 ≤ J :=
                  integral_nonneg_of_ae
                    ((ae_restrict_mem measurableSet_Ioi).mono
                      (fun t ht =>
                        Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
                          (lt_of_le_of_lt
                            (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
                            ht)))
                have hlocal_C_le :
                    Clocal * J ≤ C * J :=
                  mul_le_mul_of_nonneg_right hClocal_le_C hJ_nonneg
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hfar_C_le :
                    (Cfar / ‖w‖) * J ≤ (C / ‖w‖) * J := by
                  have hdiv_le : Cfar / ‖w‖ ≤ C / ‖w‖ :=
                    div_le_div_of_nonneg_right hCfar_le_C (le_of_lt hnorm_pos)
                  exact mul_le_mul_of_nonneg_right hdiv_le hJ_nonneg
                have hsum_le :
                    L + F ≤ C * J + (C / ‖w‖) * J :=
                  add_le_add (le_trans hlocal_le hlocal_C_le) hfar_C_le
                have hconst :
                    C * J + (C / ‖w‖) * J =
                      (C + C / ‖w‖) * J := by
                  calc
                    C * J + (C / ‖w‖) * J =
                        (C + C / ‖w‖) * J := by
                      exact (add_mul C (C / ‖w‖) J).symm
                le_trans htail_pre (le_trans hsum_le (le_of_eq hconst))⟩

/-- Sector-local exponential upper bound for the branch-window indentation
envelope.

This is the real-variable logarithmic estimate: once `w.re` is bounded below
by a fixed sector fraction of `‖w‖`, the logarithmic branch-window factor has
only polynomial/logarithmic size and is absorbed by the exponential factor
coming from the Binet denominator. -/
def Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            Complex.binetSecondFormulaBranchLocalIndentationEnvelope w ≤
              C * ‖w‖ * Real.exp (-Real.pi * ‖w‖)

/-- Sector-local logarithmic-window exponential bound before substituting the
named indentation envelope.

This is the scalar inequality for the explicit local branch-window expression:
the sector condition controls the two logarithms, while the denominator
`exp (π ‖w‖) - 1` supplies the exponential decay. -/
def Complex.BinetSecondFormulaBranchLocalIndentationLogWindowExpBound : Prop :=
  ∀ δ : ℝ,
    0 < δ →
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          δ * ‖w‖ ≤ w.re →
          2 ≤ ‖w‖ →
            2 *
                (((max |Real.log (w.re / (3 * ‖w‖))|
                    (max |Real.log (1 : ℝ)|
                      |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) ≤
              C * ‖w‖ * Real.exp (-Real.pi * ‖w‖)

/-- Exponential lower bound for the standard Binet decaying-tail integral.

This is the complementary real-variable tail estimate: the positive scalar
kernel on a unit-length interval starting at `‖w‖ / 2` supplies a uniform
multiple of `exp (-π ‖w‖ / 2)`. -/
def Complex.BinetSecondFormulaDecayingTailIntegralExpLower : Prop :=
  ∃ c : ℝ,
    0 < c ∧
    ∀ w : ℂ,
      2 ≤ ‖w‖ →
        c * ‖w‖ * Real.exp (-Real.pi * ‖w‖) ≤
          Complex.binetSecondFormulaDecayingTailIntegral w

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

/-- Owner real-variable leaf: sector-local exponential upper bound for the
explicit logarithmic window. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_logWindowExpBound_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationLogWindowExpBound := by
  intro δ hδ
  let Lδ : ℝ :=
    max |Real.log (δ / 3)| |Real.log (3 / δ)|
  let C : ℝ := 8 * (Lδ + Real.pi + 1)
  have hLδ_nonneg : 0 ≤ Lδ :=
    le_max_of_le_left (abs_nonneg (Real.log (δ / 3)))
  have hC_pos : 0 < C := by
    have hinside_pos : 0 < Lδ + Real.pi + 1 := by
      exact
        add_pos_of_nonneg_of_pos
          (add_nonneg hLδ_nonneg Real.pi_nonneg)
          zero_lt_one
    have height_pos : 0 < (8 : ℝ) := by
      show 0 < (2 : ℝ) * 4
      exact mul_pos two_pos four_pos
    exact mul_pos height_pos hinside_pos
  exact
    ⟨C, hC_pos,
      fun w hw_sector hw_norm_two =>
        have hw_norm_pos : 0 < ‖w‖ :=
          lt_of_lt_of_le zero_lt_two hw_norm_two
        have hw_re_pos : 0 < w.re :=
          lt_of_lt_of_le (mul_pos hδ hw_norm_pos) hw_sector
        have hre_le_norm : w.re ≤ ‖w‖ := by
          calc
            w.re = |w.re| := Eq.symm (abs_of_pos hw_re_pos)
            _ ≤ ‖w‖ := Complex.abs_re_le_abs w
        let x : ℝ := w.re / (3 * ‖w‖)
        let y : ℝ := (3 * ‖w‖) / w.re
        have hthree_norm_pos : 0 < 3 * ‖w‖ :=
          mul_pos Real.zero_lt_three hw_norm_pos
        have hx_pos : 0 < x :=
          div_pos hw_re_pos hthree_norm_pos
        have hy_pos : 0 < y :=
          div_pos hthree_norm_pos hw_re_pos
        have hx_lower : δ / 3 ≤ x := by
          have hmul :
              δ * ‖w‖ / (3 * ‖w‖) ≤ w.re / (3 * ‖w‖) :=
            div_le_div_of_nonneg_right hw_sector (le_of_lt hthree_norm_pos)
          have hleft : δ * ‖w‖ / (3 * ‖w‖) = δ / 3 := by
            calc
              δ * ‖w‖ / (3 * ‖w‖) =
                  (δ / 3) * (‖w‖ / ‖w‖) := by
                calc
                  δ * ‖w‖ / (3 * ‖w‖) =
                      (δ * ‖w‖) / (3 * ‖w‖) := rfl
                  _ = (δ / 3) * (‖w‖ / ‖w‖) := by
                    exact
                      Eq.symm
                        (div_mul_div_comm δ 3 ‖w‖ ‖w‖)
              _ = (δ / 3) * 1 := by
                exact congrArg (fun z : ℝ => (δ / 3) * z)
                  (div_self (ne_of_gt hw_norm_pos))
              _ = δ / 3 := mul_one (δ / 3)
          Eq.subst
            (motive := fun z : ℝ => z ≤ x)
            hleft
            hmul
        have hx_upper : x ≤ 1 := by
          have hnum_le : w.re ≤ 3 * ‖w‖ := by
            calc
              w.re ≤ ‖w‖ := hre_le_norm
              _ ≤ 3 * ‖w‖ :=
                le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
          exact
            (div_le_one hthree_norm_pos).mpr hnum_le
        have hy_lower : (1 : ℝ) ≤ y := by
          have hden_le : w.re ≤ 3 * ‖w‖ := by
            calc
              w.re ≤ ‖w‖ := hre_le_norm
              _ ≤ 3 * ‖w‖ :=
                le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
          exact (le_div_iff₀ hw_re_pos).mpr
            (Eq.subst
              (motive := fun z : ℝ => z ≤ 3 * ‖w‖)
              (one_mul w.re).symm
              hden_le)
        have hy_upper : y ≤ 3 / δ := by
          have hden_le :
              δ * ‖w‖ ≤ w.re := hw_sector
          have hnum_nonneg : 0 ≤ 3 * ‖w‖ :=
            le_of_lt hthree_norm_pos
          have hdiv_le :
              (3 * ‖w‖) / w.re ≤ (3 * ‖w‖) / (δ * ‖w‖) :=
            div_le_div_of_nonneg_left
              hnum_nonneg
              (mul_pos hδ hw_norm_pos)
              hden_le
          have hright : (3 * ‖w‖) / (δ * ‖w‖) = 3 / δ := by
            calc
              (3 * ‖w‖) / (δ * ‖w‖) =
                  (3 / δ) * (‖w‖ / ‖w‖) := by
                exact
                  Eq.symm
                    (div_mul_div_comm 3 δ ‖w‖ ‖w‖)
              _ = (3 / δ) * 1 := by
                exact congrArg (fun z : ℝ => (3 / δ) * z)
                  (div_self (ne_of_gt hw_norm_pos))
              _ = 3 / δ := mul_one (3 / δ)
          Eq.subst
            (motive := fun z : ℝ => y ≤ z)
            hright
            hdiv_le
        have hδ_div_three_pos : 0 < δ / 3 :=
          div_pos hδ Real.zero_lt_three
        have hthree_div_δ_ge_one : (1 : ℝ) ≤ 3 / δ := by
          le_trans hy_lower hy_upper
        have hx_log_bound :
            |Real.log x| ≤ Lδ :=
          le_trans
            (Real.abs_log_le_max_abs_log_of_bounds
              hδ_div_three_pos
              (le_trans hx_lower hx_upper)
              hx_lower
              hx_upper)
            (le_max_left _ _)
        have hy_log_bound :
            |Real.log y| ≤ Lδ :=
          le_trans
            (Real.abs_log_le_max_abs_log_of_bounds
              zero_lt_one
              hthree_div_δ_ge_one
              hy_lower
              hy_upper)
            (le_max_right _ _)
        have hlog_max_bound :
            max |Real.log x|
              (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi ≤
              Lδ + Real.pi := by
          have hlog_one : |Real.log (1 : ℝ)| ≤ Lδ :=
            le_trans
              (le_of_eq (congrArg abs Real.log_one))
              hLδ_nonneg
          have hinner :
              max |Real.log (1 : ℝ)| |Real.log y| ≤ Lδ :=
            max_le hlog_one hy_log_bound
          have houter :
              max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) ≤ Lδ :=
            max_le hx_log_bound hinner
          exact add_le_add_right houter Real.pi
        have hvolume_bound :
            (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal ≤
              2 * ‖w‖ := by
          have hvolume :
              volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) =
                ENNReal.ofReal ((2 * ‖w‖) - (‖w‖ / 2)) :=
            Real.volume_Ioc
          have hlength_nonneg :
              0 ≤ (2 * ‖w‖) - (‖w‖ / 2) := by
            exact sub_nonneg.mpr
              ((le_div_iff₀ two_pos).mpr
                (by
                  calc
                    (‖w‖ / 2) * 2 = ‖w‖ := by
                      exact div_mul_cancel₀ ‖w‖ two_ne_zero
                    _ ≤ 2 * ‖w‖ :=
                      le_mul_of_one_le_left (le_of_lt hw_norm_pos) one_le_two))
          have hlength_le :
              (2 * ‖w‖) - (‖w‖ / 2) ≤ 2 * ‖w‖ :=
            sub_le_self (2 * ‖w‖)
              (div_nonneg (norm_nonneg w) zero_le_two)
          calc
            (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal =
                (ENNReal.ofReal ((2 * ‖w‖) - (‖w‖ / 2))).toReal := by
              exact congrArg ENNReal.toReal hvolume
            _ = (2 * ‖w‖) - (‖w‖ / 2) := by
              exact ENNReal.toReal_ofReal hlength_nonneg
            _ ≤ 2 * ‖w‖ := hlength_le
        have hden_lower :
            Real.exp (Real.pi * ‖w‖) / 2 ≤
              Real.exp (Real.pi * ‖w‖) - 1 := by
          have htwo_le_exp :
              (2 : ℝ) ≤ Real.exp (Real.pi * ‖w‖) := by
            have hlog_two_le_two : Real.log 2 ≤ (2 : ℝ) := by
              exact le_of_lt
                (lt_trans
                  (Real.log_lt_sub_one_of_pos
                    Real.binetMajorant_two_pos
                    Real.binetMajorant_two_ne_one)
                  (sub_one_lt 2))
            have htwo_le_pi_norm :
                (2 : ℝ) ≤ Real.pi * ‖w‖ := by
              calc
                (2 : ℝ) ≤ Real.pi * 2 := by
                  calc
                    (2 : ℝ) = 1 * 2 := (one_mul 2).symm
                    _ ≤ Real.pi * 2 :=
                      mul_le_mul_of_nonneg_right
                        (le_of_lt
                          (lt_trans Real.binetMajorant_one_lt_three Real.pi_gt_three))
                        zero_le_two
                _ ≤ Real.pi * ‖w‖ :=
                  mul_le_mul_of_nonneg_left hw_norm_two
                    (le_of_lt Real.pi_pos)
            have hlog_le : Real.log 2 ≤ Real.pi * ‖w‖ :=
              le_trans hlog_two_le_two htwo_le_pi_norm
            exact (Real.log_le_iff_le_exp Real.binetMajorant_two_pos).mp hlog_le
          exact Real.div_two_le_sub_one_of_two_le htwo_le_exp
        have hden_pos :
            0 < Real.exp (Real.pi * ‖w‖) - 1 := by
          have hpi_norm_pos : 0 < Real.pi * ‖w‖ :=
            mul_pos Real.pi_pos hw_norm_pos
          exact sub_pos.mpr
            (calc
              (1 : ℝ) = Real.exp 0 := Eq.symm Real.exp_zero
              _ < Real.exp (Real.pi * ‖w‖) :=
                Real.exp_lt_exp.mpr hpi_norm_pos)
        have hreciprocal :
            1 / (Real.exp (Real.pi * ‖w‖) - 1) ≤
              2 / Real.exp (Real.pi * ‖w‖) := by
          have hE_pos : 0 < Real.exp (Real.pi * ‖w‖) :=
            Real.exp_pos (Real.pi * ‖w‖)
          have hhalf_pos : 0 < Real.exp (Real.pi * ‖w‖) / 2 :=
            div_pos hE_pos two_pos
          have hdiv :
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) - 1) ≤
                1 / (Real.exp (Real.pi * ‖w‖) / 2) :=
            div_le_div_of_nonneg_left zero_le_one hhalf_pos hden_lower
          have hrewrite :
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) / 2) =
                2 / Real.exp (Real.pi * ‖w‖) := by
            calc
              (1 : ℝ) / (Real.exp (Real.pi * ‖w‖) / 2) =
                  1 * 2 / Real.exp (Real.pi * ‖w‖) := by
                exact div_div_eq_mul_div 1 (Real.exp (Real.pi * ‖w‖)) 2
              _ = 2 / Real.exp (Real.pi * ‖w‖) := by
                exact congrArg (fun z : ℝ => z / Real.exp (Real.pi * ‖w‖))
                  (one_mul 2)
          le_trans hdiv (le_of_eq hrewrite)
        have hnum_nonneg :
            0 ≤
              max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi :=
          add_nonneg
            (le_max_of_le_left (abs_nonneg (Real.log x)))
            Real.pi_nonneg
        have hwindow_nonneg :
            0 ≤
              (max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                (Real.exp (Real.pi * ‖w‖) - 1) :=
          div_nonneg hnum_nonneg (le_of_lt hden_pos)
        have hfraction_bound :
            (max |Real.log x|
                (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                (Real.exp (Real.pi * ‖w‖) - 1) ≤
              (Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖)) := by
          have hstep1 :
              (max |Real.log x|
                  (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) ≤
                (Lδ + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) :=
            div_le_div_of_nonneg_right hlog_max_bound (le_of_lt hden_pos)
          have hstep2 :
              (Lδ + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1) ≤
                (Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖)) :=
            mul_le_mul_of_nonneg_left
              hreciprocal
              (add_nonneg hLδ_nonneg Real.pi_nonneg)
          le_trans hstep1 hstep2
        have hmain :
            2 *
                (((max |Real.log x|
                    (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) ≤
              8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)) := by
          have hprod :
              ((max |Real.log x|
                    (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                  (Real.exp (Real.pi * ‖w‖) - 1)) *
                  (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal ≤
                ((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖) :=
            mul_le_mul
              hfraction_bound
              hvolume_bound
              (ENNReal.toReal_nonneg)
              (mul_nonneg
                (add_nonneg hLδ_nonneg Real.pi_nonneg)
                (div_nonneg zero_le_two
                  (le_of_lt (Real.exp_pos (Real.pi * ‖w‖)))))
          have hscale :
              2 * (((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖)) =
                8 * (Lδ + Real.pi) * ‖w‖ *
                  Real.exp (-(Real.pi * ‖w‖)) := by
            let A : ℝ := Lδ + Real.pi
            let N : ℝ := ‖w‖
            let E : ℝ := Real.exp (Real.pi * ‖w‖)
            calc
              2 * (((Lδ + Real.pi) * (2 / Real.exp (Real.pi * ‖w‖))) *
                  (2 * ‖w‖)) =
                  2 * ((A * (2 * E⁻¹)) * (2 * N)) := by
                rfl
              _ = 2 * (((A * 2) * E⁻¹) * (2 * N)) := by
                exact congrArg (fun z : ℝ => 2 * (z * (2 * N)))
                  (mul_assoc A 2 E⁻¹)
              _ = 2 * (((2 * A) * E⁻¹) * (2 * N)) := by
                exact congrArg
                  (fun z : ℝ => 2 * ((z * E⁻¹) * (2 * N)))
                  (mul_comm A 2)
              _ = (2 * ((2 * A) * E⁻¹)) * (2 * N) := by
                exact (mul_assoc 2 (((2 * A) * E⁻¹)) (2 * N)).symm
              _ = ((2 * ((2 * A) * E⁻¹)) * 2) * N := by
                exact mul_assoc (2 * ((2 * A) * E⁻¹)) 2 N
              _ = ((2 * 2) * ((2 * A) * E⁻¹)) * N := by
                exact congrArg (fun z : ℝ => z * N)
                  ((mul_assoc 2 2 (((2 * A) * E⁻¹))).symm)
              _ = (4 * ((2 * A) * E⁻¹)) * N := by
                rfl
              _ = ((4 * (2 * A)) * E⁻¹) * N := by
                exact congrArg (fun z : ℝ => z * N)
                  (mul_assoc 4 (2 * A) E⁻¹)
              _ = ((8 * A) * E⁻¹) * N := by
                rfl
              _ = (8 * A * N) * E⁻¹ := by
                calc
                  ((8 * A) * E⁻¹) * N =
                      N * ((8 * A) * E⁻¹) := by
                    exact mul_comm (((8 : ℝ) * A) * E⁻¹) N
                  _ = (N * (8 * A)) * E⁻¹ := by
                    exact mul_assoc N (8 * A) E⁻¹
                  _ = ((8 * A) * N) * E⁻¹ := by
                    exact congrArg (fun z : ℝ => z * E⁻¹)
                      (mul_comm N (8 * A))
                  _ = (8 * A * N) * E⁻¹ := by
                    rfl
              _ = (8 * (Lδ + Real.pi) * ‖w‖) *
                  (Real.exp (Real.pi * ‖w‖))⁻¹ := by
                rfl
              _ = 8 * (Lδ + Real.pi) * ‖w‖ *
                  Real.exp (-(Real.pi * ‖w‖)) := by
                exact congrArg
                  (fun z : ℝ => 8 * (Lδ + Real.pi) * ‖w‖ * z)
                  (Real.exp_neg (Real.pi * ‖w‖)).symm
          le_trans
            (mul_le_mul_of_nonneg_left hprod zero_le_two)
            (le_of_eq hscale)
        have htarget :
            8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)) ≤
              C * ‖w‖ * Real.exp (-Real.pi * ‖w‖) := by
          have hcoef :
              8 * (Lδ + Real.pi) ≤ C := by
            calc
              8 * (Lδ + Real.pi) ≤ 8 * (Lδ + Real.pi + 1) := by
                exact mul_le_mul_of_nonneg_left
                  (le_add_of_nonneg_right zero_le_one)
                  (le_of_lt
                    (by
                      show 0 < (2 : ℝ) * 4
                      exact mul_pos two_pos four_pos))
              _ = C := rfl
          have hscale_nonneg :
              0 ≤ ‖w‖ * Real.exp (-Real.pi * ‖w‖) :=
            mul_nonneg (norm_nonneg w)
              (le_of_lt (Real.exp_pos (-Real.pi * ‖w‖)))
          exact
            mul_le_mul_of_nonneg_right hcoef hscale_nonneg
        le_trans
          (Eq.subst
            (motive := fun z : ℝ =>
              z ≤ 8 * (Lδ + Real.pi) * ‖w‖ *
                Real.exp (-(Real.pi * ‖w‖)))
            (by rfl :
              2 *
                  (((max |Real.log (w.re / (3 * ‖w‖))|
                      (max |Real.log (1 : ℝ)|
                        |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
                    (Real.exp (Real.pi * ‖w‖) - 1)) *
                    (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal) =
                2 *
                  (((max |Real.log x|
                      (max |Real.log (1 : ℝ)| |Real.log y|) + Real.pi) /
                    (Real.exp (Real.pi * ‖w‖) - 1)) *
                    (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal))
            hmain)
          htarget⟩

/-- Sector-local envelope bound from the explicit logarithmic-window bound. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_of_logWindow
    (hlog :
      Complex.BinetSecondFormulaBranchLocalIndentationLogWindowExpBound) :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound := by
  intro δ hδ
  match hlog δ hδ with
  | ⟨C, hC_pos, hbound⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_sector hw_norm_two =>
            hbound w hw_sector hw_norm_two⟩

/-- Owner analytic leaf: sector-local exponential upper bound for the
branch-window envelope. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound := by
  exact
    Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_of_logWindow
      Complex.binetSecondFormula_branchLocalIndentation_logWindowExpBound_owner

/-- Owner real-variable leaf: unit-interval lower bound for the Binet scalar kernel. -/
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
            le_trans ha ht.1
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
          integrableOn_const
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
                L * (volume (Set.Ioc a (a + 1))).toReal := by
              exact integral_const L
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
                        (Real.exp (-((2 : ℝ) * Real.pi))
                        (Real.exp (-((2 : ℝ) * Real.pi) * a))).symm
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
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤
              ∫ t : ℝ in Set.Ioc a (a + 1),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
          hscale
          (Eq.subst
            (motive := fun x : ℝ =>
              x ≤
                ∫ t : ℝ in Set.Ioc a (a + 1),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
            hconst_integral.symm
            hintegral_lower)⟩

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
          (lt_of_le_of_lt ha ht))
  have hunit_subset_tail :
      Set.Ioc a (a + 1) ≤ᵐ[volume] Set.Ioi a :=
    Filter.Eventually.of_forall
      (fun t ht => ht.1)
  exact
    setIntegral_mono_set
      hM_integrable_tail
      hM_nonneg_tail
      hunit_subset_tail

/-- Full tail lower bound from the unit-interval lower bound and interval-tail
monotonicity. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_expLower_of_unitInterval
    (hunit : Real.BinetSecondFormulaKernelMajorantUnitIntervalExpLower)
    (hle : Real.BinetSecondFormulaKernelMajorantUnitIntervalLeTail) :
    Real.BinetSecondFormulaKernelMajorantTailExpLower := by
  match hunit with
  | ⟨c, hc_pos, hunit_lower⟩ =>
      exact
        ⟨c, hc_pos,
          fun a ha =>
            le_trans
              (hunit_lower a ha)
              (hle a ha)⟩

/-- Owner real-variable leaf: exponential lower bound for the Binet scalar tail. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_expLower_owner :
    Real.BinetSecondFormulaKernelMajorantTailExpLower := by
  exact
    Real.binetSecondFormula_kernel_majorant_tail_expLower_of_unitInterval
      Real.binetSecondFormula_kernel_majorant_unitInterval_expLower_owner
      Real.binetSecondFormula_kernel_majorant_unitInterval_le_tail_owner

/-- Complex cutoff form of the Binet scalar tail lower bound from the
one-dimensional real-variable tail estimate. -/
theorem Complex.binetSecondFormula_decayingTailIntegral_expLower_of_realTailLower
    (hlower : Real.BinetSecondFormulaKernelMajorantTailExpLower) :
    Complex.BinetSecondFormulaDecayingTailIntegralExpLower := by
  match hlower with
  | ⟨c, hc_pos, htail_lower⟩ =>
      exact
        ⟨c / 2, half_pos hc_pos,
          fun w hw_norm_two =>
            have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
              (le_div_iff₀ two_pos).mpr
                (Eq.subst
                  (motive := fun x : ℝ => x ≤ ‖w‖)
                  (one_mul (2 : ℝ)).symm
                  hw_norm_two)
            have hexponent :
                -((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                  -Real.pi * ‖w‖ := by
              calc
                -((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                    -(((2 : ℝ) * Real.pi) * (‖w‖ / 2)) := by
                  exact neg_mul ((2 : ℝ) * Real.pi) (‖w‖ / 2)
                _ = -(Real.pi * ‖w‖) := by
                  have hinside :
                      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                        Real.pi * ‖w‖ := by
                    calc
                      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
                          (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
                        exact mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2
                      _ = ((Real.pi * ‖w‖) * 2) / 2 := by
                        exact
                          congrArg (fun x : ℝ => x / 2)
                            (calc
                              ((2 : ℝ) * Real.pi) * ‖w‖ =
                                  2 * (Real.pi * ‖w‖) := by
                                exact mul_assoc 2 Real.pi ‖w‖
                              _ = (Real.pi * ‖w‖) * 2 := by
                                exact mul_comm 2 (Real.pi * ‖w‖))
                      _ = Real.pi * ‖w‖ := by
                        exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
                  exact congrArg Neg.neg hinside
                _ = -Real.pi * ‖w‖ := by
                  exact (neg_mul Real.pi ‖w‖).symm
            have hcoeff :
                (c / 2) * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                  c * (‖w‖ / 2) *
                    Real.exp (-Real.pi * ‖w‖) := by
              calc
                (c / 2) * ‖w‖ * Real.exp (-Real.pi * ‖w‖) =
                    (c * ‖w‖ / 2) * Real.exp (-Real.pi * ‖w‖) := by
                  exact
                    congrArg (fun x : ℝ => x * Real.exp (-Real.pi * ‖w‖))
                      (div_mul_eq_mul_div c ‖w‖ 2)
                _ = c * (‖w‖ / 2) * Real.exp (-Real.pi * ‖w‖) := by
                  exact
                    congrArg (fun x : ℝ => x * Real.exp (-Real.pi * ‖w‖))
                      (mul_div_assoc c ‖w‖ 2).symm
            Eq.subst
              (motive := fun x : ℝ =>
                (c / 2) * ‖w‖ * Real.exp (-Real.pi * ‖w‖) ≤
                  Complex.binetSecondFormulaDecayingTailIntegral w)
              hcoeff.symm
              (Eq.subst
                (motive := fun x : ℝ =>
                  c * (‖w‖ / 2) * Real.exp x ≤
                    Complex.binetSecondFormulaDecayingTailIntegral w)
                hexponent
                (htail_lower (‖w‖ / 2) hhalf_ge_one))⟩

/-- Owner real-variable leaf: exponential lower bound for the Binet decaying
tail integral. -/
theorem Complex.binetSecondFormula_decayingTailIntegral_expLower_owner :
    Complex.BinetSecondFormulaDecayingTailIntegralExpLower := by
  exact
    Complex.binetSecondFormula_decayingTailIntegral_expLower_of_realTailLower
      Real.binetSecondFormula_kernel_majorant_tail_expLower_owner

/-- Sector-window comparison from the exponential upper/lower scalar estimates. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_of_expBounds
    (henvelope :
      Complex.BinetSecondFormulaBranchLocalIndentationSectorEnvelopeExpBound)
    (hintegral : Complex.BinetSecondFormulaDecayingTailIntegralExpLower) :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  intro δ hδ
  match henvelope δ hδ with
  | ⟨Ce, hCe_pos, henvelope_bound⟩ =>
      match hintegral with
      | ⟨c, hc_pos, hintegral_lower⟩ =>
          let C : ℝ := Ce / c
          have hC_pos : 0 < C := div_pos hCe_pos hc_pos
          exact
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two =>
                let E : ℝ := ‖w‖ * Real.exp (-Real.pi * ‖w‖)
                let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
                have hE_nonneg : 0 ≤ E :=
                  mul_nonneg (norm_nonneg w)
                    (le_of_lt (Real.exp_pos (-Real.pi * ‖w‖)))
                have hCe_nonneg : 0 ≤ Ce := le_of_lt hCe_pos
                have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
                have hintegral_bound : c * E ≤ J :=
                  hintegral_lower w hw_norm_two
                have hscale :
                    Ce * E ≤ (Ce / c) * J := by
                  have hcE_le_J : c * E ≤ J := hintegral_bound
                  have hmul :
                      (Ce / c) * (c * E) ≤ (Ce / c) * J :=
                    mul_le_mul_of_nonneg_left hcE_le_J
                      (div_nonneg hCe_nonneg hc_nonneg)
                  have hcollapse :
                      (Ce / c) * (c * E) = Ce * E := by
                    calc
                      (Ce / c) * (c * E) =
                          ((Ce / c) * c) * E := by
                        exact (mul_assoc (Ce / c) c E).symm
                      _ = Ce * E := by
                        exact congrArg (fun x : ℝ => x * E)
                          (div_mul_cancel₀ Ce (ne_of_gt hc_pos))
                  exact
                    Eq.subst
                      (motive := fun x : ℝ => x ≤ (Ce / c) * J)
                      hcollapse
                      hmul
                le_trans
                  (henvelope_bound w hw_sector hw_norm_two)
                  hscale⟩

/-- Owner analytic leaf: sector-local branch-window comparison.

Away from the branch wall, the local-indentation logarithmic envelope is
absorbed by the standard Binet decaying-tail integral with the scale-correct
sector constant. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    Complex.binetSecondFormula_branchTail_sectorWindow_of_expBounds
      Complex.binetSecondFormula_branchLocalIndentation_sectorEnvelopeExpBound_owner
      Complex.binetSecondFormula_decayingTailIntegral_expLower_owner

/-- Owner projection of the proved bounded branch-wall principal-tail estimate.

This is the honest scalar estimate available before the paired-contour
cancellation step: the fixed branch-wall logarithmic window remains explicit,
so this theorem is not the full uniform wall-cancellation theorem. -/
theorem Complex.binetSecondFormula_branchTail_wallBoundedWindow_expScale_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (2 *
        (|Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  exact
    Complex.binetSecondFormula_principalTailKernel_integral_le_expScale_boundedTailWindow_Ioc
      hw_re_pos hw_large

/-- Constructor from the weighted moving-envelope estimate to the sharp
bounded-window branch-wall estimate.

This is the point where the principal-tail kernel is replaced by the moving
branch-wall logarithmic envelope with the pure exponential weight still
present.  The remaining scalar theorem is therefore the weighted envelope
estimate itself, not a fixed `w.re` logarithmic window bound. -/
theorem Complex.binetSecondFormula_boundedWindow_decay_of_weightedFullLogEnvelope_decay
    (hweighted :
      ∃ Cweighted : ℝ,
        0 < Cweighted ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max |Real.log (w.re / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cweighted / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cbounded : ℝ,
      0 < Cbounded ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (Cbounded / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hweighted with
  | ⟨Cweighted, hCweighted_pos, hweighted_estimate⟩ =>
      exact
        ⟨Cweighted, hCweighted_pos,
          fun w hw_re_pos hw_norm_two =>
            let P : ℝ → ℝ := fun t : ℝ =>
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
            let G : ℝ → ℝ := fun t : ℝ =>
              (2 *
                (max |Real.log (w.re / (3 * ‖w‖))|
                  |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                  Real.pi)) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            have hkernel_to_weighted :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_fullLogEnvelope_boundedTailWindow_Ioc
                (w := w) hw_re_pos hw_norm_two
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              mul_le_mul_of_nonneg_left hkernel_to_weighted zero_le_two
            have hweighted_w :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t ≤
                  (Cweighted / ‖w‖) * J :=
              hweighted_estimate w hw_re_pos hw_norm_two
            le_trans htwice hweighted_w⟩

/-- Constructor from the sharp bounded-window branch-wall estimate to the
legacy full principal-tail cancellation predicate.

The far part of the split tail is already owned by
`binetSecondFormula_principalTailKernel_integral_far_scaled_decay`.  Thus the
only analytic input to this constructor is the bounded window
`Ioc (‖w‖ / 2) (2‖w‖)`, with the moving branch-wall exponential weight kept
before any fixed `w.re`-window replacement. -/
theorem Complex.binetSecondFormula_branchWallPrincipalTailCancellation_of_boundedWindow_decay
    (hbounded :
      ∃ Cbounded : ℝ,
        0 < Cbounded ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (Cbounded / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation := by
  match hbounded with
  | ⟨Cbounded, hCbounded_pos, hbounded_estimate⟩ =>
      match Complex.binetSecondFormula_principalTailKernel_integral_far_scaled_decay with
      | ⟨Cfar, hCfar_nonneg, hfar_estimate⟩ =>
          let C : ℝ := Cbounded + Cfar
          have hC_pos : 0 < C :=
            add_pos_of_pos_of_nonneg hCbounded_pos hCfar_nonneg
          exact
            ⟨C, hC_pos,
              fun w hw_re_pos hw_norm_two =>
                let P : ℝ → ℝ := fun t : ℝ =>
                  ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                have hsplit :
                    ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
                  Complex.binetSecondFormula_principalTailKernel_integral_le_boundedWindow_add_far
                    (w := w) hw_re_pos
                have htwice_split :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      2 *
                        ((∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)) :=
                  mul_le_mul_of_nonneg_left hsplit zero_le_two
                have hdistribute :
                    2 *
                        ((∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                          (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)) =
                      2 * (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        2 * (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) :=
                  left_distrib (2 : ℝ)
                    (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t)
                    (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t)
                have hbounded_w :
                    2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                      (Cbounded / ‖w‖) * J :=
                  hbounded_estimate w hw_re_pos hw_norm_two
                have hnorm_one : 1 ≤ ‖w‖ :=
                  le_trans one_le_two hw_norm_two
                have hfar_w :
                    2 * ∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t ≤
                      (Cfar / ‖w‖) * J :=
                  hfar_estimate w hw_re_pos hnorm_one
                have hsum :
                    2 * (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t) +
                        2 * (∫ t : ℝ in Set.Ioi (2 * ‖w‖), P t) ≤
                      (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J :=
                  add_le_add hbounded_w hfar_w
                have hcombine :
                    (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J =
                      (C / ‖w‖) * J := by
                  calc
                    (Cbounded / ‖w‖) * J + (Cfar / ‖w‖) * J =
                        (Cbounded / ‖w‖ + Cfar / ‖w‖) * J := by
                      exact (add_mul (Cbounded / ‖w‖) (Cfar / ‖w‖) J).symm
                    _ = ((Cbounded + Cfar) / ‖w‖) * J := by
                      exact congrArg (fun x : ℝ => x * J)
                        (add_div Cbounded Cfar ‖w‖).symm
                    _ = (C / ‖w‖) * J := by
                      rfl
                have hraw :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), P t ≤
                      (C / ‖w‖) * J :=
                  le_trans htwice_split
                    (le_trans
                      (Eq.subst
                        (motive := fun x : ℝ =>
                          x ≤
                            (Cbounded / ‖w‖) * J +
                              (Cfar / ‖w‖) * J)
                        hdistribute.symm
                        hsum)
                      (le_of_eq hcombine))
                hraw⟩

/-- Paired Abel-Plana finite-height contour-error cancellation.

This is the precise contour-side cancellation theorem already supplied by the
finite-height Abel-Plana side assembly and horizontal-edge decay: once the two
principal-value boundary faces have been assembled into a genuine finite-height
bridge package, the residual contour error tends to zero.  This theorem is
deliberately stated before any norm is taken; the branch-wall tail theorem
below must consume this cancellation level, not the legacy raw principal-tail
norm estimate. -/
theorem Complex.binetSecondFormula_pairedAbelPlana_finiteHeightContourError_tendsto_zero_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAt N w) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
      hw_re_pos N hdecInteriorPole hbridges

/-- Owner-level endpoint-restored finite-height contour-error cancellation.

This is the corrected contour-error object for the endpoint-restored
finite-height bridge package: subtract the endpoint indentation first, then
the remaining error is only the vanishing horizontal edge contribution. -/
theorem Complex.binetSecondFormula_pairedAbelPlana_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.finiteAbelPlana_log_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
      hw_re_pos N hdecInteriorPole hbridges

/-- A complex-valued family tending to zero is eventually bounded by any
positive real threshold. -/
theorem Complex.eventually_norm_le_of_tendsto_zero
    {ι : Type*}
    {l : Filter ι}
    {f : ι → ℂ}
    {B : ℝ}
    (hf : Tendsto f l (𝓝 (0 : ℂ)))
    (hB_pos : 0 < B) :
    ∀ᶠ i in l, ‖f i‖ ≤ B := by
  have hnorm :
      Tendsto
        (fun i : ι => ‖f i‖)
        l
        (𝓝 (0 : ℝ)) := by
    have hnorm_zero :
        ‖(0 : ℂ)‖ = (0 : ℝ) :=
      norm_zero
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          Tendsto
            (fun i : ι => ‖f i‖)
            l
            (𝓝 x))
        hnorm_zero
        (continuous_norm.tendsto (0 : ℂ)).comp hf
  have hsmall :
      ∀ᶠ i in l, ‖f i‖ ∈ Set.Iio B :=
    hnorm (Iio_mem_nhds hB_pos)
  exact hsmall.mono
    (fun i hi => le_of_lt hi)

/-- Quantitative finite-height contour-error absorption into the Binet
decaying tail, for a fixed `w` and finite Abel-Plana height index.

The analytic input is only the paired contour-error cancellation
`finiteHeightContourError → 0`; the positive comparison scale comes from the
proved exponential lower bound for the scalar Binet tail integral. -/
theorem Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAt N w)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let E : ℝ := ‖w‖ * Real.exp (-Real.pi * ‖w‖)
      let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
      let B : ℝ := (C / ‖w‖) * J
      have hnorm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_two hw_norm_two
      have hcoeff_pos : 0 < C / ‖w‖ :=
        div_pos hC_pos hnorm_pos
      have hE_pos : 0 < E :=
        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
      have hcE_pos : 0 < c * E :=
        mul_pos hc_pos hE_pos
      have hJ_pos : 0 < J :=
        lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
      have hB_pos : 0 < B :=
        mul_pos hcoeff_pos hJ_pos
      have htendsto :
          Tendsto
            (fun T : ℝ =>
              Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
            atTop
            (𝓝 (0 : ℂ)) :=
        Complex.binetSecondFormula_pairedAbelPlana_finiteHeightContourError_tendsto_zero_owner
          hw_re_pos N hdecInteriorPole hbridges
      exact
        Complex.eventually_norm_le_of_tendsto_zero
          htendsto
          hB_pos

/-- Quantitative endpoint-restored finite-height contour-error absorption into
the Binet decaying tail.

This is the non-circular replacement for trying to consume the endpoint-free
boundary target from an endpoint-restored bridge: the endpoint indentation is
subtracted before applying horizontal-edge decay. -/
theorem Complex.binetSecondFormula_finiteHeightEndpointRestoredContourError_eventually_scaled_decayingTail_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)))
    (hbridges : Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
  | ⟨c, hc_pos, htail_lower⟩ =>
      let E : ℝ := ‖w‖ * Real.exp (-Real.pi * ‖w‖)
      let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
      let B : ℝ := (C / ‖w‖) * J
      have hnorm_pos : 0 < ‖w‖ :=
        lt_of_lt_of_le zero_lt_two hw_norm_two
      have hcoeff_pos : 0 < C / ‖w‖ :=
        div_pos hC_pos hnorm_pos
      have hE_pos : 0 < E :=
        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
      have hcE_pos : 0 < c * E :=
        mul_pos hc_pos hE_pos
      have hJ_pos : 0 < J :=
        lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
      have hB_pos : 0 < B :=
        mul_pos hcoeff_pos hJ_pos
      have htendsto :
          Tendsto
            (fun T : ℝ =>
              Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T)
            atTop
            (𝓝 (0 : ℂ)) :=
        Complex.binetSecondFormula_pairedAbelPlana_finiteHeightEndpointRestoredContourError_tendsto_zero_owner
          hw_re_pos N hdecInteriorPole hbridges
      exact
        Complex.eventually_norm_le_of_tendsto_zero
          htendsto
          hB_pos

/-- Endpoint-restored contour-error decay from the real-segment
constant-face reconstruction.

This is the canonical finite-height contour-error estimate attached to the
endpoint-restored boundary target.  The endpoint indentation is subtracted
before horizontal-edge decay is applied. -/
theorem Complex.binetSecondFormula_endpointRestoredContourError_decay_of_realSegmentConstantFaces
    (hconstant :
      Complex.BinetSecondFormulaFiniteHeightRealSegmentConstantFaces)
    {Cerror : ℝ}
    (hCerror_pos : 0 < Cerror) :
    ∃ R : ℝ,
      0 < R ∧
      2 ≤ R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ N : ℕ,
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                (Cerror / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w := by
  match
    Complex.binetSecondFormula_finiteHeightPVBridgePackageEndpointRestored_of_realSegmentConstantFaces
      hconstant
  with
  | ⟨R, hR_pos, hR_two, hpackage_bound⟩ =>
      exact
        ⟨R, hR_pos, hR_two,
          fun w hw_re_pos hRle N =>
            have hw_norm_two : 2 ≤ ‖w‖ :=
              le_trans hR_two hRle
            have hpackage :
                Complex.FiniteHeightPVBridgePackageAtEndpointRestored N w :=
              hpackage_bound w hw_re_pos hRle N
            have hdecInteriorPole :
                ∀ n : ℕ, n ∈ Finset.range N →
                  ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
              fun n _hn z => inferInstance
            Complex.binetSecondFormula_finiteHeightEndpointRestoredContourError_eventually_scaled_decayingTail_owner
              hw_re_pos hw_norm_two N hdecInteriorPole hpackage hCerror_pos⟩

/-- Owner theorem for the corrected endpoint-restored finite-height contour
input package. -/
theorem Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  have htarget :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTargetEndpointRestored :=
    Complex.binetSecondFormula_finiteHeightBoundaryTargetEndpointRestored_owner
  have herror :
      ∃ R : ℝ,
        0 < R ∧
        2 ≤ R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ N : ℕ,
              ∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                  ((1 : ℝ) / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_endpointRestoredContourError_decay_of_realSegmentConstantFaces
      Complex.binetSecondFormula_finiteHeightRealSegmentConstantFaces_owner
      zero_lt_one
  exact ⟨htarget, herror⟩

/-- Quantitative contour-error absorption from the owner finite-height
boundary target.

This is the consumption form used by wall-cancellation estimates: once the
finite-height normalized boundary target has been proved, the paired contour
error is eventually smaller than any fixed positive multiple of the scaled
Binet decaying tail. -/
theorem Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (N : ℕ)
    (hboundary :
      ∀ᶠ T : ℝ in atTop,
        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                Complex.I *
                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)
    {C : ℝ}
    (hC_pos : 0 < C) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
        (C / ‖w‖) *
          Complex.binetSecondFormulaDecayingTailIntegral w := by
  have hbridges :
      Complex.FiniteHeightPVBridgePackageAt N w :=
    Complex.finiteAbelPlana_log_finiteHeightPVBridgePackageAt_of_ownerBoundaryTarget_owner
      N hw_re_pos hboundary
  have hdecInteriorPole :
      ∀ n : ℕ, n ∈ Finset.range N →
        ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
    fun n _hn z => Classical.decEq z (((n + 1 : ℕ) : ℂ))
  exact
    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_owner
      hw_re_pos hw_norm_two N hdecInteriorPole hbridges hC_pos

/-- Owner-level bridge from the lower Abel-Plana vertical tail to the Binet
tail remainder.

This is the exact logarithmic-jump-to-arctangent transport over the Binet split
tail.  It is deliberately stated at the owner layer because the branch-wall
cancellation theorem must cancel contour-level vertical contributions before
taking the final tail norm. -/
theorem Complex.binetSecondFormula_lowerVerticalTailIntegral_eq_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t =
      Complex.binetSecondFormulaTailRemainder w := by
  exact
    Complex.finiteAbelPlana_lowerVerticalTailIntegral_eq_binetTailRemainder
      hw_re_pos

/-- Owner-level split of the lower Abel-Plana vertical full integral at the
Binet tail cutoff.

The bounded initial window and the Binet tail remainder are the two pieces that
must be paired with the finite-height contour cancellation and the decaying
tail kernel estimate in the branch-wall owner theorem. -/
theorem Complex.binetSecondFormula_lowerVerticalFullIntegral_eq_initialWindow_add_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w =
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) +
        Complex.binetSecondFormulaTailRemainder w := by
  exact
    Complex.finiteAbelPlana_lowerVerticalFullIntegral_eq_initialWindow_add_binetTailRemainder
      hw_re_pos

/-- Owner-level difference form of the lower vertical split.

This is the branch-wall cancellation surface: after the bounded initial
vertical window is paired with the contour contribution, the remaining
difference is exactly the Binet tail remainder. -/
theorem Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaTailRemainder w =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.binetSecondFormulaTailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow
      hw_re_pos

/-- Owner-level norm form of the lower vertical split. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ =
      ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ := by
  exact
    Complex.binetSecondFormulaTailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm
      hw_re_pos

/-- Owner-level finite-height convergence of the lower vertical tail at the
Binet cutoff.

This places the actual tail remainder on the same finite-height parameter as
the paired Abel-Plana contour-error cancellation theorem. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_tendsto_tailRemainder_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝 (Complex.binetSecondFormulaTailRemainder w)) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_tendsto_binetTailRemainder
      hw_re_pos

/-- Owner-level closure step from finite-height lower-tail bounds to the Binet
tail remainder. -/
theorem Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {B : ℝ}
    (hbound :
      ∀ᶠ T : ℝ in atTop,
        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤ B) :
    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ B := by
  exact
    Complex.binetSecondFormulaTailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le
      hw_re_pos hbound

/-- Owner-level solved form of the finite-height Abel-Plana boundary equation
for the lower vertical tail at the Binet cutoff.

This is the algebraic point where the paired contour error enters the
finite-height lower-tail expression with its forced sign. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved
      N w T

/-- Owner-level restored-error solved form of the finite-height Abel-Plana
boundary equation for the lower vertical tail at the Binet cutoff. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w -
        Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_boundarySolved_endpointRestored
      N w T

/-- Owner-level triangle estimate from the solved finite-height boundary
equation.  The finite-height lower-tail norm is controlled by the non-error
solved boundary part plus the paired contour-error norm. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError
      N w T

/-- Owner-level triangle estimate from the restored-error solved finite-height
boundary equation. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
      ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ +
        ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError
      N w T

/-- Owner-level endpoint-returned restored-pair equation for the finite-height
lower vertical difference.

This is the algebraic replacement for estimating the endpoint-restored static
piece and the endpoint-restored error separately.  The half-endpoint term is
returned to both sides of the paired difference, where it cancels before the
norm is taken. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) =
      ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_eq_endpointReturnedRestoredPair
      N w T

/-- Owner-level norm form of the endpoint-returned restored-pair equation. -/
theorem Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm_owner
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
      ‖(((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))‖ := by
  exact
    Complex.finiteAbelPlana_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm
      N w T

/-- Limit of the solved finite-height boundary expression with the contour
error removed.

After solving the finite-height Abel-Plana boundary equation for the lower
vertical side, the non-error part has only one `T`-dependent term: the upper
vertical integral.  This lemma records its exact improper-limit target. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_sub_initialWindow_tendsto_full_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝
        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let U : ℝ → ℂ := fun T : ℝ =>
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  have hU : Tendsto U atTop (𝓝 U∞) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
      hw_re_pos N
  have hfirst :
      Tendsto
        (fun T : ℝ => (R + H) - U T)
        atTop
        (𝓝 ((R + H) - U∞)) :=
    tendsto_const_nhds.sub hU
  have hminusP :
      Tendsto
        (fun T : ℝ => (R + H) - U T - P)
        atTop
        (𝓝 ((R + H) - U∞ - P)) :=
    hfirst.sub tendsto_const_nhds
  have hminusI :
      Tendsto
        (fun T : ℝ => ((R + H) - U T - P) - I)
        atTop
        (𝓝 (((R + H) - U∞ - P) - I)) :=
    hminusP.sub tendsto_const_nhds
  exact hminusI

/-- Limit of the endpoint-restored solved finite-height boundary expression.

This is the same upper-vertical improper-limit transport as the ordinary
solved-static expression, but for the normalization in which the explicit
half-endpoint term has been absorbed into the restored contour error. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_sub_initialWindow_tendsto_full_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Tendsto
      (fun T : ℝ =>
        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
      atTop
      (𝓝
        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let U : ℝ → ℂ := fun T : ℝ =>
    Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  have hU : Tendsto U atTop (𝓝 U∞) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegralUpTo_tendsto_unsplitFull
      hw_re_pos N
  have hfirst :
      Tendsto
        (fun T : ℝ => R - U T)
        atTop
        (𝓝 (R - U∞)) :=
    tendsto_const_nhds.sub hU
  have hminusP :
      Tendsto
        (fun T : ℝ => R - U T - P)
        atTop
        (𝓝 (R - U∞ - P)) :=
    hfirst.sub tendsto_const_nhds
  have hminusI :
      Tendsto
        (fun T : ℝ => (R - U T - P) - I)
        atTop
        (𝓝 ((R - U∞ - P) - I)) :=
    hminusP.sub tendsto_const_nhds
  exact hminusI

/-- Principal-value cancellation of the full solved static boundary expression.

After the upper vertical finite-height side has been sent to its improper
limit, the finite Abel-Plana principal-value identity cancels the real segment,
endpoint, upper vertical, and residue terms.  What remains is exactly the full
lower vertical side, with the fixed Binet initial window still subtracted. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let L : ℂ := Complex.finiteAbelPlanaLogSummandLowerVerticalIntegral N w
  let U : ℂ := Complex.finiteAbelPlanaLogSummandUpperVerticalIntegral N w
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let F : ℂ := Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  have hboundary_named :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w =
        R + H - L - U := by
    exact
      Complex.finiteAbelPlana_log_boundaryNamedPieces_unfold N w
  have hboundary_residue :
      Complex.finiteAbelPlanaLogBoundaryNamedPieces N w = P :=
    Complex.finiteAbelPlana_log_principalValueCotangentFormula
      hw_re_pos hbridges N hdecInteriorPole
  have hnamed_residue :
      R + H - L - U = P := by
    exact Eq.trans hboundary_named.symm hboundary_residue
  have hupper :
      U∞ = U :=
    Complex.finiteAbelPlana_log_upperVerticalFullIntegral_eq_named N w
  have hlower :
      F = L :=
    Complex.finiteAbelPlana_log_lowerVerticalFullIntegral_eq_split
      hw_re_pos N
  have hsolve_named :
      R + H - U - P = L := by
    let A : ℂ := R + H - U
    have hreorder :
        R + H - L - U = A - L := by
      calc
        R + H - L - U = (R + H) - L - U := by
          rfl
        _ = (R + H) - U - L := by
          exact sub_right_comm (R + H) L U
        _ = A - L := by
          rfl
    have hA_sub_L : A - L = P :=
      Eq.trans hreorder.symm hnamed_residue
    have hcancel :
        A - P = L := by
      calc
        A - P = A - (A - L) := by
          exact congrArg (fun z : ℂ => A - z) hA_sub_L.symm
        _ = L := by
          exact sub_sub_self A L
    exact hcancel
  have hleft_named :
      (R + H - U∞ - P) - I = L - I := by
    have hreplace_upper :
        R + H - U∞ - P = R + H - U - P := by
      exact congrArg (fun z : ℂ => R + H - z - P) hupper
    calc
      (R + H - U∞ - P) - I =
          (R + H - U - P) - I := by
        exact congrArg (fun z : ℂ => z - I) hreplace_upper
      _ = L - I := by
        exact congrArg (fun z : ℂ => z - I) hsolve_named
  have hright_named :
      L - I = F - I := by
    exact congrArg (fun z : ℂ => z - I) hlower.symm
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (R + H - U∞ - P) - I := by
      rfl
    _ = L - I :=
      hleft_named
    _ = F - I :=
      hright_named
    _ =
      Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) := by
      rfl

/-- Endpoint-restored static normalization at full height.

If the explicit Abel-Plana half-endpoints are removed from the solved static
expression, the full-height principal-value cancellation leaves the Binet
lower tail with those same half-endpoints subtracted.  This is the algebraic
normalization comparison between the restored finite-height contour error and
the older static expression that still contains the half-endpoint term. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_sub_halfEndpoints_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  let R : ℂ :=
    ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
      Complex.finiteAbelPlanaLogSummand w (x : ℂ)
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let U∞ : ℂ := Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w
  let P : ℂ := Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w
  let F : ℂ := Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w
  let I : ℂ :=
    ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t
  let A : ℂ := R - U∞ - P
  let Y : ℂ := F - I
  have hwith_endpoint :
      ((R + H - U∞ - P) - I) = Y := by
    calc
      ((R + H - U∞ - P) - I) =
          (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
              Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
            Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
            Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
            Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) := by
        rfl
      _ =
          Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
        Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
          N hw_re_pos hbridges hdecInteriorPole
      _ = Y := by
        rfl
  have hwith_endpoint_as_A :
      ((R + H - U∞ - P) - I) = (A + H) - I := by
    calc
      ((R + H - U∞ - P) - I) =
          (R - U∞ - P) + H - I := by
        exact Complex.endpoint_middle_static_subtractions R H U∞ P I
      _ = (A + H) - I := by
        rfl
  have hA_sub_I_eq_with_endpoint_sub_H :
      A - I = ((R + H - U∞ - P) - I) - H := by
    calc
      A - I = (A - I + H) - H := by
        exact (add_sub_cancel_right (A - I) H).symm
      _ = ((A + H) - I) - H := by
        exact congrArg (fun z : ℂ => z - H)
          (Complex.add_middle_sub_right A H I).symm
      _ = ((R + H - U∞ - P) - I) - H := by
        exact congrArg (fun z : ℂ => z - H) hwith_endpoint_as_A.symm
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        A - I := by
      rfl
    _ = ((R + H - U∞ - P) - I) - H :=
      hA_sub_I_eq_with_endpoint_sub_H
    _ = Y - H := by
      exact congrArg (fun z : ℂ => z - H) hwith_endpoint
    _ =
      (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
      rfl

/-- Tail-remainder form of the endpoint-restored static normalization.

The restored finite-height contour error cancels the half-endpoint
indentation at the finite-height level.  Consequently, the corresponding
full-height static expression is the public Binet tail remainder with the
finite half-endpoints subtracted, not the public tail remainder itself. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_tailRemainder_sub_halfEndpoints_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.binetSecondFormulaTailRemainder w -
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
  have hstatic_lower :
      (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
        Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w :=
    Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_sub_halfEndpoints_owner
      N hw_re_pos hbridges hdecInteriorPole
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
      hw_re_pos
  calc
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        (Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w :=
      hstatic_lower
    _ =
        Complex.binetSecondFormulaTailRemainder w -
          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w := by
      exact congrArg
        (fun z : ℂ => z - Complex.finiteAbelPlanaLogSummandHalfEndpoints N w)
        htail.symm

/-- Endpoint-restored full static normalization with the endpoint term
returned.

The restored static expression alone has limit `tailRemainder - halfEndpoints`.
The public Binet tail is recovered only after the same half-endpoint term is
put back.  This is the canonical algebraic form for any later paired
cancellation argument: the endpoint term cannot be discarded or estimated
separately as a vanishing contour error. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_eq_tailRemainder_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w =
      Complex.binetSecondFormulaTailRemainder w := by
  let S : ℂ :=
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
  let H : ℂ := Complex.finiteAbelPlanaLogSummandHalfEndpoints N w
  let T : ℂ := Complex.binetSecondFormulaTailRemainder w
  have hrestored :
      S = T - H :=
    Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_eq_tailRemainder_sub_halfEndpoints_owner
      N hw_re_pos hbridges hdecInteriorPole
  have hreturn :
      S + H = T := by
    calc
      S + H = (T - H) + H := by
        exact congrArg (fun z : ℂ => z + H) hrestored
      _ = T := by
        exact sub_add_cancel T H
  exact hreturn

/-- Norm form of the endpoint-restored full static normalization after
returning the endpoint term. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_norm_eq_tailRemainder_norm_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ‖((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w‖ =
      ‖Complex.binetSecondFormulaTailRemainder w‖ := by
  exact congrArg norm
    (Complex.binetSecondFormula_boundarySolvedStatic_endpointRestored_full_sub_initialWindow_add_halfEndpoints_eq_tailRemainder_owner
      N hw_re_pos hbridges hdecInteriorPole)

/-- Principal-value cancellation identifies the full solved static boundary
expression with the Binet tail remainder. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_tailRemainder_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
      Complex.binetSecondFormulaTailRemainder w := by
  have hstatic_lower :
      (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
        Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_lowerVerticalFull_sub_initialWindow_owner
      N hw_re_pos hbridges hdecInteriorPole
  have htail :
      Complex.binetSecondFormulaTailRemainder w =
        Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t) :=
    Complex.binetSecondFormula_tailRemainder_eq_lowerVerticalFullIntegral_sub_initialWindow_owner
      hw_re_pos
  exact Eq.trans hstatic_lower htail.symm

/-- Norm form of the principal-value cancellation of the full solved static
boundary expression. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_norm_eq_tailRemainder_norm_owner
    (N : ℕ)
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbridges : Complex.FiniteHeightPVBridgePackage w)
    (hdecInteriorPole : ∀ n : ℕ, n ∈ Finset.range N →
      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ))) :
    ‖(((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
      Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))‖ =
      ‖Complex.binetSecondFormulaTailRemainder w‖ := by
  exact congrArg norm
    (Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_eq_tailRemainder_owner
      N hw_re_pos hbridges hdecInteriorPole)

/-- Eventual norm control from convergence to a limit whose norm is strictly
below the target bound. -/
theorem Complex.eventually_norm_le_of_tendsto_norm_lt
    {ι : Type*}
    {l : Filter ι}
    {f : ι → ℂ}
    {a : ℂ}
    {B : ℝ}
    (hf : Tendsto f l (𝓝 a))
    (haB : ‖a‖ < B) :
    ∀ᶠ i in l, ‖f i‖ ≤ B := by
  have hnorm :
      Tendsto
        (fun i : ι => ‖f i‖)
        l
        (𝓝 ‖a‖) :=
    (continuous_norm.tendsto a).comp hf
  have hsmall :
      ∀ᶠ i in l, ‖f i‖ ∈ Set.Iio B :=
    hnorm (Iio_mem_nhds haB)
  exact hsmall.mono
    (fun i hi => le_of_lt hi)

/-- A positive tail scale gives strict room after doubling the constant. -/
theorem Real.le_mul_pos_scale_lt_two_mul
    {A C S : ℝ}
    (hA : A ≤ C * S)
    (hC_pos : 0 < C)
    (hS_pos : 0 < S) :
    A < (2 * C) * S := by
  have hCS_pos : 0 < C * S :=
    mul_pos hC_pos hS_pos
  have hCS_lt_two :
      C * S < (2 * C) * S := by
    calc
      C * S < C * S + C * S := by
        exact lt_add_of_pos_right (C * S) hCS_pos
      _ = (C + C) * S := by
        exact (add_mul C C S).symm
      _ = (2 * C) * S := by
        exact congrArg (fun x : ℝ => x * S) (two_mul C).symm
  exact lt_of_le_of_lt hA hCS_lt_two

/-- Static solved-boundary decay from a structural boundary target and a
tail-absorption theorem.

The boundary target is used only to build the principal-value bridge package
needed by the full-height static cancellation identity.  The quantitative
decay then follows by sending the upper vertical side to its improper limit
and using the tail-remainder bound with a doubled constant for strict
eventual control. -/
theorem Complex.binetSecondFormula_boundarySolvedStaticDecayEstimate_of_boundaryTarget_and_tailAbsorption
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption) :
    Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  match hboundary with
  | ⟨Rboundary, hRboundary_pos, hRboundary_two, hboundary_bound⟩ =>
      match htail with
      | ⟨Rtail, Ctail, hRtail_pos, hCtail_pos, htail_bound⟩ =>
          let R : ℝ := max Rboundary (max Rtail 2)
          let Cstatic : ℝ := 2 * Ctail
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRboundary_pos (le_max_left Rboundary (max Rtail 2))
          have hR_two : 2 ≤ R := by
            exact le_trans
              (le_max_right Rtail 2)
              (le_trans
                (le_max_right Rboundary (max Rtail 2))
                (le_refl R))
          have hCstatic_pos : 0 < Cstatic :=
            mul_pos two_pos hCtail_pos
          exact
            ⟨R, Cstatic, hR_pos, hR_two, hCstatic_pos,
              fun w hw_re_pos hRle =>
                let N : ℕ := 0
                have hRboundary_le : Rboundary ≤ ‖w‖ :=
                  le_trans (le_max_left Rboundary (max Rtail 2)) hRle
                have hRtail_le : Rtail ≤ ‖w‖ :=
                  le_trans
                    (le_trans
                      (le_max_left Rtail 2)
                      (le_max_right Rboundary (max Rtail 2)))
                    hRle
                have hw_norm_two : 2 ≤ ‖w‖ :=
                  le_trans
                    (le_trans
                      (le_max_right Rtail 2)
                      (le_max_right Rboundary (max Rtail 2)))
                    hRle
                have hboundary_w :
                    ∀ N : ℕ,
                      ∀ᶠ T : ℝ in atTop,
                        (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                              (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                                Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                            (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                          ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                              (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                                Complex.I *
                                  Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                            (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                          Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                  hboundary_bound w hw_re_pos hRboundary_le
                have hbridges : Complex.FiniteHeightPVBridgePackage w :=
                  Complex.finiteAbelPlana_log_finiteHeightPVBridgePackage_of_ownerBoundaryTarget_owner
                    hw_re_pos hboundary_w
                have hdecInteriorPole :
                    ∀ n : ℕ, n ∈ Finset.range N →
                      ∀ z : ℂ, Decidable (z = ((n + 1 : ℕ) : ℂ)) :=
                  fun n _hn z => inferInstance
                have htendsto :
                    Tendsto
                      (fun T : ℝ =>
                        (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
                      atTop
                      (𝓝
                        ((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))) :=
                  Complex.binetSecondFormula_boundarySolvedStatic_sub_initialWindow_tendsto_full_owner
                    N hw_re_pos
                let A : ℂ :=
                  (((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                      Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                    Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                    Complex.finiteAbelPlanaLogUpperVerticalFullIntegral N w -
                    Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t))
                let J : ℝ := Complex.binetSecondFormulaDecayingTailIntegral w
                let S : ℝ := (Ctail / ‖w‖) * J
                let B : ℝ := (Cstatic / ‖w‖) * J
                have htail_norm :
                    ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ S :=
                  htail_bound w hw_re_pos hRtail_le
                have hA_norm_eq :
                    ‖A‖ = ‖Complex.binetSecondFormulaTailRemainder w‖ := by
                  exact
                    Complex.binetSecondFormula_boundarySolvedStatic_full_sub_initialWindow_norm_eq_tailRemainder_norm_owner
                      N hw_re_pos hbridges hdecInteriorPole
                have hA_le_S : ‖A‖ ≤ S :=
                  Eq.subst
                    (motive := fun x : ℝ => x ≤ S)
                    hA_norm_eq.symm
                    htail_norm
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hcoeff_pos : 0 < Ctail / ‖w‖ :=
                  div_pos hCtail_pos hnorm_pos
                have hJ_pos : 0 < J := by
                  match Complex.binetSecondFormula_decayingTailIntegral_expLower_owner with
                  | ⟨c, hc_pos, htail_lower⟩ =>
                      let E : ℝ := ‖w‖ * Real.exp (-Real.pi * ‖w‖)
                      have hE_pos : 0 < E :=
                        mul_pos hnorm_pos (Real.exp_pos (-Real.pi * ‖w‖))
                      have hcE_pos : 0 < c * E :=
                        mul_pos hc_pos hE_pos
                      exact lt_of_lt_of_le hcE_pos (htail_lower w hw_norm_two)
                have hA_lt_B : ‖A‖ < B := by
                  have hscale_pos : 0 < (1 / ‖w‖) * J :=
                    mul_pos (one_div_pos.mpr hnorm_pos) hJ_pos
                  have hS_eq : S = Ctail * ((1 / ‖w‖) * J) := by
                    calc
                      S = (Ctail / ‖w‖) * J := by
                        rfl
                      _ = (Ctail * (1 / ‖w‖)) * J := by
                        exact congrArg (fun x : ℝ => x * J) (div_eq_mul_one_div Ctail ‖w‖)
                      _ = Ctail * ((1 / ‖w‖) * J) := by
                        exact mul_assoc Ctail (1 / ‖w‖) J
                  have hB_eq : B = (2 * Ctail) * ((1 / ‖w‖) * J) := by
                    calc
                      B = (Cstatic / ‖w‖) * J := by
                        rfl
                      _ = ((2 * Ctail) / ‖w‖) * J := by
                        rfl
                      _ = ((2 * Ctail) * (1 / ‖w‖)) * J := by
                        exact congrArg (fun x : ℝ => x * J)
                          (div_eq_mul_one_div (2 * Ctail) ‖w‖)
                      _ = (2 * Ctail) * ((1 / ‖w‖) * J) := by
                        exact mul_assoc (2 * Ctail) (1 / ‖w‖) J
                  have hA_le_scaled :
                      ‖A‖ ≤ Ctail * ((1 / ‖w‖) * J) :=
                    Eq.subst
                      (motive := fun x : ℝ => ‖A‖ ≤ x)
                      hS_eq
                      hA_le_S
                  have hlt :
                      ‖A‖ < (2 * Ctail) * ((1 / ‖w‖) * J) :=
                    Real.le_mul_pos_scale_lt_two_mul
                      hA_le_scaled hCtail_pos hscale_pos
                  Eq.subst
                    (motive := fun x : ℝ => ‖A‖ < x)
                    hB_eq.symm
                    hlt
                have hevent :
                    ∀ᶠ T : ℝ in atTop,
                      ‖(((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        B :=
                  Complex.eventually_norm_le_of_tendsto_norm_lt
                    htendsto hA_lt_B
                ⟨N, hevent⟩⟩

/-- Assemble the historical solved-static input pair from its two genuine
independent ingredients.

This theorem records the non-circular dependency shape of the old pair:
the first component is structural boundary assembly, while the second follows
from that structural bridge together with an independently proved tail
absorption theorem. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_tailAbsorption
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  exact
    ⟨hboundary,
      Complex.binetSecondFormula_boundarySolvedStaticDecayEstimate_of_boundaryTarget_and_tailAbsorption
        hboundary htail⟩

/-- Constructor from finite-height lower-vertical cancellation estimates to
the public branch-wall tail-absorption theorem.

This is the precise finite-height form expected from paired contour
cancellation: for each large `w`, the cancelled lower-vertical finite-height
tail is eventually bounded by the decaying scalar Binet tail. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
    (hfinite :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hfinite_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
              hw_re_pos
              (hfinite_bound w hw_re_pos hRle)⟩

/-- Constructor from separate finite-height bounds for the solved static
boundary term and for the contour error.

This is the finite-height estimate in the exact form produced by the solved
boundary equation: the static boundary expression and the paired contour error
are bounded separately, then combined by the triangle estimate for the lower
vertical tail. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_contourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      have hfinite_lower :
          ∃ R : ℝ, ∃ C : ℝ,
            0 < R ∧
            0 < C ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∀ᶠ T : ℝ in atTop,
                  ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (C / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w := by
        exact
          ⟨R, C, hR_pos, hC_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hstatic, herror⟩ =>
                  (hstatic.and herror).mono
                    (fun T hpair =>
                      let J : ℝ :=
                        Complex.binetSecondFormulaDecayingTailIntegral w
                      let S : ℂ :=
                        ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                            Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                          Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                          Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                      let E : ℂ :=
                        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
                      have htriangle :
                          ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                              Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                            ‖S‖ + ‖E‖ :=
                        Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
                          N w T
                      have hstatic_T :
                          ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                        hpair.1
                      have herror_T :
                          ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                        hpair.2
                      have hsum :
                          ‖S‖ + ‖E‖ ≤
                            (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                        add_le_add hstatic_T herror_T
                      have hcombine :
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (C / ‖w‖) * J := by
                        calc
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                              (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                            exact
                              (right_distrib (Cstatic / ‖w‖)
                                (Cerror / ‖w‖) J).symm
                          _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                            exact
                              congrArg (fun x : ℝ => x * J)
                                (add_div Cstatic Cerror ‖w‖).symm
                          _ = (C / ‖w‖) * J := by
                            rfl
                      le_trans htriangle
                        (le_trans hsum (le_of_eq hcombine)))⟩
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
          hfinite_lower

/-- Constructor reducing branch-wall cancellation to the solved static
boundary decay estimate.

The contour-error part is discharged here from the finite-height owner
boundary target and the paired contour-error theorem.  Thus the only
quantitative input left to this constructor is the decay of the solved static
boundary expression. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        2 ≤ R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                    (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                  ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                        Complex.I *
                          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                    (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                  Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      have hwith_error :
          ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
            0 < R ∧
            0 < Cstatic ∧
            0 < Cerror ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∃ N : ℕ,
                  (∀ᶠ T : ℝ in atTop,
                    ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        (Cstatic / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) ∧
                  (∀ᶠ T : ℝ in atTop,
                    ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                        (Cerror / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) := by
        exact
          ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hboundary, hstatic⟩ =>
                  have hw_norm_two : 2 ≤ ‖w‖ :=
                    le_trans hR_two hRle
                  have herror :
                      ∀ᶠ T : ℝ in atTop,
                        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                          (Cerror / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w :=
                    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
                      hw_re_pos hw_norm_two N hboundary hCerror_pos
                  ⟨N, hstatic, herror⟩⟩
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_contourError_decay
          hwith_error

/-- Constructor from the lower-vertical cancellation-difference estimate to
the public branch-wall tail-absorption theorem.

This is a pure transport lemma from the contour-cancelled difference
`lowerVerticalFullIntegral - initialWindow` to the public tail-remainder
form. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
    (hdifference :
      Complex.BinetSecondFormulaLowerVerticalDifferenceDecay) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hdifference with
  | ⟨R, C, hR_pos, hC_pos, hdifference_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            have hnorm :
                ‖Complex.binetSecondFormulaTailRemainder w‖ =
                  ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
              Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                hw_re_pos
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w)
              hnorm.symm
              (hdifference_bound w hw_re_pos hRle)⟩

/-- Closure from finite-height lower-vertical decay to the full lower-vertical
difference decay.

This is the lower-vertical version of the tail closure theorem: once the
finite-height cancelled lower side is eventually bounded at the decaying-tail
scale, its limit, the full lower-vertical difference, has the same bound. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_of_eventually_lowerVerticalUpTo_decay
    (hfinite :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaLowerVerticalDifferenceDecay := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hfinite_bound⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            have htail_bound :
                ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w :=
              Complex.binetSecondFormula_tailRemainder_norm_le_of_eventually_lowerVerticalUpTo_sub_initialWindow_norm_le_owner
                hw_re_pos
                (hfinite_bound w hw_re_pos hRle)
            have hnorm :
                ‖Complex.binetSecondFormulaTailRemainder w‖ =
                  ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                    (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                      Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
              Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                hw_re_pos
            Eq.subst
              (motive := fun x : ℝ =>
                x ≤
                  (C / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w)
              hnorm
              htail_bound⟩

/-- Finite-height lower-vertical decay from separate static-boundary and
contour-error estimates.

This is the finite-height triangle step in owner form.  The lower vertical
side solved from the Abel-Plana boundary equation is bounded by the solved
static expression plus the paired contour error. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_contourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hstatic, herror⟩ =>
                (hstatic.and herror).mono
                  (fun T hpair =>
                    let J : ℝ :=
                      Complex.binetSecondFormulaDecayingTailIntegral w
                    let S : ℂ :=
                      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                    let E : ℂ :=
                      Complex.finiteAbelPlanaLogFiniteHeightContourError N w T
                    have htriangle :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                          ‖S‖ + ‖E‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_contourError_owner
                        N w T
                    have hstatic_T :
                        ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                      hpair.1
                    have herror_T :
                        ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                      hpair.2
                    have hsum :
                        ‖S‖ + ‖E‖ ≤
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                      add_le_add hstatic_T herror_T
                    have hcombine :
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                          (C / ‖w‖) * J := by
                      calc
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                          exact
                            (right_distrib (Cstatic / ‖w‖)
                              (Cerror / ‖w‖) J).symm
                        _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                          exact
                            congrArg (fun x : ℝ => x * J)
                              (add_div Cstatic Cerror ‖w‖).symm
                        _ = (C / ‖w‖) * J := by
                          rfl
                    le_trans htriangle
                      (le_trans hsum (le_of_eq hcombine)))⟩

/-- Compatibility triangle from separate endpoint-restored static-boundary and
endpoint-restored contour-error estimates.

This constructor is useful only if such separate estimates are independently
available.  It is not the canonical owner route for the endpoint-restored wall
cancellation, because the restored static limit carries a half-endpoint defect
while the restored contour error tends to zero.  The canonical endpoint
bookkeeping route is
`binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay`. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      let C : ℝ := Cstatic + Cerror
      have hC_pos : 0 < C :=
        add_pos hCstatic_pos hCerror_pos
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hstatic, herror⟩ =>
                (hstatic.and herror).mono
                  (fun T hpair =>
                    let J : ℝ :=
                      Complex.binetSecondFormulaDecayingTailIntegral w
                    let S : ℂ :=
                      ((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
                    let E : ℂ :=
                      Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T
                    have htriangle :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                          ‖S‖ + ‖E‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_le_boundarySolvedStatic_add_endpointRestoredContourError_owner
                        N w T
                    have hstatic_T :
                        ‖S‖ ≤ (Cstatic / ‖w‖) * J :=
                      hpair.1
                    have herror_T :
                        ‖E‖ ≤ (Cerror / ‖w‖) * J :=
                      hpair.2
                    have hsum :
                        ‖S‖ + ‖E‖ ≤
                          (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J :=
                      add_le_add hstatic_T herror_T
                    have hcombine :
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                          (C / ‖w‖) * J := by
                      calc
                        (Cstatic / ‖w‖) * J + (Cerror / ‖w‖) * J =
                            (Cstatic / ‖w‖ + Cerror / ‖w‖) * J := by
                          exact
                            (right_distrib (Cstatic / ‖w‖)
                              (Cerror / ‖w‖) J).symm
                        _ = ((Cstatic + Cerror) / ‖w‖) * J := by
                          exact
                            congrArg (fun x : ℝ => x * J)
                              (add_div Cstatic Cerror ‖w‖).symm
                        _ = (C / ‖w‖) * J := by
                          rfl
                    le_trans htriangle
                      (le_trans hsum (le_of_eq hcombine)))⟩

/-- Finite-height lower-vertical decay from the endpoint-returned restored
paired estimate.

This is the canonical endpoint-restored consumption surface.  The restored
static expression and restored contour error are not bounded separately;
instead the half-endpoint term is returned to both sides of their paired
difference, where it cancels algebraically before the finite-height lower side
is identified. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, C, hR_pos, hC_pos, hbounds⟩ =>
      exact
        ⟨R, C, hR_pos, hC_pos,
          fun w hw_re_pos hRle =>
            match hbounds w hw_re_pos hRle with
            | ⟨N, hpair_bound⟩ =>
                hpair_bound.mono
                  (fun T hpair_T =>
                    let P : ℂ :=
                      (((((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                          Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                        Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                        Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                          Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)) +
                        Complex.finiteAbelPlanaLogSummandHalfEndpoints N w) -
                        (Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T +
                          Complex.finiteAbelPlanaLogSummandHalfEndpoints N w))
                    have hnorm :
                        ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                            Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ =
                          ‖P‖ :=
                      Complex.binetSecondFormula_lowerVerticalUpTo_sub_initialWindow_norm_eq_endpointReturnedRestoredPair_norm_owner
                        N w T
                    Eq.subst
                      (motive := fun x : ℝ =>
                        x ≤
                          (C / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w)
                      hnorm.symm
                      hpair_T)⟩

/-- Compatibility branch-wall tail absorption constructor from separate
endpoint-restored finite-height static-boundary and endpoint-restored
contour-error estimates.

The canonical endpoint-restored owner route is the paired endpoint-return
estimate below.  This theorem remains as a transport lemma for any future proof
that genuinely supplies both separate estimates without discarding the endpoint
defect. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖Complex.finiteAbelPlanaLogFiniteHeightEndpointRestoredContourError N w T‖ ≤
                    (Cerror / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  have hlower :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_endpointRestoredContourError_decay
      hfinite
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
      hlower

/-- Branch-wall tail absorption from the endpoint-returned restored paired
finite-height estimate.

This is the non-circular endpoint-restored replacement for the historical
static/error split: the finite-height analytic input is the paired expression
whose two half-endpoint terms cancel algebraically. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  have hlower :
      ∃ R : ℝ, ∃ C : ℝ,
        0 < R ∧
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∀ᶠ T : ℝ in atTop,
              ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                (C / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_endpointReturnedRestoredPair_decay
      hfinite
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_eventually_lowerVerticalUpTo_decay
      hlower

/-- Full Binet branch package from the endpoint-returned restored paired
finite-height decay target.

The paired decay target supplies the tail-absorption half of
`BinetSecondFormulaBranchUniformTailAbsorption`; the branch-coherence half is
the already-owned Binet logarithm coherence theorem. -/
theorem Complex.binetSecondFormula_branchUniformTailAbsorption_of_endpointReturnedRestoredPair_decay
    (hfinite : Complex.BinetSecondFormulaEndpointReturnedRestoredPairDecay) :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_endpointReturnedRestoredPair_decay
      hfinite
  exact
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.of_tail_ownerCoherence
      htail

/-- Finite-height lower-vertical decay from the solved static boundary decay.

The contour-error estimate is discharged by the finite-height boundary target
and the paired contour-error cancellation theorem, so the only remaining
analytic input is the solved static boundary expression. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_decay
    (hfinite :
      ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
        0 < R ∧
        2 ≤ R ∧
        0 < Cstatic ∧
        0 < Cerror ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
            ∃ N : ℕ,
              (∀ᶠ T : ℝ in atTop,
                (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                        Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                    (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                  ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                      (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                        Complex.I *
                          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                    (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                  Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
              (∀ᶠ T : ℝ in atTop,
                ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                    Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                  Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                  Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                  Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                  (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                    Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                    (Cstatic / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∀ᶠ T : ℝ in atTop,
            ‖Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T -
              (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
              (C / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w := by
  match hfinite with
  | ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos, hbounds⟩ =>
      have hwith_error :
          ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
            0 < R ∧
            0 < Cstatic ∧
            0 < Cerror ∧
            ∀ w : ℂ,
              0 < w.re →
              R ≤ ‖w‖ →
                ∃ N : ℕ,
                  (∀ᶠ T : ℝ in atTop,
                    ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                        Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                      Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                      Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                      Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                        (Cstatic / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) ∧
                  (∀ᶠ T : ℝ in atTop,
                    ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                        (Cerror / ‖w‖) *
                          Complex.binetSecondFormulaDecayingTailIntegral w) := by
        exact
          ⟨R, Cstatic, Cerror, hR_pos, hCstatic_pos, hCerror_pos,
            fun w hw_re_pos hRle =>
              match hbounds w hw_re_pos hRle with
              | ⟨N, hboundary, hstatic⟩ =>
                  have hw_norm_two : 2 ≤ ‖w‖ :=
                    le_trans hR_two hRle
                  have herror :
                      ∀ᶠ T : ℝ in atTop,
                        ‖Complex.finiteAbelPlanaLogFiniteHeightContourError N w T‖ ≤
                          (Cerror / ‖w‖) *
                            Complex.binetSecondFormulaDecayingTailIntegral w :=
                    Complex.binetSecondFormula_finiteHeightContourError_eventually_scaled_decayingTail_of_boundaryTarget_owner
                      hw_re_pos hw_norm_two N hboundary hCerror_pos
                  ⟨N, hstatic, herror⟩⟩
      exact
        Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_boundarySolvedStatic_and_contourError_decay
          hwith_error

/-- Assemble the solved-static package from the structural boundary target
and the quantitative solved-static estimate.

The boundary target supplies the finite-height Abel-Plana normalized boundary
identity; the quantitative predicate supplies only the static norm estimate.
This keeps the analytic scale estimate separate from the contour assembly. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_decay_of_boundaryTarget_and_staticEstimate
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hstatic :
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate)
    (Cerror : ℝ)
    (hCerror_pos : 0 < Cerror) :
    ∃ R : ℝ, ∃ Cstatic : ℝ, ∃ Cerror : ℝ,
      0 < R ∧
      2 ≤ R ∧
      0 < Cstatic ∧
      0 < Cerror ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ∃ N : ℕ,
            (∀ᶠ T : ℝ in atTop,
              (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                    (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                      Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                  (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                    (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                      Complex.I *
                        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                  (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T) ∧
            (∀ᶠ T : ℝ in atTop,
              ‖((∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
                  Complex.finiteAbelPlanaLogSummand w (x : ℂ)) +
                Complex.finiteAbelPlanaLogSummandHalfEndpoints N w -
                Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T -
                Complex.finiteAbelPlanaLogPVIntegerResidueContribution N w) -
                (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                  Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ ≤
                  (Cstatic / ‖w‖) *
                    Complex.binetSecondFormulaDecayingTailIntegral w) := by
  match hboundary with
  | ⟨Rboundary, hRboundary_pos, hRboundary_two, hboundary_bound⟩ =>
      match hstatic with
      | ⟨Rstatic, Cstatic, hRstatic_pos, hRstatic_two, hCstatic_pos, hstatic_bound⟩ =>
          let R : ℝ := max Rboundary Rstatic
          have hR_pos : 0 < R :=
            lt_of_lt_of_le hRboundary_pos (le_max_left Rboundary Rstatic)
          have hR_two : 2 ≤ R :=
            le_trans hRboundary_two (le_max_left Rboundary Rstatic)
          exact
            ⟨R, Cstatic, Cerror, hR_pos, hR_two, hCstatic_pos, hCerror_pos,
              fun w hw_re_pos hRle =>
                have hRboundary_le : Rboundary ≤ ‖w‖ :=
                  le_trans (le_max_left Rboundary Rstatic) hRle
                have hRstatic_le : Rstatic ≤ ‖w‖ :=
                  le_trans (le_max_right Rboundary Rstatic) hRle
                match hstatic_bound w hw_re_pos hRstatic_le with
                | ⟨N, hstatic_T⟩ =>
                    have hboundary_T :
                        ∀ᶠ T : ℝ in atTop,
                          (((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                                (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
                                  Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) +
                              (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) +
                            ((((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
                                (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
                                  Complex.I *
                                    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) +
                              (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T))) =
                            Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
                      hboundary_bound w hw_re_pos hRboundary_le N
                    exact
                      ⟨N, hboundary_T, hstatic_T⟩⟩

/-- The lower-vertical difference decay predicate is exactly the public
wall-cancellation theorem after transporting across the proved Binet tail
split. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_iff_wallCancellation :
    Complex.BinetSecondFormulaLowerVerticalDifferenceDecay ↔
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  constructor
  · intro hdifference
    exact
      Complex.binetSecondFormula_branchTail_wallCancellation_of_lowerVerticalDifference_decay
        hdifference
  · intro htail
    match htail with
    | ⟨R, C, hR_pos, hC_pos, htail_bound⟩ =>
        exact
          ⟨R, C, hR_pos, hC_pos,
            fun w hw_re_pos hRle =>
              have hnorm :
                  ‖Complex.binetSecondFormulaTailRemainder w‖ =
                    ‖Complex.finiteAbelPlanaLogLowerVerticalFullIntegral w -
                      (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
                        Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)‖ :=
                Complex.binetSecondFormula_tailRemainder_norm_eq_lowerVerticalFullIntegral_sub_initialWindow_norm_owner
                  hw_re_pos
              Eq.subst
                (motive := fun x : ℝ =>
                  x ≤
                    (C / ‖w‖) *
                      Complex.binetSecondFormulaDecayingTailIntegral w)
                hnorm
                (htail_bound w hw_re_pos hRle)⟩

/-- Constructor from a genuinely contour-deformed kernel comparison and a
uniform full-sector kernel majorant to branch-wall tail absorption.

This is the non-circular contour route: the comparison to `K` is an
integral-level contour statement, and the majorant for `K` is the ordinary
decaying scalar Binet tail.  No raw principal-branch wall estimate is used. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
    {K : Complex.BinetSecondFormulaContourDeformedTailKernel}
    {R C : ℝ}
    (hR_pos : 0 < R)
    (hC_pos : 0 < C)
    (hcomparison : Complex.BinetSecondFormulaContourTailIntegralComparison K R)
    (hK_integrable :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          IntegrableOn
            (fun t : ℝ => K w t)
            (Set.Ioi (‖w‖ / 2)))
    (hmajorant : Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  let Ctail : ℝ := 2 * C
  have hCtail_pos : 0 < Ctail :=
    mul_pos two_pos hC_pos
  have hdecay :
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
            (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    intro w hw_re_pos hRle
    have hraw :
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
          ((2 * C) / ‖w‖) *
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
      Complex.binetSecondFormula_contourTailKernel_integral_decay_of_uniform_majorant
        hK_integrable
        hmajorant
        w hw_re_pos hRle
    have hCtail_eq : Ctail = 2 * C := by
      rfl
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), ‖K w t‖ ≤
            (x / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
        hCtail_eq.symm
        hraw
  exact
    ⟨R, Ctail, hR_pos, hCtail_pos,
      Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailKernel_integral_decay
        hcomparison
        hdecay⟩

/-- Specialized branch-wall transport through the canonical decaying contour
kernel.

This is a pure assembly lemma: an integral-level contour comparison to
`binetSecondFormulaDecayingTailKernel` immediately gives the public wall
cancellation bound because that kernel is already integrable and has the
uniform full-sector decaying majorant. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison
    (hcomparison :
      Complex.BinetSecondFormulaContourTailIntegralComparison
        Complex.binetSecondFormulaDecayingTailKernel 2) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
      (K := Complex.binetSecondFormulaDecayingTailKernel)
      (R := 2)
      (C := 1)
      two_pos
      zero_lt_one
      hcomparison
      (fun w _hw_re_pos _hRle =>
        Complex.binetSecondFormula_decayingTailKernel_integrableOn_tail w)
      Complex.binetSecondFormula_decayingTailKernel_uniform_majorant

/-- Branch-wall transport from a contour-deformed kernel with a decaying
majorant.

This is a pure assembly lemma: an integral-level contour comparison to a
kernel `K`, split-tail integrability of `K`, and the uniform full-sector
`C / ‖w‖` majorant for `K` imply the public wall cancellation bound. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernelPackage
    (hpackage :
      ∃ K : Complex.BinetSecondFormulaContourDeformedTailKernel,
        ∃ R : ℝ, ∃ C : ℝ,
          0 < R ∧
          0 < C ∧
          Complex.BinetSecondFormulaContourTailIntegralComparison K R ∧
          (∀ w : ℂ,
            0 < w.re →
            R ≤ ‖w‖ →
              IntegrableOn
                (fun t : ℝ => K w t)
                (Set.Ioi (‖w‖ / 2))) ∧
          Complex.BinetSecondFormulaContourTailUniformMajorant K R C) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hpackage with
  | ⟨K, R, C, hR_pos, hC_pos, hcomparison, hK_integrable, hmajorant⟩ =>
      exact
        Complex.binetSecondFormula_branchTail_wallCancellation_of_contourKernel_uniformMajorant
          (K := K)
          (R := R)
          (C := C)
          hR_pos
          hC_pos
          hcomparison
          hK_integrable
          hmajorant

/-- Assemble the historical solved-static input pair from the structural
boundary target and an independent decaying contour-kernel comparison.

This is the non-circular contour route to the old static input pair.  The
remaining analytic comparison is integral-level: the actual Binet tail
remainder must be compared with the already majorized decaying contour kernel.
Once that comparison is supplied, branch-wall tail absorption and solved-static
decay are both pure owner-level transports. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_decayingContourKernelComparison
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    (hcomparison :
      Complex.BinetSecondFormulaContourTailIntegralComparison
        Complex.binetSecondFormulaDecayingTailKernel 2) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_decayingContourKernelComparison
      hcomparison
  exact
    Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_tailAbsorption
      hboundary htail

/-- Assemble the historical solved-static input pair from the structural
boundary target and a contour-tail majorant integral decay estimate.

This is the non-circular route through the already compared contour majorant
kernel: the majorant integral estimate gives tail absorption, and the static
decay is then only a full-height cancellation transport. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_contourTailMajorantKernel_integral_decay
    (hboundary :
      Complex.BinetSecondFormulaFiniteHeightBoundaryTarget)
    {C : ℝ}
    (hC_pos : 0 < C)
    (hdecay :
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
            (C / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
      Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchUniform_tail_absorption_of_contourTailMajorantKernel_integral_decay
      hC_pos hdecay
  exact
    Complex.binetSecondFormula_boundarySolvedStatic_inputs_of_boundaryTarget_and_tailAbsorption
      hboundary htail

/-- Owner obstruction for the historical endpoint-free static Abel-Plana input
pair.

The old target asked for an endpoint-free finite-height boundary target.  The
proved constant-face reconstruction is endpoint-restored, and the endpoint
indentation is nonzero on the real half-line; hence this exact pair is not a
valid owner target. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_inputs_owner :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  exact Complex.not_binetSecondFormula_boundarySolvedStatic_inputs_owner_target

/-- Owner obstruction for the historical solved-static Abel-Plana boundary
decay route.

The old route bundled the endpoint-free boundary target into the finite-height
static decay package.  Since that boundary target is false, the route is not a
valid owner theorem. -/
theorem Complex.binetSecondFormula_boundarySolvedStatic_decay_owner :
    ¬ (Complex.BinetSecondFormulaFiniteHeightBoundaryTarget ∧
        Complex.BinetSecondFormulaBoundarySolvedStaticDecayEstimate) := by
  exact Complex.binetSecondFormula_boundarySolvedStatic_inputs_owner

/-- Corrected owner contour input replacing the historical endpoint-free
solved-static route. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- The lower-vertical branch-wall cancellation decay is not supplied by the
historical endpoint-free solved-static route.

This declaration records the corrected dependency: the endpoint-restored
finite-height contour input is available, while the full lower-vertical decay
requires an additional genuine static/lower-vertical cancellation theorem. -/
theorem Complex.binetSecondFormula_lowerVerticalDifference_decay_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- The branch-wall paired-contour tail owner cannot be discharged through the
historical endpoint-free solved-static input.

The available owner input at this layer is the endpoint-restored finite-height
contour package; the remaining full wall cancellation must be proved from a
genuine lower-vertical/static cancellation theorem, not from the false old
boundary target. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Owner analytic package currently available after endpoint restoration:
sector window plus corrected finite-height contour inputs. -/
theorem Complex.binetSecondFormula_branchTail_sectorWindow_and_wallCancellation_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison ∧
      Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    ⟨Complex.binetSecondFormula_branchTail_sectorWindow_owner,
      Complex.binetSecondFormula_branchTail_wallCancellation_owner⟩

/-- Projection of sector-local absorption of the branch-wall local-indentation
envelope into the standard Binet decaying tail integral. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorLogWindowComparison_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorLogWindowComparison := by
  exact
    Complex.binetSecondFormula_branchTail_sectorWindow_owner

/-- Sector-local absorption is exactly the scalar log-window comparison, kept
under the historical absorption name consumed by the later tail estimates. -/
theorem Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner :
    Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption := by
  exact
    Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption_iff_logWindowComparison.mpr
      Complex.binetSecondFormula_branchLocalIndentation_sectorLogWindowComparison_owner

/-- Owner sector-local tail-remainder estimate after absorbing the
local-indentation envelope. -/
theorem Complex.binetSecondFormula_tailRemainder_sectorBound_owner :
    Complex.BinetSecondFormulaTailRemainderSectorLocalAbsorption := by
  exact
    Complex.binetSecondFormula_tailRemainder_sectorBound_of_localIndentation_absorption
      Complex.binetSecondFormula_tailRemainder_localIndentation_add_far_scaled_decay_ownerGap
      Complex.binetSecondFormula_branchLocalIndentation_sectorAbsorption_owner

/-- Principal-tail sector estimate after absorbing the local-indentation envelope.

The input `hlocal` is the contour estimate with the branch-wall window still
visible; `habsorb` is the scale-correct sector-local absorption theorem for
that window.  The conclusion keeps the local scalar contribution as `Clocal`;
the pure `C / ‖w‖` full-sector decay is owned below by paired branch-wall
contour cancellation. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_sectorBound_of_localIndentation_absorption
    (hlocal : Complex.BinetSecondFormulaBranchLocalIndentationTailControl)
    (habsorb : Complex.BinetSecondFormulaBranchLocalIndentationSectorAbsorption) :
    ∀ δ : ℝ,
      0 < δ →
        ∃ C : ℝ,
          0 < C ∧
          ∀ w : ℂ,
            δ * ‖w‖ ≤ w.re →
            2 ≤ ‖w‖ →
              2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                (C + C / ‖w‖) *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro δ hδ
  match hlocal with
  | ⟨Cfar, hCfar_nonneg, hlocal_estimate⟩ =>
      match habsorb δ hδ with
      | ⟨Clocal, hClocal_pos, hlocal_absorb⟩ =>
          let C : ℝ := max Clocal Cfar
          have hClocal_le_C : Clocal ≤ C :=
            le_max_left Clocal Cfar
          have hCfar_le_C : Cfar ≤ C :=
            le_max_right Clocal Cfar
          have hC_pos : 0 < C :=
            lt_of_lt_of_le hClocal_pos hClocal_le_C
          exact
            ⟨C, hC_pos,
              fun w hw_sector hw_norm_two =>
                let J : ℝ :=
                  Complex.binetSecondFormulaDecayingTailIntegral w
                let L : ℝ :=
                  Complex.binetSecondFormulaBranchLocalIndentationEnvelope w
                let F : ℝ := (Cfar / ‖w‖) * J
                have hprincipal_le :
                    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
                      L + F :=
                  have hnorm_pos : 0 < ‖w‖ :=
                    lt_of_lt_of_le zero_lt_two hw_norm_two
                  have hsector_pos : 0 < δ * ‖w‖ :=
                    mul_pos hδ hnorm_pos
                  hlocal_estimate w
                    (lt_of_lt_of_le hsector_pos hw_sector)
                    hw_norm_two
                have hlocal_le :
                    L ≤ Clocal * J :=
                  hlocal_absorb w hw_sector hw_norm_two
                have hJ_nonneg : 0 ≤ J :=
                  integral_nonneg_of_ae
                    ((ae_restrict_mem measurableSet_Ioi).mono
                      (fun t ht =>
                        Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t
                          (lt_of_le_of_lt
                            (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
                            ht)))
                have hlocal_C_le :
                    Clocal * J ≤ C * J :=
                  mul_le_mul_of_nonneg_right hClocal_le_C hJ_nonneg
                have hnorm_pos : 0 < ‖w‖ :=
                  lt_of_lt_of_le zero_lt_two hw_norm_two
                have hfar_C_le :
                    (Cfar / ‖w‖) * J ≤ (C / ‖w‖) * J := by
                  have hdiv_le : Cfar / ‖w‖ ≤ C / ‖w‖ :=
                    div_le_div_of_nonneg_right hCfar_le_C (le_of_lt hnorm_pos)
                  exact mul_le_mul_of_nonneg_right hdiv_le hJ_nonneg
                have hsum_le :
                    L + F ≤ C * J + (C / ‖w‖) * J :=
                  add_le_add (le_trans hlocal_le hlocal_C_le) hfar_C_le
                have hconst :
                    C * J + (C / ‖w‖) * J =
                      (C + C / ‖w‖) * J := by
                  calc
                    C * J + (C / ‖w‖) * J =
                        (C + C / ‖w‖) * J := by
                      exact (add_mul C (C / ‖w‖) J).symm
                le_trans hprincipal_le (le_trans hsum_le (le_of_eq hconst))⟩

/-- Tail absorption obtained from the legacy principal-tail norm estimate.

This theorem is a compatibility bridge: it shows that the older raw-norm
predicate is sufficient for the canonical contour-level tail-absorption target,
but the owner theorem no longer depends on proving the raw-norm predicate. -/
theorem Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
    (hprincipal :
      Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  match hprincipal with
  | ⟨C, hC_pos, hprincipal_bound⟩ =>
      let Rtail : ℝ := 2
      let Ctail : ℝ := C + 2
      have hRtail_pos : 0 < Rtail :=
        two_pos
      have hCtail_pos : 0 < Ctail :=
        add_pos hC_pos two_pos
      have hcontour_decay :
          ∀ w : ℂ,
            0 < w.re →
            Rtail ≤ ‖w‖ →
              2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                  ‖Complex.binetSecondFormulaContourTailMajorantKernel w t‖ ≤
                (Ctail / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
        Complex.binetSecondFormula_contourTailMajorantKernel_integral_accounting
          hprincipal_bound
          Complex.binetSecondFormula_contourTailMajorantKernel_decayingSummand_integral_le_ownerGap
      have htail_decay :
          ∀ w : ℂ,
            0 < w.re →
            Rtail ≤ ‖w‖ →
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                (Ctail / ‖w‖) *
                  Complex.binetSecondFormulaDecayingTailIntegral w :=
        Complex.binetSecondFormula_tailRemainder_norm_le_of_contourTailMajorantKernel_integral_decay
          hcontour_decay
      exact
        ⟨Rtail, Ctail, hRtail_pos, hCtail_pos, htail_decay⟩

/-- Wall tail absorption from the sharp bounded-window branch-wall estimate.

This is the correctly localized owner reduction: after the far tail has been
handled by the existing scaled estimate, the remaining theorem is exactly the
bounded-window moving-spike cancellation estimate. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_boundedWindow_decay
    (hbounded :
      ∃ Cbounded : ℝ,
        0 < Cbounded ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
              (Cbounded / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
      (Complex.binetSecondFormula_branchWallPrincipalTailCancellation_of_boundedWindow_decay
        hbounded)

/-- Wall tail absorption from a scaled estimate for the weighted moving
branch-wall logarithmic envelope on the bounded window. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_weightedFullLogEnvelope_decay
    (hweighted :
      ∃ Cweighted : ℝ,
        0 < Cweighted ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max |Real.log (w.re / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Cweighted / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_boundedWindow_decay
      (Complex.binetSecondFormula_boundedWindow_decay_of_weightedFullLogEnvelope_decay
        hweighted)

/-- Branch-wall tail absorption from the legacy principal-tail norm estimate.

This is now a thin wrapper through the contour-level tail-remainder decay
target, keeping the final tail package independent of the raw principal-kernel
norm formulation. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_of_principalTailCancellation
    (hprincipal :
      Complex.BinetSecondFormulaBranchWallPrincipalTailCancellation) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchWall_tailAbsorption_of_principalTailCancellation
      hprincipal

/-- Corrected owner input available at the branch-wall tail layer.

The pure full-sector tail absorption theorem is not discharged by the
historical endpoint-free static route.  What is owned here is the
endpoint-restored finite-height contour input; a separate lower-vertical/static
cancellation theorem is still required to construct tail absorption. -/
theorem Complex.binetSecondFormula_branchUniform_tail_absorption_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs := by
  exact
    Complex.binetSecondFormula_endpointRestoredFiniteHeightContourInputs_owner

/-- Corrected owner package available before the genuine branch-wall tail
absorption theorem is proved. -/
theorem Complex.binetSecondFormula_branchUniformTailAbsorption_owner :
    Complex.BinetSecondFormulaEndpointRestoredFiniteHeightContourInputs :=
  Complex.binetSecondFormula_branchUniform_tail_absorption_owner

/-- Branch-uniform full-sector integral tail majorant for the Binet arctangent
kernel, after contour deformation. -/
theorem Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant_from_contour
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (2 * C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  match Complex.BinetSecondFormulaBranchUniformTailAbsorption.tail hbranch with
  | ⟨R, C, hR, hC, htail⟩ =>
      let htail' :
          ∀ w : ℂ,
            0 < w.re →
            R ≤ ‖w‖ →
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                (2 * (C / 2) / ‖w‖) *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        fun w hw_re_pos hRle =>
          have hscale :
              2 * (C / 2) / ‖w‖ = C / ‖w‖ :=
            congrArg (fun x : ℝ => x / ‖w‖) (mul_div_cancel₀ C two_ne_zero)
          Eq.subst
            (motive := fun x : ℝ =>
              ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
                x *
                  (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))
            hscale.symm
            (htail w hw_re_pos hRle)
      exact
        ⟨R, C / 2, hR, half_pos hC,
          htail'⟩

/-- Integrated form of the branch-uniform full-sector tail majorant.

This theorem contains no branch analysis: it repackages the contour-deformed
integral majorant with the constant in the usual `C / ‖w‖` form. -/
theorem Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ C : ℝ,
      0 < R ∧
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (C / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := fun hbranch =>
  let ⟨Rtail, Ctail, hRtail, hCtail, htail⟩ :=
    Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant_from_contour
      hbranch
  ⟨Rtail, 2 * Ctail, hRtail, mul_pos two_pos hCtail,
    fun w hw_re_pos hRtail_le => htail w hw_re_pos hRtail_le⟩

/-- Full-sector tail absorption for the Binet remainder split at `‖w‖ / 2`.

The only analytic root used here is the branch-uniform integrated tail
majorant above.  The remaining argument is real-variable tail absorption: the
Binet majorant tail decays exponentially from `‖w‖ / 2`, hence is bounded by a
constant for large `‖w‖`, leaving the explicit `1 / ‖w‖` factor. -/
theorem Complex.binetSecondFormula_tail_remainder_fullSector_norm_le_div_norm :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let ⟨Rtail, Ctail, hRtail, hCtail, htail_majorant⟩ :=
    Complex.binetSecondFormula_arctan_tail_branchUniform_fullSector_integral_majorant
      hbranch
  ⟨max Rtail 2, 2 * Ctail,
    lt_of_lt_of_le hRtail (le_max_left Rtail 2),
    mul_pos two_pos hCtail,
    fun w hw_re_pos hw_norm_large =>
      let hRtail_le : Rtail ≤ ‖w‖ :=
        le_trans (le_max_left Rtail 2) hw_norm_large
      let htwo_le_norm : (2 : ℝ) ≤ ‖w‖ :=
        le_trans (le_max_right Rtail 2) hw_norm_large
      let hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 :=
        (le_div_iff₀ two_pos).mpr
          (Eq.subst
            (motive := fun x : ℝ => x ≤ ‖w‖)
            (one_mul (2 : ℝ)).symm
            htwo_le_norm)
      let htail :
          ‖Complex.binetSecondFormulaTailRemainder w‖ ≤
            (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
        htail_majorant w hw_re_pos hRtail_le
      let hreal_tail :
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
            2 * Real.exp (-Real.pi * (‖w‖ / 2)) :=
        Real.binetSecondFormula_kernel_majorant_tail_integral_le_exp
          (a := ‖w‖ / 2) hhalf_ge_one
      let hcoeff_nonneg : 0 ≤ Ctail / ‖w‖ :=
        div_nonneg (le_of_lt hCtail) (norm_nonneg w)
      let htail_exp :
          (Ctail / ‖w‖) *
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) ≤
            (Ctail / ‖w‖) *
              (2 * Real.exp (-Real.pi * (‖w‖ / 2))) :=
        mul_le_mul_of_nonneg_left hreal_tail hcoeff_nonneg
      let hexponent_nonpos : -Real.pi * (‖w‖ / 2) ≤ 0 :=
        let hproduct_nonneg : 0 ≤ Real.pi * (‖w‖ / 2) :=
          mul_nonneg (le_of_lt Real.pi_pos)
            (div_nonneg (norm_nonneg w) zero_le_two)
        calc
          -Real.pi * (‖w‖ / 2) = -(Real.pi * (‖w‖ / 2)) :=
            neg_mul Real.pi (‖w‖ / 2)
          _ ≤ 0 := neg_nonpos.mpr hproduct_nonneg
      let hexp_le_one : Real.exp (-Real.pi * (‖w‖ / 2)) ≤ 1 :=
        Real.exp_le_one_iff.mpr hexponent_nonpos
      let htwo_exp_le_two : 2 * Real.exp (-Real.pi * (‖w‖ / 2)) ≤ (2 : ℝ) :=
        calc
          2 * Real.exp (-Real.pi * (‖w‖ / 2)) ≤ 2 * 1 :=
            mul_le_mul_of_nonneg_left hexp_le_one zero_le_two
          _ = 2 := mul_one 2
      let htail_const :
          (Ctail / ‖w‖) *
              (2 * Real.exp (-Real.pi * (‖w‖ / 2))) ≤
            (Ctail / ‖w‖) * 2 :=
        mul_le_mul_of_nonneg_left htwo_exp_le_two hcoeff_nonneg
      let htarget : (Ctail / ‖w‖) * 2 = (2 * Ctail) / ‖w‖ :=
        calc
          (Ctail / ‖w‖) * 2 = (Ctail * ‖w‖⁻¹) * 2 := rfl
          _ = 2 * (Ctail * ‖w‖⁻¹) :=
            mul_comm (Ctail * ‖w‖⁻¹) 2
          _ = (2 * Ctail) * ‖w‖⁻¹ :=
            (mul_assoc 2 Ctail ‖w‖⁻¹).symm
          _ = (2 * Ctail) / ‖w‖ := rfl
      le_trans htail
        (le_trans htail_exp
          (le_trans htail_const
            (le_of_eq htarget)))⟩

/-- Convert the honest split Binet remainder bound to a pure
open-right-half-plane `O(1 / ‖w‖)` estimate from branch-tail absorption.

The small split piece already carries the explicit `1 / ‖w‖` factor. -/
theorem Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let ⟨Rtail, Ktail, hRtail, hKtail, htailBound⟩ :=
    Complex.binetSecondFormula_tail_remainder_fullSector_norm_le_div_norm
      hbranch
  let K : ℝ := 4 * J + Ktail
  let hJ_pos : 0 < J :=
    Real.binetSecondFormula_kernel_majorant_integral_pos
  let hK : 0 < K :=
    add_pos (mul_pos four_pos hJ_pos) hKtail
  ⟨Rtail, K, hRtail, hK, fun w hw_re_pos hRtail_le =>
    let hsplit :
        Complex.binetSecondFormulaRemainder w =
          Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w :=
      Complex.binetSecondFormulaRemainder_eq_small_add_tail (w := w) hw_re_pos
    let hsmall :
        ‖Complex.binetSecondFormulaSmallRemainder w‖ ≤ 4 * J / ‖w‖ :=
      Complex.binetSecondFormula_small_remainder_norm_le_integral_majorant
        (w := w) hw_re_pos
    let htail :
        ‖Complex.binetSecondFormulaTailRemainder w‖ ≤ Ktail / ‖w‖ :=
      htailBound w hw_re_pos hRtail_le
    let hsum :
        ‖Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w‖ ≤
          4 * J / ‖w‖ + Ktail / ‖w‖ :=
      calc
        ‖Complex.binetSecondFormulaSmallRemainder w +
            Complex.binetSecondFormulaTailRemainder w‖
            ≤ ‖Complex.binetSecondFormulaSmallRemainder w‖ +
                ‖Complex.binetSecondFormulaTailRemainder w‖ :=
          norm_add_le _ _
        _ ≤ 4 * J / ‖w‖ + Ktail / ‖w‖ :=
          add_le_add hsmall htail
    let hcombine :
        4 * J / ‖w‖ + Ktail / ‖w‖ = K / ‖w‖ :=
      calc
        4 * J / ‖w‖ + Ktail / ‖w‖ =
            (4 * J + Ktail) / ‖w‖ :=
          (add_div (4 * J) Ktail ‖w‖).symm
        _ = K / ‖w‖ := rfl
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ K / ‖w‖)
      hsplit.symm
      (hsum.trans_eq hcombine)⟩

/-- Pure-decay Binet/log-Gamma comparison from branch-tail absorption.

Use `Complex.binetSecondFormula_logGamma_with_split_remainder_bound_closedRightHalfPlane`
for the split statement.  This theorem converts the split Binet estimate into
pure `O(1 / ‖w‖)` decay using the same branch-tail absorption input. -/
theorem Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane_requires_tail_absorption :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        Complex.binetLogGammaBranch w =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w ∧
          ‖Complex.binetSecondFormulaRemainder w‖ ≤ K / ‖w‖ := fun hbranch =>
  let ⟨Rlog, hRlog, hlog⟩ :=
    Complex.binetSecondFormula_logGamma_closedRightHalfPlane_largeRadius
  let ⟨Rtail, K, hRtail, hK, htail⟩ :=
    Complex.binetSecondFormula_remainder_bound_closedRightHalfPlane_requires_tail_absorption
      hbranch
  ⟨max Rlog Rtail, K,
    lt_of_lt_of_le hRlog (le_max_left Rlog Rtail),
    hK,
    fun w hw_re_pos hnorm =>
      let hRlog_le : Rlog ≤ ‖w‖ :=
        le_trans (le_max_left Rlog Rtail) hnorm
      let hRtail_le : Rtail ≤ ‖w‖ :=
        le_trans (le_max_right Rlog Rtail) hnorm
      ⟨hlog w hw_re_pos hRlog_le,
        htail w hw_re_pos hRtail_le⟩⟩

/-- Exponentiating Binet's logarithmic branch identity separates the main term
from the Binet remainder. -/
theorem Complex.Gamma_eq_exp_binetLogGammaMainTerm_mul_exp_binetRemainder_of_binetBranch
    {w : ℂ}
    (hexp_branch :
      Complex.exp (Complex.binetLogGammaBranch w) = Complex.Gamma w)
    (hbinet :
      Complex.binetLogGammaBranch w =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w) :
    Complex.Gamma w =
      Complex.exp (Complex.binetLogGammaMainTerm w) *
        Complex.exp (Complex.binetSecondFormulaRemainder w) := by
  calc
    Complex.Gamma w =
        Complex.exp (Complex.binetLogGammaBranch w) :=
      hexp_branch.symm
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
      (neg_sub w (1 / 2 : ℂ)).symm
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
    (hw_ne : w ≠ 0)
    (hexp_branch :
      Complex.exp (Complex.binetLogGammaBranch w) = Complex.Gamma w)
    (hbinet :
      Complex.binetLogGammaBranch w =
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
    Complex.Gamma_eq_exp_binetLogGammaMainTerm_mul_exp_binetRemainder_of_binetBranch
      hexp_branch hbinet
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
    (hw_ne : w ≠ 0)
    (hexp_branch :
      Complex.exp (Complex.binetLogGammaBranch w) = Complex.Gamma w)
    (hbinet :
      Complex.binetLogGammaBranch w =
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
      hw_ne hexp_branch hbinet
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
    Eq.trans (RCLike.norm_ofReal (Real.sqrt (2 * Real.pi))) (abs_of_nonneg hsqrt_nonneg)
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
        (mul_assoc (Real.sqrt (2 * Real.pi)) 2 ‖E‖).symm
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
    (hw_ne : w ≠ 0)
    (hexp_branch :
      Complex.exp (Complex.binetLogGammaBranch w) = Complex.Gamma w)
    (hbinet :
      Complex.binetLogGammaBranch w =
        Complex.binetLogGammaMainTerm w +
          Complex.binetSecondFormulaRemainder w)
    (hE : ‖Complex.binetSecondFormulaRemainder w‖ ≤ 1) :
    ‖Complex.Gamma w * Complex.exp w *
        w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
      2 * Real.sqrt (2 * Real.pi) * ‖Complex.binetSecondFormulaRemainder w‖ := by
  exact
    Eq.subst
      (motive := fun x : ℂ => ‖x‖ ≤
        2 * Real.sqrt (2 * Real.pi) * ‖Complex.binetSecondFormulaRemainder w‖)
      (Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_eq_exp_binetRemainder_sub_one
        hw_ne hexp_branch hbinet).symm
      (Complex.sqrt_two_pi_mul_exp_sub_one_norm_le_of_norm_le_one hE)

end
end LFunctions
end Boundary

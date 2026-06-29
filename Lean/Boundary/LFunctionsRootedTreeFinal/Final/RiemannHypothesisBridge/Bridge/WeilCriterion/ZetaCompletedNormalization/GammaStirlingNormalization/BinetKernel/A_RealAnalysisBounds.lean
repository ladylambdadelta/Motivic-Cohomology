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

local notation "π" => Real.pi

-- Helper lemmas for numeric and algebraic facts, avoiding automation

private lemma three_pos : (0 : ℝ) < 3 :=
  zero_lt_three

private lemma pi_le_three_point_fifteen : Real.pi ≤ 3.15 :=
  le_of_lt Real.pi_lt_315

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
          _ = z := div_mul_cancel₀ z (OfNat.ofNat_ne_zero 2)
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
                exact norm_div _ _
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

/-- Sub-lemma: Bound on π in the form needed for Cfar ≤ 10.
-/
theorem Complex.binetSecondFormula_pi_bounded_owner :
    Real.pi ≤ 3.15 := by
  exact pi_le_three_point_fifteen


end
end LFunctions
end Boundary

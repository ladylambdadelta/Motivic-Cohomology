import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.BlockDerivatives

/-!
# Basic real-phase reductions for logarithmic phase estimates

This file owns the elementary real-phase objects, unit-norm exponential sums,
single-point block bounds, and the first angle-period reductions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The real exponential attached to a scalar phase has unit norm. -/
theorem Complex.realPhase_exp_I_norm
    (φ : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.exp (Complex.I * (φ x : ℂ))‖ = 1 := by
  have hexp_re : (Complex.I * (φ x : ℂ)).re = 0 := by
    calc
      (Complex.I * (φ x : ℂ)).re = -((φ x : ℂ).im) :=
        Complex.I_mul_re (φ x : ℂ)
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im (φ x))
      _ = 0 :=
        neg_zero
  calc
    ‖Complex.exp (Complex.I * (φ x : ℂ))‖ =
        Complex.abs (Complex.exp (Complex.I * (φ x : ℂ))) :=
      Complex.norm_eq_abs (Complex.exp (Complex.I * (φ x : ℂ)))
    _ = Real.exp (Complex.I * (φ x : ℂ)).re :=
      Complex.abs_exp (Complex.I * (φ x : ℂ))
    _ = Real.exp 0 :=
      congrArg Real.exp hexp_re
    _ = 1 :=
      Real.exp_zero

/-- Finite exponential sums are trivially bounded by the length of their
indexing interval.  This is the nonoscillatory endpoint of the first derivative
argument. -/
theorem Complex.realPhase_integer_block_bound_by_card
    (φ : ℝ → ℝ)
    {a b : ℕ} :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ((Finset.Icc a b).card : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc a b,
          ‖Complex.exp (Complex.I * (φ n : ℂ))‖ :=
      norm_sum_le (Finset.Icc a b)
        (fun n => Complex.exp (Complex.I * (φ n : ℂ)))
    _ = ∑ n ∈ Finset.Icc a b, (1 : ℝ) := by
      exact Finset.sum_congr rfl
        (fun n hn => Complex.realPhase_exp_I_norm φ n)
    _ = ((Finset.Icc a b).card : ℝ) := by
      calc
        ∑ n ∈ Finset.Icc a b, (1 : ℝ) =
            (Finset.Icc a b).card • (1 : ℝ) := by
          exact Finset.sum_const (1 : ℝ)
        _ = ((Finset.Icc a b).card : ℝ) * 1 := by
          exact nsmul_eq_mul (Finset.Icc a b).card (1 : ℝ)
        _ = ((Finset.Icc a b).card : ℝ) := by
          exact mul_one ((Finset.Icc a b).card : ℝ)

/-- Phase increment between adjacent integer samples. -/
def Complex.realPhase_integerIncrement
    (φ : ℝ → ℝ)
    (n : ℕ) : ℝ :=
  φ (n + 1 : ℕ) - φ n

/-- Separation of all adjacent phase increments from integral multiples of
`2π`.  This is the missing frequency-separation hypothesis in the honest
Kusmin-Landau estimate for `exp(i φ(n))`. -/
def Complex.realPhase_integerIncrementSeparatedOn
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (lam : ℝ) : Prop :=
  ∀ n : ℕ,
    n ∈ Finset.Ico a b →
      ∀ k : ℤ,
        lam ≤
          ‖Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ))‖

/-- Monotonicity of the adjacent integer phase increments on a block.

This is the discrete finite-difference hypothesis needed in the honest
Kusmin-Landau summation-by-parts primitive.  Separation from `2πℤ` alone is not
enough: adjacent increments can alternate between two separated frequencies and
keep the sampled phases aligned over long blocks. -/
def Complex.realPhase_integerIncrementMonotoneOn
    (φ : ℝ → ℝ)
    (a b : ℕ) : Prop :=
  MonotoneOn
    (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
    (Finset.Ico a b : Set ℕ) ∨
  AntitoneOn
    (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
    (Finset.Ico a b : Set ℕ)

/-- Adjacent phase increment reduced to the fundamental interval `(-π, π]`.

This is the no-winding coordinate needed by the Abel-variation proof.  Raw
monotonicity of increments is not enough: the inverse denominator is periodic
and can wind around `2πℤ` many times. -/
def Complex.realPhase_reducedIntegerIncrement
    (φ : ℝ → ℝ)
    (n : ℕ) : ℝ :=
  toIocMod Real.two_pi_pos (-Real.pi)
    (Complex.realPhase_integerIncrement φ n)

/-- No-winding monotonicity of adjacent increments after reduction to
`(-π, π]`. -/
def Complex.realPhase_reducedIntegerIncrementMonotoneOn
    (φ : ℝ → ℝ)
    (a b : ℕ) : Prop :=
  MonotoneOn
    (fun n : ℕ => Complex.realPhase_reducedIntegerIncrement φ n)
    (Finset.Ico a b : Set ℕ) ∨
  AntitoneOn
    (fun n : ℕ => Complex.realPhase_reducedIntegerIncrement φ n)
    (Finset.Ico a b : Set ℕ)

/-- Endpoint control for a one-point exponential block. -/
theorem Complex.realPhase_singleton_integer_block_bound
    (φ : ℝ → ℝ)
    (a : ℕ)
    {lam : ℝ}
    (hlam_pos : 0 < lam) :
    ‖∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  have hblock :
      ‖∑ n ∈ Finset.Icc a a,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          ((Finset.Icc a a).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card φ
  have hcard : ((Finset.Icc a a).card : ℝ) = 1 := by
    have hIcc : Finset.Icc a a = ({a} : Finset ℕ) :=
      Finset.Icc_self a
    have hcard_nat : (Finset.Icc a a).card = 1 := by
      calc
        (Finset.Icc a a).card = ({a} : Finset ℕ).card :=
          congrArg Finset.card hIcc
        _ = 1 :=
          Finset.card_singleton a
    calc
      ((Finset.Icc a a).card : ℝ) = ((1 : ℕ) : ℝ) :=
        congrArg (fun n : ℕ => (n : ℝ)) hcard_nat
      _ = 1 :=
        Nat.cast_one
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
    inv_nonneg.mpr hlam_pos.le
  have hone_le_four : (1 : ℝ) ≤ 4 * 1 := by
    exact real_one_le_four_mul_one_for_logarithmicPhase
  have hone_le_endpoint : (1 : ℝ) ≤ 4 * (lam⁻¹ + 1) := by
    have hone_le_sum : (1 : ℝ) ≤ lam⁻¹ + 1 :=
      le_add_of_nonneg_left hlam_inv_nonneg
    exact le_trans hone_le_four
      (mul_le_mul_of_nonneg_left hone_le_sum
        real_zero_le_four_for_logarithmicPhase)
  have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
    mul_nonneg real_zero_le_four_for_logarithmicPhase Real.pi_nonneg
  have hvariation_nonneg : 0 ≤ 4 * Real.pi * lam⁻¹ :=
    mul_nonneg hfour_pi_nonneg hlam_inv_nonneg
  have hone_le_target :
      (1 : ℝ) ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
    le_trans hone_le_endpoint
      (le_add_of_nonneg_right hvariation_nonneg)
  exact le_trans hblock
    (Eq.subst
      (motive := fun c : ℝ =>
        c ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
      hcard.symm
      hone_le_target)

/-- Reciprocal norm control from a positive denominator lower bound. -/
theorem Complex.realPhase_inv_norm_le_of_denominator_lower_bound
    {z : ℂ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hden : lam ≤ 2 * ‖z‖) :
    ‖z⁻¹‖ ≤ 2 * lam⁻¹ := by
  have hhalf_pos : 0 < lam / 2 := by
    exact real_div_two_pos_of_pos_for_logarithmicPhase hlam_pos
  have hnorm_lower : lam / 2 ≤ ‖z‖ := by
    have hden' : lam ≤ ‖z‖ * 2 := by
      exact Eq.subst (motive := fun r : ℝ => lam ≤ r) (mul_comm 2 ‖z‖) hden
    exact real_div_two_le_of_le_mul_two_for_logarithmicPhase hlam_pos hden'
  have hinv_mono : ‖z‖⁻¹ ≤ (lam / 2)⁻¹ :=
    inv_anti₀ hhalf_pos hnorm_lower
  have hhalf_inv : (lam / 2)⁻¹ = 2 * lam⁻¹ := by
    exact real_inv_div_two_eq_two_mul_inv_for_logarithmicPhase
  calc
    ‖z⁻¹‖ = ‖z‖⁻¹ :=
      norm_inv z
    _ ≤ (lam / 2)⁻¹ :=
      hinv_mono
    _ = 2 * lam⁻¹ :=
      hhalf_inv

/-- The `(-π, π]` representative is obtained by subtracting an integral
multiple of `2π`. -/
theorem Complex.realPhase_twoPi_toIocMod_integerDistance
    (θ : ℝ) :
    ∃ k : ℤ,
      θ - (2 * Real.pi * (k : ℝ)) =
        toIocMod Real.two_pi_pos (-Real.pi) θ := by
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ
  have howner :
      θ - k • ((2 * Real.pi) : ℝ) =
        toIocMod Real.two_pi_pos (-Real.pi) θ :=
    self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  have hzsmul :
      k • ((2 * Real.pi) : ℝ) = 2 * Real.pi * (k : ℝ) := by
    calc
      k • ((2 * Real.pi) : ℝ) = (k : ℝ) * (2 * Real.pi) := by
        exact zsmul_eq_mul (2 * Real.pi) k
      _ = 2 * Real.pi * (k : ℝ) := by
        exact mul_comm (k : ℝ) (2 * Real.pi)
  exact Exists.intro k
    (Eq.subst
      (motive := fun r : ℝ =>
        θ - r = toIocMod Real.two_pi_pos (-Real.pi) θ)
      hzsmul
      howner)

/-- Chord estimate for a reduced angle in `(-π, π]`. -/
theorem Complex.realPhase_reducedAngle_le_two_mul_chord_norm
    {ψ : ℝ}
    (hψ : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ‖ψ‖ ≤
      2 * ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
  have hψ_mod :
      toIocMod Real.two_pi_pos (-Real.pi) ψ = ψ := by
    exact (toIocMod_eq_self Real.two_pi_pos).mpr
      (real_mem_Ioc_pi_to_periodic_upper_for_logarithmicPhase hψ)
  have hangle :
        InnerProductGeometry.angle (Complex.exp ((ψ : ℂ) * Complex.I)) 1 = ‖ψ‖ := by
    have hangle_abs :
        InnerProductGeometry.angle (Complex.exp ((ψ : ℂ) * Complex.I)) 1 =
          |toIocMod Real.two_pi_pos (-Real.pi) ψ| :=
      Complex.angle_exp_one ψ
    have habs_norm :
        |toIocMod Real.two_pi_pos (-Real.pi) ψ| = ‖ψ‖ := by
      calc
        |toIocMod Real.two_pi_pos (-Real.pi) ψ| = |ψ| :=
          congrArg abs hψ_mod
        _ = ‖ψ‖ :=
          (Real.norm_eq_abs ψ).symm
    exact hangle_abs.trans habs_norm
  have hunit :
      ‖Complex.exp ((ψ : ℂ) * Complex.I)‖ = 1 := by
    have hcomm :
        Complex.exp ((ψ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (ψ : ℂ)) :=
      congrArg Complex.exp (mul_comm (ψ : ℂ) Complex.I)
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ = 1)
      hcomm.symm
      (Complex.realPhase_exp_I_norm (fun _ : ℝ => ψ) 0)
  have harc :
      ‖ψ‖ ≤
        Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ := by
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖)
      hangle
      (Complex.angle_le_mul_norm_sub hunit norm_one)
  have hconstant :
      Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ ≤
        2 * ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ := by
    have hpi_half : Real.pi / 2 ≤ (2 : ℝ) := by
      exact real_pi_div_two_le_two_for_logarithmicPhase
    exact mul_le_mul_of_nonneg_right hpi_half
      (norm_nonneg (Complex.exp ((ψ : ℂ) * Complex.I) - 1))
  have hnorm_transport :
      2 * ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
        2 * ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
    have hcomm_exp :
        Complex.exp ((ψ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (ψ : ℂ)) :=
      congrArg Complex.exp (mul_comm (ψ : ℂ) Complex.I)
    have hnorm :
        ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
          ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
      calc
        ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
            ‖Complex.exp (Complex.I * (ψ : ℂ)) - 1‖ :=
          congrArg (fun z : ℂ => ‖z - 1‖) hcomm_exp
        _ = ‖-(1 - Complex.exp (Complex.I * (ψ : ℂ)))‖ := by
          congr 1
          exact complex_sub_one_eq_neg_one_sub_for_logarithmicPhase
            (Complex.exp (Complex.I * (ψ : ℂ)))
        _ = ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ :=
          norm_neg (1 - Complex.exp (Complex.I * (ψ : ℂ)))
    exact congrArg (fun r : ℝ => 2 * r) hnorm
  exact le_trans harc
    (Eq.subst
      (motive := fun target : ℝ =>
        Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ ≤ target)
      hnorm_transport
      hconstant)

end

end LFunctions
end Boundary

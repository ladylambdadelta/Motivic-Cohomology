import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Angle
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Rat.Cast.Order

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Complex exponential period transport for real angles shifted by an integral
multiple of `2π`. -/
theorem Complex.exp_mul_I_real_sub_int_two_pi_period_for_logarithmicPhase
    (θ : ℝ)
    (k : ℤ) :
    Complex.exp (((θ - k • (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
  have hscalar : k • ((2 * Real.pi) : ℝ) = (k : ℝ) * (2 * Real.pi) :=
    zsmul_eq_mul (2 * Real.pi) k
  have harg :
      θ - k • ((2 * Real.pi) : ℝ) = θ - (k : ℝ) * (2 * Real.pi) :=
    congrArg (fun q : ℝ => θ - q) hscalar
  have hleft :
      Complex.exp (((θ - k • (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((θ - (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) :=
    congrArg (fun q : ℝ => Complex.exp ((q : ℂ) * Complex.I)) harg
  have htwo_pi_cast :
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) =
        2 * ↑Real.pi * Complex.I := by
    exact congrArg (fun q : ℂ => q * Complex.I)
      (Complex.ofReal_mul 2 Real.pi)
  have hsub :
      (((θ - (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
        (θ : ℂ) * Complex.I - (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    calc
      (((θ - (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
          =
          (((θ : ℂ) - (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) *
            Complex.I) := by
            exact congrArg (fun q : ℂ => q * Complex.I)
              (Complex.ofReal_sub θ ((k : ℝ) * (2 * Real.pi)))
      _ =
          (((θ : ℂ) - ((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ))) *
            Complex.I) := by
            exact congrArg
              (fun q : ℂ => ((θ : ℂ) - q) * Complex.I)
              (Complex.ofReal_mul (k : ℝ) (2 * Real.pi))
      _ =
          (θ : ℂ) * Complex.I -
            (((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) * Complex.I) := by
            exact sub_mul
              (θ : ℂ)
              ((k : ℂ) * ((2 * Real.pi : ℝ) : ℂ))
              Complex.I
      _ =
          (θ : ℂ) * Complex.I -
            (k : ℂ) * (((2 * Real.pi : ℝ) : ℂ) * Complex.I) := by
            exact congrArg
              (fun q : ℂ => (θ : ℂ) * Complex.I - q)
              (mul_assoc (k : ℂ) ((2 * Real.pi : ℝ) : ℂ) Complex.I)
      _ =
          (θ : ℂ) * Complex.I - (k : ℂ) * (2 * ↑Real.pi * Complex.I) := by
            exact congrArg
              (fun q : ℂ => (θ : ℂ) * Complex.I - (k : ℂ) * q)
              htwo_pi_cast
  have hperiod :
      Complex.exp ((θ : ℂ) * Complex.I - (k : ℂ) * (2 * ↑Real.pi * Complex.I)) =
        Complex.exp ((θ : ℂ) * Complex.I) :=
    Complex.exp_periodic.sub_int_mul_eq k
  exact Eq.trans hleft (Eq.trans (congrArg Complex.exp hsub) hperiod)

/-- Period transport for the chord denominator. -/
theorem Complex.realPhase_geometricDenominator_norm_eq_toIocMod
    (θ : ℝ) :
    ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ =
      ‖1 -
        Complex.exp
          (Complex.I *
            ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ))‖ := by
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ
  have hmod :
      θ - k • ((2 * Real.pi) : ℝ) =
        toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ :=
    self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  have hperiod :
      Complex.exp
          (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    have hraw :
        Complex.exp (((θ - k • (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
      exact Complex.exp_mul_I_real_sub_int_two_pi_period_for_logarithmicPhase θ k
    have hmod_complex :
        (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) =
          ((θ - k • ((2 * Real.pi) : ℝ) : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hmod.symm
    exact Eq.trans
      (congrArg
        (fun z : ℂ => Complex.exp (z * Complex.I))
        hmod_complex)
      hraw
  have hleft_comm :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    exact congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  have hright_comm :
      Complex.exp
          (Complex.I * ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) =
        Complex.exp
          (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.exp
      (mul_comm Complex.I ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ))
  have hexp :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp
          (Complex.I * ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) := by
    exact Eq.trans hleft_comm (Eq.trans hperiod.symm hright_comm.symm)
  exact congrArg (fun z : ℂ => ‖1 - z‖) hexp

/-- Nearest-period representative chord estimate for the real unit circle. -/
theorem Complex.realPhase_twoPi_integerDistance_le_two_mul_chord_norm
    (θ : ℝ) :
    ∃ k : ℤ,
      ‖θ - (2 * Real.pi * (k : ℝ))‖ ≤
        2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
  match Complex.realPhase_twoPi_toIocMod_integerDistance θ with
  | ⟨k, hk⟩ =>
    have hmem :
        toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ ∈
          Set.Ioc (-Real.pi) Real.pi := by
      exact real_toIocMod_mem_Ioc_pi_for_logarithmicPhase θ
    have hred :
        ‖toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ‖ ≤
          2 *
            ‖1 -
              Complex.exp
                (Complex.I *
                  ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ))‖ :=
      Complex.realPhase_reducedAngle_le_two_mul_chord_norm hmem
    have hperiod :
        2 *
            ‖1 -
              Complex.exp
                (Complex.I *
                  ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ))‖ =
          2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
      exact congrArg (fun r : ℝ => 2 * r)
        (Complex.realPhase_geometricDenominator_norm_eq_toIocMod θ).symm
    exact Exists.intro k
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖x‖ ≤ 2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖)
        hk.symm
        (Eq.subst
          (motive := fun target : ℝ =>
            ‖toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ‖ ≤ target)
          hperiod
          hred))

/-- Chord lower bound on the unit circle from separation from `2πℤ`.

This is the real trigonometric core behind the geometric denominator estimate:
the nearest `2πℤ` distance to `θ` is controlled by the chord length
`|1 - exp(iθ)|`. -/
theorem Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
    {θ lam : ℝ}
    (hlam_pos : 0 < lam)
    (hsep : ∀ k : ℤ, lam ≤ ‖θ - (2 * Real.pi * (k : ℝ))‖) :
    lam ≤ 2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
  match Complex.realPhase_twoPi_integerDistance_le_two_mul_chord_norm θ with
  | ⟨k, hk⟩ =>
    exact le_trans (hsep k) hk

/-- Geometric denominator lower bound from separation from all `2πℤ`
frequencies.

The classical estimate is
`|1 - exp(iθ)| = 2 |sin(θ/2)|`, together with the chord lower bound on the
circle and `π ≤ 4`; the stated reciprocal form is the one used by the finite
Dirichlet-test assembly. -/
theorem Complex.realPhase_geometricDenominator_inv_norm_bound
    {θ lam : ℝ}
    (hlam_pos : 0 < lam)
    (hsep : ∀ k : ℤ, lam ≤ ‖θ - (2 * Real.pi * (k : ℝ))‖) :
    ‖(1 - Complex.exp (Complex.I * (θ : ℂ)))⁻¹‖ ≤
      2 * lam⁻¹ := by
  exact
    Complex.realPhase_inv_norm_le_of_denominator_lower_bound
      hlam_pos
      (Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
        hlam_pos hsep)

/-- Endpoint contribution in the finite monotone-increment Dirichlet test. -/
theorem Complex.realPhase_monotoneIncrement_dirichlet_endpoint_bound
    {lam : ℝ}
    (hlam_pos : 0 < lam) :
    (1 : ℝ) ≤ 2 * (lam⁻¹ + 1) := by
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
    inv_nonneg.mpr hlam_pos.le
  have hone_le_sum : (1 : ℝ) ≤ lam⁻¹ + 1 :=
    le_add_of_nonneg_left hlam_inv_nonneg
  exact le_trans hone_le_sum
    (by
      have hsum_nonneg : 0 ≤ lam⁻¹ + 1 :=
        add_nonneg hlam_inv_nonneg zero_le_one
      calc
        lam⁻¹ + 1 ≤ 2 * (lam⁻¹ + 1) := by
          exact real_sum_le_two_mul_self_of_nonneg_for_logarithmicPhase
            hsum_nonneg
        _ = 2 * (lam⁻¹ + 1) := rfl)

/-- Finite Abel-transform norm assembly for one prefix. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_norm_assembly
    {S boundary variation : ℂ}
    {lam : ℝ}
    (hS : S = boundary + variation)
    (hboundary : ‖boundary‖ ≤ 4 * (lam⁻¹ + 1))
    (hvariation : ‖variation‖ ≤ 4 * Real.pi * lam⁻¹) :
    ‖S‖ ≤ 4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  have hnorm :
      ‖S‖ ≤ ‖boundary‖ + ‖variation‖ := by
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ‖boundary‖ + ‖variation‖)
      hS.symm
      (norm_add_le boundary variation)
  have hsum :
      ‖boundary‖ + ‖variation‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
    add_le_add hboundary hvariation
  exact le_trans hnorm hsum

/-- Singleton prefix in the finite Abel transform: the whole prefix is an
endpoint term and the variation term is zero. -/
theorem Complex.realPhase_monotoneIncrement_singleton_prefix_abel_terms_bounded
    (φ : ℝ → ℝ)
    (a : ℕ)
    {lam : ℝ}
    (hlam_pos : 0 < lam) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a a,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * Real.pi * lam⁻¹ := by
  let boundary : ℂ :=
    ∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))
  let variation : ℂ := 0
  have hsum_eq :
      (∑ n ∈ Finset.Icc a a,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation :=
    (add_zero boundary).symm
  have hboundary_bound :
      ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) := by
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
    have hone_bound :
        (1 : ℝ) ≤ 2 * (lam⁻¹ + 1) :=
      Complex.realPhase_monotoneIncrement_dirichlet_endpoint_bound hlam_pos
    exact le_trans hblock
      (Eq.subst
        (motive := fun c : ℝ => c ≤ 4 * (lam⁻¹ + 1))
        hcard.symm
        (le_trans hone_bound
          (by
            have hsum_nonneg : 0 ≤ lam⁻¹ + 1 :=
              add_nonneg (inv_nonneg.mpr hlam_pos.le) zero_le_one
            exact mul_le_mul_of_nonneg_right
              real_two_le_four_for_logarithmicPhase
              hsum_nonneg)))
  have hvariation_bound :
      ‖variation‖ ≤ 4 * Real.pi * lam⁻¹ := by
    have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
      inv_nonneg.mpr hlam_pos.le
    have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
      mul_nonneg real_zero_le_four_for_logarithmicPhase
        (le_of_lt Real.pi_pos)
    have htarget_nonneg : 0 ≤ 4 * Real.pi * lam⁻¹ :=
      mul_nonneg hfour_pi_nonneg hlam_inv_nonneg
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * Real.pi * lam⁻¹)
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      htarget_nonneg
  exact Exists.intro boundary
    (Exists.intro variation
      (And.intro hsum_eq
        (And.intro hboundary_bound hvariation_bound)))

/-- Separation from `2πℤ` makes the finite Abel geometric denominator
nonzero. -/
theorem Complex.realPhase_geometricDenominator_ne_zero_of_separatedIncrement
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hn : n ∈ Finset.Ico a b) :
    (1 -
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerIncrement φ n : ℂ))) ≠ 0 := by
  intro hzero
  have hlower :
      lam ≤
        2 *
          ‖1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ))‖ :=
    Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
      hlam_pos
      (hsep n hn)
  have hright_zero :
      (2 : ℝ) *
          ‖1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ))‖ =
        0 := by
    calc
      (2 : ℝ) *
          ‖1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ))‖ =
          (2 : ℝ) * ‖(0 : ℂ)‖ := by
        exact congrArg (fun z : ℂ => (2 : ℝ) * ‖z‖) hzero
      _ = (2 : ℝ) * 0 := by
        exact congrArg (fun r : ℝ => (2 : ℝ) * r) (norm_zero : ‖(0 : ℂ)‖ = 0)
      _ = 0 := by
        exact mul_zero (2 : ℝ)
  have hlam_nonpos : lam ≤ 0 :=
    Eq.subst
      (motive := fun r : ℝ => lam ≤ r)
      hright_zero
      hlower
  exact (not_le_of_gt hlam_pos) hlam_nonpos

/-- The one-step geometric denominator inverts the finite phase difference. -/
theorem Complex.realPhase_geometricDenominator_inv_mul_step_difference
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hn : n ∈ Finset.Ico a b) :
    ((1 -
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹) *
      (Complex.exp (Complex.I * (φ n : ℂ)) -
        Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ))) =
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  let u : ℂ := Complex.exp (Complex.I * (φ n : ℂ))
  let r : ℂ :=
    Complex.exp
      (Complex.I *
        (Complex.realPhase_integerIncrement φ n : ℂ))
  have hstep :
      Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ)) = u * r := by
    have hphase :
        Complex.I * (φ (n + 1 : ℕ) : ℂ) =
          Complex.I * (φ n : ℂ) +
            Complex.I *
              (Complex.realPhase_integerIncrement φ n : ℂ) := by
      have hsub :
          ((φ (n + 1 : ℕ) - φ n : ℝ) : ℂ) =
            (φ (n + 1 : ℕ) : ℂ) - (φ n : ℂ) :=
        Complex.ofReal_sub (φ (n + 1 : ℕ)) (φ n)
      calc
        Complex.I * (φ (n + 1 : ℕ) : ℂ) =
            Complex.I * (φ n : ℂ) +
              Complex.I * ((φ (n + 1 : ℕ) : ℂ) - (φ n : ℂ)) :=
          complex_I_mul_eq_I_mul_add_I_mul_sub_for_logarithmicPhase
            (φ n : ℂ)
            (φ (n + 1 : ℕ) : ℂ)
        _ = Complex.I * (φ n : ℂ) +
              Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ) := by
          exact congrArg
            (fun z : ℂ => Complex.I * (φ n : ℂ) + Complex.I * z)
            hsub.symm
    calc
      Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ)) =
          Complex.exp
            (Complex.I * (φ n : ℂ) +
              Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)) := by
        exact congrArg Complex.exp hphase
      _ = u * r :=
        Complex.exp_add
          (Complex.I * (φ n : ℂ))
          (Complex.I *
            (Complex.realPhase_integerIncrement φ n : ℂ))
  have hden_ne :
      (1 - r) ≠ 0 := by
    exact
      Complex.realPhase_geometricDenominator_ne_zero_of_separatedIncrement
        φ hlam_pos hsep hn
  calc
    ((1 - r)⁻¹) *
        (u - Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ))) =
        ((1 - r)⁻¹) * (u - u * r) := by
      exact congrArg (fun z : ℂ => ((1 - r)⁻¹) * (u - z)) hstep
    _ = ((1 - r)⁻¹) * (u * (1 - r)) := by
      congr 1
      exact complex_sub_mul_self_eq_mul_one_sub_for_logarithmicPhase u r
    _ = u := by
      exact complex_inv_mul_mul_right_cancel_for_logarithmicPhase hden_ne

/-- Inverse geometric denominator attached to an adjacent integer phase
increment. -/
def Complex.realPhase_inverseGeometricDenominator
    (φ : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  (1 -
    Complex.exp
      (Complex.I *
        (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹

/-- Unit-modulus phase sample used in the finite Abel transform. -/
def Complex.realPhase_integerUnit
    (φ : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (φ n : ℂ))

/-- Endpoint term in the non-singleton finite Abel transform. -/
def Complex.realPhase_prefixAbelBoundary
    (φ : ℝ → ℝ)
    (a m : ℕ) : ℂ :=
  Complex.realPhase_inverseGeometricDenominator φ a *
      Complex.realPhase_integerUnit φ a +
    (1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
      Complex.realPhase_integerUnit φ m

/-- Variation term in the non-singleton finite Abel transform. -/
def Complex.realPhase_prefixAbelVariation
    (φ : ℝ → ℝ)
    (a m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioo a m,
    (Complex.realPhase_inverseGeometricDenominator φ n -
        Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
      Complex.realPhase_integerUnit φ n

/-- Generic finite Abel telescoping identity over `Ico`. -/
theorem Complex.finiteAbel_Ico_mul_sub_telescope
    (A u : ℕ → ℂ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
      A a * u a - A (m - 1) * u m +
        ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n := by
  revert a
  induction m with
  | zero =>
      intro a ham
      exact False.elim ((Nat.not_lt_zero a) ham)
  | succ m ih =>
      intro a ham
      match lt_or_eq_of_le (Nat.le_of_lt_succ ham) with
      | Or.inl ham_strict =>
        have hIco :
            Finset.Ico a (m + 1) = insert m (Finset.Ico a m) := by
          exact Nat.Ico_succ_right_eq_insert_Ico (Nat.le_of_lt ham_strict)
        have hIoo :
            Finset.Ioo a (m + 1) = insert m (Finset.Ioo a m) := by
          ext n
          constructor
          · intro hn
            have hn_bounds : a < n ∧ n < m + 1 :=
              Finset.mem_Ioo.mp hn
            match (inferInstance : Decidable (n = m)) with
            | isTrue hnm =>
                exact Finset.mem_insert.mpr (Or.inl hnm)
            | isFalse hnm =>
                have hn_lt_m : n < m :=
                  match Nat.lt_succ_iff_lt_or_eq.mp hn_bounds.right with
                  | Or.inl hn_lt_m => hn_lt_m
                  | Or.inr hn_eq_m => False.elim (hnm hn_eq_m)
                exact Finset.mem_insert.mpr
                  (Or.inr (Finset.mem_Ioo.mpr ⟨hn_bounds.left, hn_lt_m⟩))
          · intro hn
            match Finset.mem_insert.mp hn with
            | Or.inl hm_eq =>
                exact Finset.mem_Ioo.mpr
                  ⟨Eq.subst (motive := fun q : ℕ => a < q) hm_eq.symm ham_strict,
                    Eq.subst (motive := fun q : ℕ => q < m + 1) hm_eq.symm
                      (Nat.lt_succ_self m)⟩
            | Or.inr hn_inner =>
                have hn_bounds : a < n ∧ n < m :=
                  Finset.mem_Ioo.mp hn_inner
                exact Finset.mem_Ioo.mpr
                  ⟨hn_bounds.left, lt_trans hn_bounds.right (Nat.lt_succ_self m)⟩
        have hm_not_Ico : m ∉ Finset.Ico a m :=
          Finset.right_not_mem_Ico
        have hm_not_Ioo : m ∉ Finset.Ioo a m :=
          Finset.right_not_mem_Ioo
        have hind :
            (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
              A a * u a - A (m - 1) * u m +
                ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
          ih ham_strict
        calc
          (∑ n ∈ Finset.Ico a (m + 1), A n * (u n - u (n + 1))) =
              ∑ n ∈ insert m (Finset.Ico a m),
                A n * (u n - u (n + 1)) := by
            exact congrArg
              (fun s : Finset ℕ =>
                ∑ n ∈ s, A n * (u n - u (n + 1)))
              hIco
          _ =
              A m * (u m - u (m + 1)) +
                ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) :=
            Finset.sum_insert hm_not_Ico
          _ =
              A m * (u m - u (m + 1)) +
                (A a * u a - A (m - 1) * u m +
                  ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n) := by
            exact congrArg
              (fun z : ℂ => A m * (u m - u (m + 1)) + z)
              hind
          _ =
              A a * u a - A m * u (m + 1) +
                ∑ n ∈ insert m (Finset.Ioo a m),
                  (A n - A (n - 1)) * u n := by
            calc
              A m * (u m - u (m + 1)) +
                  (A a * u a - A (m - 1) * u m +
                    ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n)
                  =
                  (A m * u m - A m * u (m + 1)) +
                    (A a * u a - A (m - 1) * u m +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n) := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      (A a * u a - A (m - 1) * u m +
                        ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n))
                  (mul_sub (A m) (u m) (u (m + 1)))
              _ =
                  A a * u a - A m * u (m + 1) +
                    (A m * u m - A (m - 1) * u m) +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n := by
                exact complex_finiteAbel_successor_reassociate_for_logarithmicPhase
                  (A a * u a)
                  (A (m - 1) * u m)
                  (A m * u m)
                  (A m * u (m + 1))
                  (∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n)
              _ =
                  A a * u a - A m * u (m + 1) +
                    (A m * u m - A (m - 1) * u m) +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n := by
                rfl
              _ =
                  A a * u a - A m * u (m + 1) +
                    ((A m * u m - A (m - 1) * u m) +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n) := by
                exact add_assoc
                  (A a * u a - A m * u (m + 1))
                  (A m * u m - A (m - 1) * u m)
                  (∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n)
              _ =
                  A a * u a - A m * u (m + 1) +
                    ((A m - A (m - 1)) * u m +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n) := by
                exact congrArg
                  (fun z : ℂ =>
                    A a * u a - A m * u (m + 1) +
                      (z +
                        ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n))
                  (sub_mul (A m) (A (m - 1)) (u m)).symm
              _ =
                  A a * u a - A m * u (m + 1) +
                    ∑ n ∈ insert m (Finset.Ioo a m),
                      (A n - A (n - 1)) * u n := by
                exact congrArg
                  (fun z : ℂ => A a * u a - A m * u (m + 1) + z)
                  (Eq.symm
                    (Finset.sum_insert
                      (s := Finset.Ioo a m)
                      (a := m)
                      (f := fun n : ℕ => (A n - A (n - 1)) * u n)
                      hm_not_Ioo))
          _ =
              A a * u a - A m * u (m + 1) +
                ∑ n ∈ Finset.Ioo a (m + 1), (A n - A (n - 1)) * u n := by
            exact
              congrArg
                (fun s : Finset ℕ =>
                  A a * u a - A m * u (m + 1) +
                    ∑ n ∈ s, (A n - A (n - 1)) * u n)
                hIoo.symm
          _ =
              A a * u a - A ((m + 1) - 1) * u (m + 1) +
                ∑ n ∈ Finset.Ioo a (m + 1), (A n - A (n - 1)) * u n := by
            exact congrArg
              (fun q : ℕ =>
                A a * u a - A q * u (m + 1) +
                  ∑ n ∈ Finset.Ioo a (m + 1), (A n - A (n - 1)) * u n)
              (Nat.succ_sub_one m).symm
      | Or.inr rfl =>
        have hIco : Finset.Ico a (a + 1) = ({a} : Finset ℕ) :=
          Nat.Ico_succ_singleton a
        have hIoo : Finset.Ioo a (a + 1) = (∅ : Finset ℕ) := by
          ext n
          constructor
          · intro hn
            have hn_bounds : a < n ∧ n < a + 1 :=
              Finset.mem_Ioo.mp hn
            exact False.elim
              ((Nat.not_lt_of_ge (Nat.succ_le_of_lt hn_bounds.left))
                hn_bounds.right)
          · intro hn
            exact False.elim (Finset.not_mem_empty n hn)
        calc
          (∑ n ∈ Finset.Ico a (a + 1), A n * (u n - u (n + 1))) =
              A a * (u a - u (a + 1)) := by
            calc
              ∑ n ∈ Finset.Ico a (a + 1), A n * (u n - u (n + 1))
                  = ∑ n ∈ ({a} : Finset ℕ), A n * (u n - u (n + 1)) := by
                exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, A n * (u n - u (n + 1))) hIco
              _ = A a * (u a - u (a + 1)) := by
                exact Finset.sum_singleton (fun n : ℕ => A n * (u n - u (n + 1))) a
          _ =
              A a * u a - A ((a + 1) - 1) * u (a + 1) +
                ∑ n ∈ Finset.Ioo a (a + 1), (A n - A (n - 1)) * u n := by
            calc
              A a * (u a - u (a + 1))
                  = A a * u a - A ((a + 1) - 1) * u (a + 1) := by
                    exact complex_finiteAbel_singleton_step_for_logarithmicPhase A u a
              _ = A a * u a - A ((a + 1) - 1) * u (a + 1) +
                  ∑ n ∈ Finset.Ioo a (a + 1), (A n - A (n - 1)) * u n := by
                calc
                  A a * u a - A ((a + 1) - 1) * u (a + 1) =
                      A a * u a - A ((a + 1) - 1) * u (a + 1) +
                        ∑ n ∈ (∅ : Finset ℕ), (A n - A (n - 1)) * u n := by
                    exact (add_zero
                      (A a * u a - A ((a + 1) - 1) * u (a + 1))).symm
                  _ =
                      A a * u a - A ((a + 1) - 1) * u (a + 1) +
                        ∑ n ∈ Finset.Ioo a (a + 1), (A n - A (n - 1)) * u n := by
                    exact congrArg
                      (fun s : Finset ℕ =>
                        A a * u a - A ((a + 1) - 1) * u (a + 1) +
                          ∑ n ∈ s, (A n - A (n - 1)) * u n)
                      hIoo.symm

/-- Exact `Ico` telescoping form of the finite Abel transform. -/
theorem Complex.realPhase_prefixAbel_Ico_telescope
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    (∑ n ∈ Finset.Ico a m,
      Complex.realPhase_integerUnit φ n) =
        Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
          Complex.realPhase_integerUnit φ m +
        Complex.realPhase_prefixAbelVariation φ a m := by
  let A : ℕ → ℂ := Complex.realPhase_inverseGeometricDenominator φ
  let u : ℕ → ℂ := Complex.realPhase_integerUnit φ
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hterm :
      (∑ n ∈ Finset.Ico a m, u n) =
        ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        have hn_block : n ∈ Finset.Ico a b :=
          Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
        have hstep :
            A n * (u n - u (n + 1)) = u n := by
          unfold A u Complex.realPhase_inverseGeometricDenominator
            Complex.realPhase_integerUnit
          exact
            Complex.realPhase_geometricDenominator_inv_mul_step_difference
              φ hlam_pos hsep hn_block
        hstep.symm)
  have htelescope :
      (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
        A a * u a - A (m - 1) * u m +
          ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
    Complex.finiteAbel_Ico_mul_sub_telescope A u ham
  calc
    (∑ n ∈ Finset.Ico a m,
      Complex.realPhase_integerUnit φ n) =
        (∑ n ∈ Finset.Ico a m, u n) := by
      rfl
    _ = ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) :=
      hterm
    _ =
        A a * u a - A (m - 1) * u m +
          ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
      htelescope
    _ =
        Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a -
        Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
          Complex.realPhase_integerUnit φ m +
        Complex.realPhase_prefixAbelVariation φ a m := by
      unfold A u Complex.realPhase_prefixAbelVariation
      rfl

/-- The exact finite Abel identity for the non-singleton phase prefix. -/
theorem Complex.realPhase_prefixAbel_identity
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    (∑ n ∈ Finset.Icc a m,
      Complex.realPhase_integerUnit φ n) =
        Complex.realPhase_prefixAbelBoundary φ a m +
          Complex.realPhase_prefixAbelVariation φ a m := by
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hsplit :
      (∑ n ∈ Finset.Icc a m,
        Complex.realPhase_integerUnit φ n) =
          (∑ n ∈ Finset.Ico a m,
            Complex.realPhase_integerUnit φ n) +
            Complex.realPhase_integerUnit φ m := by
    have hinsert :
        insert m (Finset.Ico a m) = Finset.Icc a m :=
      Finset.Ico_insert_right hm_bounds.1
    have hnot : m ∉ Finset.Ico a m :=
      Finset.right_not_mem_Ico
    calc
      (∑ n ∈ Finset.Icc a m,
        Complex.realPhase_integerUnit φ n) =
          ∑ n ∈ insert m (Finset.Ico a m),
            Complex.realPhase_integerUnit φ n := by
        exact congrArg
          (fun s : Finset ℕ =>
            ∑ n ∈ s, Complex.realPhase_integerUnit φ n)
          hinsert.symm
      _ =
          Complex.realPhase_integerUnit φ m +
            ∑ n ∈ Finset.Ico a m,
              Complex.realPhase_integerUnit φ n :=
        Finset.sum_insert hnot
      _ =
          (∑ n ∈ Finset.Ico a m,
            Complex.realPhase_integerUnit φ n) +
            Complex.realPhase_integerUnit φ m :=
        add_comm _ _
  have htelescope :
      (∑ n ∈ Finset.Ico a m,
        Complex.realPhase_integerUnit φ n) =
          Complex.realPhase_inverseGeometricDenominator φ a *
            Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
            Complex.realPhase_integerUnit φ m +
          Complex.realPhase_prefixAbelVariation φ a m :=
    Complex.realPhase_prefixAbel_Ico_telescope
      φ ham hm hlam_pos hsep
  calc
    (∑ n ∈ Finset.Icc a m,
      Complex.realPhase_integerUnit φ n) =
        (∑ n ∈ Finset.Ico a m,
          Complex.realPhase_integerUnit φ n) +
          Complex.realPhase_integerUnit φ m :=
      hsplit
    _ =
        (Complex.realPhase_inverseGeometricDenominator φ a *
            Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
            Complex.realPhase_integerUnit φ m +
          Complex.realPhase_prefixAbelVariation φ a m) +
          Complex.realPhase_integerUnit φ m := by
      exact congrArg
        (fun z : ℂ => z + Complex.realPhase_integerUnit φ m)
        htelescope
    _ =
        Complex.realPhase_prefixAbelBoundary φ a m +
          Complex.realPhase_prefixAbelVariation φ a m := by
      unfold Complex.realPhase_prefixAbelBoundary
      exact complex_prefixAbel_boundary_rearrange_for_logarithmicPhase
        (Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a)
        (Complex.realPhase_inverseGeometricDenominator φ (m - 1))
        (Complex.realPhase_integerUnit φ m)
        (Complex.realPhase_prefixAbelVariation φ a m)

/-- Endpoint estimate for the explicit finite Abel boundary term. -/
theorem Complex.realPhase_prefixAbelBoundary_norm_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * lam⁻¹) :
    ‖Complex.realPhase_prefixAbelBoundary φ a m‖ ≤
      4 * (lam⁻¹ + 1) := by
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_mem : a ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr ⟨le_rfl, lt_of_lt_of_le ham hm_bounds.2⟩
  have hm_pred_mem : m - 1 ∈ Finset.Ico a b := by
    have ha_pred : a ≤ m - 1 :=
      Nat.le_pred_of_lt ham
    have hm_pos : 0 < m :=
      lt_of_le_of_lt (Nat.zero_le a) ham
    have hpred_lt_m : m - 1 < m :=
      Nat.pred_lt (Nat.ne_of_gt hm_pos)
    have hpred_lt_b : m - 1 < b :=
      lt_of_lt_of_le hpred_lt_m hm_bounds.2
    exact Finset.mem_Ico.mpr ⟨ha_pred, hpred_lt_b⟩
  have ha_den :
      ‖Complex.realPhase_inverseGeometricDenominator φ a‖ ≤
        2 * lam⁻¹ :=
    hden a ha_mem
  have hm_den :
      ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
        2 * lam⁻¹ :=
    hden (m - 1) hm_pred_mem
  have ha_unit :
      ‖Complex.realPhase_integerUnit φ a‖ = 1 :=
    Complex.realPhase_exp_I_norm φ a
  have hm_unit :
      ‖Complex.realPhase_integerUnit φ m‖ = 1 :=
    Complex.realPhase_exp_I_norm φ m
  have hfirst :
      ‖Complex.realPhase_inverseGeometricDenominator φ a *
        Complex.realPhase_integerUnit φ a‖ ≤ 2 * lam⁻¹ := by
    calc
      ‖Complex.realPhase_inverseGeometricDenominator φ a *
        Complex.realPhase_integerUnit φ a‖ =
          ‖Complex.realPhase_inverseGeometricDenominator φ a‖ *
            ‖Complex.realPhase_integerUnit φ a‖ :=
        norm_mul
          (Complex.realPhase_inverseGeometricDenominator φ a)
          (Complex.realPhase_integerUnit φ a)
      _ = ‖Complex.realPhase_inverseGeometricDenominator φ a‖ * 1 := by
        exact congrArg
          (fun r : ℝ =>
            ‖Complex.realPhase_inverseGeometricDenominator φ a‖ * r)
          ha_unit
      _ = ‖Complex.realPhase_inverseGeometricDenominator φ a‖ :=
        mul_one _
      _ ≤ 2 * lam⁻¹ :=
        ha_den
  have hsecond :
      ‖(1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
        Complex.realPhase_integerUnit φ m‖ ≤ 1 + 2 * lam⁻¹ := by
    have hfactor :
        ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
          1 + 2 * lam⁻¹ := by
      calc
        ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
            ‖(1 : ℂ)‖ +
              ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ := by
          exact norm_sub_le 1
            (Complex.realPhase_inverseGeometricDenominator φ (m - 1))
        _ = 1 +
              ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ := by
          exact congrArg
            (fun r : ℝ =>
              r + ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖)
            norm_one
        _ ≤ 1 + 2 * lam⁻¹ :=
          add_le_add_left hm_den 1
    calc
      ‖(1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
        Complex.realPhase_integerUnit φ m‖ =
          ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ *
            ‖Complex.realPhase_integerUnit φ m‖ :=
        norm_mul
          (1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1))
          (Complex.realPhase_integerUnit φ m)
      _ = ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ * 1 := by
        exact congrArg
          (fun r : ℝ =>
            ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ * r)
          hm_unit
      _ = ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ :=
        mul_one _
      _ ≤ 1 + 2 * lam⁻¹ :=
        hfactor
  have hboundary :
      ‖Complex.realPhase_prefixAbelBoundary φ a m‖ ≤
        2 * lam⁻¹ + (1 + 2 * lam⁻¹) := by
    unfold Complex.realPhase_prefixAbelBoundary
    exact le_trans
      (norm_add_le
        (Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a)
        ((1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
          Complex.realPhase_integerUnit φ m))
      (add_le_add hfirst hsecond)
  have hlam_inv_nonneg : 0 ≤ lam⁻¹ :=
    inv_nonneg.mpr hlam_pos.le
  have htarget :
      2 * lam⁻¹ + (1 + 2 * lam⁻¹) ≤
        4 * (lam⁻¹ + 1) := by
    have hone_le_four : (1 : ℝ) ≤ 4 :=
      Eq.subst
        (motive := fun r : ℝ => (1 : ℝ) ≤ r)
        (mul_one (4 : ℝ))
        real_one_le_four_mul_one_for_logarithmicPhase
    have hleft_reorder :
        2 * lam⁻¹ + (1 + 2 * lam⁻¹) =
          (2 * lam⁻¹ + 2 * lam⁻¹) + 1 := by
      calc
        2 * lam⁻¹ + (1 + 2 * lam⁻¹) =
            2 * lam⁻¹ + (2 * lam⁻¹ + 1) :=
          congrArg (fun r : ℝ => 2 * lam⁻¹ + r)
            (add_comm 1 (2 * lam⁻¹))
        _ = (2 * lam⁻¹ + 2 * lam⁻¹) + 1 :=
          (add_assoc (2 * lam⁻¹) (2 * lam⁻¹) 1).symm
    have hleft_fold :
        (2 * lam⁻¹ + 2 * lam⁻¹) + 1 =
          4 * lam⁻¹ + 1 :=
      congrArg (fun r : ℝ => r + 1)
        (real_two_mul_add_two_mul_eq_four_mul_for_logarithmicPhase lam⁻¹)
    have hleft_eq :
        2 * lam⁻¹ + (1 + 2 * lam⁻¹) =
          4 * lam⁻¹ + 1 :=
      Eq.trans hleft_reorder hleft_fold
    have htarget_expand :
        4 * (lam⁻¹ + 1) = 4 * lam⁻¹ + 4 := by
      calc
        4 * (lam⁻¹ + 1) = 4 * lam⁻¹ + 4 * 1 :=
          mul_add (4 : ℝ) lam⁻¹ 1
        _ = 4 * lam⁻¹ + 4 :=
          congrArg (fun r : ℝ => 4 * lam⁻¹ + r)
            (mul_one (4 : ℝ))
    have hcore :
        4 * lam⁻¹ + 1 ≤ 4 * lam⁻¹ + 4 :=
      add_le_add_left hone_le_four (4 * lam⁻¹)
    exact Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 4 * (lam⁻¹ + 1))
      hleft_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          4 * lam⁻¹ + 1 ≤ right)
        htarget_expand.symm
        hcore)
  exact le_trans hboundary htarget

/-- Separation from `2πℤ` descends to separation of the reduced increment from
zero in the fundamental interval. -/
theorem Complex.realPhase_reducedIntegerIncrement_norm_lower_bound
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {lam : ℝ}
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hn : n ∈ Finset.Ico a b) :
    lam ≤ ‖Complex.realPhase_reducedIntegerIncrement φ n‖ := by
  match
    Complex.realPhase_twoPi_toIocMod_integerDistance
      (Complex.realPhase_integerIncrement φ n) with
  | ⟨k, hk⟩ =>
    have hsep_k :
        lam ≤
          ‖Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ))‖ :=
      hsep n hn k
    exact Eq.subst
      (motive := fun x : ℝ => lam ≤ ‖x‖)
      hk
      hsep_k

/-- The inverse geometric denominator is unchanged by reducing the increment
to the fundamental interval. -/
theorem Complex.realPhase_inverseGeometricDenominator_eq_reduced
    (φ : ℝ → ℝ)
    (n : ℕ) :
    Complex.realPhase_inverseGeometricDenominator φ n =
      (1 -
        Complex.exp
          (Complex.I *
            (Complex.realPhase_reducedIntegerIncrement φ n : ℂ)))⁻¹ := by
  unfold Complex.realPhase_inverseGeometricDenominator
    Complex.realPhase_reducedIntegerIncrement
  let θ : ℝ := Complex.realPhase_integerIncrement φ n
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ
  have hmod :
      θ - k • ((2 * Real.pi) : ℝ) =
        toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ :=
    self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  have hperiod :
      Complex.exp
          (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ) *
            Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    have hraw :
        Complex.exp (((θ - k • (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
      exact Complex.exp_mul_I_real_sub_int_two_pi_period_for_logarithmicPhase θ k
    have hmod_complex :
        (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) =
          ((θ - k • ((2 * Real.pi) : ℝ) : ℝ) : ℂ) :=
      congrArg (fun x : ℝ => (x : ℂ)) hmod.symm
    exact Eq.trans
      (congrArg
        (fun z : ℂ => Complex.exp (z * Complex.I))
        hmod_complex)
      hraw
  have hleft_comm :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) :=
    congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  have hright_comm :
      Complex.exp
          (Complex.I *
            ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) =
        Complex.exp
          (((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ) *
            Complex.I) :=
    congrArg Complex.exp
      (mul_comm Complex.I
        ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ))
  have hexp :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp
          (Complex.I *
            ((toIocMod (α := ℝ) Real.two_pi_pos (-Real.pi) θ : ℝ) : ℂ)) :=
    Eq.trans hleft_comm (Eq.trans hperiod.symm hright_comm.symm)
  exact congrArg Inv.inv
    (congrArg (fun z : ℂ => 1 - z) hexp)


end

end LFunctions
end Boundary

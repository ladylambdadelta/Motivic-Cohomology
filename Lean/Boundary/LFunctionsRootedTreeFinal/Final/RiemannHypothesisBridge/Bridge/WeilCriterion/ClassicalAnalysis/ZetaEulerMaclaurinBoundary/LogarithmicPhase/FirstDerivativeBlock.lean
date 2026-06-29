import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.RealPhaseBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcVariation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.SecondDerivativeVdc
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

open scoped ComplexConjugate Topology

/-- Numeric normalization used by the logarithmic phase block constants. -/
theorem Real.four_mul_four_eq_sixteen_for_logarithmicPhase :
    (4 * 4 : ℝ) = 16 := by
  have hnat : (4 * 4 : ℕ) = 16 :=
    rfl
  have hcast_mul :
      (((4 * 4 : ℕ) : ℝ) = (4 : ℝ) * 4) :=
    Nat.cast_mul 4 4
  have hcast_value :
      (((4 * 4 : ℕ) : ℝ) = (16 : ℝ)) :=
    Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ)) hnat)
      Nat.cast_ofNat
  exact Eq.trans hcast_mul.symm hcast_value

/-- Numeric normalization used by the logarithmic phase block constants. -/
theorem Real.four_add_sixteen_eq_twenty_for_logarithmicPhase :
    (4 + 16 : ℝ) = 20 := by
  have hnat : (4 + 16 : ℕ) = 20 :=
    rfl
  have hcast_add :
      (((4 + 16 : ℕ) : ℝ) = (4 : ℝ) + 16) :=
    Nat.cast_add 4 16
  have hcast_value :
      (((4 + 16 : ℕ) : ℝ) = (20 : ℝ)) :=
    Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ)) hnat)
      Nat.cast_ofNat
  exact Eq.trans hcast_add.symm hcast_value

/-- Nonnegativity of the numeric block remainder. -/
theorem Real.sixteen_nonneg_for_logarithmicPhase :
    0 ≤ (16 : ℝ) := by
  exact Nat.cast_nonneg 16

/-- The logarithmic block lower-bound parameter is positive away from
zero frequency. -/
theorem Complex.logarithmicPhase_block_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (b : ℕ) :
    0 < (‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ) := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have hb_pos_real : 0 < ((b + 1 : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr hb_pos_nat
  exact div_pos ht_pos hb_pos_real

/-- The reciprocal of the logarithmic block lower-bound parameter is the block
length scale divided by `|t|`. -/
theorem Complex.logarithmicPhase_block_lowerParameter_inv_eq
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (b : ℕ) :
    (((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ))⁻¹) =
      ((b + 1 : ℕ) : ℝ) / ‖t‖ := by
  have ht_ne : (‖t‖ : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  have hb_ne : (((b + 1 : ℕ) : ℝ)) ≠ 0 := by
    have hb_pos_nat : 0 < b + 1 :=
      Nat.succ_pos b
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb_pos_nat)
  calc
    (((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ))⁻¹) =
        ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
      inv_div ((‖t‖ : ℝ)) (((b + 1 : ℕ) : ℝ))

/-- The corrected endpoint-plus-reduced-arc block constant is bounded by a
single numeral constant convenient for dyadic summation. -/
theorem Complex.logarithmicPhase_exact_block_constant_le_twenty
    {x : ℝ}
    (hx : 0 ≤ x) :
    4 * (x + 1) + 4 * Real.pi * x ≤ 20 * (x + 1) := by
  have hpi_x : Real.pi * x ≤ 4 * x :=
    mul_le_mul_of_nonneg_right Real.pi_le_four hx
  have hfour_pi_x :
      4 * Real.pi * x ≤ 4 * (4 * x) := by
    have hmul :
        4 * (Real.pi * x) ≤ 4 * (4 * x) :=
      mul_le_mul_of_nonneg_left hpi_x zero_le_four
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * (4 * x))
      (mul_assoc (4 : ℝ) Real.pi x).symm
      hmul
  have hfour_four :
      4 * (4 * x) = 16 * x := by
    calc
      4 * (4 * x) = (4 * 4 : ℝ) * x :=
        (mul_assoc (4 : ℝ) 4 x).symm
      _ = 16 * x :=
        congrArg (fun r : ℝ => r * x)
          Real.four_mul_four_eq_sixteen_for_logarithmicPhase
  have hpi_bound :
      4 * Real.pi * x ≤ 16 * x :=
    Eq.subst
      (motive := fun r : ℝ => 4 * Real.pi * x ≤ r)
      hfour_four
      hfour_pi_x
  have hreduce :
      4 * (x + 1) + 4 * Real.pi * x ≤
        4 * (x + 1) + 16 * x :=
    add_le_add_left hpi_bound (4 * (x + 1))
  have hleft_expand :
      4 * (x + 1) + 16 * x =
        20 * x + 4 := by
    have hfour_expand :
        4 * (x + 1) = 4 * x + 4 := by
      calc
        4 * (x + 1) = 4 * x + 4 * 1 :=
          mul_add (4 : ℝ) x 1
        _ = 4 * x + 4 :=
          congrArg (fun r : ℝ => 4 * x + r)
            (mul_one (4 : ℝ))
    have hcomm :
        (4 * x + 4) + 16 * x =
          (4 * x + 16 * x) + 4 := by
      calc
        (4 * x + 4) + 16 * x =
            4 * x + (4 + 16 * x) :=
          add_assoc (4 * x) 4 (16 * x)
        _ = 4 * x + (16 * x + 4) :=
          congrArg (fun r : ℝ => 4 * x + r)
            (add_comm 4 (16 * x))
        _ = (4 * x + 16 * x) + 4 :=
          (add_assoc (4 * x) (16 * x) 4).symm
    have hfold :
        4 * x + 16 * x = 20 * x := by
      calc
        4 * x + 16 * x = (4 + 16 : ℝ) * x :=
          (add_mul (4 : ℝ) 16 x).symm
        _ = 20 * x :=
          congrArg (fun r : ℝ => r * x)
            Real.four_add_sixteen_eq_twenty_for_logarithmicPhase
    calc
      4 * (x + 1) + 16 * x =
          (4 * x + 4) + 16 * x :=
        congrArg (fun r : ℝ => r + 16 * x) hfour_expand
      _ = (4 * x + 16 * x) + 4 :=
        hcomm
      _ = 20 * x + 4 :=
        congrArg (fun r : ℝ => r + 4) hfold
  have hright_expand :
      20 * (x + 1) = 20 * x + 20 := by
    calc
      20 * (x + 1) = 20 * x + 20 * 1 :=
        mul_add (20 : ℝ) x 1
      _ = 20 * x + 20 :=
        congrArg (fun r : ℝ => 20 * x + r)
          (mul_one (20 : ℝ))
  have hfour_le_twenty : (4 : ℝ) ≤ 20 := by
    have hsixteen_nonneg : 0 ≤ (16 : ℝ) :=
      Real.sixteen_nonneg_for_logarithmicPhase
    calc
      (4 : ℝ) ≤ 4 + 16 :=
        le_add_of_nonneg_right hsixteen_nonneg
      _ = 20 :=
        Real.four_add_sixteen_eq_twenty_for_logarithmicPhase
  have hcore :
      20 * x + 4 ≤ 20 * x + 20 :=
    add_le_add_left hfour_le_twenty (20 * x)
  exact le_trans hreduce
    (Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 20 * (x + 1))
      hleft_expand.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          20 * x + 4 ≤ right)
        hright_expand.symm
        hcore))

/-- Real first-derivative-test primitive for the logarithmic scalar phase on
one integer block. -/
theorem Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
            ‖deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  let lam : ℝ := ‖t‖ / ((b + 1 : ℕ) : ℝ)
  have hlam_pos : 0 < lam :=
    Complex.logarithmicPhase_block_lowerParameter_pos t ht b
  have hfirst :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
    Complex.realPhase_firstDerivative_integer_block_bound
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ha hab hlam_pos
      hderiv_antitone
      hderiv_lower
      hinc_mono
      hred_mono
      hsep
  have hlam_inv :
      lam⁻¹ = ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    Complex.logarithmicPhase_block_lowerParameter_inv_eq t ht b
  have hexact :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) +
            4 * Real.pi * (((b + 1 : ℕ) : ℝ) / ‖t‖) :=
    Eq.subst
    (motive := fun scale : ℝ =>
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (scale + 1) + 4 * Real.pi * scale)
    hlam_inv
    hfirst
  have hscale_nonneg :
      0 ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_nonneg (Nat.cast_nonneg (b + 1)) ht_pos.le
  exact le_trans hexact
    (Complex.logarithmicPhase_exact_block_constant_le_twenty hscale_nonneg)

/-- Continuous first-derivative-test primitive for the sampled logarithmic
phase on one integer block.

This is the exact analytic theorem still needed from the van der Corput
first-derivative method after all concrete derivative computations have been
peeled into owner lemmas above. -/
theorem Complex.logarithmicPhase_firstDerivative_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
            ‖deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  have hphase :
      (∑ n ∈ Finset.Icc a b,
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
          t n)
  have hreal_block :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hred_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
    hphase.symm
    hreal_block

/-- Standard first-derivative estimate on one monotone logarithmic-phase block.

This is the local van der Corput input: if the phase derivative has monotone
magnitude and is bounded below by `lam` on `[a,b]`, then the sampled exponential
sum over the block has the stated reciprocal-derivative bound. -/
theorem Complex.logarithmicPhase_monotone_firstDerivative_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  have hsample :
      (∑ n ∈ Finset.Icc a b,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n := by
    exact Finset.sum_congr rfl
      (fun n hn_mem =>
        have hn_one : 1 ≤ n :=
          le_trans ha (Finset.mem_Icc.mp hn_mem).1
        have hn_pos : 0 < n :=
          Nat.lt_of_succ_le hn_one
        (Complex.logarithmicPhase_integer_sample_eq t hn_pos).symm)
  have hblock :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n‖ ≤
          20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hred_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
    hsample.symm
    hblock

/-- The one-block estimate is already bounded by the dyadic-cover expression
used by the global theorem. -/
theorem Complex.logarithmicPhase_single_block_le_dyadic_cover_expression
    (t : ℝ)
    (N : ℕ) :
    20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
      20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
  have hlog_nonneg : (0 : ℝ) ≤ (Nat.log2 (N + 1) : ℝ) :=
    Nat.cast_nonneg (Nat.log2 (N + 1))
  have hinside :
      ((N + 1 : ℕ) : ℝ) / ‖t‖ + 1 ≤
        ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 := by
    calc
      ((N + 1 : ℕ) : ℝ) / ‖t‖ + 1 ≤
          ((N + 1 : ℕ) : ℝ) / ‖t‖ + (Nat.log2 (N + 1) : ℝ) + 1 := by
        exact add_le_add_right
          (le_add_of_nonneg_right hlog_nonneg)
          1
      _ = ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 :=
        rfl
  exact mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg 20)

/-- Dyadic block cover primitive for logarithmic-phase partial sums.

This isolates the finite combinatorics of decomposing `[1,N]` into dyadic
blocks and applying the one-block estimate on each block. -/
theorem Complex.logarithmicPhase_dyadic_block_cover_bound
    (hblock :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                ‖∑ n ∈ Finset.Icc a b,
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                  20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          ‖∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              20 *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
  intro t ht N
  by_cases hN : N = 0
  · have hsum_zero :
        (∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) = 0 := by
      exact Finset.sum_eq_zero
        (fun n hn => by
          have hn_bounds : 1 ≤ n ∧ n ≤ N :=
            Finset.mem_Icc.mp hn
          have hn_le_zero : n ≤ 0 :=
            Eq.subst (motive := fun k : ℕ => n ≤ k) hN hn_bounds.2
          have hn_not_one : ¬ 1 ≤ n :=
            fun hone_le_n =>
              have hone_le_zero : 1 ≤ 0 :=
                le_trans hone_le_n hn_le_zero
              Nat.not_succ_le_zero 0 hone_le_zero
          exact False.elim (hn_not_one hn_bounds.1))
    have htarget_nonneg :
        0 ≤ 20 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
      have hnorm_pos : 0 < ‖t‖ :=
        lt_of_lt_of_le zero_lt_one ht
      have hquot_nonneg :
          0 ≤ ((N + 1 : ℕ) : ℝ) / ‖t‖ :=
        div_nonneg (Nat.cast_nonneg (N + 1)) hnorm_pos.le
      have hlog_nonneg : 0 ≤ (Nat.log2 (N + 1) : ℝ) :=
        Nat.cast_nonneg (Nat.log2 (N + 1))
      have hinside_nonneg :
          0 ≤ ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 :=
        add_nonneg (add_nonneg hquot_nonneg hlog_nonneg) zero_le_one
      exact mul_nonneg (Nat.cast_nonneg 20) hinside_nonneg
    have hnorm_zero_eq_zero : ‖(0 : ℂ)‖ = 0 :=
      norm_zero
    have htarget_norm_zero :
        ‖(0 : ℂ)‖ ≤
          20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
      Eq.subst
        (motive := fun r : ℝ =>
          r ≤
            20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1))
        hnorm_zero_eq_zero.symm
        htarget_nonneg
    exact Eq.subst
      (motive := fun S : ℂ =>
        ‖S‖ ≤
          20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1))
      hsum_zero.symm
      htarget_norm_zero
  · have hN_pos : 1 ≤ N :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
    have hsingle :
        ‖∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
      hblock t ht (le_refl 1) hN_pos
    have hcover :
        20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
          20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
      Complex.logarithmicPhase_single_block_le_dyadic_cover_expression t N
    exact le_trans hsingle hcover

/-- The classical absolute constant widens the endpoint-plus-square-root
target. -/
theorem Real.logarithmicPhase_target_le_twenty_mul
    {x : ℝ}
    (hx : 0 ≤ x) :
    x ≤ 20 * x := by
  have hone_le_twenty : (1 : ℝ) ≤ 20 := by
    have hnineteen_nonneg : 0 ≤ (19 : ℝ) :=
      Nat.cast_nonneg 19
    calc
      (1 : ℝ) ≤ 1 + 19 :=
        le_add_of_nonneg_right hnineteen_nonneg
      _ = 20 := by
        have hnat : (1 + 19 : ℕ) = 20 :=
          rfl
        have hcast_add :
            (((1 + 19 : ℕ) : ℝ) = (1 : ℝ) + 19) :=
          have hraw :
              (((1 + 19 : ℕ) : ℝ) =
                ((1 : ℕ) : ℝ) + ((19 : ℕ) : ℝ)) :=
            Nat.cast_add 1 19
          have hone :
              ((1 : ℕ) : ℝ) = (1 : ℝ) :=
            Nat.cast_one
          have hnineteen :
              ((19 : ℕ) : ℝ) = (19 : ℝ) :=
            Nat.cast_ofNat
          have hleft :
              ((1 : ℕ) : ℝ) + ((19 : ℕ) : ℝ) =
                (1 : ℝ) + ((19 : ℕ) : ℝ) :=
            congrArg (fun r : ℝ => r + ((19 : ℕ) : ℝ)) hone
          have hright :
              (1 : ℝ) + ((19 : ℕ) : ℝ) = (1 : ℝ) + 19 :=
            congrArg (fun r : ℝ => (1 : ℝ) + r) hnineteen
          Eq.trans hraw (Eq.trans hleft hright)
        have hcast_value :
            (((1 + 19 : ℕ) : ℝ) = (20 : ℝ)) :=
          Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat
        exact Eq.trans hcast_add.symm hcast_value
  have hmul :
      1 * x ≤ 20 * x :=
    mul_le_mul_of_nonneg_right hone_le_twenty hx
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 20 * x)
      (one_mul x)
      hmul

/-- A nonnegative target is bounded by eighty copies of itself. -/
theorem Real.logarithmicPhase_target_le_eighty_mul
    {x : ℝ}
    (hx : 0 ≤ x) :
    x ≤ 80 * x := by
  have hone_le_eighty : (1 : ℝ) ≤ 80 := by
    have hseventy_nine_nonneg : 0 ≤ (79 : ℝ) :=
      Nat.cast_nonneg 79
    calc
      (1 : ℝ) ≤ 1 + 79 :=
        le_add_of_nonneg_right hseventy_nine_nonneg
      _ = 80 := by
        have hnat : (1 + 79 : ℕ) = 80 :=
          rfl
        have hcast_add :
            (((1 + 79 : ℕ) : ℝ) = (1 : ℝ) + 79) :=
          have hraw :
              (((1 + 79 : ℕ) : ℝ) =
                ((1 : ℕ) : ℝ) + ((79 : ℕ) : ℝ)) :=
            Nat.cast_add 1 79
          have hone :
              ((1 : ℕ) : ℝ) = (1 : ℝ) :=
            Nat.cast_one
          have hseventy_nine :
              ((79 : ℕ) : ℝ) = (79 : ℝ) :=
            Nat.cast_ofNat
          have hleft :
              ((1 : ℕ) : ℝ) + ((79 : ℕ) : ℝ) =
                (1 : ℝ) + ((79 : ℕ) : ℝ) :=
            congrArg (fun r : ℝ => r + ((79 : ℕ) : ℝ)) hone
          have hright :
              (1 : ℝ) + ((79 : ℕ) : ℝ) = (1 : ℝ) + 79 :=
            congrArg (fun r : ℝ => (1 : ℝ) + r) hseventy_nine
          Eq.trans hraw (Eq.trans hleft hright)
        have hcast_value :
            (((1 + 79 : ℕ) : ℝ) = (80 : ℝ)) :=
          Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ)) hnat)
            Nat.cast_ofNat
        exact Eq.trans hcast_add.symm hcast_value
  have hmul :
      1 * x ≤ 80 * x :=
    mul_le_mul_of_nonneg_right hone_le_eighty hx
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ 80 * x)
      (one_mul x)
      hmul

/-- The logarithmic endpoint-plus-square-root target is nonnegative. -/
theorem Real.logarithmicPhase_endpoint_sqrt_target_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (b : ℕ) :
    0 ≤ (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
  Real.secondDerivativeVdc_target_nonneg (b := b) ht

end

end LFunctions
end Boundary

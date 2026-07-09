import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.ReducedArcVariation
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor

/-!
# Second-derivative van der Corput block estimate

This file owns the abstract finite second-derivative van der Corput input for
real phases sampled on integer blocks.  The logarithmic phase file supplies the
concrete curvature lower bound for `φ(x) = -t log x` and consumes the generic
estimate here.

The intended constructive proof chain is:

* partition the integer block by derivative-frequency windows;
* use the curvature lower bound to control the length of resonant packets;
* use the existing first-derivative/Kusmin-Landau mechanism on nonresonant
  packets;
* sum the packet estimates to obtain the endpoint scale plus the square-root
  curvature scale.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite complex sum is bounded by a uniform bound times the number of
summands.  This is the basic packet-counting estimate used in the
second-derivative VdC decomposition. -/
theorem Complex.finite_sum_norm_le_card_mul_of_norm_le
    {ι : Type*}
    (s : Finset ι)
    (u : ι → ℂ)
    {M : ℝ}
    (hM : 0 ≤ M)
    (hu : ∀ i : ι, i ∈ s → ‖u i‖ ≤ M) :
    ‖∑ i ∈ s, u i‖ ≤ ((s.card : ℝ) * M) := by
  have hsum_norm :
      ‖∑ i ∈ s, u i‖ ≤ ∑ i ∈ s, ‖u i‖ :=
    norm_sum_le s u
  have hsum_bound :
      (∑ i ∈ s, ‖u i‖) ≤ ∑ i ∈ s, M :=
    Finset.sum_le_sum
      (fun i hi => hu i hi)
  have hconstant_sum :
      (∑ i ∈ s, M) = ((s.card : ℝ) * M) :=
    Eq.trans
      (Finset.sum_const M)
      (nsmul_eq_mul s.card M)
  exact
    le_trans hsum_norm
      (le_trans hsum_bound
        (le_of_eq hconstant_sum))

/-- Unit-bounded finite complex sums are bounded by the cardinality of their
index set. -/
theorem Complex.finite_sum_norm_le_card_of_norm_le_one
    {ι : Type*}
    (s : Finset ι)
    (u : ι → ℂ)
    (hu : ∀ i : ι, i ∈ s → ‖u i‖ ≤ 1) :
    ‖∑ i ∈ s, u i‖ ≤ (s.card : ℝ) := by
  have hbound :
      ‖∑ i ∈ s, u i‖ ≤ ((s.card : ℝ) * 1) :=
    Complex.finite_sum_norm_le_card_mul_of_norm_le
      s u zero_le_one hu
  have hcard_mul_one :
      ((s.card : ℝ) * 1) = (s.card : ℝ) :=
    mul_one (s.card : ℝ)
  exact
    le_trans hbound
      (le_of_eq hcard_mul_one)

/-- Non-singleton prefix in the finite Abel transform.  This is the remaining
finite summation-by-parts identity plus monotone-variation estimate. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded_of_lt
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a m,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * Real.pi * lam⁻¹ := by
  let boundary : ℂ := Complex.realPhase_prefixAbelBoundary φ a m
  let variation : ℂ := Complex.realPhase_prefixAbelVariation φ a m
  have hidentity :
      (∑ n ∈ Finset.Icc a m,
        Complex.realPhase_integerUnit φ n) =
          boundary + variation :=
    Complex.realPhase_prefixAbel_identity
      φ ham hm hlam_pos hsep
  have hden' :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * lam⁻¹ :=
    fun n hn => hden n hn
  have hboundary :
      ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) :=
    Complex.realPhase_prefixAbelBoundary_norm_bound
      φ ham hm hlam_pos hden'
  have hvariation :
      ‖variation‖ ≤ 4 * Real.pi * lam⁻¹ :=
    Complex.realPhase_prefixAbelVariation_norm_bound
      φ ham hm hlam_pos hinc_mono hred_mono hsep hden'
  exact
    Exists.intro boundary
      (Exists.intro variation
        (And.intro hidentity
          (And.intro hboundary hvariation)))

/-- The finite Abel transform supplies boundary and variation terms satisfying
the needed prefix bounds. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a m,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * Real.pi * lam⁻¹ := by
  by_cases hma : m = a
  · exact Eq.subst
      (motive := fun r : ℕ =>
        ∃ boundary variation : ℂ,
          (∑ n ∈ Finset.Icc a r,
            Complex.exp (Complex.I * (φ n : ℂ))) =
              boundary + variation ∧
          ‖boundary‖ ≤ 4 * (lam⁻¹ + 1) ∧
          ‖variation‖ ≤ 4 * Real.pi * lam⁻¹)
      hma.symm
        (Complex.realPhase_monotoneIncrement_singleton_prefix_abel_terms_bounded
        φ a hlam_pos)
  · have hm_bounds : a ≤ m ∧ m ≤ b :=
        Finset.mem_Icc.mp hm
    have ham : a < m :=
      lt_of_le_of_ne hm_bounds.1 (Ne.symm hma)
    exact
      Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded_of_lt
        φ ha hab_lt ham hm hlam_pos hinc_mono hred_mono hsep hden

/-- Prefix-sum form of the finite monotone-increment Dirichlet estimate.

This is the actual finite summation-by-parts theorem: every initial segment of
the block is controlled by the same endpoint and variation bound. -/
theorem Complex.realPhase_monotoneIncrement_partialSummation_prefix_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hm : m ∈ Finset.Icc a b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    ‖∑ n ∈ Finset.Icc a m,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  match
    Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded
      φ ha hab_lt hm hlam_pos hinc_mono hred_mono hsep hden with
  | ⟨boundary, variation, hS, hboundary, hvariation⟩ =>
        exact
        Complex.realPhase_monotoneIncrement_prefix_abel_norm_assembly
          hS hboundary hvariation

/-- Norm estimate after the finite Abel transform for monotone adjacent
frequencies. -/
theorem Complex.realPhase_monotoneIncrement_abel_transform_norm_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  have hb_mem : b ∈ Finset.Icc a b :=
    Finset.mem_Icc.mpr ⟨le_of_lt hab_lt, le_rfl⟩
  exact
    Complex.realPhase_monotoneIncrement_partialSummation_prefix_bound
      φ ha hab_lt hb_mem hlam_pos hinc_mono hred_mono hsep hden

/-- Monotone-frequency finite Dirichlet-test core.

This is the summation-by-parts/variation step: once every adjacent frequency
has a geometric denominator bounded by `2 / lam`, monotonicity of the increments
controls the boundary and variation terms. -/
theorem Complex.realPhase_monotoneIncrement_dirichlet_variation_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_monotoneIncrement_abel_transform_norm_bound
      φ ha hab_lt hlam_pos hinc_mono hred_mono hsep hden

/-- Nontrivial monotone separated-increment Dirichlet-test primitive.

This is the genuine finite summation-by-parts case: at least one adjacent
increment is present, so the separation hypothesis supplies the geometric
denominators and monotonicity controls the variation term. -/
theorem Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound_of_lt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  have hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * lam⁻¹ := by
    intro n hn
    exact
      Complex.realPhase_geometricDenominator_inv_norm_bound
        hlam_pos
        (hsep n hn)
  exact
    Complex.realPhase_monotoneIncrement_dirichlet_variation_bound
      φ ha hab_lt hlam_pos hinc_mono hred_mono hsep hden

/-- Finite Dirichlet-test primitive for monotone separated increments.

This is the discrete summation core behind Kusmin-Landau: the adjacent
increments must move monotonically through frequency space and stay separated
from every `2πℤ` resonance by at least `lam`.  The endpoint `+1` is necessary
for singleton blocks, where the separation hypothesis is vacuous. -/
theorem Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  match lt_or_eq_of_le hab with
  | Or.inl hab_lt =>
      exact
      Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound_of_lt
        φ ha hab_lt hlam_pos hinc_mono hred_mono hsep
  | Or.inr hab_eq =>
      exact
      Eq.subst
        (motive := fun c : ℕ =>
          ‖∑ n ∈ Finset.Icc a c,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹)
        hab_eq
        (Complex.realPhase_singleton_integer_block_bound φ a hlam_pos)

/-- Finite monotone separated-increment exponential-sum primitive.

This is the public finite-difference Kusmin-Landau surface.  It is a thin
wrapper over the Dirichlet-test primitive with the boundary-safe constant
`4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹`. -/
theorem Complex.realPhase_separatedIncrement_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlam_pos : 0 < lam)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound
      φ ha hab hlam_pos hinc_mono hred_mono hsep

/-- Honest Kusmin-Landau block estimate with the required monotone separated
finite-difference hypothesis. -/
theorem Complex.realPhase_kusminLandau_integer_block_bound_of_separatedIncrement
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          lam ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_separatedIncrement_integer_block_bound
      φ ha hab hlam_pos hinc_mono hred_mono hsep

/-- Kusmin-Landau/van der Corput finite first-derivative core for real phases.

This is the genuine oscillatory analytic primitive: the phase derivative stays
monotone with fixed sign modulo the frequency lattice and is separated from
`2πℤ`, so cancellation gives a reciprocal-derivative bound independent of the
length of the block.  A lower bound on `|φ'|` alone is not enough, because it
does not separate the integer increments from resonant multiples of `2π`. -/
theorem Complex.realPhase_kusminLandau_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          lam ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_kusminLandau_integer_block_bound_of_separatedIncrement
      φ ha hab hlam_pos hderiv_antitone hderiv_lower hinc_mono hred_mono hsep

/-- General finite first-derivative estimate for a real phase sampled on an
integer block.

This is the owner-level van der Corput primitive needed by the second
derivative B-process.  The assumptions record the actual analytic input:
monotonicity of the absolute derivative, a positive lower bound, reduced
monotonicity, and separation from the frequency lattice. -/
theorem Complex.realPhase_firstDerivative_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          lam ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b lam) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  have hosc :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ :=
    Complex.realPhase_kusminLandau_integer_block_bound
      φ ha hab hlam_pos hderiv_antitone hderiv_lower hinc_mono hred_mono hsep
  exact hosc

/-- The square-root scale in the second-derivative estimate is nonnegative. -/
theorem Real.secondDerivativeVdc_sqrtScale_nonneg
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 ≤ Real.sqrt (1 + T) := by
  exact Real.sqrt_nonneg (1 + T)

/-- The endpoint first-derivative scale in the second-derivative estimate is
nonnegative. -/
theorem Real.secondDerivativeVdc_endpointScale_nonneg
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 ≤ (((b + 1 : ℕ) : ℝ) / T) := by
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  exact div_nonneg (Nat.cast_nonneg (b + 1)) hT_nonneg

/-- The final second-derivative VdC target is nonnegative. -/
theorem Real.secondDerivativeVdc_target_nonneg
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 ≤ (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  exact
    add_nonneg
      (Real.secondDerivativeVdc_endpointScale_nonneg (b := b) hT)
      (Real.secondDerivativeVdc_sqrtScale_nonneg hT)

/-- A packet already bounded by the square-root scale satisfies the final
second-derivative VdC target by the trivial unit-norm estimate.

This is the terminal estimate for resonant packets after the curvature counting
lemma has bounded their cardinality. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_sqrt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hcard :
      ((Finset.Icc a b).card : ℝ) ≤ Real.sqrt (1 + T)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have htrivial :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          ((Finset.Icc a b).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card φ
  have hsqrt_le_target :
      Real.sqrt (1 + T) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
    exact le_add_of_nonneg_left
      (Real.secondDerivativeVdc_endpointScale_nonneg (b := b) hT)
  exact le_trans htrivial (le_trans hcard hsqrt_le_target)

/-- A packet already bounded by the endpoint first-derivative scale satisfies
the final second-derivative VdC target by the trivial unit-norm estimate.

This is the terminal estimate for packets controlled by the derivative-window
width rather than by the square-root curvature scale. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_endpoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hcard :
      ((Finset.Icc a b).card : ℝ) ≤ (((b + 1 : ℕ) : ℝ) / T)) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have htrivial :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          ((Finset.Icc a b).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card φ
  have hendpoint_le_target :
      (((b + 1 : ℕ) : ℝ) / T) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
    exact le_add_of_nonneg_right
      (Real.secondDerivativeVdc_sqrtScale_nonneg hT)
  exact le_trans htrivial (le_trans hcard hendpoint_le_target)

/-- The final target follows from any direct packet cardinality estimate by
the endpoint-plus-square-root scale. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_target
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hcard :
      ((Finset.Icc a b).card : ℝ) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have htrivial :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          ((Finset.Icc a b).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card φ
  exact le_trans htrivial hcard

/-- A singleton packet satisfies the second-derivative VdC target. -/
theorem Complex.realPhase_secondDerivative_vdc_singleton_integer_block_bound
    (φ : ℝ → ℝ)
    (a : ℕ)
    {T : ℝ}
    (hT : 1 ≤ T) :
    ‖∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((a + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have hone_le_arg : 1 ≤ 1 + T := by
    exact le_add_of_nonneg_right (le_trans zero_le_one hT)
  have hone_le_sqrt : (1 : ℝ) ≤ Real.sqrt (1 + T) :=
    (Real.one_le_sqrt).mpr hone_le_arg
  have hIcc :
        Finset.Icc a a = ({a} : Finset ℕ) :=
    Finset.Icc_self a
  have hcard_nat : (Finset.Icc a a).card = 1 := by
    have hcard_eq_singleton_card :
        (Finset.Icc a a).card = ({a} : Finset ℕ).card :=
      congrArg Finset.card hIcc
    have hsingleton_card :
        ({a} : Finset ℕ).card = 1 :=
        Finset.card_singleton a
    exact Eq.trans hcard_eq_singleton_card hsingleton_card
  have hcard_real :
      ((Finset.Icc a a).card : ℝ) = 1 := by
    exact Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ)) hcard_nat)
      Nat.cast_one
  have hcard_le_sqrt :
      ((Finset.Icc a a).card : ℝ) ≤ Real.sqrt (1 + T) :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ Real.sqrt (1 + T))
      hcard_real.symm
      hone_le_sqrt
  exact
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_sqrt
      φ hT hcard_le_sqrt

/-- Cardinality of an integer block as the real endpoint length, when the
successor-right endpoint contains the left endpoint. -/
theorem Real.secondDerivativeVdc_card_Icc_eq_endpoint_length
    {a b : ℕ}
    (hab : a ≤ b + 1) :
    ((Finset.Icc a b).card : ℝ) =
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have hcard_nat :
      (Finset.Icc a b).card = b + 1 - a :=
    Nat.card_Icc a b
  have hcast_sub :
      (((b + 1 - a : ℕ) : ℝ)) =
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
    Nat.cast_sub hab
  exact Eq.trans
    (congrArg (fun n : ℕ => (n : ℝ)) hcard_nat)
    hcast_sub

/-- Cardinality of an integer block is bounded by the real endpoint length,
when the successor-right endpoint contains the left endpoint. -/
theorem Real.secondDerivativeVdc_card_Icc_le_endpoint_length
    {a b : ℕ}
    (hab : a ≤ b + 1) :
    ((Finset.Icc a b).card : ℝ) ≤
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
  le_of_eq (Real.secondDerivativeVdc_card_Icc_eq_endpoint_length hab)

/-- If a natural interval has length at most the square-root scale, the
corresponding exponential block already satisfies the VdC target. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_sqrt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlength :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ Real.sqrt (1 + T))
    (hab : a ≤ b + 1) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have hcard_le_length :
      ((Finset.Icc a b).card : ℝ) ≤ (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
    exact Real.secondDerivativeVdc_card_Icc_le_endpoint_length hab
  exact
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_sqrt
      φ hT (le_trans hcard_le_length hlength)

/-- If a natural interval has length at most the endpoint scale, the
corresponding exponential block already satisfies the VdC target. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_endpoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlength :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ (((b + 1 : ℕ) : ℝ) / T))
    (hab : a ≤ b + 1) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have hcard_le_length :
      ((Finset.Icc a b).card : ℝ) ≤ (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
    exact Real.secondDerivativeVdc_card_Icc_le_endpoint_length hab
  exact
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_endpoint
      φ hT (le_trans hcard_le_length hlength)

/-- If the whole integer interval is already shorter than the final VdC scale,
the second-derivative estimate follows from the unit-norm cardinality bound. -/
theorem Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_length_le_target
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hlength :
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)))
    (hab : a ≤ b + 1) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      (((b + 1 : ℕ) : ℝ) / T +
        Real.sqrt (1 + T)) := by
  have hcard_le_length :
      ((Finset.Icc a b).card : ℝ) ≤ (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
    exact Real.secondDerivativeVdc_card_Icc_le_endpoint_length hab
  exact
    Complex.realPhase_secondDerivative_vdc_integer_block_bound_of_card_le_target
      φ (le_trans hcard_le_length hlength)

/-- Lower mean-value estimate for the derivative in the positive-curvature
orientation of the second-derivative VdC argument. -/
theorem Real.deriv_growth_from_second_derivative_lower_on_Icc
    (φ : ℝ → ℝ)
    {A B C x y : ℝ}
    (hcont :
      ContinuousOn (fun z : ℝ => deriv φ z) (Set.Icc A B))
    (hdiff :
      DifferentiableOn ℝ (fun z : ℝ => deriv φ z)
        (interior (Set.Icc A B)))
    (hlower :
      ∀ z : ℝ,
        z ∈ interior (Set.Icc A B) →
          C ≤ deriv (deriv φ) z)
    (hx : x ∈ Set.Icc A B)
    (hy : y ∈ Set.Icc A B)
    (hxy : x ≤ y) :
    C * (y - x) ≤ deriv φ y - deriv φ x := by
  exact
    (convex_Icc A B).mul_sub_le_image_sub_of_le_deriv
      hcont hdiff hlower x hx y hy hxy

/-- Oriented first-derivative separation forced by a signed second-derivative
lower bound on a finite VdC block. -/
theorem Complex.realPhase_secondDerivative_vdc_oriented_deriv_separation
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T x y : ℝ}
    (hcont :
      ContinuousOn (fun z : ℝ => deriv φ z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hdiff :
      DifferentiableOn ℝ (fun z : ℝ => deriv φ z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))))
    (horientation :
      (MonotoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            0 ≤ deriv (deriv φ) z) ∨
      (AntitoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            deriv (deriv φ) z ≤ 0))
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) ≤
            ‖deriv (deriv φ) z‖)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤ deriv φ y - deriv φ x) ∨
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤ deriv φ x - deriv φ y) := by
  let C : ℝ :=
    T *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹)
  match horientation with
  | Or.inl hpos =>
      have hlower :
          ∀ z : ℝ,
            z ∈ interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) →
              C ≤ deriv (deriv φ) z := by
        intro z hz
        have hz_closed :
            z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
          interior_subset hz
        have hsecond_nonneg : 0 ≤ deriv (deriv φ) z :=
          hpos.2 z hz_closed
        have hnorm_eq :
            ‖deriv (deriv φ) z‖ = deriv (deriv φ) z :=
          Real.norm_of_nonneg hsecond_nonneg
        exact
          Eq.subst
            (motive := fun r : ℝ => C ≤ r)
            hnorm_eq
            (hcurvature_lower z hz_closed)
      exact Or.inl
        (Real.deriv_growth_from_second_derivative_lower_on_Icc
          φ hcont hdiff hlower hx hy hxy)
  | Or.inr hneg =>
      let ψ : ℝ → ℝ := fun u : ℝ => -deriv φ u
      have hcont_neg : ContinuousOn ψ
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
        hcont.neg
      have hdiff_neg : DifferentiableOn ℝ ψ
          (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))) :=
        hdiff.neg
      have hlower :
          ∀ z : ℝ,
            z ∈ interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) →
              C ≤ deriv ψ z := by
        intro z hz
        have hz_closed :
            z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
          interior_subset hz
        have hsecond_nonpos : deriv (deriv φ) z ≤ 0 :=
          hneg.2 z hz_closed
        have hnorm_eq :
            ‖deriv (deriv φ) z‖ = -deriv (deriv φ) z :=
          Real.norm_of_nonpos hsecond_nonpos
        have hpsi_deriv :
            deriv ψ z = -deriv (deriv φ) z := by
          exact deriv.neg
        have hcurv_to_neg :
            C ≤ -deriv (deriv φ) z :=
          Eq.subst
            (motive := fun r : ℝ => C ≤ r)
            hnorm_eq
            (hcurvature_lower z hz_closed)
        exact
          Eq.subst
            (motive := fun r : ℝ => C ≤ r)
            hpsi_deriv.symm
            hcurv_to_neg
      have hgrowth :
          C * (y - x) ≤ ψ y - ψ x :=
        (convex_Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)).mul_sub_le_image_sub_of_le_deriv
          hcont_neg hdiff_neg hlower x hx y hy hxy
      have hdrop_eq :
          ψ y - ψ x = deriv φ x - deriv φ y := by
        calc
          ψ y - ψ x = (-deriv φ y) - (-deriv φ x) := by
            rfl
          _ = deriv φ x - deriv φ y :=
            neg_sub_neg (deriv φ y) (deriv φ x)
      exact Or.inr
        (Eq.subst
          (motive := fun r : ℝ => C * (y - x) ≤ r)
          hdrop_eq
          hgrowth)

/-- Norm form of the derivative separation forced by second-derivative
curvature on a finite VdC block. -/
theorem Complex.realPhase_secondDerivative_vdc_deriv_norm_separation
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T x y : ℝ}
    (hcont :
      ContinuousOn (fun z : ℝ => deriv φ z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hdiff :
      DifferentiableOn ℝ (fun z : ℝ => deriv φ z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))))
    (horientation :
      (MonotoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            0 ≤ deriv (deriv φ) z) ∨
      (AntitoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            deriv (deriv φ) z ≤ 0))
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) ≤
            ‖deriv (deriv φ) z‖)
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hy : y ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))
    (hxy : x ≤ y) :
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (y - x) ≤ ‖deriv φ y - deriv φ x‖) := by
  have horiented :
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (y - x) ≤ deriv φ y - deriv φ x) ∨
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (y - x) ≤ deriv φ x - deriv φ y) :=
    Complex.realPhase_secondDerivative_vdc_oriented_deriv_separation
      φ hcont hdiff horientation hcurvature_lower hx hy hxy
  match horiented with
  | Or.inl hforward =>
      exact le_trans hforward (le_abs_self (deriv φ y - deriv φ x))
  | Or.inr hbackward =>
      have hneg_eq :
          deriv φ x - deriv φ y = -(deriv φ y - deriv φ x) := by
        exact (neg_sub (deriv φ y) (deriv φ x)).symm
      have hbackward_neg :
          (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (y - x) ≤ -(deriv φ y - deriv φ x)) :=
        Eq.subst
          (motive := fun r : ℝ =>
            (T *
                ((((b + 1 : ℕ) : ℝ) *
                  (((b + 1 : ℕ) : ℝ)))⁻¹) *
                (y - x) ≤ r))
          hneg_eq
          hbackward
      exact
        le_trans hbackward_neg (neg_le_abs (deriv φ y - deriv φ x))

/-- In the long branch, the real block length is positive. -/
theorem Real.secondDerivativeVdc_long_length_pos
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlong :
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    0 < (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  have htarget_nonneg :
      0 ≤ (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) :=
    Real.secondDerivativeVdc_target_nonneg hT
  exact lt_of_le_of_lt htarget_nonneg hlong

/-- A positive real cast difference `b+1-a` forces the corresponding natural
inequality. -/
theorem Nat.le_succ_of_cast_sub_pos
    {a b : ℕ}
    (hpos : 0 < (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    a ≤ b + 1 := by
  match Nat.lt_or_ge a (b + 2) with
  | Or.inl hlt =>
        exact Nat.lt_succ_iff.mp hlt
  | Or.inr hge =>
        have hsucc_le_a : b + 1 ≤ a :=
        le_trans (Nat.le_succ (b + 1)) hge
        have hcast_le : (((b + 1 : ℕ) : ℝ)) ≤ (a : ℝ) :=
        Nat.cast_le.mpr hsucc_le_a
        have hsub_nonpos : (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤ 0 :=
        sub_nonpos.mpr hcast_le
        exact False.elim (not_lt_of_ge hsub_nonpos hpos)

/-- In the long branch, the natural interval endpoint order is nonempty at
the successor-right endpoint. -/
theorem Nat.secondDerivativeVdc_long_le_succ
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlong :
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    a ≤ b + 1 := by
  exact
    Nat.le_succ_of_cast_sub_pos
      (Real.secondDerivativeVdc_long_length_pos hT hlong)

/-- Integer derivative-frequency packet for a real phase.  The packet consists
of those integer samples whose derivative lies in the unit window centered at
the integer frequency `m`. -/
def Complex.realPhase_secondDerivative_vdc_derivPacket
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (m : ℤ) : Finset ℕ :=
  (Finset.Icc a b).filter
    (fun n : ℕ =>
      ((m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n) ∧
        (deriv φ n < (m : ℝ) + (1 / 2 : ℝ)))

/-- Membership in a derivative-frequency packet exposes both the ambient block
membership and the derivative-window inequalities. -/
theorem Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ} :
    n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ↔
      n ∈ Finset.Icc a b ∧
        ((m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n) ∧
          (deriv φ n < (m : ℝ) + (1 / 2 : ℝ)) := by
  exact Finset.mem_filter

/-- A packet member is a member of the original integer block. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ}
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    n ∈ Finset.Icc a b := by
  exact
    (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff
      φ).mp hn |>.1

/-- A packet member has derivative above the lower edge of its frequency
window. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_lower
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ}
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    (m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n := by
  exact
    ((Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff
      φ).mp hn).2.1

/-- A packet member has derivative below the upper edge of its frequency
window. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_upper
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ}
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    deriv φ n < (m : ℝ) + (1 / 2 : ℝ) := by
  exact
    ((Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff
      φ).mp hn).2.2

/-- The least integer sample in a nonempty derivative packet is a member of
that packet. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_min_mem
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp ∈
      Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
  Finset.min'_mem
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) hp

/-- The greatest integer sample in a nonempty derivative packet is a member of
that packet. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_max_mem
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp ∈
      Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
  Finset.max'_mem
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) hp

/-- Every member of a nonempty derivative packet lies above the packet
minimum. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty)
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp ≤ n :=
  Finset.min'_le
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) n hn

/-- Every member of a nonempty derivative packet lies below the packet
maximum. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_le_max_of_mem
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty)
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    n ≤ (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp :=
  Finset.le_max'
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) n hn

/-- A nonempty derivative packet is contained in the natural interval between
its least and greatest samples. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_subset_min_max
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty) :
    Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ⊆
        Finset.Icc
        ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp)
        ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp) := by
  intro n hn
  exact Finset.mem_Icc.mpr
    (And.intro
        (Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
        φ hp hn)
        (Complex.realPhase_secondDerivative_vdc_derivPacket_le_max_of_mem
        φ hp hn))

/-- Cardinality of a nonempty derivative packet is bounded by its endpoint
span plus one. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_nat
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty) :
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card ≤
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 -
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp := by
  have hcard_subset :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card ≤
        (Finset.Icc
          ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp)
          ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp)).card :=
    Finset.card_le_card
        (Complex.realPhase_secondDerivative_vdc_derivPacket_subset_min_max
        φ hp)
  have hcard_Icc :
      (Finset.Icc
          ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp)
          ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp)).card =
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 -
          (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp :=
    Nat.card_Icc
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp)
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp)
  exact le_trans hcard_subset
    (le_of_eq hcard_Icc)

/-- Real form of the endpoint-span cardinality bound for one nonempty
derivative packet. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_span
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty) :
    ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
      (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 : ℕ) : ℝ) -
        (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp : ℕ) : ℝ) := by
  have hnat :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card ≤
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 -
          (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_nat
      φ hp
  have hreal :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 -
          (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  have hmin_le_max_succ :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp ≤
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 :=
    Nat.le_trans
        (Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
        φ hp
        (Complex.realPhase_secondDerivative_vdc_derivPacket_max_mem
          φ hp))
      (Nat.le_succ
        ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp))
  have hcast_sub :
      (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 -
          (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp : ℕ) : ℝ) =
        (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp + 1 : ℕ) : ℝ) -
          (((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp : ℕ) : ℝ) :=
    Nat.cast_sub hmin_le_max_succ
  exact le_trans hreal (le_of_eq hcast_sub)

/-- The derivative values at any two samples in the same packet differ by
less than one in the oriented order. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
    (φ : ℝ → ℝ)
    {a b p q : ℕ}
    {m : ℤ}
    (hp : p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)
    (hq : q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    deriv φ q - deriv φ p < 1 := by
  have hp_lower :
      (m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ p :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hp
  have hq_upper :
      deriv φ q < (m : ℝ) + (1 / 2 : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_upper φ hq
  have hspan :
      deriv φ q - deriv φ p <
        ((m : ℝ) + (1 / 2 : ℝ)) - ((m : ℝ) - (1 / 2 : ℝ)) :=
    lt_of_lt_of_le
      (sub_lt_sub_right hq_upper (deriv φ p))
      (sub_le_sub_left hp_lower ((m : ℝ) + (1 / 2 : ℝ)))
  have hedge :
      ((m : ℝ) + (1 / 2 : ℝ)) - ((m : ℝ) - (1 / 2 : ℝ)) = 1 := by
    calc
      ((m : ℝ) + (1 / 2 : ℝ)) - ((m : ℝ) - (1 / 2 : ℝ)) =
          ((m : ℝ) + (1 / 2 : ℝ)) + (-((m : ℝ) - (1 / 2 : ℝ))) :=
        sub_eq_add_neg ((m : ℝ) + (1 / 2 : ℝ)) ((m : ℝ) - (1 / 2 : ℝ))
      _ = ((m : ℝ) + (1 / 2 : ℝ)) + (-(m : ℝ) + (1 / 2 : ℝ)) := by
        exact congrArg
          (fun r : ℝ => ((m : ℝ) + (1 / 2 : ℝ)) + r)
          (Eq.trans
            (neg_sub (m : ℝ) (1 / 2 : ℝ))
            (Eq.trans
              (sub_eq_add_neg (1 / 2 : ℝ) (m : ℝ))
              (add_comm (1 / 2 : ℝ) (-(m : ℝ)))))
      _ = (((m : ℝ) + (-(m : ℝ))) + ((1 / 2 : ℝ) + (1 / 2 : ℝ))) := by
        exact add_add_add_comm (m : ℝ) (1 / 2 : ℝ) (-(m : ℝ)) (1 / 2 : ℝ)
      _ = (0 : ℝ) + ((1 / 2 : ℝ) + (1 / 2 : ℝ)) := by
        exact congrArg
          (fun r : ℝ => r + ((1 / 2 : ℝ) + (1 / 2 : ℝ)))
          (add_neg_cancel (m : ℝ))
      _ = (1 / 2 : ℝ) + (1 / 2 : ℝ) :=
        zero_add ((1 / 2 : ℝ) + (1 / 2 : ℝ))
      _ = 1 :=
        add_halves (1 : ℝ)
  exact
    Eq.subst
      (motive := fun r : ℝ => deriv φ q - deriv φ p < r)
      hedge
      hspan

/-- The derivative values at any two samples in the same packet differ by
less than one in absolute value. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_norm_lt_one
    (φ : ℝ → ℝ)
    {a b p q : ℕ}
    {m : ℤ}
    (hp : p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)
    (hq : q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    ‖deriv φ q - deriv φ p‖ < 1 := by
  have hupper :
      deriv φ q - deriv φ p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      φ hp hq
  have hlower_oriented :
      deriv φ p - deriv φ q < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      φ hq hp
  have hneg_lower :
      -1 < deriv φ q - deriv φ p := by
    have hneg_lt :
        -(1 : ℝ) < -(deriv φ p - deriv φ q) :=
      neg_lt_neg hlower_oriented
    exact lt_of_lt_of_eq hneg_lt
      (neg_sub (deriv φ p) (deriv φ q))
  have habs :
      |deriv φ q - deriv φ p| < 1 :=
    abs_lt.mpr (And.intro hneg_lower hupper)
  have hnorm :
      ‖deriv φ q - deriv φ p‖ =
        |deriv φ q - deriv φ p| :=
    Real.norm_eq_abs (deriv φ q - deriv φ p)
  exact
    Eq.subst
      (motive := fun r : ℝ => r < 1)
      hnorm.symm
      habs

/-- The integer frequency window index attached to one integer sample. -/
def Complex.realPhase_secondDerivative_vdc_derivPacketIndex
    (φ : ℝ → ℝ)
    (n : ℕ) : ℤ :=
  ⌊deriv φ n + (1 / 2 : ℝ)⌋

/-- The finite set of derivative-frequency packets that can be occupied by
samples from the integer block. -/
def Complex.realPhase_secondDerivative_vdc_activeDerivPackets
    (φ : ℝ → ℝ)
    (a b : ℕ) : Finset ℤ :=
  (Finset.Icc a b).image
    (fun n : ℕ => Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n)

/-- The packet index attached to a block sample is active. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b := by
  exact Finset.mem_image.mpr
    (Exists.intro n (And.intro hn rfl))

/-- The active packet set has cardinality bounded by the cardinality of the
underlying integer block. -/
theorem Complex.realPhase_secondDerivative_vdc_activeDerivPackets_card_le_block
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b).card ≤
      (Finset.Icc a b).card := by
  exact Finset.card_image_le

/-- The active packet count is bounded by the real block cardinality. -/
theorem Complex.realPhase_secondDerivative_vdc_activeDerivPackets_card_real_le_block
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ((Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b).card : ℝ) ≤
      ((Finset.Icc a b).card : ℝ) := by
  exact Nat.cast_le.mpr
    (Complex.realPhase_secondDerivative_vdc_activeDerivPackets_card_le_block φ a b)

/-- The floor-selected packet index puts a sample into its own derivative
window. -/
theorem Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    n ∈
      Complex.realPhase_secondDerivative_vdc_derivPacket φ a b
        (Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n) := by
  let x : ℝ := deriv φ n
  let m : ℤ := ⌊x + (1 / 2 : ℝ)⌋
  have hm_eq :
      m = Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n :=
    rfl
  have hfloor_lower_raw : (m : ℝ) ≤ x + (1 / 2 : ℝ) :=
    Int.floor_le (x + (1 / 2 : ℝ))
  have hlower :
      (m : ℝ) - (1 / 2 : ℝ) ≤ x :=
    (sub_le_iff_le_add).mpr hfloor_lower_raw
  have hfloor_upper_raw :
      x + (1 / 2 : ℝ) < (m : ℝ) + 1 :=
    Int.lt_floor_add_one (x + (1 / 2 : ℝ))
  have hupper_raw :
      x < (m : ℝ) + 1 - (1 / 2 : ℝ) :=
    (lt_sub_iff_add_lt).mpr hfloor_upper_raw
  have hone_sub_half :
      (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) :=
    (eq_sub_iff_add_eq.mpr (add_halves (1 : ℝ))).symm
  have hupper_edge :
      (m : ℝ) + 1 - (1 / 2 : ℝ) =
        (m : ℝ) + (1 / 2 : ℝ) := by
    calc
      (m : ℝ) + 1 - (1 / 2 : ℝ) =
          (m : ℝ) + (1 - (1 / 2 : ℝ)) := by
        exact add_sub_assoc (m : ℝ) 1 (1 / 2 : ℝ)
      _ = (m : ℝ) + (1 / 2 : ℝ) := by
        exact congrArg (fun y : ℝ => (m : ℝ) + y) hone_sub_half
  have hupper :
      x < (m : ℝ) + (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun r : ℝ => x < r)
      hupper_edge
      hupper_raw
  have hmem_m :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff φ).mpr
        (And.intro hn
        (And.intro
          (Eq.subst
            (motive := fun y : ℝ =>
              (m : ℝ) - (1 / 2 : ℝ) ≤ y)
            rfl
            hlower)
          (Eq.subst
            (motive := fun y : ℝ =>
              y < (m : ℝ) + (1 / 2 : ℝ))
            rfl
            hupper)))
  exact
    Eq.subst
      (motive := fun k : ℤ =>
        n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b k)
      hm_eq
      hmem_m

/-- Every block sample lies in one active derivative-frequency packet. -/
theorem Complex.realPhase_secondDerivative_vdc_exists_active_derivPacket
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    ∃ m : ℤ,
      m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b ∧
        n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m := by
  let m : ℤ := Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n
  have hm_active :
      m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hn
  have hn_packet :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hn
  exact Exists.intro m (And.intro hm_active hn_packet)

/-- A half-open derivative packet is exactly the fiber of the packet-index map
inside the ambient integer block. -/
theorem Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ} :
    n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ↔
      n ∈ Finset.Icc a b ∧
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m := by
  constructor
  · intro hn
    let x : ℝ := deriv φ n
    have hblock : n ∈ Finset.Icc a b :=
      Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
    have hlower :
        (m : ℝ) - (1 / 2 : ℝ) ≤ x :=
      Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
    have hupper :
        x < (m : ℝ) + (1 / 2 : ℝ) :=
      Complex.realPhase_secondDerivative_vdc_derivPacket_upper φ hn
    have hfloor_lower :
        (m : ℝ) ≤ x + (1 / 2 : ℝ) :=
      (sub_le_iff_le_add).mp hlower
    have hfloor_upper :
        x + (1 / 2 : ℝ) < (m : ℝ) + 1 := by
      have hhalf_add_half : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 :=
        add_halves (1 : ℝ)
      have hupper_add :
          x + (1 / 2 : ℝ) <
            ((m : ℝ) + (1 / 2 : ℝ)) + (1 / 2 : ℝ) :=
        add_lt_add_right hupper (1 / 2 : ℝ)
      have hedge :
          ((m : ℝ) + (1 / 2 : ℝ)) + (1 / 2 : ℝ) =
            (m : ℝ) + 1 := by
        calc
          ((m : ℝ) + (1 / 2 : ℝ)) + (1 / 2 : ℝ) =
              (m : ℝ) + ((1 / 2 : ℝ) + (1 / 2 : ℝ)) :=
            add_assoc (m : ℝ) (1 / 2 : ℝ) (1 / 2 : ℝ)
          _ = (m : ℝ) + 1 := by
            exact congrArg (fun y : ℝ => (m : ℝ) + y) hhalf_add_half
      exact
        Eq.subst
          (motive := fun r : ℝ => x + (1 / 2 : ℝ) < r)
          hedge
          hupper_add
    have hfloor :
        ⌊x + (1 / 2 : ℝ)⌋ = m :=
      Int.floor_eq_iff.mpr
        (And.intro hfloor_lower hfloor_upper)
    have hindex :
        Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
      hfloor
    exact And.intro hblock hindex
  · intro hn
    have hblock : n ∈ Finset.Icc a b := hn.1
    have hown :
        n ∈
          Complex.realPhase_secondDerivative_vdc_derivPacket φ a b
            (Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n) :=
      Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hblock
    exact
      Eq.subst
        (motive := fun k : ℤ =>
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b k)
        hn.2
        hown

/-- Distinct active derivative packets are disjoint. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_disjoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m₁ m₂ : ℤ}
    (hm : m₁ ≠ m₂) :
    Disjoint
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₁)
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₂) := by
  exact Finset.disjoint_left.mpr
    (fun n hn₁ hn₂ =>
        have hidx₁ :
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m₁ :=
        ((Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
          φ).mp hn₁).2
        have hidx₂ :
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m₂ :=
        ((Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
          φ).mp hn₂).2
        have hm_eq : m₁ = m₂ :=
        hidx₁.symm.trans hidx₂
      hm hm_eq)

/-- Any nonempty derivative packet has an active packet index. -/
theorem Complex.realPhase_secondDerivative_vdc_derivPacket_index_active_of_mem
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {m : ℤ}
    {n : ℕ}
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b := by
  have hblock : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hidx :
      Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
    ((Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq
      φ).mp hn).2
  have hactive_index :
      Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hblock
  exact
    Eq.subst
      (motive := fun k : ℤ =>
        k ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b)
      hidx
      hactive_index

/-- Every block sample is contained in the union of active derivative packets,
expressed as an existential cover. -/
theorem Complex.realPhase_secondDerivative_vdc_block_subset_activePacket_exists
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    ∃ m : ℤ,
      m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b ∧
        n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
  Complex.realPhase_secondDerivative_vdc_exists_active_derivPacket φ hn

/-- Every active-packet member lies in the original block. -/
theorem Complex.realPhase_secondDerivative_vdc_activePacket_member_mem_block
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {m : ℤ}
    (hm : m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b)
    (hn : n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m) :
    n ∈ Finset.Icc a b :=
  Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn

/-- The finite union of all active derivative-frequency packets. -/
def Complex.realPhase_secondDerivative_vdc_activePacketUnion
    (φ : ℝ → ℝ)
    (a b : ℕ) : Finset ℕ :=
  (Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b).biUnion
    (fun m : ℤ => Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)

/-- Membership in the active packet union is equivalent to membership in the
original integer block. -/
theorem Complex.mem_realPhase_secondDerivative_vdc_activePacketUnion_iff
    (φ : ℝ → ℝ)
    {a b n : ℕ} :
    n ∈ Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b ↔
      n ∈ Finset.Icc a b := by
  constructor
  · intro hn
    have hexists :
        ∃ m : ℤ,
          m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
        Finset.mem_biUnion.mp hn
    match hexists with
    | Exists.intro m hmhn =>
        exact
          Complex.realPhase_secondDerivative_vdc_activePacket_member_mem_block
            φ hmhn.1 hmhn.2
  · intro hn
    have hexists :
        ∃ m : ℤ,
          m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
      Complex.realPhase_secondDerivative_vdc_block_subset_activePacket_exists
        φ hn
    exact Finset.mem_biUnion.mpr hexists

/-- The active packet union is exactly the original integer block. -/
theorem Complex.realPhase_secondDerivative_vdc_activePacketUnion_eq_block
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b =
        Finset.Icc a b :=
  Finset.ext
    (fun n =>
      Complex.mem_realPhase_secondDerivative_vdc_activePacketUnion_iff φ)

/-- Active derivative packets are pairwise disjoint as a finite family. -/
theorem Complex.realPhase_secondDerivative_vdc_activeDerivPackets_pairwiseDisjoint
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ∀ m₁ ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
      ∀ m₂ ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        m₁ ≠ m₂ →
          Disjoint
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₁)
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₂) := by
  intro m₁ hm₁ m₂ hm₂ hne
  exact
    Complex.realPhase_secondDerivative_vdc_derivPacket_disjoint
      φ hne

/-- The original block sum is the sum over the active packet union. -/
theorem Complex.realPhase_secondDerivative_vdc_block_sum_eq_activePacketUnion_sum
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))) =
    ∑ n ∈ Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b,
      Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact
    congrArg
      (fun s : Finset ℕ =>
        ∑ n ∈ s, Complex.exp (Complex.I * (φ n : ℂ)))
        (Complex.realPhase_secondDerivative_vdc_activePacketUnion_eq_block
        φ a b).symm

/-- The finite exponential sum over one derivative-frequency packet. -/
def Complex.realPhase_secondDerivative_vdc_packetSum
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (m : ℤ) : ℂ :=
  ∑ n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m,
    Complex.exp (Complex.I * (φ n : ℂ))

/-- The active packet union sum expands as the sum of packet sums. -/
theorem Complex.realPhase_secondDerivative_vdc_activePacketUnion_sum_eq_packetSums
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b,
      Complex.exp (Complex.I * (φ n : ℂ))) =
    ∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b m := by
  exact
    Finset.sum_biUnion
        (Complex.realPhase_secondDerivative_vdc_activeDerivPackets_pairwiseDisjoint
        φ a b)

/-- The total active-packet sum is exactly the original integer-block sum. -/
theorem Complex.realPhase_secondDerivative_vdc_activePacketSums_eq_block_sum
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b m) =
    ∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ)) := by
  have hblock_to_union :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
      ∑ n ∈ Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b,
        Complex.exp (Complex.I * (φ n : ℂ)) :=
    Complex.realPhase_secondDerivative_vdc_block_sum_eq_activePacketUnion_sum
      φ a b
  have hunion_to_packets :
      (∑ n ∈ Complex.realPhase_secondDerivative_vdc_activePacketUnion φ a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
      ∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m :=
    Complex.realPhase_secondDerivative_vdc_activePacketUnion_sum_eq_packetSums
      φ a b
  exact (hblock_to_union.trans hunion_to_packets).symm

/-- Norm form of the exact active-packet reconstruction. -/
theorem Complex.realPhase_secondDerivative_vdc_activePacketSums_norm_eq_block_norm
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ =
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ :=
  congrArg norm
    (Complex.realPhase_secondDerivative_vdc_activePacketSums_eq_block_sum
      φ a b)

/-- Trivial cardinality bound for one derivative-frequency packet. -/
theorem Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (m : ℤ) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) := by
  have hunit :
      ∀ n : ℕ,
        n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m →
          ‖Complex.exp (Complex.I * (φ n : ℂ))‖ ≤ 1 := by
    intro n hn
    exact le_of_eq (Complex.realPhase_exp_I_norm φ n)
  exact
    Complex.finite_sum_norm_le_card_of_norm_le_one
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)
      (fun n : ℕ => Complex.exp (Complex.I * (φ n : ℂ)))
      hunit

/-- A derivative-frequency packet whose cardinality is already within the
final VdC target has its packet sum within the same target. -/
theorem Complex.realPhase_secondDerivative_vdc_packetSum_bound_of_card_le_target
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    {m : ℤ}
    (hcard :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T))) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ ≤
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  exact
    le_trans
        (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card φ a b m)
      hcard

/-- Shifted phase difference used in Weyl differencing for an abstract real
phase. -/
def Complex.realPhase_secondDerivative_vdc_shiftedDifference
    (φ : ℝ → ℝ)
    (h : ℕ)
    (x : ℝ) : ℝ :=
  φ (x + h) - φ x

/-- Shifted correlation sum appearing in the abstract Weyl-differencing
B-process. -/
def Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
    (φ : ℝ → ℝ)
    (h a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc a (b - h),
    Complex.exp
        (Complex.I *
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ))

/-- The shifted-difference phase has unit-modulus exponential terms. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedDifference_exp_norm
    (φ : ℝ → ℝ)
    (h n : ℕ) :
    ‖Complex.exp
        (Complex.I *
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ))‖ = 1 := by
  exact
    Complex.realPhase_exp_I_norm
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) n

/-- Unit coefficient attached to an abstract real phase. -/
def Complex.realPhase_secondDerivative_vdc_coefficient
    (φ : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (φ n : ℂ))

/-- Squared complex norm as `Complex.normSq`, in the form needed by the
finite Weyl expansion. -/
theorem Complex.norm_sq_eq_normSq
    (z : ℂ) :
    ‖z‖ ^ 2 = Complex.normSq z := by
  have hnorm_abs : ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  have hsq_abs : Complex.abs z ^ 2 = Complex.normSq z :=
    (Complex.normSq_eq_abs z).symm
  exact Eq.trans
    (congrArg (fun r : ℝ => r ^ 2) hnorm_abs)
    hsq_abs

/-- Original coefficient block for an abstract real phase. -/
def Complex.realPhase_secondDerivative_vdc_coefficientBlock
    (φ : ℝ → ℝ)
    (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc a b,
    Complex.realPhase_secondDerivative_vdc_coefficient φ n

/-- The coefficient block is the original real-phase exponential sum. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_eq_original_sum
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  exact Eq.refl
    (∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ)))

/-- Norm form of the coefficient-block identity. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_eq_original_sum_norm
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
  congrArg norm
    (Complex.realPhase_secondDerivative_vdc_coefficientBlock_eq_original_sum
      φ a b)

/-- The abstract real-phase coefficient has unit norm. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficient_norm
    (φ : ℝ → ℝ)
    (n : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficient φ n‖ = 1 := by
  exact Complex.realPhase_exp_I_norm φ n

/-- The abstract real-phase coefficient has unit `normSq`. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficient_normSq
    (φ : ℝ → ℝ)
    (n : ℕ) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficient φ n) = 1 := by
  have hnorm_sq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficient φ n‖ ^ 2 =
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficient φ n) :=
    Complex.norm_sq_eq_normSq
        (Complex.realPhase_secondDerivative_vdc_coefficient φ n)
  have hnorm :
      ‖Complex.realPhase_secondDerivative_vdc_coefficient φ n‖ = 1 :=
    Complex.realPhase_secondDerivative_vdc_coefficient_norm φ n
  have hone_sq : (1 : ℝ) ^ 2 = 1 := by
    calc
      (1 : ℝ) ^ 2 = (1 : ℝ) * 1 :=
        pow_two (1 : ℝ)
      _ = 1 :=
        mul_one (1 : ℝ)
  have hleft :
      ‖Complex.realPhase_secondDerivative_vdc_coefficient φ n‖ ^ 2 = 1 :=
    Eq.trans
      (congrArg (fun r : ℝ => r ^ 2) hnorm)
      hone_sq
  exact Eq.trans hnorm_sq.symm hleft

/-- Coefficient blocks are trivially bounded by their length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_blockLength
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      ((Finset.Icc a b).card : ℝ) := by
  have hunit :
      ∀ n : ℕ,
        n ∈ Finset.Icc a b →
          ‖Complex.realPhase_secondDerivative_vdc_coefficient φ n‖ ≤ 1 := by
    intro n hn
    exact le_of_eq
        (Complex.realPhase_secondDerivative_vdc_coefficient_norm φ n)
  exact
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Finset.Icc a b)
        (Complex.realPhase_secondDerivative_vdc_coefficient φ)
      hunit

/-- Coefficient blocks are trivially bounded by the real endpoint length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_endpoint_length
    (φ : ℝ → ℝ)
    {a b : ℕ}
    (hab : a ≤ b + 1) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  exact le_trans
    (Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_blockLength
      φ a b)
    (Real.secondDerivativeVdc_card_Icc_le_endpoint_length hab)

/-- Conjugating a real-phase coefficient changes the sign of the phase. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficient_conj
    (φ : ℝ → ℝ)
    (n : ℕ) :
    star (Complex.realPhase_secondDerivative_vdc_coefficient φ n) =
      Complex.exp (Complex.I * (-(φ n) : ℂ)) := by
  have hstar_exp :
      star (Complex.exp (Complex.I * (φ n : ℂ))) =
        Complex.exp (star (Complex.I * (φ n : ℂ))) :=
    (Complex.exp_conj (Complex.I * (φ n : ℂ))).symm
  have hstar_arg :
      star (Complex.I * (φ n : ℂ)) =
        Complex.I * (-(φ n) : ℂ) := by
    calc
      star (Complex.I * (φ n : ℂ)) =
          star Complex.I * star (φ n : ℂ) := by
        exact (starRingEnd ℂ).map_mul Complex.I (φ n : ℂ)
      _ = (-Complex.I) * star (φ n : ℂ) := by
        exact congrArg (fun z : ℂ => z * star (φ n : ℂ)) Complex.conj_I
      _ = (-Complex.I) * (φ n : ℂ) := by
        exact congrArg (fun z : ℂ => (-Complex.I) * z)
          (Complex.conj_ofReal (φ n))
      _ = Complex.I * (-(φ n) : ℂ) := by
        calc
          (-Complex.I) * (φ n : ℂ) =
              -(Complex.I * (φ n : ℂ)) := by
            exact neg_mul Complex.I (φ n : ℂ)
          _ = Complex.I * (-(φ n : ℂ)) := by
            exact (mul_neg Complex.I (φ n : ℂ)).symm
          _ = Complex.I * (-(φ n) : ℂ) := by
            exact rfl
  exact Eq.trans hstar_exp (congrArg Complex.exp hstar_arg)

/-- A shifted-difference exponential is the shifted coefficient times the
conjugate unshifted coefficient. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedDifference_exp_eq_coeff_mul_conj
    (φ : ℝ → ℝ)
    (h n : ℕ) :
    Complex.exp
        (Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ)) =
      Complex.realPhase_secondDerivative_vdc_coefficient φ (n + h) *
        star (Complex.realPhase_secondDerivative_vdc_coefficient φ n) := by
  have hphase_sub :
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ) =
        (φ ((n + h : ℕ) : ℝ) : ℂ) + (-(φ n) : ℂ) := by
    have hnat_add :
        (((n + h : ℕ) : ℝ)) = (n : ℝ) + h :=
      Nat.cast_add n h
    have hphase_shift :
        φ ((n : ℝ) + h) = φ ((n + h : ℕ) : ℝ) :=
      congrArg φ hnat_add.symm
    show
        ((φ ((n : ℝ) + h) - φ n : ℝ) : ℂ) =
          (φ ((n + h : ℕ) : ℝ) : ℂ) + (-(φ n) : ℂ)
    calc
      ((φ ((n : ℝ) + h) - φ n : ℝ) : ℂ) =
          (φ ((n : ℝ) + h) : ℂ) - (φ n : ℂ) := by
        exact Complex.ofReal_sub (φ ((n : ℝ) + h)) (φ n)
      _ = (φ ((n : ℝ) + h) : ℂ) + -(φ n : ℂ) := by
        exact sub_eq_add_neg (φ ((n : ℝ) + h) : ℂ) (φ n : ℂ)
      _ = (φ ((n + h : ℕ) : ℝ) : ℂ) + -(φ n : ℂ) := by
        exact congrArg
          (fun y : ℝ => (y : ℂ) + -(φ n : ℂ))
          hphase_shift
      _ = (φ ((n + h : ℕ) : ℝ) : ℂ) + (-(φ n) : ℂ) := by
        exact Eq.refl ((φ ((n + h : ℕ) : ℝ) : ℂ) + (-(φ n) : ℂ))
  have harg :
      Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ) =
        Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ) +
          Complex.I * (-(φ n) : ℂ) := by
    calc
      Complex.I *
          (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ) =
          Complex.I * ((φ ((n + h : ℕ) : ℝ) : ℂ) + (-(φ n) : ℂ)) := by
        exact congrArg (fun z : ℂ => Complex.I * z) hphase_sub
      _ =
          Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ) +
            Complex.I * (-(φ n) : ℂ) := by
        exact mul_add Complex.I (φ ((n + h : ℕ) : ℝ) : ℂ) (-(φ n) : ℂ)
  have hexp_split :
      Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ)) =
        Complex.exp (Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (-(φ n) : ℂ)) := by
    exact Eq.trans
      (congrArg Complex.exp harg)
        (Complex.exp_add
        (Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ))
        (Complex.I * (-(φ n) : ℂ)))
  have hcoeff_shift :
      Complex.realPhase_secondDerivative_vdc_coefficient φ (n + h) =
        Complex.exp (Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ)) := by
    exact rfl
  have hcoeff_conj :
      star (Complex.realPhase_secondDerivative_vdc_coefficient φ n) =
        Complex.exp (Complex.I * (-(φ n) : ℂ)) :=
    Complex.realPhase_secondDerivative_vdc_coefficient_conj φ n
  have hright :
      Complex.realPhase_secondDerivative_vdc_coefficient φ (n + h) *
        star (Complex.realPhase_secondDerivative_vdc_coefficient φ n) =
        Complex.exp (Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (-(φ n) : ℂ)) := by
    exact Eq.trans
      (congrArg
        (fun z : ℂ =>
          z * star (Complex.realPhase_secondDerivative_vdc_coefficient φ n))
        hcoeff_shift)
      (congrArg
        (fun z : ℂ => Complex.exp (Complex.I * (φ ((n + h : ℕ) : ℝ) : ℂ)) * z)
        hcoeff_conj)
  exact Eq.trans hexp_split hright.symm

/-- Coefficient-side shifted autocorrelation over the part of the block where
both `n` and `n + h` remain in range. -/
def Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation
    (φ : ℝ → ℝ)
    (h a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc a (b - h),
    Complex.realPhase_secondDerivative_vdc_coefficient φ (n + h) *
      star (Complex.realPhase_secondDerivative_vdc_coefficient φ n)

/-- The phase-difference shifted correlation is the coefficient-side shifted
autocorrelation. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_eq_coefficientShiftedCorrelation
    (φ : ℝ → ℝ)
    (h a b : ℕ) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b =
      Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b := by
  show
      (∑ n ∈ Finset.Icc a (b - h),
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ))) =
        ∑ n ∈ Finset.Icc a (b - h),
          Complex.realPhase_secondDerivative_vdc_coefficient φ (n + h) *
            star (Complex.realPhase_secondDerivative_vdc_coefficient φ n)
  exact Finset.sum_congr (Eq.refl (Finset.Icc a (b - h)))
    (fun n hn =>
      Complex.realPhase_secondDerivative_vdc_shiftedDifference_exp_eq_coeff_mul_conj
        φ h n)

/-- Norm form of the shifted-correlation coefficient bridge. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_eq_coefficientShiftedCorrelation_norm
    (φ : ℝ → ℝ)
    (h a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ =
      ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖ :=
  congrArg norm
    (Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_eq_coefficientShiftedCorrelation
      φ h a b)

/-- Trivial cardinality bound for one shifted correlation. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_le_card
    (φ : ℝ → ℝ)
    (h a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤
      ((Finset.Icc a (b - h)).card : ℝ) := by
  have hunit :
      ∀ n : ℕ,
        n ∈ Finset.Icc a (b - h) →
          ‖Complex.exp
            (Complex.I *
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ))‖ ≤
            1 := by
    intro n hn
    exact le_of_eq
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference_exp_norm
        φ h n)
  exact
    Complex.finite_sum_norm_le_card_of_norm_le_one
      (Finset.Icc a (b - h))
      (fun n : ℕ =>
        Complex.exp
          (Complex.I *
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h n : ℂ)))
      hunit

/-- Trivial cardinality bound for coefficient-side shifted autocorrelations. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation_norm_le_card
    (φ : ℝ → ℝ)
    (h a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖ ≤
      ((Finset.Icc a (b - h)).card : ℝ) := by
  have hnorm_eq :
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ =
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖ :=
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_eq_coefficientShiftedCorrelation_norm
      φ h a b
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        r ≤ ((Finset.Icc a (b - h)).card : ℝ))
      hnorm_eq
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_le_card
        φ h a b)

/-- First-derivative estimate for an abstract shifted-correlation block, with
the actual finite-difference hypotheses exposed. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_firstDerivative_data
    (φ : ℝ → ℝ)
    {a b h : ℕ}
    {lam : ℝ}
    (ha : 1 ≤ a)
    (habh : a ≤ b - h)
    (hlam_pos : 0 < lam)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          lam ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h) lam) :
    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤
      4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ := by
  exact
    Complex.realPhase_firstDerivative_integer_block_bound
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h)
      ha habh hlam_pos hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- The curvature-scale lower parameter for a nonzero shift is positive. -/
theorem Real.secondDerivativeVdc_shiftedLowerParameter_pos
    {b h : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hpos : 1 ≤ h) :
    0 <
      T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (h : ℝ) := by
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one hT
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hBB_pos :
      0 <
        (((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ))) :=
    mul_pos hB_pos hB_pos
  have hBB_inv_pos :
      0 <
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) :=
    inv_pos.mpr hBB_pos
  have hh_pos : 0 < (h : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hpos)
  exact
    mul_pos
      (mul_pos hT_pos hBB_inv_pos)
      hh_pos

/-- Shifted-correlation estimate at the curvature-growth scale, with the
remaining first-derivative finite-difference data exposed. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_curvatureScale_data
    (φ : ℝ → ℝ)
    {a b h : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (hpos : 1 ≤ h)
    (habh : a ≤ b - h)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
        (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ) ≤
            ‖deriv
              (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h)
        (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))) :
    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤
      4 *
          ((T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))⁻¹ +
            1) +
        4 * Real.pi *
          (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))⁻¹ := by
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_firstDerivative_data
      φ ha habh
      (Real.secondDerivativeVdc_shiftedLowerParameter_pos hT hpos)
      hderiv_antitone hderiv_lower hinc_mono hred_mono hsep

/-- Positive shifts used in the finite Weyl-differencing average. -/
def Complex.realPhase_secondDerivative_vdc_shiftRange
    (H : ℕ) : Finset ℕ :=
  Finset.Icc 1 H

/-- The total shifted-correlation envelope over the positive Weyl shifts. -/
def Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖

/-- Length of the original integer block as a real number. -/
def Real.secondDerivativeVdc_blockLength
    (a b : ℕ) : ℝ :=
  ((Finset.Icc a b).card : ℝ)

/-- The block-length definition is nonnegative. -/
theorem Real.secondDerivativeVdc_blockLength_nonneg
    (a b : ℕ) :
    0 ≤ Real.secondDerivativeVdc_blockLength a b := by
  exact Nat.cast_nonneg (Finset.Icc a b).card

/-- The block-length definition agrees with the endpoint length when the
successor-right endpoint contains the left endpoint. -/
theorem Real.secondDerivativeVdc_blockLength_eq_endpoint_length
    {a b : ℕ}
    (hab : a ≤ b + 1) :
    Real.secondDerivativeVdc_blockLength a b =
      (((b + 1 : ℕ) : ℝ) - (a : ℝ)) := by
  exact Real.secondDerivativeVdc_card_Icc_eq_endpoint_length hab

/-- The diagonal term in the coefficient-block autocorrelation is exactly the
block length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficient_diagonal_sum_eq_blockLength
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    (∑ n ∈ Finset.Icc a b,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficient φ n)) =
      Real.secondDerivativeVdc_blockLength a b := by
  have hunit_sum :
      (∑ n ∈ Finset.Icc a b,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficient φ n)) =
        ∑ n ∈ Finset.Icc a b, (1 : ℝ) :=
    Finset.sum_congr
      (Eq.refl (Finset.Icc a b))
      (fun n hn =>
        Complex.realPhase_secondDerivative_vdc_coefficient_normSq φ n)
  have hconst :
      (∑ n ∈ Finset.Icc a b, (1 : ℝ)) =
        ((Finset.Icc a b).card : ℝ) := by
    calc
      (∑ n ∈ Finset.Icc a b, (1 : ℝ)) =
          (Finset.Icc a b).card • (1 : ℝ) :=
        Finset.sum_const (1 : ℝ)
      _ = ((Finset.Icc a b).card : ℝ) * 1 :=
        nsmul_eq_mul (Finset.Icc a b).card (1 : ℝ)
      _ = ((Finset.Icc a b).card : ℝ) :=
        mul_one ((Finset.Icc a b).card : ℝ)
  exact Eq.trans hunit_sum hconst

/-- The coefficient-block trivial estimate in block-length notation. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_real_blockLength
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.secondDerivativeVdc_blockLength a b := by
  exact
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_blockLength
      φ a b

/-- Norm-square form of the coefficient-block square. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_eq_normSq
    (φ : ℝ → ℝ)
    (a b : ℕ) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 =
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
  Complex.norm_sq_eq_normSq
    (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b)

/-- Weyl-differencing majorant before arithmetic optimization. -/
def Real.secondDerivativeVdc_weylEnvelopeMajorant
    (a b H : ℕ)
    (envelope : ℝ) : ℝ :=
  Real.sqrt
    (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
      (((Real.secondDerivativeVdc_blockLength a b) +
          2 * envelope) *
        ((H : ℝ)⁻¹)))

/-- Weyl-differencing majorant retaining the exact weighted positive-shift
autocorrelation mass before replacing every weight by the full shift length. -/
def Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant
    (a b H : ℕ)
    (weightedMass : ℝ) : ℝ :=
  Real.sqrt
    (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
      (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass) *
        (((H : ℝ) * (H : ℝ))⁻¹)))

/-- The Weyl-envelope majorant is nonnegative. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_nonneg
    (a b H : ℕ)
    (envelope : ℝ) :
    0 ≤ Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope := by
  exact Real.sqrt_nonneg
    (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
      (((Real.secondDerivativeVdc_blockLength a b) +
          2 * envelope) *
        ((H : ℝ)⁻¹)))

/-- The weighted Weyl-envelope majorant is nonnegative. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_nonneg
    (a b H : ℕ)
    (weightedMass : ℝ) :
    0 ≤ Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant
      a b H weightedMass := by
  exact Real.sqrt_nonneg
    (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
      (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass) *
        (((H : ℝ) * (H : ℝ))⁻¹)))

/-- The left factor in the Weyl-envelope majorant is nonnegative. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_leftFactor_nonneg
    (a b H : ℕ) :
    0 ≤ Real.secondDerivativeVdc_blockLength a b + (H : ℝ) := by
  exact add_nonneg
    (Real.secondDerivativeVdc_blockLength_nonneg a b)
    (Nat.cast_nonneg H)

/-- The reciprocal of a positive Weyl averaging length is nonnegative. -/
theorem Real.secondDerivativeVdc_shiftLength_inv_nonneg
    {H : ℕ}
    (hH : 1 ≤ H) :
    0 ≤ ((H : ℝ)⁻¹) := by
  have hH_pos : 0 < (H : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hH)
  exact inv_nonneg.mpr (le_of_lt hH_pos)

/-- The inner envelope factor is monotone in the shifted-correlation envelope. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_inner_mono
    {a b H : ℕ}
    {envelope envelope' : ℝ}
    (hH : 1 ≤ H)
    (henv : envelope ≤ envelope') :
    ((Real.secondDerivativeVdc_blockLength a b) + 2 * envelope) *
        ((H : ℝ)⁻¹) ≤
      ((Real.secondDerivativeVdc_blockLength a b) + 2 * envelope') *
        ((H : ℝ)⁻¹) := by
  have htwo_env :
      2 * envelope ≤ 2 * envelope' :=
    mul_le_mul_of_nonneg_left henv zero_le_two
  have hadd :
      Real.secondDerivativeVdc_blockLength a b + 2 * envelope ≤
        Real.secondDerivativeVdc_blockLength a b + 2 * envelope' :=
    add_le_add_left htwo_env (Real.secondDerivativeVdc_blockLength a b)
  exact mul_le_mul_of_nonneg_right
    hadd
    (Real.secondDerivativeVdc_shiftLength_inv_nonneg hH)

/-- The Weyl-envelope majorant is monotone in the shifted-correlation
envelope. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_mono
    {a b H : ℕ}
    {envelope envelope' : ℝ}
    (hH : 1 ≤ H)
    (henv : envelope ≤ envelope') :
    Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope' := by
  have hinner :
      ((Real.secondDerivativeVdc_blockLength a b) + 2 * envelope) *
          ((H : ℝ)⁻¹) ≤
        ((Real.secondDerivativeVdc_blockLength a b) + 2 * envelope') *
          ((H : ℝ)⁻¹) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_inner_mono hH henv
  have hproduct :
      ((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 * envelope) *
            ((H : ℝ)⁻¹)) ≤
        ((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 * envelope') *
            ((H : ℝ)⁻¹)) :=
    mul_le_mul_of_nonneg_left
      hinner
      (Real.secondDerivativeVdc_weylEnvelopeMajorant_leftFactor_nonneg a b H)
  exact Real.sqrt_le_sqrt hproduct

/-- The weighted Weyl-envelope majorant is monotone in the weighted
positive-difference mass. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_mono
    {a b H : ℕ}
    {weightedMass weightedMass' : ℝ}
    (hH : 1 ≤ H)
    (hmass : weightedMass ≤ weightedMass') :
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H weightedMass ≤
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant
        a b H weightedMass' := by
  have htwo_mass :
      2 * weightedMass ≤ 2 * weightedMass' :=
    mul_le_mul_of_nonneg_left hmass zero_le_two
  have hinner_left :
      (H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass ≤
        (H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass' :=
    add_le_add_left htwo_mass
      ((H : ℝ) * Real.secondDerivativeVdc_blockLength a b)
  have hH_pos : 0 < (H : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hH)
  have hHH_nonneg : 0 ≤ (H : ℝ) * (H : ℝ) :=
    mul_nonneg (le_of_lt hH_pos) (le_of_lt hH_pos)
  have hHH_inv_nonneg :
      0 ≤ (((H : ℝ) * (H : ℝ))⁻¹) :=
    inv_nonneg.mpr hHH_nonneg
  have hinner :
      ((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass) *
          (((H : ℝ) * (H : ℝ))⁻¹) ≤
        ((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 * weightedMass') *
          (((H : ℝ) * (H : ℝ))⁻¹) :=
    mul_le_mul_of_nonneg_right hinner_left hHH_inv_nonneg
  have hproduct :
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 * weightedMass) *
            (((H : ℝ) * (H : ℝ))⁻¹)) ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 * weightedMass') *
            (((H : ℝ) * (H : ℝ))⁻¹)) :=
    mul_le_mul_of_nonneg_left
      hinner
      (Real.secondDerivativeVdc_weylEnvelopeMajorant_leftFactor_nonneg a b H)
  exact Real.sqrt_le_sqrt hproduct

/-- Substituting `H` times an unweighted envelope into the weighted Weyl
majorant recovers the ordinary Weyl-envelope majorant. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_H_mul_eq_weylEnvelope
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (envelope : ℝ) :
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
        ((H : ℝ) * envelope) =
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope := by
  let h : ℝ := (H : ℝ)
  let B : ℝ := Real.secondDerivativeVdc_blockLength a b
  let E : ℝ := envelope
  let A : ℝ := B + h
  let C : ℝ := B + 2 * E
  have hh_pos : 0 < h :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hH)
  have hh_ne : h ≠ 0 :=
    ne_of_gt hh_pos
  have htwice :
      2 * (h * E) = h * (2 * E) := by
    calc
      2 * (h * E) = (2 * h) * E :=
        (mul_assoc 2 h E).symm
      _ = (h * 2) * E := by
        exact congrArg (fun r : ℝ => r * E) (mul_comm 2 h)
      _ = h * (2 * E) :=
        mul_assoc h 2 E
  have hweighted_inner_num :
      h * B + 2 * (h * E) = h * C := by
    calc
      h * B + 2 * (h * E) =
          h * B + h * (2 * E) := by
        exact congrArg (fun r : ℝ => h * B + r) htwice
      _ = h * (B + 2 * E) :=
        (mul_add h B (2 * E)).symm
      _ = h * C :=
        rfl
  have hweighted_inner :
      (h * B + 2 * (h * E)) * ((h * h)⁻¹) =
        C * h⁻¹ := by
    calc
      (h * B + 2 * (h * E)) * ((h * h)⁻¹) =
          (h * C) * ((h * h)⁻¹) := by
        exact congrArg (fun r : ℝ => r * ((h * h)⁻¹)) hweighted_inner_num
      _ = C * (h * ((h * h)⁻¹)) := by
        calc
          (h * C) * ((h * h)⁻¹) =
              (C * h) * ((h * h)⁻¹) := by
            exact congrArg (fun r : ℝ => r * ((h * h)⁻¹))
              (mul_comm h C)
          _ = C * (h * ((h * h)⁻¹)) :=
            mul_assoc C h ((h * h)⁻¹)
      _ = C * h⁻¹ := by
        have hcancel :
            h * ((h * h)⁻¹) = h⁻¹ := by
          have hmul_inv :
              (h * h)⁻¹ = h⁻¹ * h⁻¹ :=
            mul_inv_rev h h
          calc
            h * ((h * h)⁻¹) =
                h * (h⁻¹ * h⁻¹) := by
              exact congrArg (fun r : ℝ => h * r) hmul_inv
            _ = (h * h⁻¹) * h⁻¹ :=
              (mul_assoc h h⁻¹ h⁻¹).symm
            _ = 1 * h⁻¹ := by
              exact congrArg (fun r : ℝ => r * h⁻¹)
                (mul_inv_cancel₀ hh_ne)
            _ = h⁻¹ :=
              one_mul h⁻¹
        exact congrArg (fun r : ℝ => C * r) hcancel
  have hradicand :
      A * ((h * B + 2 * (h * E)) * ((h * h)⁻¹)) =
        A * (C * h⁻¹) :=
    congrArg (fun r : ℝ => A * r) hweighted_inner
  show
    Real.sqrt (A * ((h * B + 2 * (h * E)) * ((h * h)⁻¹))) =
      Real.sqrt (A * (C * h⁻¹))
  exact congrArg Real.sqrt hradicand

/-- A weighted Weyl-envelope majorant controlled by `H` times an envelope is
bounded by the ordinary Weyl-envelope majorant for that envelope. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_le_weylEnvelope_of_le_H_mul
    {a b H : ℕ}
    {weightedMass envelope : ℝ}
    (hH : 1 ≤ H)
    (hmass : weightedMass ≤ (H : ℝ) * envelope) :
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H weightedMass ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope := by
  have hmono :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H weightedMass ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          ((H : ℝ) * envelope) :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_mono hH hmass
  have heq :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          ((H : ℝ) * envelope) =
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_H_mul_eq_weylEnvelope
      hH envelope
  exact le_trans hmono (le_of_eq heq)

/-- Square-root elimination for the Weyl-envelope majorant. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_radicand_le_sq
    {a b H : ℕ}
    {envelope M : ℝ}
    (hM : 0 ≤ M)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
          (((Real.secondDerivativeVdc_blockLength a b) +
              2 * envelope) *
            ((H : ℝ)⁻¹)) ≤
        M ^ 2) :
    Real.secondDerivativeVdc_weylEnvelopeMajorant a b H envelope ≤ M := by
  have hsqrt_le :
      Real.sqrt
          (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
            (((Real.secondDerivativeVdc_blockLength a b) +
                2 * envelope) *
              ((H : ℝ)⁻¹))) ≤
        Real.sqrt (M ^ 2) :=
    Real.sqrt_le_sqrt hrad
  have hsqrt_sq : Real.sqrt (M ^ 2) = M :=
    Real.sqrt_sq_eq_abs M |>.trans (abs_of_nonneg hM)
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        Real.sqrt
          (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
            (((Real.secondDerivativeVdc_blockLength a b) +
                2 * envelope) *
              ((H : ℝ)⁻¹))) ≤ r)
      hsqrt_sq
      hsqrt_le

/-- Square-root elimination for the weighted Weyl-envelope majorant. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_le_of_radicand_le_sq
    {a b H : ℕ}
    {weightedMass M : ℝ}
    (hM : 0 ≤ M)
    (hrad :
      ((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 * weightedMass) *
            (((H : ℝ) * (H : ℝ))⁻¹)) ≤
        M ^ 2) :
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant
        a b H weightedMass ≤ M := by
  have hsqrt_le :
      Real.sqrt
          (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
            (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
                2 * weightedMass) *
              (((H : ℝ) * (H : ℝ))⁻¹))) ≤
        Real.sqrt (M ^ 2) :=
    Real.sqrt_le_sqrt hrad
  have hsqrt_sq : Real.sqrt (M ^ 2) = M :=
    Real.sqrt_sq_eq_abs M |>.trans (abs_of_nonneg hM)
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        Real.sqrt
          (((Real.secondDerivativeVdc_blockLength a b) + (H : ℝ)) *
            (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
                2 * weightedMass) *
              (((H : ℝ) * (H : ℝ))⁻¹))) ≤ r)
      hsqrt_sq
      hsqrt_le

/-- Coefficients extended by zero outside the original integer block.

This is the finite-algebra device used in the Weyl average: all translated
windows are summed over one ambient integer interval, while the coefficient
itself remembers the original block. -/
def Complex.realPhase_secondDerivative_vdc_coefficientExtended
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (n : ℤ) : ℂ :=
  if (a : ℤ) ≤ n ∧ n ≤ (b : ℤ) then
    Complex.realPhase_secondDerivative_vdc_coefficient φ n.toNat
  else
    0

/-- The zero-extended coefficient agrees with the integer-indexed coefficient
inside the original block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_mem
    (φ : ℝ → ℝ)
    (a b : ℕ)
    {n : ℤ}
    (hn : (a : ℤ) ≤ n ∧ n ≤ (b : ℤ)) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n =
      Complex.realPhase_secondDerivative_vdc_coefficient φ n.toNat := by
  exact if_pos hn

/-- The zero-extended coefficient vanishes outside the original block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_not_mem
    (φ : ℝ → ℝ)
    (a b : ℕ)
    {n : ℤ}
    (hn : ¬ ((a : ℤ) ≤ n ∧ n ≤ (b : ℤ))) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n = 0 := by
  exact if_neg hn

/-- Nat-indexed form of the zero-extension agreement on the original block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) =
      Complex.realPhase_secondDerivative_vdc_coefficient φ n := by
  have hbounds_nat : a ≤ n ∧ n ≤ b :=
    Finset.mem_Icc.mp hn
  have hbounds_int : (a : ℤ) ≤ (n : ℤ) ∧ (n : ℤ) ≤ (b : ℤ) :=
    And.intro
      (Int.ofNat_le.mpr hbounds_nat.1)
      (Int.ofNat_le.mpr hbounds_nat.2)
  have hext :
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) =
        Complex.realPhase_secondDerivative_vdc_coefficient φ ((n : ℤ).toNat) :=
    Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_mem
      φ a b hbounds_int
  have htoNat : ((n : ℤ).toNat) = n :=
    Int.toNat_natCast n
  exact Eq.trans hext
    (congrArg
      (fun k : ℕ => Complex.realPhase_secondDerivative_vdc_coefficient φ k)
      htoNat)

/-- A translated zero-extended coefficient can be nonzero only when the
translated index lies in the original block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_eq_zero_of_add_not_mem
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {m : ℤ}
    {h : ℕ}
    (hnot : ¬ ((a : ℤ) ≤ m + (h : ℤ) ∧ m + (h : ℤ) ≤ (b : ℤ))) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)) = 0 :=
  Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_not_mem
    φ a b hnot

/-- A nonzero translated term determines the original integer index that it
hits. -/
theorem Complex.realPhase_secondDerivative_vdc_translate_hit_index_mem
    {a b H : ℕ}
    {m : ℤ}
    {h : ℕ}
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hmh : (a : ℤ) ≤ m + (h : ℤ) ∧ m + (h : ℤ) ≤ (b : ℤ)) :
    ((m + (h : ℤ)).toNat) ∈ Finset.Icc a b := by
  have hleft_toNat :
      a ≤ (m + (h : ℤ)).toNat := by
    have hmono :
        (a : ℤ).toNat ≤ (m + (h : ℤ)).toNat :=
      Int.toNat_le_toNat hmh.1
    exact hmono
  have hright_toNat :
      (m + (h : ℤ)).toNat ≤ b :=
    Int.toNat_le.mpr hmh.2
  exact Finset.mem_Icc.mpr
    (And.intro hleft_toNat hright_toNat)

/-- Integer translate bases used in the finite Weyl average.  The interval
`[a-H, b]` contains the exact translate bases whose windows
`m + 1, ..., m + H` cover the original block; the final endpoint `b` adds a
zero translate, but gives the clean cardinality `blockLength + H`. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateBase
    (a b H : ℕ) : Finset ℤ :=
  Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ)

/-- One length-`H` translated window of the zero-extended coefficient sequence. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateSum
    (φ : ℝ → ℝ)
    (a b H : ℕ)
    (m : ℤ) : ℂ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))

/-- For a fixed original index `n`, the translate bases that hit `n` with a
positive Weyl shift. -/
def Complex.realPhase_secondDerivative_vdc_weylHitBases
    (a b H n : ℕ) : Finset ℤ :=
  (Complex.realPhase_secondDerivative_vdc_shiftRange H).image
    (fun h : ℕ => (n : ℤ) - (h : ℤ))

/-- A hit base obtained from a Weyl shift lies in the ambient translate base. -/
theorem Complex.realPhase_secondDerivative_vdc_weylHitBase_mem_translateBase
    {a b H n h : ℕ}
    (hn : n ∈ Finset.Icc a b)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    ((n : ℤ) - (h : ℤ)) ∈
      Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H := by
  show ((n : ℤ) - (h : ℤ)) ∈
    Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ)
  have hn_bounds : a ≤ n ∧ n ≤ b :=
    Finset.mem_Icc.mp hn
  have hh_bounds : 1 ≤ h ∧ h ≤ H :=
    Finset.mem_Icc.mp hh
  have hlower_left :
      (a : ℤ) - (H : ℤ) ≤ (a : ℤ) - (h : ℤ) :=
    sub_le_sub_left
      (Int.ofNat_le.mpr hh_bounds.2)
      (a : ℤ)
  have hlower_right :
      (a : ℤ) - (h : ℤ) ≤ (n : ℤ) - (h : ℤ) :=
    sub_le_sub_right
      (Int.ofNat_le.mpr hn_bounds.1)
      (h : ℤ)
  have hlower :
      (a : ℤ) - (H : ℤ) ≤ (n : ℤ) - (h : ℤ) :=
    le_trans hlower_left hlower_right
  have hsub_le_n :
      (n : ℤ) - (h : ℤ) ≤ (n : ℤ) :=
    sub_le_self (n : ℤ) (Int.natCast_nonneg h)
  have hupper :
      (n : ℤ) - (h : ℤ) ≤ (b : ℤ) :=
    le_trans hsub_le_n
      (Int.ofNat_le.mpr hn_bounds.2)
  exact Finset.mem_Icc.mpr (And.intro hlower hupper)

/-- The hit-base map `h ↦ n-h` is injective on the Weyl shift range. -/
theorem Complex.realPhase_secondDerivative_vdc_weylHitBase_injective
    {H n : ℕ} :
    Set.InjOn
      (fun h : ℕ => (n : ℤ) - (h : ℤ))
        (Complex.realPhase_secondDerivative_vdc_shiftRange H : Set ℕ) := by
  intro h₁ hh₁ h₂ hh₂ heq
  have hcast : (h₁ : ℤ) = (h₂ : ℤ) :=
    (Int.sub_left_inj (n : ℤ)).mp heq
  exact Int.ofNat.inj hcast

/-- The fixed-index hit-base set has exactly `H` elements. -/
theorem Complex.realPhase_secondDerivative_vdc_weylHitBases_card_eq
    (a b H n : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n).card = H := by
  show
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).image
        (fun h : ℕ => (n : ℤ) - (h : ℤ))).card = H
  have hshift_card :
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H := by
    have hcard :
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H + 1 - 1 :=
      Nat.card_Icc 1 H
    exact Eq.trans hcard (Nat.succ_sub_one H)
  have himage :
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).image
        (fun h : ℕ => (n : ℤ) - (h : ℤ))).card =
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card :=
    Finset.card_image_of_injOn
        (Complex.realPhase_secondDerivative_vdc_weylHitBase_injective
        (H := H) (n := n))
  exact Eq.trans himage hshift_card

/-- Summing a zero-extended coefficient over the hit bases of one original
index contributes exactly `H` copies of that coefficient. -/
theorem Complex.realPhase_secondDerivative_vdc_weylHitBases_sum_eq
    (φ : ℝ → ℝ)
    {a b H n : ℕ}
    (hn : n ∈ Finset.Icc a b) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
      (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficient φ n := by
  have hext :
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) =
        Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
    Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
      φ hn
  have hconst :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
        ((Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n).card : ℂ) *
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) :=
    Eq.trans
      (Finset.sum_const
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)))
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n).card
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)))
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n).card : ℂ) =
        (H : ℂ) :=
    congrArg (fun k : ℕ => (k : ℂ))
        (Complex.realPhase_secondDerivative_vdc_weylHitBases_card_eq a b H n)
  exact
    Eq.trans hconst
      (Eq.trans
        (congrArg
          (fun z : ℂ =>
            z *
              Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ))
          hcard)
        (congrArg
          (fun z : ℂ => (H : ℂ) * z)
          hext))

/-- Translating the ambient base interval by one fixed shift rewrites the
fixed-shift Weyl sum as a sum over the translated integer interval. -/
theorem Complex.realPhase_secondDerivative_vdc_fixedShift_translate_to_indexInterval
    (φ : ℝ → ℝ)
    {a b H h : ℕ} :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
      ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n := by
  show
      (∑ m ∈ Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
        ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n
  exact
    Finset.sum_bij
      (fun m _ => m + (h : ℤ))
      (fun m hm =>
        have hmbounds :
            (a : ℤ) - (H : ℤ) ≤ m ∧ m ≤ (b : ℤ) :=
          Finset.mem_Icc.mp hm
        Finset.mem_Icc.mpr
          (And.intro
            (add_le_add_right hmbounds.1 (h : ℤ))
            (add_le_add_right hmbounds.2 (h : ℤ))))
      (fun m₁ _hm₁ m₂ _hm₂ heq => add_right_cancel heq)
      (fun n hn =>
        have hnbounds :
            ((a : ℤ) - (H : ℤ)) + (h : ℤ) ≤ n ∧
              n ≤ (b : ℤ) + (h : ℤ) :=
          Finset.mem_Icc.mp hn
        ⟨n - (h : ℤ),
          (by
              have hlower_shift :
                  ((a : ℤ) - (H : ℤ)) + (h : ℤ) - (h : ℤ) ≤
                    n - (h : ℤ) :=
                sub_le_sub_right hnbounds.1 (h : ℤ)
              have hlower_cancel :
                  ((a : ℤ) - (H : ℤ)) + (h : ℤ) - (h : ℤ) =
                    (a : ℤ) - (H : ℤ) :=
                add_sub_cancel_right ((a : ℤ) - (H : ℤ)) (h : ℤ)
              have hlower :
                  (a : ℤ) - (H : ℤ) ≤ n - (h : ℤ) :=
                Eq.subst
                  (motive := fun z : ℤ => z ≤ n - (h : ℤ))
                  hlower_cancel
                  hlower_shift
              have hupper_shift :
                  n - (h : ℤ) ≤ ((b : ℤ) + (h : ℤ)) - (h : ℤ) :=
                sub_le_sub_right hnbounds.2 (h : ℤ)
              have hupper_cancel :
                  ((b : ℤ) + (h : ℤ)) - (h : ℤ) = (b : ℤ) :=
                add_sub_cancel_right (b : ℤ) (h : ℤ)
              have hupper :
                  n - (h : ℤ) ≤ (b : ℤ) :=
                Eq.subst
                  (motive := fun z : ℤ => n - (h : ℤ) ≤ z)
                  hupper_cancel
                  hupper_shift
              exact Finset.mem_Icc.mpr (And.intro hlower hupper)),
          sub_add_cancel n (h : ℤ)⟩)
      (fun m _hm =>
        congrArg
          (fun z : ℤ =>
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b z)
          (Eq.refl (m + (h : ℤ))))

/-- The natural block, embedded in the integers, is contained in the
translated index interval for any valid Weyl shift. -/
theorem Complex.realPhase_secondDerivative_vdc_natBlock_subset_fixedShift_indexInterval
    {a b H h : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    (Finset.Icc a b).image (fun n : ℕ => (n : ℤ)) ⊆
        Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)) := by
  intro n hn
  match Finset.mem_image.mp hn with
  | ⟨k, hk, hkn⟩ =>
      have hkbounds : a ≤ k ∧ k ≤ b :=
        Finset.mem_Icc.mp hk
      have hhbounds : 1 ≤ h ∧ h ≤ H :=
        Finset.mem_Icc.mp hh
      have hlower₀ :
          (a : ℤ) - (H : ℤ) ≤ (a : ℤ) - (h : ℤ) :=
        sub_le_sub_left (Int.ofNat_le.mpr hhbounds.2) (a : ℤ)
      have hlower₁ :
          (a : ℤ) - (h : ℤ) ≤ (k : ℤ) - (h : ℤ) :=
        sub_le_sub_right (Int.ofNat_le.mpr hkbounds.1) (h : ℤ)
      have hlower₂ :
          ((a : ℤ) - (H : ℤ)) + (h : ℤ) ≤ (k : ℤ) := by
        have hmain :
            (a : ℤ) - (H : ℤ) ≤ (k : ℤ) - (h : ℤ) :=
          le_trans hlower₀ hlower₁
        exact Int.add_le_iff_le_sub.mpr hmain
      have hupper :
          (k : ℤ) ≤ (b : ℤ) + (h : ℤ) :=
        le_trans (Int.ofNat_le.mpr hkbounds.2)
          (le_add_of_nonneg_right (Int.natCast_nonneg h))
      exact Eq.subst
        (motive := fun z : ℤ =>
          z ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)))
        hkn
        (Finset.mem_Icc.mpr (And.intro hlower₂ hupper))

/-- Outside the original integer block, the zero-extended coefficient
contributes zero. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_eq_zero_of_not_natBlockImage
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {n : ℤ}
    (hn : n ∉ (Finset.Icc a b).image (fun k : ℕ => (k : ℤ))) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n = 0 := by
  have hnot_bounds : ¬ ((a : ℤ) ≤ n ∧ n ≤ (b : ℤ)) := by
    intro hbounds
    have hn_nonneg : 0 ≤ n :=
      le_trans (Int.natCast_nonneg a) hbounds.1
    have htoNat_mem : n.toNat ∈ Finset.Icc a b := by
        have hleft : a ≤ n.toNat :=
        Int.toNat_le_toNat hbounds.1
        have hright : n.toNat ≤ b :=
        Int.toNat_le.mpr hbounds.2
        exact Finset.mem_Icc.mpr (And.intro hleft hright)
    have hcast_toNat : (n.toNat : ℤ) = n :=
      Int.toNat_of_nonneg hn_nonneg
    exact hn
      (Finset.mem_image.mpr
        ⟨n.toNat, htoNat_mem, hcast_toNat⟩)
  exact
    Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_not_mem
      φ a b hnot_bounds

/-- If the translated integer interval contains the original block, then the
zero-extended coefficient sum over that interval is exactly the original
coefficient block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_indexInterval_sum_eq_block
    (φ : ℝ → ℝ)
    {a b H h : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    (∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) =
      Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b := by
  let large : Finset ℤ :=
    Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ))
  let blockImage : Finset ℤ :=
    (Finset.Icc a b).image (fun n : ℕ => (n : ℤ))
  have hsubset : blockImage ⊆ large :=
    Complex.realPhase_secondDerivative_vdc_natBlock_subset_fixedShift_indexInterval
      hH hH_block hh
  have htrim :
      (∑ n ∈ large,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) =
        ∑ n ∈ blockImage,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n :=
    Eq.symm
      (Finset.sum_subset hsubset
        (fun n hn_large hn_not_block =>
          Complex.realPhase_secondDerivative_vdc_coefficientExtended_eq_zero_of_not_natBlockImage
            φ hn_not_block))
  have hinj :
      Set.InjOn (fun n : ℕ => (n : ℤ)) (Finset.Icc a b : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    exact Int.ofNat.inj heq
  have himage :
      (∑ n ∈ blockImage,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) =
        ∑ n ∈ Finset.Icc a b,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) :=
    Finset.sum_image hinj
  have hnat :
      (∑ n ∈ Finset.Icc a b,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
        ∑ n ∈ Finset.Icc a b,
          Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
    Finset.sum_congr
      (Eq.refl (Finset.Icc a b))
      (fun n hn =>
        Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
          φ hn)
  exact Eq.trans htrim (Eq.trans himage hnat)

/-- For one fixed positive shift, summing the translated zero-extended
coefficient over the ambient translate base recovers the original block sum. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_fixedShift_sum_eq_block
    (φ : ℝ → ℝ)
    {a b H h : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
      Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b := by
  exact Eq.trans
    (Complex.realPhase_secondDerivative_vdc_fixedShift_translate_to_indexInterval
      φ)
    (Complex.realPhase_secondDerivative_vdc_coefficientExtended_indexInterval_sum_eq_block
      φ hH hH_block hh)

/-- Translating the ambient base interval by one fixed shift rewrites the
fixed-shift norm-square Weyl sum as a sum over the translated integer
interval. -/
theorem Complex.realPhase_secondDerivative_vdc_fixedShift_translate_normSq_to_indexInterval
    (φ : ℝ → ℝ)
    {a b H h : ℕ} :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) =
      ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) := by
  show
      (∑ m ∈ Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ),
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) =
        ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)
  exact
    Finset.sum_bij
      (fun m _ => m + (h : ℤ))
      (fun m hm =>
        have hmbounds :
            (a : ℤ) - (H : ℤ) ≤ m ∧ m ≤ (b : ℤ) :=
          Finset.mem_Icc.mp hm
        Finset.mem_Icc.mpr
          (And.intro
            (add_le_add_right hmbounds.1 (h : ℤ))
            (add_le_add_right hmbounds.2 (h : ℤ))))
      (fun m₁ _hm₁ m₂ _hm₂ heq => add_right_cancel heq)
      (fun n hn =>
        have hnbounds :
            ((a : ℤ) - (H : ℤ)) + (h : ℤ) ≤ n ∧
              n ≤ (b : ℤ) + (h : ℤ) :=
          Finset.mem_Icc.mp hn
        ⟨n - (h : ℤ),
          (by
              have hlower_shift :
                  ((a : ℤ) - (H : ℤ)) + (h : ℤ) - (h : ℤ) ≤
                    n - (h : ℤ) :=
                sub_le_sub_right hnbounds.1 (h : ℤ)
              have hlower_cancel :
                  ((a : ℤ) - (H : ℤ)) + (h : ℤ) - (h : ℤ) =
                    (a : ℤ) - (H : ℤ) :=
                add_sub_cancel_right ((a : ℤ) - (H : ℤ)) (h : ℤ)
              have hlower :
                  (a : ℤ) - (H : ℤ) ≤ n - (h : ℤ) :=
                Eq.subst
                  (motive := fun z : ℤ => z ≤ n - (h : ℤ))
                  hlower_cancel
                  hlower_shift
              have hupper_shift :
                  n - (h : ℤ) ≤ ((b : ℤ) + (h : ℤ)) - (h : ℤ) :=
                sub_le_sub_right hnbounds.2 (h : ℤ)
              have hupper_cancel :
                  ((b : ℤ) + (h : ℤ)) - (h : ℤ) = (b : ℤ) :=
                add_sub_cancel_right (b : ℤ) (h : ℤ)
              have hupper :
                  n - (h : ℤ) ≤ (b : ℤ) :=
                Eq.subst
                  (motive := fun z : ℤ => n - (h : ℤ) ≤ z)
                  hupper_cancel
                  hupper_shift
              exact Finset.mem_Icc.mpr (And.intro hlower hupper)),
          sub_add_cancel n (h : ℤ)⟩)
      (fun m _hm =>
        congrArg
          (fun z : ℤ =>
            Complex.normSq
              (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b z))
          (Eq.refl (m + (h : ℤ))))

/-- The zero-extended norm-square coefficient vanishes outside the original
integer block. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_normSq_eq_zero_of_not_natBlockImage
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {n : ℤ}
    (hn : n ∉ (Finset.Icc a b).image (fun k : ℕ => (k : ℤ))) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) = 0 := by
  have hzero :
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n = 0 :=
    Complex.realPhase_secondDerivative_vdc_coefficientExtended_eq_zero_of_not_natBlockImage
      φ hn
  exact Eq.trans
    (congrArg Complex.normSq hzero)
    Complex.normSq_zero

/-- The norm-square zero-extension sum over a containing translated integer
interval is exactly the original block length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientExtended_normSq_indexInterval_sum_eq_blockLength
    (φ : ℝ → ℝ)
    {a b H h : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    (∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ)),
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
      Real.secondDerivativeVdc_blockLength a b := by
  let large : Finset ℤ :=
    Finset.Icc (((a : ℤ) - (H : ℤ)) + (h : ℤ)) ((b : ℤ) + (h : ℤ))
  let blockImage : Finset ℤ :=
    (Finset.Icc a b).image (fun n : ℕ => (n : ℤ))
  have hsubset : blockImage ⊆ large :=
    Complex.realPhase_secondDerivative_vdc_natBlock_subset_fixedShift_indexInterval
      hH hH_block hh
  have htrim :
      (∑ n ∈ large,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
        ∑ n ∈ blockImage,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) :=
    Eq.symm
      (Finset.sum_subset hsubset
        (fun n hn_large hn_not_block =>
          Complex.realPhase_secondDerivative_vdc_coefficientExtended_normSq_eq_zero_of_not_natBlockImage
            φ hn_not_block))
  have hinj :
      Set.InjOn (fun n : ℕ => (n : ℤ)) (Finset.Icc a b : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    exact Int.ofNat.inj heq
  have himage :
      (∑ n ∈ blockImage,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
        ∑ n ∈ Finset.Icc a b,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) :=
    Finset.sum_image hinj
  have hnat :
      (∑ n ∈ Finset.Icc a b,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficient φ n) :=
    Finset.sum_congr
      (Eq.refl (Finset.Icc a b))
      (fun n hn =>
        congrArg Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
            φ hn))
  exact Eq.trans htrim
    (Eq.trans himage
      (Eq.trans hnat
        (Complex.realPhase_secondDerivative_vdc_coefficient_diagonal_sum_eq_blockLength
          φ a b)))

/-- For one fixed positive shift, summing the norm-squares of the translated
zero-extended coefficients over the ambient translate base gives the original
block length. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_fixedShift_normSq_sum_eq_blockLength
    (φ : ℝ → ℝ)
    {a b H h : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) =
      Real.secondDerivativeVdc_blockLength a b := by
  exact Eq.trans
    (Complex.realPhase_secondDerivative_vdc_fixedShift_translate_normSq_to_indexInterval
      φ)
    (Complex.realPhase_secondDerivative_vdc_coefficientExtended_normSq_indexInterval_sum_eq_blockLength
      φ hH hH_block hh)

/-- The double Weyl translate sum, after zero-extension, partitions by the
original block index hit by `m+h`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_sum_partition
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
      ∑ n ∈ Finset.Icc a b,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) := by
  have hfixed :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
            Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b :=
    fun h hh =>
      Complex.realPhase_secondDerivative_vdc_weylTranslate_fixedShift_sum_eq_block
        φ hH hH_block hh
  show
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
      ∑ n ∈ Finset.Icc a b,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)
  have hswap :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)) :=
    Finset.sum_comm
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ))) =
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b :=
    Finset.sum_congr
      (Eq.refl (Complex.realPhase_secondDerivative_vdc_shiftRange H))
      (fun h hh => hfixed h hh)
  have hsum_const :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) =
        (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b := by
    have hconst_sum :
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) =
          ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℂ) *
            Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b :=
      Eq.trans
        (Finset.sum_const
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b))
        (nsmul_eq_mul
          (Complex.realPhase_secondDerivative_vdc_shiftRange H).card
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b))
    have hcard :
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℂ) =
          (H : ℂ) := by
      have hshift_card :
          (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H := by
        have hcard_nat :
            (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H + 1 - 1 :=
          Nat.card_Icc 1 H
        exact Eq.trans hcard_nat (Nat.succ_sub_one H)
      exact congrArg (fun n : ℕ => (n : ℂ)) hshift_card
    exact Eq.trans hconst_sum
      (congrArg
        (fun z : ℂ =>
          z * Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b)
        hcard)
  have hhit :
      (∑ n ∈ Finset.Icc a b,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
        (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b := by
    have hinner :
        (∑ n ∈ Finset.Icc a b,
          ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
          ∑ n ∈ Finset.Icc a b,
            (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
        Finset.sum_congr
        (Eq.refl (Finset.Icc a b))
        (fun n hn =>
          Complex.realPhase_secondDerivative_vdc_weylHitBases_sum_eq
            φ hn)
    have hfactor :
        (∑ n ∈ Finset.Icc a b,
          (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficient φ n) =
          (H : ℂ) *
            ∑ n ∈ Finset.Icc a b,
              Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
      (Finset.mul_sum (Finset.Icc a b)
        (fun n : ℕ => Complex.realPhase_secondDerivative_vdc_coefficient φ n)
        (H : ℂ)).symm
    show
      (∑ n ∈ Finset.Icc a b,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
        (H : ℂ) *
          ∑ n ∈ Finset.Icc a b,
            Complex.realPhase_secondDerivative_vdc_coefficient φ n
    exact Eq.trans hinner hfactor
  exact Eq.trans hswap
    (Eq.trans hconst
      (Eq.trans hsum_const hhit.symm))

/-- The block is nonempty when the Weyl averaging length is bounded by its
cardinality and the averaging length is positive. -/
theorem Nat.realPhase_secondDerivative_vdc_nonempty_of_shiftLength_le_card
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    a ≤ b := by
  have hcard_pos : 0 < (Finset.Icc a b).card :=
    lt_of_lt_of_le (Nat.lt_of_succ_le hH) hH_block
  match Finset.card_pos.mp hcard_pos with
  | ⟨n, hn⟩ =>
        have hbounds : a ≤ n ∧ n ≤ b :=
        Finset.mem_Icc.mp hn
        exact le_trans hbounds.1 hbounds.2

/-- Integer endpoint arithmetic for the translate-base interval. -/
theorem Int.realPhase_secondDerivative_vdc_translateBase_length_eq
    {a b H : ℕ}
    (hab : a ≤ b) :
    (b : ℤ) + 1 - ((a : ℤ) - (H : ℤ)) =
      (((Finset.Icc a b).card + H : ℕ) : ℤ) := by
  have hcard :
      ((Finset.Icc a b).card : ℤ) =
        ((b + 1 - a : ℕ) : ℤ) :=
    congrArg (fun n : ℕ => (n : ℤ)) (Nat.card_Icc a b)
  have hnat_sub :
      ((b + 1 - a : ℕ) : ℤ) =
        (b : ℤ) + 1 - (a : ℤ) := by
    have hab_succ : a ≤ b + 1 :=
      le_trans hab (Nat.le_succ b)
    exact Nat.cast_sub hab_succ
  have hblock :
      ((Finset.Icc a b).card : ℤ) =
        (b : ℤ) + 1 - (a : ℤ) :=
    Eq.trans hcard hnat_sub
  have hsum :
      (((Finset.Icc a b).card + H : ℕ) : ℤ) =
        ((Finset.Icc a b).card : ℤ) + (H : ℤ) :=
    Nat.cast_add (Finset.Icc a b).card H
  have harith :
      (b : ℤ) + 1 - ((a : ℤ) - (H : ℤ)) =
        ((b : ℤ) + 1 - (a : ℤ)) + (H : ℤ) := by
    let x : ℤ := (b : ℤ) + 1
    let y : ℤ := (a : ℤ)
    let z : ℤ := (H : ℤ)
    have hleft :
        x - (y - z) = x + z - y :=
      sub_sub_eq_add_sub x y z
    have hright :
        (x - y) + z = x + z - y :=
      sub_add_eq_add_sub x y z
    exact Eq.trans hleft hright.symm
  exact
    Eq.trans harith
      (Eq.trans
        (congrArg (fun z : ℤ => z + (H : ℤ)) hblock.symm)
        hsum.symm)

/-- The translate-base integer interval has the endpoint order needed for
`Int.card_Icc_of_le`. -/
theorem Int.realPhase_secondDerivative_vdc_translateBase_left_le_right_succ
    {a b H : ℕ}
    (hab : a ≤ b) :
    (a : ℤ) - (H : ℤ) ≤ (b : ℤ) + 1 := by
  have ha_le_b_succ : (a : ℤ) ≤ (b : ℤ) + 1 := by
    have hab_succ : a ≤ b + 1 :=
      le_trans hab (Nat.le_succ b)
    exact Int.ofNat_le.mpr hab_succ
  have hsub_le_a :
      (a : ℤ) - (H : ℤ) ≤ (a : ℤ) :=
    sub_le_self (a : ℤ) (Int.natCast_nonneg H)
  exact le_trans hsub_le_a ha_le_b_succ

/-- Exact cardinality identity for the integer translate-base interval. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_nat_eq
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card =
      (Finset.Icc a b).card + H := by
  have hab : a ≤ b :=
    Nat.realPhase_secondDerivative_vdc_nonempty_of_shiftLength_le_card
      hH hH_block
  show
    (Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ)).card =
      (Finset.Icc a b).card + H
  have hleft :
      (((Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ)).card : ℕ) : ℤ) =
        (b : ℤ) + 1 - ((a : ℤ) - (H : ℤ)) :=
    Int.card_Icc_of_le
      (a := (a : ℤ) - (H : ℤ))
      (b := (b : ℤ))
      (Int.realPhase_secondDerivative_vdc_translateBase_left_le_right_succ
        (a := a) (b := b) (H := H) hab)
  have hright :
      (b : ℤ) + 1 - ((a : ℤ) - (H : ℤ)) =
        (((Finset.Icc a b).card + H : ℕ) : ℤ) :=
    Int.realPhase_secondDerivative_vdc_translateBase_length_eq
      (a := a) (b := b) (H := H) hab
  exact Int.ofNat.inj (Eq.trans hleft hright)

/-- Exact cardinality of the ambient Weyl translate-base interval. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_eq_block_add_H
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ((Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card : ℝ) =
      Real.secondDerivativeVdc_blockLength a b + (H : ℝ) := by
  show
    ((Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card : ℝ) =
      ((Finset.Icc a b).card : ℝ) + (H : ℝ)
  have hnat :
        (Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card =
        (Finset.Icc a b).card + H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_nat_eq
      hH hH_block
  have hcast :
      (((Finset.Icc a b).card + H : ℕ) : ℝ) =
        ((Finset.Icc a b).card : ℝ) + (H : ℝ) :=
    Nat.cast_add (Finset.Icc a b).card H
  exact Eq.trans
    (congrArg (fun n : ℕ => (n : ℝ)) hnat)
    hcast

/-- The translate-base cardinality is bounded by `blockLength + H`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_le_block_add_H
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ((Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card : ℝ) ≤
      Real.secondDerivativeVdc_blockLength a b + (H : ℝ) := by
  exact le_of_eq
    (Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_eq_block_add_H
      hH hH_block)

/-- The Weyl translate average covers every original coefficient exactly
`H` times. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_sum_eq_H_mul_block
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
      (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b := by
  have hpartition :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
        ∑ n ∈ Finset.Icc a b,
          ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_sum_partition
      φ hH hH_block
  have hinner :
      (∑ n ∈ Finset.Icc a b,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylHitBases a b H n,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) =
        ∑ n ∈ Finset.Icc a b,
          (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
    Finset.sum_congr
      (Eq.refl (Finset.Icc a b))
      (fun n hn =>
        Complex.realPhase_secondDerivative_vdc_weylHitBases_sum_eq
          φ hn)
  have hfactor :
      (∑ n ∈ Finset.Icc a b,
        (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficient φ n) =
        (H : ℂ) *
          ∑ n ∈ Finset.Icc a b,
            Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
    (Finset.mul_sum (Finset.Icc a b)
      (fun n : ℕ => Complex.realPhase_secondDerivative_vdc_coefficient φ n)
      (H : ℂ)).symm
  show
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
      (H : ℂ) *
        ∑ n ∈ Finset.Icc a b,
          Complex.realPhase_secondDerivative_vdc_coefficient φ n
  exact Eq.trans hpartition
    (Eq.trans hinner hfactor)

/-- Finite Cauchy-Schwarz for complex sums in `normSq` form. -/
theorem Complex.finset_normSq_sum_le_card_mul_sum_normSq
    {ι : Type*}
    (s : Finset ι)
    (u : ι → ℂ) :
    Complex.normSq (∑ i ∈ s, u i) ≤
      (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (u i) := by
  have hnormSq_left :
      Complex.normSq (∑ i ∈ s, u i) =
        ‖∑ i ∈ s, u i‖ ^ 2 :=
    Complex.normSq_eq_norm_sq (∑ i ∈ s, u i)
  have htriangle :
      ‖∑ i ∈ s, u i‖ ≤ ∑ i ∈ s, ‖u i‖ :=
    norm_sum_le s u
  have hnorm_nonneg :
      0 ≤ ‖∑ i ∈ s, u i‖ :=
    norm_nonneg (∑ i ∈ s, u i)
  have hsum_nonneg :
      0 ≤ ∑ i ∈ s, ‖u i‖ :=
    Finset.sum_nonneg
      (fun i hi => norm_nonneg (u i))
  have hsq_triangle :
      ‖∑ i ∈ s, u i‖ ^ 2 ≤ (∑ i ∈ s, ‖u i‖) ^ 2 := by
    calc
      ‖∑ i ∈ s, u i‖ ^ 2 =
          ‖∑ i ∈ s, u i‖ * ‖∑ i ∈ s, u i‖ :=
        pow_two ‖∑ i ∈ s, u i‖
      _ ≤ (∑ i ∈ s, ‖u i‖) * (∑ i ∈ s, ‖u i‖) :=
        mul_le_mul htriangle htriangle hnorm_nonneg hsum_nonneg
      _ = (∑ i ∈ s, ‖u i‖) ^ 2 :=
        (pow_two (∑ i ∈ s, ‖u i‖)).symm
  have hreal_cauchy :
      (∑ i ∈ s, ‖u i‖) ^ 2 ≤
        (s.card : ℝ) * ∑ i ∈ s, ‖u i‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsum_normSq :
      (∑ i ∈ s, ‖u i‖ ^ 2) =
        ∑ i ∈ s, Complex.normSq (u i) :=
    Finset.sum_congr
      (Eq.refl s)
      (fun i hi =>
        (Complex.normSq_eq_norm_sq (u i)).symm)
  have htarget :
      (s.card : ℝ) * ∑ i ∈ s, ‖u i‖ ^ 2 =
        (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (u i) :=
    congrArg (fun r : ℝ => (s.card : ℝ) * r) hsum_normSq
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ (s.card : ℝ) * ∑ i ∈ s, Complex.normSq (u i))
      hnormSq_left.symm
      (le_trans hsq_triangle
        (le_trans hreal_cauchy
          (le_of_eq htarget)))

/-- Exact finite Gram expansion of a sum of complex vectors.

The diagonal contributes the sum of pointwise norm-squares and the two
off-diagonal orders combine into twice the real part of the ordered
correlation. -/
theorem Complex.normSq_eq_re_mul_star
    (z : ℂ) :
    Complex.normSq z = (z * star z).re := by
  have hmul :
      z * star z = (Complex.normSq z : ℂ) :=
    Complex.mul_conj z
  have hre :
      (z * star z).re = Complex.normSq z :=
    congrArg Complex.re hmul
  exact hre.symm

/-- Distributivity of a finite complex Gram product. -/
theorem Complex.finset_sum_mul_star_sum_eq_double_sum
    (shifts : Finset ℕ)
    (v : ℕ → ℂ) :
    (∑ h₂ ∈ shifts, v h₂) *
        star (∑ h₁ ∈ shifts, v h₁) =
      ∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts,
          v h₂ * star (v h₁) := by
  have hstar :
      star (∑ h₁ ∈ shifts, v h₁) =
        ∑ h₁ ∈ shifts, star (v h₁) :=
    star_sum shifts v
  have hreplace_star :
      (∑ h₂ ∈ shifts, v h₂) *
          star (∑ h₁ ∈ shifts, v h₁) =
        (∑ h₂ ∈ shifts, v h₂) *
          (∑ h₁ ∈ shifts, star (v h₁)) :=
    congrArg
      (fun z : ℂ => (∑ h₂ ∈ shifts, v h₂) * z)
      hstar
  have hleft_distrib :
      (∑ h₂ ∈ shifts, v h₂) *
          (∑ h₁ ∈ shifts, star (v h₁)) =
        ∑ h₂ ∈ shifts,
          v h₂ * (∑ h₁ ∈ shifts, star (v h₁)) :=
    Finset.sum_mul shifts (fun h₂ : ℕ => v h₂)
      (∑ h₁ ∈ shifts, star (v h₁))
  have hright_distrib :
      (∑ h₂ ∈ shifts,
          v h₂ * (∑ h₁ ∈ shifts, star (v h₁))) =
        ∑ h₂ ∈ shifts,
          ∑ h₁ ∈ shifts,
            v h₂ * star (v h₁) :=
    Finset.sum_congr
      (Eq.refl shifts)
      (fun h₂ hh₂ =>
        Finset.mul_sum shifts (fun h₁ : ℕ => star (v h₁)) (v h₂))
  have hcommute :
      (∑ h₂ ∈ shifts,
          ∑ h₁ ∈ shifts,
            v h₂ * star (v h₁)) =
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            v h₂ * star (v h₁) :=
    Finset.sum_comm
  exact
    Eq.trans hreplace_star
      (Eq.trans hleft_distrib
        (Eq.trans hright_distrib hcommute))

theorem Complex.normSq_finset_sum_eq_re_double_sum
    (shifts : Finset ℕ)
    (v : ℕ → ℂ) :
    Complex.normSq (∑ h ∈ shifts, v h) =
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts,
          (v h₂ * star (v h₁)).re) := by
  let z : ℂ := ∑ h ∈ shifts, v h
  have hnorm :
      Complex.normSq z = (z * star z).re :=
    Complex.normSq_eq_re_mul_star z
  have hproduct :
      z * star z =
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            v h₂ * star (v h₁) :=
    Complex.finset_sum_mul_star_sum_eq_double_sum shifts v
  have hre_product :
      (z * star z).re =
        (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            v h₂ * star (v h₁)).re :=
    congrArg Complex.re hproduct
  have hre_sum :
      (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            v h₂ * star (v h₁)).re =
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            (v h₂ * star (v h₁)).re := by
    exact
      Eq.trans
        (Complex.re_sum
          (s := shifts)
          (f := fun h₁ : ℕ =>
            ∑ h₂ ∈ shifts, v h₂ * star (v h₁)))
        (Finset.sum_congr
          (Eq.refl shifts)
          (fun h₁ hh₁ =>
            Complex.re_sum
              (s := shifts)
              (f := fun h₂ : ℕ => v h₂ * star (v h₁))))
  exact
    Eq.trans hnorm
      (Eq.trans hre_product hre_sum)

/-- Summing the fixed-vector Gram identity over an outer finite set and moving
the outer sum inside the correlation. -/
theorem Complex.finset_sum_re_double_sum_eq_re_double_correlation
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ m ∈ outer,
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts,
          (u m h₂ * star (u m h₁)).re)) =
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts,
          (∑ m ∈ outer, u m h₂ * star (u m h₁)).re) := by
  let term : μ → ℕ → ℕ → ℝ :=
    fun m h₁ h₂ => (u m h₂ * star (u m h₁)).re
  have houter_h₁ :
      (∑ m ∈ outer,
        (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts, term m h₁ h₂)) =
        ∑ h₁ ∈ shifts,
          ∑ m ∈ outer,
            ∑ h₂ ∈ shifts, term m h₁ h₂ :=
    Finset.sum_comm
  have houter_h₂ :
      (∑ h₁ ∈ shifts,
          ∑ m ∈ outer,
            ∑ h₂ ∈ shifts, term m h₁ h₂) =
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            ∑ m ∈ outer, term m h₁ h₂ :=
    Finset.sum_congr
      (Eq.refl shifts)
      (fun h₁ hh₁ => Finset.sum_comm)
  have hre_inside :
      (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            ∑ m ∈ outer, term m h₁ h₂) =
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts,
            (∑ m ∈ outer, u m h₂ * star (u m h₁)).re :=
    Finset.sum_congr
      (Eq.refl shifts)
      (fun h₁ hh₁ =>
        Finset.sum_congr
          (Eq.refl shifts)
          (fun h₂ hh₂ =>
            (Complex.re_sum
              (s := outer)
              (f := fun m : μ => u m h₂ * star (u m h₁))).symm))
  exact
    Eq.trans houter_h₁
      (Eq.trans houter_h₂ hre_inside)

theorem Complex.finset_normSq_sum_over_outer_eq_re_double_correlation
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ m ∈ outer,
      Complex.normSq (∑ h ∈ shifts, u m h)) =
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts,
          (∑ m ∈ outer, u m h₂ * star (u m h₁)).re) := by
  have hfixed :
      (∑ m ∈ outer,
        Complex.normSq (∑ h ∈ shifts, u m h)) =
        (∑ m ∈ outer,
          (∑ h₁ ∈ shifts,
            ∑ h₂ ∈ shifts,
              (u m h₂ * star (u m h₁)).re)) :=
    Finset.sum_congr
      (Eq.refl outer)
      (fun m hm =>
        Complex.normSq_finset_sum_eq_re_double_sum
          shifts
          (fun h : ℕ => u m h))
  exact
    Eq.trans hfixed
        (Complex.finset_sum_re_double_sum_eq_re_double_correlation
        outer shifts u)

/-- The diagonal of the finite Gram double sum is the sum of pointwise
norm-squares. -/
theorem Complex.finset_gram_diagonal_re_eq_normSq_sum
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ h ∈ shifts,
      (∑ m ∈ outer, u m h * star (u m h)).re) =
      (∑ h ∈ shifts,
        ∑ m ∈ outer, Complex.normSq (u m h)) := by
  exact
    Finset.sum_congr
      (Eq.refl shifts)
      (fun h hh =>
        Eq.trans
          (Complex.re_sum (s := outer)
            (fun m : μ => u m h * star (u m h)))
          (Finset.sum_congr
            (Eq.refl outer)
            (fun m hm =>
              congrArg Complex.re
                (Complex.mul_conj (u m h)))))

/-- Reversing an off-diagonal Gram pair conjugates the correlation, so the two
real parts agree. -/
theorem Complex.finset_gram_pair_reverse_re_eq
    {μ : Type*}
    (outer : Finset μ)
    (u : μ → ℕ → ℂ)
    (h₁ h₂ : ℕ) :
    (∑ m ∈ outer, u m h₁ * star (u m h₂)).re =
      (∑ m ∈ outer, u m h₂ * star (u m h₁)).re := by
  let z : ℂ := ∑ m ∈ outer, u m h₂ * star (u m h₁)
  let w : ℂ := ∑ m ∈ outer, u m h₁ * star (u m h₂)
  have hterm :
      ∀ m : μ,
        m ∈ outer →
          star (u m h₂ * star (u m h₁)) =
            u m h₁ * star (u m h₂) := by
    intro m hm
    exact
      Eq.trans
        (star_mul (u m h₂) (star (u m h₁)))
        (congrArg
          (fun y : ℂ => y * star (u m h₂))
          (star_star (u m h₁)))
  have hstar_z :
      star z = w := by
    exact
      Eq.trans
        (star_sum outer (fun m : μ => u m h₂ * star (u m h₁)))
        (Finset.sum_congr
          (Eq.refl outer)
          (fun m hm => hterm m hm))
  have hw_re :
      w.re = (star z).re :=
    congrArg Complex.re hstar_z.symm
  have hstar_re :
      (star z).re = z.re :=
    Complex.conj_re z
  have hresult :
      w.re = z.re :=
    Eq.trans hw_re hstar_re
  exact hresult

/-- One row of a finite real matrix splits into its diagonal entry, the lower
entries, and the upper entries. -/
theorem Finset.sum_filter_eq_self_singleton_nat
    (s : Finset ℕ)
    (F : ℕ → ℝ)
    {i : ℕ}
    (hi : i ∈ s) :
    (∑ j ∈ s.filter (fun j : ℕ => j = i), F j) = F i := by
  have hfilter :
      s.filter (fun j : ℕ => j = i) = {i} := by
    have hraw :
        s.filter (fun j : ℕ => j = i) = if i ∈ s then {i} else ∅ :=
        Finset.filter_eq' s i
    have hif :
        (if i ∈ s then {i} else ∅) = ({i} : Finset ℕ) :=
      if_pos hi
    exact Eq.trans hraw hif
  exact
    Eq.trans
      (congrArg (fun t : Finset ℕ => ∑ j ∈ t, F j) hfilter)
      (Finset.sum_singleton F i)

/-- The off-diagonal part of a row over naturals splits into lower and upper
entries. -/
theorem Finset.sum_filter_ne_eq_lower_add_upper_nat
    (s : Finset ℕ)
    (F : ℕ → ℝ)
    (i : ℕ) :
    (∑ j ∈ s.filter (fun j : ℕ => j ≠ i), F j) =
      (∑ j ∈ s.filter (fun j : ℕ => j < i), F j) +
        (∑ j ∈ s.filter (fun j : ℕ => i < j), F j) := by
  have hne_filter :
      s.filter (fun j : ℕ => j ≠ i) =
        s.filter (fun j : ℕ => j < i ∨ i < j) :=
    Finset.filter_congr
      (fun j hj =>
        ne_iff_lt_or_gt)
  have hor_filter :
      s.filter (fun j : ℕ => j < i ∨ i < j) =
        s.filter (fun j : ℕ => j < i) ∪
          s.filter (fun j : ℕ => i < j) :=
    Finset.filter_or
      (s := s)
      (p := fun j : ℕ => j < i)
      (q := fun j : ℕ => i < j)
  have hfilter_union :
      s.filter (fun j : ℕ => j ≠ i) =
        s.filter (fun j : ℕ => j < i) ∪
          s.filter (fun j : ℕ => i < j) :=
    Eq.trans hne_filter hor_filter
  have hdisjoint :
      Disjoint
        (s.filter (fun j : ℕ => j < i))
        (s.filter (fun j : ℕ => i < j)) := by
    exact
      (Finset.disjoint_filter).mpr
        (fun j hj hj_lt_i =>
          not_lt_of_gt hj_lt_i)
  exact
    Eq.trans
      (congrArg (fun t : Finset ℕ => ∑ j ∈ t, F j) hfilter_union)
      (Finset.sum_union hdisjoint)

theorem Finset.sum_row_eq_diag_add_lower_add_upper_nat
    (s : Finset ℕ)
    (F : ℕ → ℕ → ℝ)
    {i : ℕ}
    (hi : i ∈ s) :
    (∑ j ∈ s, F i j) =
      F i i +
        (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
          (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) := by
  have hsplit :
      (∑ j ∈ s, F i j) =
        (∑ j ∈ s.filter (fun j : ℕ => j = i), F i j) +
          (∑ j ∈ s.filter (fun j : ℕ => j ≠ i), F i j) :=
    (Finset.sum_filter_add_sum_filter_not
      (s := s)
      (p := fun j : ℕ => j = i)
      (f := fun j : ℕ => F i j)).symm
  have hdiag :
      (∑ j ∈ s.filter (fun j : ℕ => j = i), F i j) = F i i :=
    Finset.sum_filter_eq_self_singleton_nat
      s
      (fun j : ℕ => F i j)
      hi
  have hoff :
      (∑ j ∈ s.filter (fun j : ℕ => j ≠ i), F i j) =
        (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
          (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) :=
    Finset.sum_filter_ne_eq_lower_add_upper_nat
      s
      (fun j : ℕ => F i j)
      i
  exact
    Eq.trans hsplit
      (Eq.trans
        (congrArg
          (fun right : ℝ =>
            (∑ j ∈ s.filter (fun j : ℕ => j = i), F i j) + right)
          hoff)
        (Eq.trans
          (congrArg
            (fun left : ℝ =>
              left +
                ((∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
                  (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)))
            hdiag)
          (add_assoc
            (F i i)
            (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j)
            (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)).symm))

/-- For a symmetric finite real matrix, the strict lower-triangular sum equals
the strict upper-triangular sum. -/
theorem Finset.sum_lower_eq_sum_upper_of_symm_nat
    (s : Finset ℕ)
    (F : ℕ → ℕ → ℝ)
    (hsymm :
      ∀ i : ℕ,
        i ∈ s →
          ∀ j : ℕ,
            j ∈ s →
              F i j = F j i) :
    (∑ i ∈ s,
      ∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) =
      (∑ i ∈ s,
        ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) := by
  have hcomm :
      (∑ i ∈ s,
        ∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) =
        ∑ j ∈ s,
          ∑ i ∈ s.filter (fun i : ℕ => j < i), F i j := by
    exact
        Finset.sum_comm'
        (s := s)
        (t := fun i : ℕ => s.filter (fun j : ℕ => j < i))
        (t' := s)
        (s' := fun j : ℕ => s.filter (fun i : ℕ => j < i))
        (f := fun i j : ℕ => F i j)
        (fun i j =>
          Iff.intro
            (fun hij =>
              And.intro
                (Finset.mem_filter.mpr
                  (And.intro hij.1 (Finset.mem_filter.mp hij.2).2))
                (Finset.mem_filter.mp hij.2).1)
            (fun hji =>
              And.intro
                (Finset.mem_filter.mp hji.1).1
                (Finset.mem_filter.mpr
                  (And.intro hji.2 (Finset.mem_filter.mp hji.1).2))))
  have hsymm_sum :
      (∑ j ∈ s,
          ∑ i ∈ s.filter (fun i : ℕ => j < i), F i j) =
        ∑ j ∈ s,
          ∑ i ∈ s.filter (fun i : ℕ => j < i), F j i := by
    exact
        Finset.sum_congr
        (Eq.refl s)
        (fun j hj =>
          Finset.sum_congr
            (Eq.refl (s.filter (fun i : ℕ => j < i)))
            (fun i hi =>
              hsymm i (Finset.mem_filter.mp hi).1 j hj))
  exact Eq.trans hcomm hsymm_sum

/-- Adding equal lower and upper triangular sums gives twice the ordered
upper-triangular sum. -/
theorem Finset.sum_lower_add_sum_upper_eq_two_mul_upper_of_symm_nat
    (s : Finset ℕ)
    (F : ℕ → ℕ → ℝ)
    (hsymm :
      ∀ i : ℕ,
        i ∈ s →
          ∀ j : ℕ,
            j ∈ s →
              F i j = F j i) :
    (∑ i ∈ s,
      ∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
      (∑ i ∈ s,
        ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) =
      (∑ i ∈ s,
        ∑ j ∈ s.filter (fun j : ℕ => i < j), 2 * F i j) := by
  let lower : ℝ :=
    ∑ i ∈ s, ∑ j ∈ s.filter (fun j : ℕ => j < i), F i j
  let upper : ℝ :=
    ∑ i ∈ s, ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j
  have hlower_eq_upper : lower = upper :=
    Finset.sum_lower_eq_sum_upper_of_symm_nat s F hsymm
  have hupper_add :
      upper + upper =
        ∑ i ∈ s,
          ((∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) +
            (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)) := by
    exact
      (Finset.sum_add_distrib
        (s := s)
        (f := fun i : ℕ =>
          ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)
        (g := fun i : ℕ =>
          ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)).symm
  have hpoint :
      (∑ i ∈ s,
          ((∑ j ∈ s.filter (fun j : ℕ => i < j), F i j) +
            (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j))) =
        ∑ i ∈ s,
          ∑ j ∈ s.filter (fun j : ℕ => i < j), 2 * F i j := by
    exact
        Finset.sum_congr
        (Eq.refl s)
        (fun i hi =>
          Eq.trans
            ((Finset.sum_add_distrib
              (s := s.filter (fun j : ℕ => i < j))
              (f := fun j : ℕ => F i j)
              (g := fun j : ℕ => F i j)).symm)
            (Finset.sum_congr
              (Eq.refl (s.filter (fun j : ℕ => i < j)))
              (fun j hj =>
                (two_mul (F i j)).symm)))
  have hreplace :
      lower + upper = upper + upper :=
    congrArg (fun x : ℝ => x + upper) hlower_eq_upper
  exact
    Eq.trans hreplace
      (Eq.trans hupper_add hpoint)

/-- A finite symmetric real matrix splits into its diagonal plus twice the
strictly ordered upper-triangular part. -/
theorem Finset.sum_sum_eq_diagonal_add_ordered_of_symm_nat
    (s : Finset ℕ)
    (F : ℕ → ℕ → ℝ)
    (hsymm :
      ∀ i : ℕ,
        i ∈ s →
          ∀ j : ℕ,
            j ∈ s →
              F i j = F j i) :
    (∑ i ∈ s, ∑ j ∈ s, F i j) =
      (∑ i ∈ s, F i i) +
        (∑ i ∈ s,
          ∑ j ∈ s.filter (fun j : ℕ => i < j),
            2 * F i j) := by
  have hrow :
      (∑ i ∈ s, ∑ j ∈ s, F i j) =
        ∑ i ∈ s,
          (F i i +
            (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
              (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j)) :=
    Finset.sum_congr
      (Eq.refl s)
      (fun i hi =>
        Finset.sum_row_eq_diag_add_lower_add_upper_nat
          s F hi)
  have hcollect :
      (∑ i ∈ s,
          (F i i +
            (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j) +
              (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j))) =
          (∑ i ∈ s, F i i) +
          ((∑ i ∈ s,
            (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j)) +
            (∑ i ∈ s,
              (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j))) := by
    let lower : ℕ → ℝ :=
      fun i : ℕ => ∑ j ∈ s.filter (fun j : ℕ => j < i), F i j
    let upper : ℕ → ℝ :=
      fun i : ℕ => ∑ j ∈ s.filter (fun j : ℕ => i < j), F i j
    have habc :
        (∑ i ∈ s, ((F i i + lower i) + upper i)) =
          (∑ i ∈ s, (F i i + lower i)) + (∑ i ∈ s, upper i) :=
        Finset.sum_add_distrib
    have hab :
        (∑ i ∈ s, (F i i + lower i)) =
          (∑ i ∈ s, F i i) + (∑ i ∈ s, lower i) :=
        Finset.sum_add_distrib
    have hcollected :
        (∑ i ∈ s, ((F i i + lower i) + upper i)) =
          ((∑ i ∈ s, F i i) + (∑ i ∈ s, lower i)) +
            (∑ i ∈ s, upper i) :=
      Eq.trans habc
        (congrArg
          (fun left : ℝ => left + (∑ i ∈ s, upper i))
          hab)
    have hassoc :
        ((∑ i ∈ s, F i i) + (∑ i ∈ s, lower i)) +
            (∑ i ∈ s, upper i) =
          (∑ i ∈ s, F i i) +
            ((∑ i ∈ s, lower i) + (∑ i ∈ s, upper i)) :=
      add_assoc
        (∑ i ∈ s, F i i)
        (∑ i ∈ s, lower i)
        (∑ i ∈ s, upper i)
    exact Eq.trans hcollected hassoc
  have htriangles :
      ((∑ i ∈ s,
        (∑ j ∈ s.filter (fun j : ℕ => j < i), F i j)) +
        (∑ i ∈ s,
          (∑ j ∈ s.filter (fun j : ℕ => i < j), F i j))) =
        ∑ i ∈ s,
          (∑ j ∈ s.filter (fun j : ℕ => i < j), 2 * F i j) :=
    Finset.sum_lower_add_sum_upper_eq_two_mul_upper_of_symm_nat
      s F hsymm
  exact
    Eq.trans hrow
      (Eq.trans hcollect
        (congrArg
          (fun tail : ℝ => (∑ i ∈ s, F i i) + tail)
          htriangles))

/-- Splitting a finite Gram double sum into its diagonal and ordered
off-diagonal pairs. -/
theorem Complex.finset_gram_double_re_eq_diagonal_add_ordered_pairReal
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ h₁ ∈ shifts,
      ∑ h₂ ∈ shifts,
        (∑ m ∈ outer, u m h₂ * star (u m h₁)).re) =
      (∑ h ∈ shifts,
        ∑ m ∈ outer, Complex.normSq (u m h)) +
        (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
            2 * (∑ m ∈ outer, u m h₂ * star (u m h₁)).re) := by
  let F : ℕ → ℕ → ℝ :=
    fun h₁ h₂ => (∑ m ∈ outer, u m h₂ * star (u m h₁)).re
  have hsymm :
      ∀ h₁ : ℕ,
        h₁ ∈ shifts →
          ∀ h₂ : ℕ,
            h₂ ∈ shifts →
              F h₁ h₂ = F h₂ h₁ := by
    intro h₁ hh₁ h₂ hh₂
    exact
      Complex.finset_gram_pair_reverse_re_eq outer u h₂ h₁
  have hsplit :
      (∑ h₁ ∈ shifts, ∑ h₂ ∈ shifts, F h₁ h₂) =
        (∑ h ∈ shifts, F h h) +
          (∑ h₁ ∈ shifts,
            ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
              2 * F h₁ h₂) :=
    Finset.sum_sum_eq_diagonal_add_ordered_of_symm_nat
      shifts F hsymm
  have hdiag :
      (∑ h ∈ shifts, F h h) =
        ∑ h ∈ shifts,
          ∑ m ∈ outer, Complex.normSq (u m h) :=
    Complex.finset_gram_diagonal_re_eq_normSq_sum
      outer shifts u
  exact
    Eq.trans hsplit
      (congrArg
        (fun diagonal : ℝ =>
          diagonal +
            (∑ h₁ ∈ shifts,
              ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
                2 * F h₁ h₂))
        hdiag)

theorem Complex.finset_normSq_sum_over_outer_eq_diagonal_add_ordered_pairReal
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ m ∈ outer,
      Complex.normSq (∑ h ∈ shifts, u m h)) =
      (∑ h ∈ shifts,
        ∑ m ∈ outer, Complex.normSq (u m h)) +
        (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
            2 * (∑ m ∈ outer, u m h₂ * star (u m h₁)).re) := by
  exact
    Eq.trans
        (Complex.finset_normSq_sum_over_outer_eq_re_double_correlation
        outer shifts u)
        (Complex.finset_gram_double_re_eq_diagonal_add_ordered_pairReal
        outer shifts u)

/-- Finite Hilbert-space square expansion over complex-valued functions.

This is the abstract algebra behind the Weyl translate energy estimate: expand
`∑ₘ |∑ₕ u(m,h)|²`, keep the diagonal terms, pair the two off-diagonal orders,
and bound each paired real part by the norm of the corresponding correlation
sum. -/
theorem Complex.finset_normSq_sum_over_outer_le_diagonal_add_ordered_offDiagonal
    {μ : Type*}
    (outer : Finset μ)
    (shifts : Finset ℕ)
    (u : μ → ℕ → ℂ) :
    (∑ m ∈ outer,
      Complex.normSq (∑ h ∈ shifts, u m h)) ≤
      (∑ h ∈ shifts,
        ∑ m ∈ outer, Complex.normSq (u m h)) +
        (∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
            2 * ‖∑ m ∈ outer, u m h₂ * star (u m h₁)‖) := by
  classical
  let corr : ℕ → ℕ → ℂ :=
    fun h₂ h₁ => ∑ m ∈ outer, u m h₂ * star (u m h₁)
  let pairReal : ℝ :=
    ∑ h₁ ∈ shifts,
      ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
        2 * (corr h₂ h₁).re
  have hnormSq_expand :
      (∑ m ∈ outer,
        Complex.normSq (∑ h ∈ shifts, u m h)) =
        (∑ h ∈ shifts,
          ∑ m ∈ outer, Complex.normSq (u m h)) + pairReal := by
    exact
      Complex.finset_normSq_sum_over_outer_eq_diagonal_add_ordered_pairReal
        outer shifts u
  have hpair_le_norm :
      pairReal ≤
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
            2 * ‖corr h₂ h₁‖ := by
    show
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
          2 * (corr h₂ h₁).re) ≤
        ∑ h₁ ∈ shifts,
          ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
            2 * ‖corr h₂ h₁‖
    exact
        Finset.sum_le_sum
        (fun h₁ hh₁ =>
          Finset.sum_le_sum
            (fun h₂ hh₂ =>
              mul_le_mul_of_nonneg_left
                (Complex.re_le_abs (corr h₂ h₁))
                zero_le_two))
  have htarget :
      (∑ h ∈ shifts,
        ∑ m ∈ outer, Complex.normSq (u m h)) + pairReal ≤
        (∑ h ∈ shifts,
          ∑ m ∈ outer, Complex.normSq (u m h)) +
          (∑ h₁ ∈ shifts,
            ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
              2 * ‖corr h₂ h₁‖) :=
    add_le_add_left hpair_le_norm
      (∑ h ∈ shifts, ∑ m ∈ outer, Complex.normSq (u m h))
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          (∑ h ∈ shifts,
            ∑ m ∈ outer, Complex.normSq (u m h)) +
            (∑ h₁ ∈ shifts,
              ∑ h₂ ∈ shifts.filter (fun h₂ : ℕ => h₁ < h₂),
                2 * ‖∑ m ∈ outer, u m h₂ * star (u m h₁)‖))
      hnormSq_expand.symm
      htarget

/-- Diagonal contribution in the finite Weyl translate square expansion. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  (H : ℝ) * Real.secondDerivativeVdc_blockLength a b

/-- Positive-difference mass in the finite Weyl translate-square expansion.
For a difference `k`, there are at most `H-k` ordered shift pairs contributing
that autocorrelation. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
    ((H - k : ℕ) : ℝ) *
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖

/-- Diagonal part of the expanded Weyl translate square before evaluation. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
    ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))

/-- Off-diagonal part of the expanded Weyl translate square, still indexed by
ordered shift pairs. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
    ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
        (fun h₂ : ℕ => h₁ < h₂),
      2 *
        ‖∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
            star
              (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
                (m + (h₁ : ℤ)))‖

/-- Expanding each translate square separates the diagonal terms and the
paired ordered off-diagonal terms. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_expanded_diagonal_add_offDiagonal
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion φ a b H +
        Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H := by
  show
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) ≤
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) +
        ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
              (fun h₂ : ℕ => h₁ < h₂),
            2 *
              ‖∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
                Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
                  star
                    (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
                      (m + (h₁ : ℤ)))‖
  exact
    Complex.finset_normSq_sum_over_outer_le_diagonal_add_ordered_offDiagonal
        (Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H)
        (Complex.realPhase_secondDerivative_vdc_shiftRange H)
      (fun m h =>
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
          (m + (h : ℤ)))

/-- The expanded diagonal part contributes exactly `H` copies of the original
block length. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion_eq_mass
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion φ a b H =
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) =
      (H : ℝ) * Real.secondDerivativeVdc_blockLength a b
  have hpoint :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h : ℤ)))) =
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Real.secondDerivativeVdc_blockLength a b :=
    Finset.sum_congr
      (Eq.refl (Complex.realPhase_secondDerivative_vdc_shiftRange H))
      (fun h hh =>
        Complex.realPhase_secondDerivative_vdc_weylTranslate_fixedShift_normSq_sum_eq_blockLength
          φ hH hH_block hh)
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_blockLength a b) =
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) *
          Real.secondDerivativeVdc_blockLength a b :=
    Eq.trans
      (Finset.sum_const (Real.secondDerivativeVdc_blockLength a b))
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card
        (Real.secondDerivativeVdc_blockLength a b))
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) =
        (H : ℝ) := by
    have hcard_nat :
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H + 1 - 1 :=
      Nat.card_Icc 1 H
    exact congrArg (fun n : ℕ => (n : ℝ))
      (Eq.trans hcard_nat (Nat.succ_sub_one H))
  exact Eq.trans hpoint
    (Eq.trans hconst
      (congrArg
        (fun r : ℝ => r * Real.secondDerivativeVdc_blockLength a b)
        hcard))

/-- Translating an ordered off-diagonal pair by its lower shift rewrites the
pair-correlation sum over the corresponding integer index interval. -/
theorem Complex.realPhase_secondDerivative_vdc_pairCorrelation_translate_to_indexInterval
    (φ : ℝ → ℝ)
    {a b H h₁ h₂ : ℕ}
    (hlt : h₁ < h₂) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
        star
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (m + (h₁ : ℤ)))) =
      ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (n + ((h₂ - h₁ : ℕ) : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) := by
  show
    (∑ m ∈ Finset.Icc ((a : ℤ) - (H : ℤ)) (b : ℤ),
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
        star
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (m + (h₁ : ℤ)))) =
      ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (n + ((h₂ - h₁ : ℕ) : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)
  exact
    Finset.sum_bij
      (fun m _ => m + (h₁ : ℤ))
      (fun m hm =>
        have hmbounds :
            (a : ℤ) - (H : ℤ) ≤ m ∧ m ≤ (b : ℤ) :=
          Finset.mem_Icc.mp hm
        Finset.mem_Icc.mpr
          (And.intro
            (add_le_add_right hmbounds.1 (h₁ : ℤ))
            (add_le_add_right hmbounds.2 (h₁ : ℤ))))
      (fun m₁ _hm₁ m₂ _hm₂ heq => add_right_cancel heq)
      (fun n hn =>
        have hnbounds :
            ((a : ℤ) - (H : ℤ)) + (h₁ : ℤ) ≤ n ∧
              n ≤ (b : ℤ) + (h₁ : ℤ) :=
          Finset.mem_Icc.mp hn
        ⟨n - (h₁ : ℤ),
          (by
            have hlower_shift :
                ((a : ℤ) - (H : ℤ)) + (h₁ : ℤ) - (h₁ : ℤ) ≤
                  n - (h₁ : ℤ) :=
              sub_le_sub_right hnbounds.1 (h₁ : ℤ)
            have hlower_cancel :
                ((a : ℤ) - (H : ℤ)) + (h₁ : ℤ) - (h₁ : ℤ) =
                  (a : ℤ) - (H : ℤ) :=
              add_sub_cancel_right ((a : ℤ) - (H : ℤ)) (h₁ : ℤ)
            have hlower :
                (a : ℤ) - (H : ℤ) ≤ n - (h₁ : ℤ) :=
              Eq.subst
                (motive := fun z : ℤ => z ≤ n - (h₁ : ℤ))
                hlower_cancel
                hlower_shift
            have hupper_shift :
                n - (h₁ : ℤ) ≤ ((b : ℤ) + (h₁ : ℤ)) - (h₁ : ℤ) :=
              sub_le_sub_right hnbounds.2 (h₁ : ℤ)
            have hupper_cancel :
                ((b : ℤ) + (h₁ : ℤ)) - (h₁ : ℤ) = (b : ℤ) :=
              add_sub_cancel_right (b : ℤ) (h₁ : ℤ)
            have hupper :
                n - (h₁ : ℤ) ≤ (b : ℤ) :=
              Eq.subst
                (motive := fun z : ℤ => n - (h₁ : ℤ) ≤ z)
                hupper_cancel
                hupper_shift
            exact Finset.mem_Icc.mpr (And.intro hlower hupper)),
          sub_add_cancel n (h₁ : ℤ)⟩)
      (fun m _hm =>
        have hnat :
            h₂ = h₁ + (h₂ - h₁) :=
          (Nat.add_sub_of_le (le_of_lt hlt)).symm
        have hint :
            (h₂ : ℤ) = (h₁ : ℤ) + ((h₂ - h₁ : ℕ) : ℤ) := by
          exact congrArg (fun n : ℕ => (n : ℤ)) hnat
        have hindex :
            m + (h₂ : ℤ) =
              (m + (h₁ : ℤ)) + ((h₂ - h₁ : ℕ) : ℤ) := by
          calc
            m + (h₂ : ℤ) =
                m + ((h₁ : ℤ) + ((h₂ - h₁ : ℕ) : ℤ)) :=
              congrArg (fun z : ℤ => m + z) hint
            _ =
                (m + (h₁ : ℤ)) + ((h₂ - h₁ : ℕ) : ℤ) :=
              (add_assoc m (h₁ : ℤ) ((h₂ - h₁ : ℕ) : ℤ)).symm
        congrArg
          (fun z : ℤ =>
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b z *
              star
                (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
                  (m + (h₁ : ℤ))))
          hindex)

/-- Outside the natural shifted-correlation range, at least one of the two
zero-extended coefficients in a fixed pair correlation vanishes. -/
theorem Complex.realPhase_secondDerivative_vdc_pairCorrelation_term_eq_zero_of_not_shiftedBlock
    (φ : ℝ → ℝ)
    {a b k : ℕ}
    {n : ℤ}
    (hn :
      n ∉ (Finset.Icc a (b - k)).image (fun r : ℕ => (r : ℤ))) :
    Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) *
        star (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) =
      0 := by
  by_cases hn_bounds : (a : ℤ) ≤ n ∧ n ≤ (b : ℤ)
  · by_cases hnk_bounds :
        (a : ℤ) ≤ n + (k : ℤ) ∧ n + (k : ℤ) ≤ (b : ℤ)
    · have hn_nonneg : 0 ≤ n :=
        le_trans (Int.natCast_nonneg a) hn_bounds.1
      have hn_toNat : ((n.toNat : ℕ) : ℤ) = n :=
        Int.toNat_of_nonneg hn_nonneg
      have hn_left : a ≤ n.toNat := by
        have hleft_int : (a : ℤ) ≤ ((n.toNat : ℕ) : ℤ) :=
          Eq.subst
            (motive := fun z : ℤ => (a : ℤ) ≤ z)
            hn_toNat.symm
            hn_bounds.1
        exact Int.ofNat_le.mp hleft_int
      have hn_add_le_b : n.toNat + k ≤ b := by
        have hcast_add :
            (((n.toNat + k : ℕ) : ℤ)) = n + (k : ℤ) := by
          calc
            ((n.toNat + k : ℕ) : ℤ) =
                ((n.toNat : ℕ) : ℤ) + (k : ℤ) :=
              Int.ofNat_add n.toNat k
            _ = n + (k : ℤ) :=
              congrArg (fun z : ℤ => z + (k : ℤ)) hn_toNat
        have hle_int :
            (((n.toNat + k : ℕ) : ℤ)) ≤ (b : ℤ) :=
          Eq.subst
            (motive := fun z : ℤ => z ≤ (b : ℤ))
            hcast_add.symm
            hnk_bounds.2
        exact Int.ofNat_le.mp hle_int
      have hn_right : n.toNat ≤ b - k :=
        Nat.le_sub_of_add_le hn_add_le_b
      exact
        False.elim
          (hn
            (Finset.mem_image.mpr
              ⟨n.toNat, Finset.mem_Icc.mpr (And.intro hn_left hn_right), hn_toNat⟩))
    · have hleft_zero :
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) = 0 :=
        Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_not_mem
          φ a b hnk_bounds
      exact Eq.trans
        (congrArg
          (fun z : ℂ =>
            z *
              star (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n))
          hleft_zero)
        (zero_mul
          (star (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)))
  · have hright_zero :
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n = 0 :=
      Complex.realPhase_secondDerivative_vdc_coefficientExtended_of_not_mem
        φ a b hn_bounds
    exact Eq.trans
      (congrArg
        (fun z : ℂ =>
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) *
            star z)
        hright_zero)
      (Eq.trans
        (congrArg
          (fun z : ℂ =>
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) * z)
          (map_zero (starRingEnd ℂ)))
        (mul_zero
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)))))

/-- The natural shifted-correlation block, embedded in the integers, is
contained in the translated pair-correlation index interval. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedBlock_subset_pairIndexInterval
    {a b H h₁ h₂ : ℕ}
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    (Finset.Icc a (b - (h₂ - h₁))).image (fun n : ℕ => (n : ℤ)) ⊆
        Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)) := by
  intro n hn
  match Finset.mem_image.mp hn with
  | ⟨r, hr, hrn⟩ =>
        have hr_bounds : a ≤ r ∧ r ≤ b - (h₂ - h₁) :=
        Finset.mem_Icc.mp hr
        have hh₁_bounds : 1 ≤ h₁ ∧ h₁ ≤ H :=
        Finset.mem_Icc.mp hh₁
        have hlower₀ :
          (a : ℤ) - (H : ℤ) ≤ (a : ℤ) - (h₁ : ℤ) :=
        sub_le_sub_left (Int.ofNat_le.mpr hh₁_bounds.2) (a : ℤ)
        have hlower₁ :
          (a : ℤ) - (h₁ : ℤ) ≤ (r : ℤ) - (h₁ : ℤ) :=
        sub_le_sub_right (Int.ofNat_le.mpr hr_bounds.1) (h₁ : ℤ)
        have hlower_main :
          (a : ℤ) - (H : ℤ) ≤ (r : ℤ) - (h₁ : ℤ) :=
        le_trans hlower₀ hlower₁
        have hlower :
          ((a : ℤ) - (H : ℤ)) + (h₁ : ℤ) ≤ (r : ℤ) :=
        Int.add_le_iff_le_sub.mpr hlower_main
        have hupper₀ :
          r ≤ b :=
        le_trans hr_bounds.2 (Nat.sub_le b (h₂ - h₁))
        have hupper :
          (r : ℤ) ≤ (b : ℤ) + (h₁ : ℤ) :=
        le_trans (Int.ofNat_le.mpr hupper₀)
          (le_add_of_nonneg_right (Int.natCast_nonneg h₁))
        exact Eq.subst
          (motive := fun z : ℤ =>
            z ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)))
          hrn
          (Finset.mem_Icc.mpr (And.intro hlower hupper))

/-- An ordered Weyl-shift difference fits in the integer block gap whenever
the averaging length fits in the block cardinality. -/
theorem Nat.realPhase_secondDerivative_vdc_ordered_shift_difference_le_block_gap
    {a b H h₁ h₂ : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    h₂ - h₁ ≤ b - a := by
  have hab : a ≤ b :=
    Nat.realPhase_secondDerivative_vdc_nonempty_of_shiftLength_le_card
      hH hH_block
  have hh₁_bounds : 1 ≤ h₁ ∧ h₁ ≤ H :=
    Finset.mem_Icc.mp hh₁
  have hh₂_bounds : 1 ≤ h₂ ∧ h₂ ≤ H :=
    Finset.mem_Icc.mp hh₂
  have hcard :
      (Finset.Icc a b).card = b + 1 - a :=
    Nat.card_Icc a b
  have hH_le_endpoint : H ≤ b + 1 - a :=
    Eq.subst
      (motive := fun n : ℕ => H ≤ n)
      hcard
      hH_block
  have hdiff_add_left :
      h₂ - h₁ + h₁ = h₂ :=
    Nat.sub_add_cancel (le_of_lt hlt)
  have hdiff_succ_le_h₂ :
      h₂ - h₁ + 1 ≤ h₂ := by
    have hstep :
        h₂ - h₁ + 1 ≤ h₂ - h₁ + h₁ :=
      Nat.add_le_add_left hh₁_bounds.1 (h₂ - h₁)
    exact
      Eq.subst
        (motive := fun n : ℕ => h₂ - h₁ + 1 ≤ n)
        hdiff_add_left
        hstep
  have hdiff_succ_le_endpoint :
      h₂ - h₁ + 1 ≤ b + 1 - a :=
    le_trans hdiff_succ_le_h₂
      (le_trans hh₂_bounds.2 hH_le_endpoint)
  have hsub :
      h₂ - h₁ + 1 - 1 ≤ b + 1 - a - 1 :=
    Nat.sub_le_sub_right hdiff_succ_le_endpoint 1
  have hleft :
      h₂ - h₁ + 1 - 1 = h₂ - h₁ :=
    Nat.add_one_sub_one (h₂ - h₁)
  have hright :
      b + 1 - a - 1 = b - a := by
    have hsucc_sub :
        b + 1 - a = (b - a) + 1 :=
      Nat.succ_sub hab
    exact
      Eq.trans
        (congrArg (fun n : ℕ => n - 1) hsucc_sub)
        (Nat.add_one_sub_one (b - a))
  have hsub_left :
      h₂ - h₁ ≤ b + 1 - a - 1 :=
    Eq.subst
      (motive := fun n : ℕ => n ≤ b + 1 - a - 1)
      hleft
        hsub
  exact
    Eq.subst
      (motive := fun n : ℕ => h₂ - h₁ ≤ n)
      hright
        hsub_left

/-- The translated pair-correlation index interval trims to the ordinary
coefficient-side shifted correlation for the difference `h₂-h₁`. -/
theorem Complex.realPhase_secondDerivative_vdc_pairCorrelation_indexInterval_sum_eq_shiftedCoefficient
    (φ : ℝ → ℝ)
    {a b H h₁ h₂ : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    (∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)),
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
          (n + ((h₂ - h₁ : ℕ) : ℤ)) *
        star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
      Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation
        φ (h₂ - h₁) a b := by
  let k : ℕ := h₂ - h₁
  let large : Finset ℤ :=
    Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ))
  let shiftedImage : Finset ℤ :=
    (Finset.Icc a (b - k)).image (fun n : ℕ => (n : ℤ))
  have hsubset : shiftedImage ⊆ large :=
    Complex.realPhase_secondDerivative_vdc_shiftedBlock_subset_pairIndexInterval
        hh₁ hh₂ hlt
  have htrim :
      (∑ n ∈ large,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
        ∑ n ∈ shiftedImage,
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) *
            star
              (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) :=
    Eq.symm
      (Finset.sum_subset hsubset
        (fun n hn_large hn_not_shifted =>
          Complex.realPhase_secondDerivative_vdc_pairCorrelation_term_eq_zero_of_not_shiftedBlock
            φ hn_not_shifted))
  have hinj :
      Set.InjOn (fun n : ℕ => (n : ℤ)) (Finset.Icc a (b - k) : Set ℕ) := by
    intro n₁ hn₁ n₂ hn₂ heq
    exact Int.ofNat.inj heq
  have himage :
      (∑ n ∈ shiftedImage,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n + (k : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
        ∑ n ∈ Finset.Icc a (b - k),
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b ((n : ℤ) + (k : ℤ)) *
            star
              (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)) :=
    Finset.sum_image hinj
  have hidentify :
      (∑ n ∈ Finset.Icc a (b - k),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b ((n : ℤ) + (k : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ))) =
        Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ k a b := by
    show
      (∑ n ∈ Finset.Icc a (b - k),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b ((n : ℤ) + (k : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ))) =
        ∑ n ∈ Finset.Icc a (b - k),
          Complex.realPhase_secondDerivative_vdc_coefficient φ (n + k) *
            star (Complex.realPhase_secondDerivative_vdc_coefficient φ n)
    exact Finset.sum_congr
      (Eq.refl (Finset.Icc a (b - k)))
      (fun n hn => by
        have hn_bounds : a ≤ n ∧ n ≤ b - k :=
          Finset.mem_Icc.mp hn
        have hn_mem : n ∈ Finset.Icc a b := by
          exact Finset.mem_Icc.mpr
            (And.intro hn_bounds.1
              (le_trans hn_bounds.2 (Nat.sub_le b k)))
        have hnk_le_b : n + k ≤ b := by
          have hn_le : n ≤ b - k := hn_bounds.2
          have hk_le_gap :
              k ≤ b - a :=
            Nat.realPhase_secondDerivative_vdc_ordered_shift_difference_le_block_gap
              hH hH_block hh₁ hh₂ hlt
          have hk_le_b : k ≤ b :=
            le_trans hk_le_gap (Nat.sub_le b a)
          exact Nat.add_le_of_le_sub hk_le_b hn_le
        have hnk_mem : n + k ∈ Finset.Icc a b := by
          exact Finset.mem_Icc.mpr
            (And.intro
              (le_trans hn_bounds.1 (Nat.le_add_right n k))
              hnk_le_b)
        have hsum_index :
            ((n : ℤ) + (k : ℤ)) = ((n + k : ℕ) : ℤ) :=
          (Int.ofNat_add n k).symm
        have hleft :
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b ((n : ℤ) + (k : ℤ)) =
              Complex.realPhase_secondDerivative_vdc_coefficient φ (n + k) :=
          Eq.trans
            (congrArg
              (fun z : ℤ =>
                Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b z)
              hsum_index)
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
              φ hnk_mem)
        have hright :
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ) =
              Complex.realPhase_secondDerivative_vdc_coefficient φ n :=
          Complex.realPhase_secondDerivative_vdc_coefficientExtended_natCast_of_mem
            φ hn_mem
        exact Eq.trans
          (congrArg
            (fun z : ℂ =>
              z *
                star
                  (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (n : ℤ)))
            hleft)
          (congrArg
            (fun z : ℂ =>
              Complex.realPhase_secondDerivative_vdc_coefficient φ (n + k) *
                star z)
            hright))
  exact Eq.trans htrim (Eq.trans himage hidentify)

/-- One fixed ordered off-diagonal shift pair contributes the shifted
correlation for the positive difference `h₂-h₁`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_pairCorrelation_eq_shifted
    (φ : ℝ → ℝ)
    {a b H h₁ h₂ : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card)
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
        star
          (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (m + (h₁ : ℤ)))) =
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ (h₂ - h₁) a b := by
  have htranslate :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
              (m + (h₁ : ℤ)))) =
        ∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)),
          Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
              (n + ((h₂ - h₁ : ℕ) : ℤ)) *
            star
              (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n) :=
    Complex.realPhase_secondDerivative_vdc_pairCorrelation_translate_to_indexInterval
      φ hlt
  have htrim :
      (∑ n ∈ Finset.Icc (((a : ℤ) - (H : ℤ)) + (h₁ : ℤ)) ((b : ℤ) + (h₁ : ℤ)),
        Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
            (n + ((h₂ - h₁ : ℕ) : ℤ)) *
          star
            (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b n)) =
        Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation
          φ (h₂ - h₁) a b :=
    Complex.realPhase_secondDerivative_vdc_pairCorrelation_indexInterval_sum_eq_shiftedCoefficient
      φ hH hH_block hh₁ hh₂ hlt
  have hbridge :
      Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation
          φ (h₂ - h₁) a b =
        Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ (h₂ - h₁) a b :=
    (Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_eq_coefficientShiftedCorrelation
      φ (h₂ - h₁) a b).symm
  exact Eq.trans htranslate (Eq.trans htrim hbridge)

/-- The ordered off-diagonal expansion is bounded by summing the norm of the
corresponding shifted correlation over all ordered positive-difference pairs. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion_le_pairNorms
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H ≤
      ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
            (fun h₂ : ℕ => h₁ < h₂),
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (h₂ - h₁) a b‖ := by
  show
    (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
          (fun h₂ : ℕ => h₁ < h₂),
        2 *
          ‖∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
            Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
              star
                (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
                  (m + (h₁ : ℤ)))‖) ≤
      ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
            (fun h₂ : ℕ => h₁ < h₂),
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (h₂ - h₁) a b‖
  exact Finset.sum_le_sum
    (fun h₁ hh₁ =>
        Finset.sum_le_sum
        (fun h₂ hh₂_filter => by
          have hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
            (Finset.mem_filter.mp hh₂_filter).1
          have hlt : h₁ < h₂ :=
            (Finset.mem_filter.mp hh₂_filter).2
          have hcorr :
              (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
                Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b (m + (h₂ : ℤ)) *
                  star
                    (Complex.realPhase_secondDerivative_vdc_coefficientExtended φ a b
                      (m + (h₁ : ℤ)))) =
                Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ (h₂ - h₁) a b :=
            Complex.realPhase_secondDerivative_vdc_weylTranslate_pairCorrelation_eq_shifted
              φ hH hH_block hh₁ hh₂ hlt
          exact le_of_eq
            (congrArg
              (fun z : ℂ => 2 * ‖z‖)
              hcorr)))

/-- Positive start indices for ordered Weyl shift pairs with fixed difference
`k`: the pair is `(h₁, h₁+k)`. -/
def Complex.realPhase_secondDerivative_vdc_weylPairStartRange
    (H k : ℕ) : Finset ℕ :=
  Finset.Icc 1 (H - k)

/-- The fixed-difference pair start range has exactly `H-k` elements. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairStartRange_card_eq
    (H k : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k).card = H - k := by
  show (Finset.Icc 1 (H - k)).card = H - k
  have hcard :
      (Finset.Icc 1 (H - k)).card = (H - k) + 1 - 1 :=
    Nat.card_Icc 1 (H - k)
  exact Eq.trans hcard (Nat.succ_sub_one (H - k))

/-- For a fixed positive difference, summing a constant over the valid start
range gives the expected `H-k` multiplicity. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairStartRange_sum_const
    (H k : ℕ)
    (M : ℝ) :
    (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k, M) =
      ((H - k : ℕ) : ℝ) * M := by
  have hconst :
      (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k, M) =
        ((Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k).card : ℝ) * M :=
    Eq.trans
      (Finset.sum_const M)
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k).card
        M)
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k).card : ℝ) =
        ((H - k : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
        (Complex.realPhase_secondDerivative_vdc_weylPairStartRange_card_eq H k)
  exact Eq.trans hconst (congrArg (fun r : ℝ => r * M) hcard)

/-- The positive difference of an ordered Weyl shift pair is again in the
Weyl shift range. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairDifference_mem_shiftRange
    {H h₁ h₂ : ℕ}
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    h₂ - h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H := by
  have hh₂_bounds : 1 ≤ h₂ ∧ h₂ ≤ H :=
    Finset.mem_Icc.mp hh₂
  have hpos : 1 ≤ h₂ - h₁ :=
    Nat.succ_le_iff.mp (Nat.sub_pos_of_lt hlt)
  have hle : h₂ - h₁ ≤ H :=
    le_trans (Nat.sub_le h₂ h₁) hh₂_bounds.2
  exact Finset.mem_Icc.mpr (And.intro hpos hle)

/-- The lower shift of an ordered Weyl pair is a valid start for its positive
difference. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairStart_mem_startRange
    {H h₁ h₂ : ℕ}
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₂ : h₂ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hlt : h₁ < h₂) :
    h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H (h₂ - h₁) := by
  show h₁ ∈ Finset.Icc 1 (H - (h₂ - h₁))
  have hh₁_bounds : 1 ≤ h₁ ∧ h₁ ≤ H :=
    Finset.mem_Icc.mp hh₁
  have hh₂_bounds : 1 ≤ h₂ ∧ h₂ ≤ H :=
    Finset.mem_Icc.mp hh₂
  have hsum_eq : h₁ + (h₂ - h₁) = h₂ :=
    Nat.add_sub_of_le (le_of_lt hlt)
  have hsum_le : h₁ + (h₂ - h₁) ≤ H :=
    Eq.subst
      (motive := fun n : ℕ => n ≤ H)
      hsum_eq.symm
        hh₂_bounds.2
  have hstart_le : h₁ ≤ H - (h₂ - h₁) :=
    Nat.le_sub_of_add_le hsum_le
  exact Finset.mem_Icc.mpr (And.intro hh₁_bounds.1 hstart_le)

/-- A positive difference and a valid start reconstruct an ordered Weyl shift
pair. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairStart_add_difference_mem
    {H k h₁ : ℕ}
    (hk : k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k) :
    h₁ + k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H := by
  have hh₁_explicit : h₁ ∈ Finset.Icc 1 (H - k) :=
    hh₁
  have hk_bounds : 1 ≤ k ∧ k ≤ H :=
    Finset.mem_Icc.mp hk
  have hh₁_bounds : 1 ≤ h₁ ∧ h₁ ≤ H - k :=
    Finset.mem_Icc.mp hh₁_explicit
  have hleft : 1 ≤ h₁ + k :=
    le_trans hh₁_bounds.1 (Nat.le_add_right h₁ k)
  have hright : h₁ + k ≤ H := by
    exact Nat.add_le_of_le_sub hk_bounds.2 hh₁_bounds.2
  exact Finset.mem_Icc.mpr (And.intro hleft hright)

/-- A positive difference and a valid start reconstruct a strictly ordered
shift pair. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairStart_lt_add_difference
    {H k h₁ : ℕ}
    (hk : k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H)
    (hh₁ : h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k) :
    h₁ < h₁ + k := by
  have hk_pos : 1 ≤ k :=
    (Finset.mem_Icc.mp hk).1
  exact Nat.lt_add_of_pos_right (Nat.lt_of_succ_le hk_pos)

/-- Reindex ordered shift pairs by their positive difference and starting
shift. -/
theorem Complex.realPhase_secondDerivative_vdc_weylPairNorms_reindex_by_difference
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
          (fun h₂ : ℕ => h₁ < h₂),
        2 *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
            φ (h₂ - h₁) a b‖) =
      ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖ := by
  let shifts : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_shiftRange H
  let starts : ℕ → Finset ℕ :=
    fun k : ℕ => Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k
  let upperStarts : ℕ → Finset ℕ :=
    fun h₁ : ℕ => shifts.filter (fun h₂ : ℕ => h₁ < h₂)
  have hleft_sigma :
      (∑ h₁ ∈ shifts,
        ∑ h₂ ∈ upperStarts h₁,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (h₂ - h₁) a b‖) =
        ∑ p ∈ shifts.sigma upperStarts,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (p.2 - p.1) a b‖ :=
    Finset.sum_sigma' shifts upperStarts
      (fun h₁ h₂ =>
        2 *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
            φ (h₂ - h₁) a b‖)
  have hright_sigma :
      (∑ k ∈ shifts,
        ∑ h₁ ∈ starts k,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖) =
        ∑ p ∈ shifts.sigma starts,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ p.1 a b‖ :=
    Finset.sum_sigma' shifts starts
      (fun k h₁ =>
        2 *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
            φ k a b‖)
  have hsigma :
      (∑ p ∈ shifts.sigma upperStarts,
        2 *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
            φ (p.2 - p.1) a b‖) =
        ∑ p ∈ shifts.sigma starts,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ p.1 a b‖ := by
    exact Finset.sum_bij'
      (α := ℝ)
      (fun p _ => (Sigma.mk (p.2 - p.1) p.1 : Sigma fun _ : ℕ => ℕ))
      (fun p _ => (Sigma.mk p.2 (p.2 + p.1) : Sigma fun _ : ℕ => ℕ))
      (by
        intro p hp
        have hp_mem : p.1 ∈ shifts ∧ p.2 ∈ upperStarts p.1 :=
          Finset.mem_sigma.mp hp
        have hh₁ : p.1 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          hp_mem.1
        have hp2_filter : p.2 ∈ shifts.filter (fun h₂ : ℕ => p.1 < h₂) :=
          hp_mem.2
        have hh₂ : p.2 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          (Finset.mem_filter.mp hp2_filter).1
        have hlt : p.1 < p.2 :=
          (Finset.mem_filter.mp hp2_filter).2
        exact Finset.mem_sigma.mpr
          (And.intro
            (Complex.realPhase_secondDerivative_vdc_weylPairDifference_mem_shiftRange
              hh₁ hh₂ hlt)
            (Complex.realPhase_secondDerivative_vdc_weylPairStart_mem_startRange
              hh₁ hh₂ hlt)))
      (by
        intro p hp
        have hp_mem : p.1 ∈ shifts ∧ p.2 ∈ starts p.1 :=
          Finset.mem_sigma.mp hp
        have hk : p.1 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          hp_mem.1
        have hstart :
            p.2 ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H p.1 :=
          hp_mem.2
        have hstart_bounds : 1 ≤ p.2 ∧ p.2 ≤ H - p.1 := by
          exact Finset.mem_Icc.mp hstart
        have hstart_le_H : p.2 ≤ H :=
          le_trans hstart_bounds.2 (Nat.sub_le H p.1)
        have hstart_shift :
            p.2 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          Finset.mem_Icc.mpr (And.intro hstart_bounds.1 hstart_le_H)
        have hsum_mem :
            p.2 + p.1 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          Complex.realPhase_secondDerivative_vdc_weylPairStart_add_difference_mem
            hk hstart
        have hlt :
            p.2 < p.2 + p.1 :=
          Complex.realPhase_secondDerivative_vdc_weylPairStart_lt_add_difference
            hk hstart
        exact Finset.mem_sigma.mpr
          (And.intro hstart_shift
            (Finset.mem_filter.mpr (And.intro hsum_mem hlt))))
      (by
        intro p hp
        have hp_mem : p.1 ∈ shifts ∧ p.2 ∈ upperStarts p.1 :=
          Finset.mem_sigma.mp hp
        have hp2_filter : p.2 ∈ shifts.filter (fun h₂ : ℕ => p.1 < h₂) :=
          hp_mem.2
        have hlt : p.1 < p.2 :=
          (Finset.mem_filter.mp hp2_filter).2
        have hfirst :
            p.1 + (p.2 - p.1) = p.2 :=
          Nat.add_sub_of_le (le_of_lt hlt)
        exact Sigma.ext rfl (heq_of_eq hfirst))
      (by
        intro p hp
        have hp_mem : p.1 ∈ shifts ∧ p.2 ∈ starts p.1 :=
          Finset.mem_sigma.mp hp
        have hk : p.1 ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H :=
          hp_mem.1
        have hstart :
            p.2 ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H p.1 :=
          hp_mem.2
        have hsub :
            p.2 + p.1 - p.2 = p.1 :=
          Nat.add_sub_cancel_left p.2 p.1
        exact Sigma.ext hsub (heq_of_eq rfl))
      (by
        intro p hp
        exact Eq.refl
          (2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (p.2 - p.1) a b‖))
  exact Eq.trans hleft_sigma
    (Eq.trans hsigma hright_sigma.symm)

/-- Grouping ordered positive-difference pairs by `k = h₂-h₁` gives the
weighted shifted-correlation mass. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_pairNorms_le_weighted
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
          (fun h₂ : ℕ => h₁ < h₂),
        2 *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
            φ (h₂ - h₁) a b‖) ≤
      2 *
        Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H := by
  have hreindex :
      (∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ h₂ ∈ (Complex.realPhase_secondDerivative_vdc_shiftRange H).filter
            (fun h₂ : ℕ => h₁ < h₂),
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ (h₂ - h₁) a b‖) =
        ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k,
            2 *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖ :=
    Complex.realPhase_secondDerivative_vdc_weylPairNorms_reindex_by_difference
      φ a b H
  have hinner :
      (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ∑ h₁ ∈ Complex.realPhase_secondDerivative_vdc_weylPairStartRange H k,
          2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖) =
        ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((H - k : ℕ) : ℝ) *
            (2 *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖) :=
    Finset.sum_congr
      (Eq.refl (Complex.realPhase_secondDerivative_vdc_shiftRange H))
      (fun k hk =>
        Complex.realPhase_secondDerivative_vdc_weylPairStartRange_sum_const
          H k
          (2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖))
  have hfactor :
      (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - k : ℕ) : ℝ) *
          (2 *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖)) =
        2 * (
          ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            ((H - k : ℕ) : ℝ) *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖) := by
    have hpoint :
        (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((H - k : ℕ) : ℝ) *
            (2 *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖)) =
          (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            2 *
              (((H - k : ℕ) : ℝ) *
                ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                  φ k a b‖)) :=
        Finset.sum_congr
        (Eq.refl (Complex.realPhase_secondDerivative_vdc_shiftRange H))
        (fun k hk =>
          Eq.trans
            ((mul_assoc
              (((H - k : ℕ) : ℝ))
              (2 : ℝ)
              (‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖)).symm)
            (Eq.trans
              (congrArg
                (fun r : ℝ =>
                  r *
                    ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                      φ k a b‖)
                (mul_comm ((H - k : ℕ) : ℝ) 2))
              (mul_assoc
                (2 : ℝ)
                ((H - k : ℕ) : ℝ)
                (‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                  φ k a b‖))))
    have hmul_sum :
        (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          2 *
            (((H - k : ℕ) : ℝ) *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                φ k a b‖)) =
          2 * (
            ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
              ((H - k : ℕ) : ℝ) *
                ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
                  φ k a b‖) :=
      (Finset.mul_sum
        (Complex.realPhase_secondDerivative_vdc_shiftRange H)
        (fun k : ℕ =>
          ((H - k : ℕ) : ℝ) *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation
              φ k a b‖)
        2).symm
    exact Eq.trans hpoint hmul_sum
  exact le_of_eq (Eq.trans hreindex (Eq.trans hinner hfactor))

/-- Grouping the expanded ordered off-diagonal terms by their positive shift
difference gives the weighted positive-difference mass. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion_le_weighted
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H ≤
      2 *
        Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H := by
  exact le_trans
    (Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion_le_pairNorms
      φ hH hH_block)
    (Complex.realPhase_secondDerivative_vdc_weylTranslate_pairNorms_le_weighted
      φ a b H)

/-- Off-diagonal contribution in the finite Weyl translate square expansion,
grouped by the positive shift difference. -/
def Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalMajorant
    (φ : ℝ → ℝ)
    (a b H : ℕ) : ℝ :=
  (H : ℝ) *
    (2 *
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        φ a b H)

/-- The weighted positive-difference mass is bounded by `H` times the
unweighted shifted-correlation envelope. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass_le
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass φ a b H ≤
      (H : ℝ) *
        Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H := by
  show
    (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ((H - k : ℕ) : ℝ) *
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖) ≤
      (H : ℝ) *
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖
  have hpoint :
      ∀ k : ℕ,
        k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ((H - k : ℕ) : ℝ) *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖ ≤
            (H : ℝ) *
              ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖ := by
    intro k hk
    have hsub_le : H - k ≤ H :=
      Nat.sub_le H k
    exact mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr hsub_le)
      (norm_nonneg
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b))
  have hsum :
      (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - k : ℕ) : ℝ) *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖) ≤
        ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (H : ℝ) *
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖ :=
    Finset.sum_le_sum hpoint
  have hfactor :
      (∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (H : ℝ) *
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖) =
        (H : ℝ) *
          ∑ k ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖ :=
    (Finset.mul_sum
        (Complex.realPhase_secondDerivative_vdc_shiftRange H)
      (fun k : ℕ =>
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ k a b‖)
      (H : ℝ)).symm
  exact le_trans hsum (le_of_eq hfactor)

/-- Exact finite Weyl translate-square estimate before replacing the weights
`H-k` by the coarse bound `H`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_diagonal_add_weighted
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        2 *
          Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H := by
  have hexpand :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
        Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion φ a b H +
          Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_expanded_diagonal_add_offDiagonal
      φ hH hH_block
  have hdiag :
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion φ a b H =
        Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion_eq_mass
      φ hH hH_block
  have hoff :
      Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H ≤
        2 *
          Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion_le_weighted
      φ hH hH_block
  have hcombined :
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalExpansion φ a b H +
          Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalExpansion φ a b H ≤
        Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
          2 *
            Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
              φ a b H :=
    add_le_add (le_of_eq hdiag) hoff
  exact le_trans hexpand hcombined

/-- Replacing the weighted positive-difference mass by the coarse envelope
gives the off-diagonal majorant. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_diagonal_add_weighted_le_diagonal_add_offDiagonal
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        2 *
          Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H ≤
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalMajorant φ a b H := by
  have hmass :
      Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass φ a b H ≤
        (H : ℝ) *
          Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass_le
      φ a b H
  have htwice :
      2 *
          Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H ≤
        2 *
          ((H : ℝ) *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) :=
    mul_le_mul_of_nonneg_left hmass zero_le_two
  show
    Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        2 *
          Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H ≤
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        (H : ℝ) *
          (2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H)
  have hmul_assoc :
      2 *
          ((H : ℝ) *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) =
        (H : ℝ) *
          (2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) := by
    calc
      2 *
          ((H : ℝ) *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) =
          (2 * (H : ℝ)) *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H :=
        (mul_assoc 2 (H : ℝ)
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H)).symm
      _ =
          ((H : ℝ) * 2) *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H :=
        congrArg
          (fun r : ℝ =>
            r *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H)
          (mul_comm 2 (H : ℝ))
      _ =
          (H : ℝ) *
            (2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) :=
        mul_assoc (H : ℝ) 2
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H)
  exact add_le_add_left
    (le_trans htwice (le_of_eq hmul_assoc))
    (Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H)

/-- The expanded translate-square energy is bounded by its diagonal mass plus
the paired positive-shift autocorrelation majorant. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_diagonal_add_offDiagonal
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
      Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalMajorant φ a b H := by
  exact le_trans
    (Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_diagonal_add_weighted
      φ hH hH_block)
    (Complex.realPhase_secondDerivative_vdc_weylTranslate_diagonal_add_weighted_le_diagonal_add_offDiagonal
      φ a b H)

/-- The diagonal/off-diagonal Weyl translate majorant is the compact envelope
form used by the averaged estimate. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_diagonal_add_offDiagonal_eq
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
        Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalMajorant φ a b H =
      (H : ℝ) *
        (Real.secondDerivativeVdc_blockLength a b +
          2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
              φ a b H) := by
  show
    (H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
        (H : ℝ) *
          (2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
              φ a b H) =
      (H : ℝ) *
        (Real.secondDerivativeVdc_blockLength a b +
          2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
              φ a b H)
  exact (mul_add (H : ℝ)
    (Real.secondDerivativeVdc_blockLength a b)
    (2 *
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
        φ a b H)).symm

/-- The total square of all Weyl translates is controlled by the diagonal
mass and the positive shifted-correlation envelope. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_normSq_sum_le
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
      Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
      (H : ℝ) *
        (Real.secondDerivativeVdc_blockLength a b +
          2 *
            Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
              φ a b H) := by
  have henergy :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) ≤
        Complex.realPhase_secondDerivative_vdc_weylTranslateDiagonalMass φ a b H +
          Complex.realPhase_secondDerivative_vdc_weylTranslateOffDiagonalMajorant φ a b H :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_diagonal_add_offDiagonal
      φ hH hH_block
  exact le_trans henergy
    (le_of_eq
        (Complex.realPhase_secondDerivative_vdc_weylTranslate_diagonal_add_offDiagonal_eq
        φ a b H))

/-- The averaged translate identity, converted to a real `normSq` identity. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_eq
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.normSq
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
      ((H : ℝ) * (H : ℝ)) *
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) := by
  have hsum_eq :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
        Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) =
        (H : ℂ) * Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_sum_eq_H_mul_block
      φ hH hH_block
  have hnorm_mul :
      Complex.normSq
          ((H : ℂ) *
            Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) =
        Complex.normSq (H : ℂ) *
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
    Complex.normSq_mul
      (H : ℂ)
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b)
  have hnorm_H :
      Complex.normSq (H : ℂ) = (H : ℝ) * (H : ℝ) :=
    Complex.normSq_natCast H
  exact
    Eq.trans
      (congrArg Complex.normSq hsum_eq)
      (Eq.trans hnorm_mul
        (congrArg
          (fun r : ℝ =>
            r *
              Complex.normSq
                (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b))
          hnorm_H))

/-- Cauchy-Schwarz applied to the outer translate sum. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_le
    (φ : ℝ → ℝ)
    {a b H : ℕ} :
    Complex.normSq
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m) ≤
      ((Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H).card : ℝ) *
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H,
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)) := by
  exact
    Complex.finset_normSq_sum_le_card_mul_sum_normSq
        (Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H)
      (fun m : ℤ =>
        Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m)

/-- The finite Weyl estimate before division by `H²`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylAverage_predivision
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ((H : ℝ) * (H : ℝ)) *
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((H : ℝ) *
          (Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                φ a b H)) := by
  let base : Finset ℤ :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H
  let translate : ℤ → ℂ :=
    fun m : ℤ =>
      Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m
  let energy : ℝ :=
    ∑ m ∈ base, Complex.normSq (translate m)
  let block : ℝ := Real.secondDerivativeVdc_blockLength a b
  let envelope : ℝ :=
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H
  have htotal_eq :
      Complex.normSq (∑ m ∈ base, translate m) =
        ((H : ℝ) * (H : ℝ)) *
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_eq
      φ hH hH_block
  have htotal_le :
      Complex.normSq (∑ m ∈ base, translate m) ≤
        (base.card : ℝ) * energy :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_le
      φ
  have hleft_le :
      ((H : ℝ) * (H : ℝ)) *
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
        (base.card : ℝ) * energy :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (base.card : ℝ) * energy)
      htotal_eq
      htotal_le
  have hcard :
      (base.card : ℝ) ≤ block + (H : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_le_block_add_H
      hH hH_block
  have henergy :
      energy ≤
        (H : ℝ) * (block + 2 * envelope) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_normSq_sum_le
      φ hH hH_block
  have henergy_nonneg : 0 ≤ energy :=
    Finset.sum_nonneg
      (fun m hm =>
        Complex.normSq_nonneg (translate m))
  have hright_nonneg :
      0 ≤ block + (H : ℝ) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_leftFactor_nonneg a b H
  have hmul :
      (base.card : ℝ) * energy ≤
        (block + (H : ℝ)) *
          ((H : ℝ) * (block + 2 * envelope)) :=
    mul_le_mul hcard henergy henergy_nonneg hright_nonneg
  exact le_trans hleft_le hmul

/-- The finite Weyl estimate before division by `H²`, retaining the exact
weighted positive-difference mass. -/
theorem Complex.realPhase_secondDerivative_vdc_weightedWeylAverage_predivision
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ((H : ℝ) * (H : ℝ)) *
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
          2 *
            Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
              φ a b H) := by
  let base : Finset ℤ :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateBase a b H
  let translate : ℤ → ℂ :=
    fun m : ℤ =>
      Complex.realPhase_secondDerivative_vdc_weylTranslateSum φ a b H m
  let energy : ℝ :=
    ∑ m ∈ base, Complex.normSq (translate m)
  let block : ℝ := Real.secondDerivativeVdc_blockLength a b
  let weightedMass : ℝ :=
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
      φ a b H
  have htotal_eq :
      Complex.normSq (∑ m ∈ base, translate m) =
        ((H : ℝ) * (H : ℝ)) *
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_eq
      φ hH hH_block
  have htotal_le :
      Complex.normSq (∑ m ∈ base, translate m) ≤
        (base.card : ℝ) * energy :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_total_normSq_le
      φ
  have hleft_le :
      ((H : ℝ) * (H : ℝ)) *
          Complex.normSq
            (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
        (base.card : ℝ) * energy :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (base.card : ℝ) * energy)
      htotal_eq
      htotal_le
  have hcard :
      (base.card : ℝ) ≤ block + (H : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_weylTranslateBase_card_le_block_add_H
      hH hH_block
  have henergy :
      energy ≤ (H : ℝ) * block + 2 * weightedMass :=
    Complex.realPhase_secondDerivative_vdc_weylTranslate_energy_le_diagonal_add_weighted
      φ hH hH_block
  have henergy_nonneg : 0 ≤ energy :=
    Finset.sum_nonneg
      (fun m hm =>
        Complex.normSq_nonneg (translate m))
  have hright_nonneg :
      0 ≤ block + (H : ℝ) :=
    Real.secondDerivativeVdc_weylEnvelopeMajorant_leftFactor_nonneg a b H
  have hmul :
      (base.card : ℝ) * energy ≤
        (block + (H : ℝ)) *
          ((H : ℝ) * block + 2 * weightedMass) :=
    mul_le_mul hcard henergy henergy_nonneg hright_nonneg
  exact le_trans hleft_le hmul

/-- Positive averaging length permits division of the predivision Weyl
estimate by `H²`. -/
theorem Real.secondDerivativeVdc_weylAverage_division_arithmetic
    {H : ℕ}
    {left blockLength envelope : ℝ}
    (hH : 1 ≤ H)
    (hpre :
      ((H : ℝ) * (H : ℝ)) * left ≤
        (blockLength + (H : ℝ)) *
          ((H : ℝ) * (blockLength + 2 * envelope))) :
    left ≤
      (blockLength + (H : ℝ)) *
        ((blockLength + 2 * envelope) * ((H : ℝ)⁻¹)) := by
  let h : ℝ := (H : ℝ)
  let A : ℝ := blockLength + h
  let C : ℝ := blockLength + 2 * envelope
  have hh_pos : 0 < h :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hH)
  have hh_nonneg : 0 ≤ h :=
    le_of_lt hh_pos
  have hhh_pos : 0 < h * h :=
    mul_pos hh_pos hh_pos
  have hhh_nonneg : 0 ≤ h * h :=
    le_of_lt hhh_pos
  have hhh_ne : h * h ≠ 0 :=
    ne_of_gt hhh_pos
  have hinv_nonneg : 0 ≤ (h * h)⁻¹ :=
    inv_nonneg.mpr hhh_nonneg
  have hpre_local :
      (h * h) * left ≤ A * (h * C) :=
    hpre
  have hdiv :
      ((h * h) * left) * ((h * h)⁻¹) ≤
        (A * (h * C)) * ((h * h)⁻¹) :=
    mul_le_mul_of_nonneg_right hpre_local hinv_nonneg
  have hleft_cancel :
      ((h * h) * left) * ((h * h)⁻¹) = left := by
    calc
      ((h * h) * left) * ((h * h)⁻¹) =
          left * ((h * h) * ((h * h)⁻¹)) := by
        calc
          ((h * h) * left) * ((h * h)⁻¹) =
              (h * h) * (left * ((h * h)⁻¹)) :=
            mul_assoc (h * h) left ((h * h)⁻¹)
          _ = left * ((h * h) * ((h * h)⁻¹)) := by
            calc
              (h * h) * (left * ((h * h)⁻¹)) =
                  ((h * h) * left) * ((h * h)⁻¹) :=
                (mul_assoc (h * h) left ((h * h)⁻¹)).symm
              _ = (left * (h * h)) * ((h * h)⁻¹) := by
                exact congrArg (fun r : ℝ => r * ((h * h)⁻¹))
                  (mul_comm (h * h) left)
              _ = left * ((h * h) * ((h * h)⁻¹)) :=
                mul_assoc left (h * h) ((h * h)⁻¹)
      _ = left * 1 := by
        exact congrArg (fun r : ℝ => left * r)
          (mul_inv_cancel₀ hhh_ne)
      _ = left :=
        mul_one left
  have hright_cancel :
      (A * (h * C)) * ((h * h)⁻¹) =
        A * (C * h⁻¹) := by
    have hhinv :
        h * ((h * h)⁻¹) = h⁻¹ := by
      have hmul_inv :
          (h * h)⁻¹ = h⁻¹ * h⁻¹ :=
        mul_inv_rev h h
      calc
        h * ((h * h)⁻¹) =
            h * (h⁻¹ * h⁻¹) := by
          exact congrArg (fun r : ℝ => h * r) hmul_inv
        _ = (h * h⁻¹) * h⁻¹ :=
          (mul_assoc h h⁻¹ h⁻¹).symm
        _ = 1 * h⁻¹ := by
          exact congrArg (fun r : ℝ => r * h⁻¹)
            (mul_inv_cancel₀ (ne_of_gt hh_pos))
        _ = h⁻¹ :=
          one_mul h⁻¹
    calc
      (A * (h * C)) * ((h * h)⁻¹) =
          A * ((h * C) * ((h * h)⁻¹)) :=
        mul_assoc A (h * C) ((h * h)⁻¹)
      _ = A * (C * (h * ((h * h)⁻¹))) := by
        exact congrArg (fun r : ℝ => A * r)
          (calc
            (h * C) * ((h * h)⁻¹) =
                C * (h * ((h * h)⁻¹)) := by
              calc
                (h * C) * ((h * h)⁻¹) =
                    (C * h) * ((h * h)⁻¹) := by
                  exact congrArg (fun r : ℝ => r * ((h * h)⁻¹))
                    (mul_comm h C)
                _ = C * (h * ((h * h)⁻¹)) :=
                  mul_assoc C h ((h * h)⁻¹))
      _ = A * (C * h⁻¹) := by
        exact congrArg (fun r : ℝ => A * (C * r)) hhinv
  have hresult :
      left ≤ A * (C * h⁻¹) :=
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ A * (C * h⁻¹))
      hleft_cancel
      (Eq.subst
        (motive := fun rhs : ℝ =>
          ((h * h) * left) * ((h * h)⁻¹) ≤ rhs)
        hright_cancel
        hdiv)
  exact hresult

/-- Positive averaging length permits division of the weighted predivision Weyl
estimate by `H²`. -/
theorem Real.secondDerivativeVdc_weightedWeylAverage_division_arithmetic
    {H : ℕ}
    {left blockLength weightedMass : ℝ}
    (hH : 1 ≤ H)
    (hpre :
      ((H : ℝ) * (H : ℝ)) * left ≤
        (blockLength + (H : ℝ)) *
          ((H : ℝ) * blockLength + 2 * weightedMass)) :
    left ≤
      (blockLength + (H : ℝ)) *
        (((H : ℝ) * blockLength + 2 * weightedMass) *
          (((H : ℝ) * (H : ℝ))⁻¹)) := by
  let h : ℝ := (H : ℝ)
  let A : ℝ := blockLength + h
  let D : ℝ := h * blockLength + 2 * weightedMass
  have hh_pos : 0 < h :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le hH)
  have hhh_pos : 0 < h * h :=
    mul_pos hh_pos hh_pos
  have hhh_nonneg : 0 ≤ h * h :=
    le_of_lt hhh_pos
  have hhh_ne : h * h ≠ 0 :=
    ne_of_gt hhh_pos
  have hinv_nonneg : 0 ≤ (h * h)⁻¹ :=
    inv_nonneg.mpr hhh_nonneg
  have hpre_local :
      (h * h) * left ≤ A * D :=
    hpre
  have hdiv :
      ((h * h) * left) * ((h * h)⁻¹) ≤
        (A * D) * ((h * h)⁻¹) :=
    mul_le_mul_of_nonneg_right hpre_local hinv_nonneg
  have hleft_cancel :
      ((h * h) * left) * ((h * h)⁻¹) = left := by
    calc
      ((h * h) * left) * ((h * h)⁻¹) =
          left * ((h * h) * ((h * h)⁻¹)) := by
        calc
          ((h * h) * left) * ((h * h)⁻¹) =
              (h * h) * (left * ((h * h)⁻¹)) :=
            mul_assoc (h * h) left ((h * h)⁻¹)
          _ = left * ((h * h) * ((h * h)⁻¹)) := by
            calc
              (h * h) * (left * ((h * h)⁻¹)) =
                  ((h * h) * left) * ((h * h)⁻¹) :=
                (mul_assoc (h * h) left ((h * h)⁻¹)).symm
              _ = (left * (h * h)) * ((h * h)⁻¹) := by
                exact congrArg (fun r : ℝ => r * ((h * h)⁻¹))
                  (mul_comm (h * h) left)
              _ = left * ((h * h) * ((h * h)⁻¹)) :=
                mul_assoc left (h * h) ((h * h)⁻¹)
      _ = left * 1 := by
        exact congrArg (fun r : ℝ => left * r)
          (mul_inv_cancel₀ hhh_ne)
      _ = left :=
        mul_one left
  have hright_assoc :
      (A * D) * ((h * h)⁻¹) =
        A * (D * ((h * h)⁻¹)) :=
    mul_assoc A D ((h * h)⁻¹)
  have hresult :
      left ≤ A * (D * ((h * h)⁻¹)) :=
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ A * (D * ((h * h)⁻¹)))
      hleft_cancel
      (Eq.subst
        (motive := fun rhs : ℝ =>
          ((h * h) * left) * ((h * h)⁻¹) ≤ rhs)
        hright_assoc
        hdiv)
  exact hresult

/-- Division of the Weyl average inequality by the positive averaging length. -/
theorem Complex.realPhase_secondDerivative_vdc_weylAverage_division
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                φ a b H) *
          ((H : ℝ)⁻¹)) := by
  exact
    Real.secondDerivativeVdc_weylAverage_division_arithmetic
      hH
        (Complex.realPhase_secondDerivative_vdc_weylAverage_predivision
        φ hH hH_block)

/-- Division of the weighted Weyl average inequality by the positive averaging
length. -/
theorem Complex.realPhase_secondDerivative_vdc_weightedWeylAverage_division
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                φ a b H) *
          (((H : ℝ) * (H : ℝ))⁻¹)) := by
  exact
    Real.secondDerivativeVdc_weightedWeylAverage_division_arithmetic
      hH
        (Complex.realPhase_secondDerivative_vdc_weightedWeylAverage_predivision
        φ hH hH_block)

/-- `normSq` expansion of the coefficient-block autocorrelation estimate.

This is the finite double-sum part of Weyl differencing: after expanding
`Complex.normSq (∑ c_n)`, the diagonal contributes the block length and the
off-diagonal terms are grouped by positive shifts. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_normSq_le_autocorrelationEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                φ a b H) *
          ((H : ℝ)⁻¹)) := by
  exact
    Complex.realPhase_secondDerivative_vdc_weylAverage_division
      φ hH hH_block

/-- `normSq` expansion of the coefficient-block autocorrelation estimate with
the exact weighted positive-difference mass. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_normSq_le_weightedAutocorrelation
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    Complex.normSq
        (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                φ a b H) *
          (((H : ℝ) * (H : ℝ))⁻¹)) := by
  exact
    Complex.realPhase_secondDerivative_vdc_weightedWeylAverage_division
      φ hH hH_block

/-- Autocorrelation form of the coefficient-block norm square.

This is the exact finite expansion of `|∑ c_n|^2` into the diagonal term plus
positive and negative shifts.  It is the algebraic core of finite Weyl
differencing. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_le_autocorrelationEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                φ a b H) *
          ((H : ℝ)⁻¹)) := by
  have hnormSq :
      Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          ((Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                  φ a b H) *
            ((H : ℝ)⁻¹)) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_normSq_le_autocorrelationEnvelope
      φ hH hH_block
  have hsq_eq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 =
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_eq_normSq
      φ a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
            ((Real.secondDerivativeVdc_blockLength a b +
                2 *
                  Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                    φ a b H) *
              ((H : ℝ)⁻¹)))
      hsq_eq.symm
      hnormSq

/-- Autocorrelation form of the coefficient-block norm square with the exact
weighted positive-difference mass. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_le_weightedAutocorrelation
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                φ a b H) *
          (((H : ℝ) * (H : ℝ))⁻¹)) := by
  have hnormSq :
      Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                  φ a b H) *
            (((H : ℝ) * (H : ℝ))⁻¹)) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_normSq_le_weightedAutocorrelation
      φ hH hH_block
  have hsq_eq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 =
        Complex.normSq
          (Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_eq_normSq
      φ a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
            (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
                2 *
                  Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                    φ a b H) *
              (((H : ℝ) * (H : ℝ))⁻¹)))
      hsq_eq.symm
      hnormSq

/-- Finite Weyl shift-averaging identity for one coefficient block.

This is the algebraic identity that replaces a coefficient block by an average
of its positive shifts plus boundary terms.  It is independent of the
particular phase. -/
theorem Complex.realPhase_secondDerivative_vdc_weyl_shift_average_identity
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
      (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
        ((Real.secondDerivativeVdc_blockLength a b +
            2 *
              Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                φ a b H) *
          ((H : ℝ)⁻¹)) := by
  exact
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_le_autocorrelationEnvelope
      φ hH hH_block

/-- Square-root extraction from the finite Weyl norm-square inequality. -/
theorem Complex.realPhase_secondDerivative_vdc_norm_le_weylEnvelope_of_sq
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hsq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          ((Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                  φ a b H) *
            ((H : ℝ)⁻¹))) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) := by
  show
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.sqrt
        ((Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          ((Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                  φ a b H) *
            ((H : ℝ)⁻¹)))
  exact Real.le_sqrt_of_sq_le hsq

/-- Square-root extraction from the weighted finite Weyl norm-square
inequality. -/
theorem Complex.realPhase_secondDerivative_vdc_norm_le_weightedWeylEnvelope_of_sq
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hsq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                  φ a b H) *
            (((H : ℝ) * (H : ℝ))⁻¹))) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H) := by
  show
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.sqrt
        ((Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                  φ a b H) *
            (((H : ℝ) * (H : ℝ))⁻¹)))
  exact Real.le_sqrt_of_sq_le hsq

/-- Finite Weyl differencing for one coefficient block.

This is the purely finite algebraic owner theorem behind the long
second-derivative step.  It contains no calculus or logarithmic-phase input:
the original coefficient block is bounded by its block length, the averaging
length, and the envelope of positive shifted autocorrelations. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_weylEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) := by
  have hsq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          ((Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope
                  φ a b H) *
            ((H : ℝ)⁻¹)) :=
    Complex.realPhase_secondDerivative_vdc_weyl_shift_average_identity
      φ hH hH_block
  exact
    Complex.realPhase_secondDerivative_vdc_norm_le_weylEnvelope_of_sq
      φ hH hsq

/-- Finite Weyl differencing for one coefficient block with the exact weighted
positive-difference mass. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_weightedWeylEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H) := by
  have hsq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ^ 2 ≤
        (Real.secondDerivativeVdc_blockLength a b + (H : ℝ)) *
          (((H : ℝ) * Real.secondDerivativeVdc_blockLength a b +
              2 *
                Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
                  φ a b H) *
            (((H : ℝ) * (H : ℝ))⁻¹)) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_sq_le_weightedAutocorrelation
      φ hH hH_block
  exact
    Complex.realPhase_secondDerivative_vdc_norm_le_weightedWeylEnvelope_of_sq
      φ hH hsq

/-- Original-sum form of the finite Weyl differencing inequality. -/
theorem Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weylEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) := by
  have hblock :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
        Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_weylEnvelope
      φ hH hH_block
  have hnorm_eq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_eq_original_sum_norm
      φ a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
            (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H))
      hnorm_eq
      hblock

/-- Original-sum form of the weighted finite Weyl differencing inequality. -/
theorem Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weightedWeylEnvelope
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    (hH : 1 ≤ H)
    (hH_block : H ≤ (Finset.Icc a b).card) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
        (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H) := by
  have hblock :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H) :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_le_weightedWeylEnvelope
      φ hH hH_block
  have hnorm_eq :
      ‖Complex.realPhase_secondDerivative_vdc_coefficientBlock φ a b‖ =
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.realPhase_secondDerivative_vdc_coefficientBlock_norm_eq_original_sum_norm
      φ a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
            (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
              φ a b H))
      hnorm_eq
      hblock

/-- Membership in the Weyl shift range is exactly being a positive shift no
larger than the averaging length. -/
theorem Complex.mem_realPhase_secondDerivative_vdc_shiftRange_iff
    {H h : ℕ} :
    h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H ↔ 1 ≤ h ∧ h ≤ H := by
  exact Finset.mem_Icc

/-- Every member of the Weyl shift range is a positive shift. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_pos
    {H h : ℕ}
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    1 ≤ h :=
  (Complex.mem_realPhase_secondDerivative_vdc_shiftRange_iff.mp hh).1

/-- Every member of the Weyl shift range is bounded by the averaging length. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_le
    {H h : ℕ}
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    h ≤ H :=
  (Complex.mem_realPhase_secondDerivative_vdc_shiftRange_iff.mp hh).2

/-- If the Weyl shift length fits inside the integer block, then every Weyl
shift leaves a nonempty shifted block endpoint. -/
theorem Nat.realPhase_secondDerivative_vdc_shift_le_block_gap
    {a b H h : ℕ}
    (hH : H ≤ b - a)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    h ≤ b - a :=
  le_trans
    (Complex.realPhase_secondDerivative_vdc_shiftRange_le hh)
    hH

/-- A valid Weyl shift preserves the lower endpoint after subtracting the
shift from the upper endpoint. -/
theorem Nat.realPhase_secondDerivative_vdc_lower_le_sub_shift
    {a b H h : ℕ}
    (hH : H ≤ b - a)
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    a ≤ b - h := by
  have hh_gap : h ≤ b - a :=
    Nat.realPhase_secondDerivative_vdc_shift_le_block_gap hH hh
  have hh_pos : 0 < h :=
    Nat.lt_of_succ_le
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
  have hgap_pos : 0 < b - a :=
    lt_of_lt_of_le hh_pos hh_gap
  have hab : a ≤ b :=
    le_of_lt (tsub_pos_iff_lt.mp hgap_pos)
  have hha : h + a ≤ b := by
    exact Nat.add_le_of_le_sub hab hh_gap
  exact
    Nat.le_sub_of_add_le
      (Eq.subst
        (motive := fun n : ℕ => n ≤ b)
        (add_comm h a)
        hha)

/-- The Weyl shift range has at most `H` elements. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_card_le
    (H : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_shiftRange H).card ≤ H := by
  have hcard :
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H + 1 - 1 :=
    Nat.card_Icc 1 H
  have hsucc_sub_one : H + 1 - 1 = H :=
    Nat.succ_sub_one H
  exact
    Eq.subst
      (motive := fun n : ℕ =>
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card ≤ n)
      hsucc_sub_one.symm
      (le_of_eq hcard)

/-- The Weyl shift range has exactly `H` elements. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_card_eq
    (H : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H := by
  have hcard :
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card = H + 1 - 1 :=
    Nat.card_Icc 1 H
  have hsucc_sub_one : H + 1 - 1 = H :=
    Nat.succ_sub_one H
  exact Eq.trans hcard hsucc_sub_one

/-- Real cardinality bound for the Weyl shift range. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_le
    (H : ℕ) :
    ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) ≤ (H : ℝ) :=
  Nat.cast_le.mpr
    (Complex.realPhase_secondDerivative_vdc_shiftRange_card_le H)

/-- Real cardinality identity for the Weyl shift range. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_eq
    (H : ℕ) :
    ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) = (H : ℝ) :=
  congrArg (fun n : ℕ => (n : ℝ))
    (Complex.realPhase_secondDerivative_vdc_shiftRange_card_eq H)

/-- Constant sums over the Weyl shift range are exactly `H` times the
constant. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const
    (H : ℕ)
    (M : ℝ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M) =
      (H : ℝ) * M := by
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M) =
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M :=
    Eq.trans
      (Finset.sum_const M)
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card M)
  exact Eq.trans hconst
    (congrArg (fun r : ℝ => r * M)
        (Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_eq H))

/-- The shifted-correlation envelope is nonnegative. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_nonneg
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    0 ≤
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H := by
  show
    0 ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖
  exact Finset.sum_nonneg
    (fun h hh =>
      norm_nonneg
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b))

/-- The shifted-correlation envelope is bounded by the sum of the lengths of
the shifted blocks. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_card_sum
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((Finset.Icc a (b - h)).card : ℝ) := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((Finset.Icc a (b - h)).card : ℝ)
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_norm_le_card
        φ h a b)

/-- Coefficient-side form of the shifted-correlation envelope cardinality
bound. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelationEnvelope_le_card_sum
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖ ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((Finset.Icc a (b - h)).card : ℝ) := by
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation_norm_le_card
        φ h a b)

/-- A shifted integer block is a subset of the original block. -/
theorem Finset.Icc_sub_right_subset_Icc
    {a b h : ℕ} :
    Finset.Icc a (b - h) ⊆ Finset.Icc a b := by
  intro n hn
  have hbounds : a ≤ n ∧ n ≤ b - h :=
    Finset.mem_Icc.mp hn
  exact Finset.mem_Icc.mpr
    (And.intro hbounds.1
      (le_trans hbounds.2 (Nat.sub_le b h)))

/-- A shifted integer block has cardinality at most the original block. -/
theorem Nat.card_Icc_sub_right_le_card_Icc
    (a b h : ℕ) :
    (Finset.Icc a (b - h)).card ≤ (Finset.Icc a b).card :=
  Finset.card_le_card Finset.Icc_sub_right_subset_Icc

/-- Real cardinality bound for one shifted integer block. -/
theorem Real.card_Icc_sub_right_le_card_Icc
    (a b h : ℕ) :
    ((Finset.Icc a (b - h)).card : ℝ) ≤
      ((Finset.Icc a b).card : ℝ) :=
  Nat.cast_le.mpr (Nat.card_Icc_sub_right_le_card_Icc a b h)

/-- The shifted-correlation envelope is bounded by `H` times the original
block length. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_shiftLength_mul_blockLength
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      (H : ℝ) * Real.secondDerivativeVdc_blockLength a b := by
  have hcard_sum :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((Finset.Icc a (b - h)).card : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_card_sum
      φ a b H
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ((Finset.Icc a (b - h)).card : ℝ) ≤
            Real.secondDerivativeVdc_blockLength a b := by
    intro h hh
    show
      ((Finset.Icc a (b - h)).card : ℝ) ≤
        ((Finset.Icc a b).card : ℝ)
    exact Real.card_Icc_sub_right_le_card_Icc a b h
  have hsum_bound :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((Finset.Icc a (b - h)).card : ℝ)) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_blockLength a b :=
    Finset.sum_le_sum hpoint
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_blockLength a b) =
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) *
          Real.secondDerivativeVdc_blockLength a b :=
    Eq.trans
      (Finset.sum_const (Real.secondDerivativeVdc_blockLength a b))
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card
        (Real.secondDerivativeVdc_blockLength a b))
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) *
          Real.secondDerivativeVdc_blockLength a b ≤
        (H : ℝ) * Real.secondDerivativeVdc_blockLength a b :=
    mul_le_mul_of_nonneg_right
        (Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_le H)
      (Real.secondDerivativeVdc_blockLength_nonneg a b)
  exact
    le_trans hcard_sum
      (le_trans hsum_bound
        (le_trans (le_of_eq hconst) hcard))

/-- The coefficient-side shifted autocorrelation envelope is bounded by `H`
times the original block length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelationEnvelope_le_shiftLength_mul_blockLength
    (φ : ℝ → ℝ)
    (a b H : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖) ≤
      (H : ℝ) * Real.secondDerivativeVdc_blockLength a b := by
  have hcard_sum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((Finset.Icc a (b - h)).card : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelationEnvelope_le_card_sum
      φ a b H
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ((Finset.Icc a (b - h)).card : ℝ) ≤
            Real.secondDerivativeVdc_blockLength a b := by
    intro h hh
    show
      ((Finset.Icc a (b - h)).card : ℝ) ≤
        ((Finset.Icc a b).card : ℝ)
    exact Real.card_Icc_sub_right_le_card_Icc a b h
  have hsum_bound :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((Finset.Icc a (b - h)).card : ℝ)) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_blockLength a b :=
    Finset.sum_le_sum hpoint
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_blockLength a b) =
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) *
          Real.secondDerivativeVdc_blockLength a b :=
    Eq.trans
      (Finset.sum_const (Real.secondDerivativeVdc_blockLength a b))
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card
        (Real.secondDerivativeVdc_blockLength a b))
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) *
          Real.secondDerivativeVdc_blockLength a b ≤
        (H : ℝ) * Real.secondDerivativeVdc_blockLength a b :=
    mul_le_mul_of_nonneg_right
        (Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_le H)
      (Real.secondDerivativeVdc_blockLength_nonneg a b)
  exact
    le_trans hcard_sum
      (le_trans hsum_bound
        (le_trans (le_of_eq hconst) hcard))

/-- A pointwise coefficient-side shifted autocorrelation bound controls its
envelope by the exact shift-range length. -/
theorem Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelationEnvelope_le_exact_H_mul
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {M : ℝ}
    (hbound :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖ ≤ M) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖) ≤
      (H : ℝ) * M := by
  have hsum_bound :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_coefficientShiftedCorrelation φ h a b‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M :=
    Finset.sum_le_sum
      (fun h hh => hbound h hh)
  exact le_trans hsum_bound
    (le_of_eq
        (Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const H M))

/-- A pointwise shifted-correlation bound controls the finite shifted envelope. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_of_forall
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {M : ℝ}
    (hM : 0 ≤ M)
    (hbound :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤ M) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M
  have hsum_bound :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M :=
    Finset.sum_le_sum
      (fun h hh => hbound h hh)
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M) =
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M :=
    Eq.trans
      (Finset.sum_const M)
      (nsmul_eq_mul
        (Complex.realPhase_secondDerivative_vdc_shiftRange H).card M)
  exact le_trans hsum_bound (le_of_eq hconst)

/-- A pointwise shifted-correlation bound and the shift-cardinality bound
control the envelope by `H * M`. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_H_mul
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {M : ℝ}
    (hM : 0 ≤ M)
    (hbound :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤ M) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      (H : ℝ) * M := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
        ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M :=
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_of_forall
      φ hM hbound
  have hcard :
      ((Complex.realPhase_secondDerivative_vdc_shiftRange H).card : ℝ) * M ≤
        (H : ℝ) * M :=
    mul_le_mul_of_nonneg_right
        (Complex.realPhase_secondDerivative_vdc_shiftRange_card_real_le H)
      hM
  exact le_trans henvelope hcard

/-- A pointwise shifted-correlation bound controls the envelope by the exact
shift-range length. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_exact_H_mul
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {M : ℝ}
    (hbound :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤ M) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      (H : ℝ) * M := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
      (H : ℝ) * M
  have hsum_bound :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M :=
    Finset.sum_le_sum
      (fun h hh => hbound h hh)
  exact le_trans hsum_bound
    (le_of_eq
        (Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const H M))

/-- Curvature-scale first-derivative majorant for one shifted correlation. -/
def Real.secondDerivativeVdc_shiftedCorrelationMajorant
    (T : ℝ)
    (b h : ℕ) : ℝ :=
  4 *
      ((T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))⁻¹ +
        1) +
    4 * Real.pi *
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          (h : ℝ))⁻¹

/-- The curvature-scale shifted-correlation majorant is nonnegative for
positive curvature scale and positive shift. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg
    {T : ℝ}
    {b h : ℕ}
    (hT : 1 ≤ T)
    (hh : 1 ≤ h) :
    0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h := by
  let lam : ℝ :=
    T *
      ((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ)))⁻¹) *
      (h : ℝ)
  have hlam_pos :
      0 < lam :=
    Real.secondDerivativeVdc_shiftedLowerParameter_pos hT hh
  have hlam_inv_nonneg :
      0 ≤ lam⁻¹ :=
    inv_nonneg.mpr (le_of_lt hlam_pos)
  have hinner_nonneg :
      0 ≤ lam⁻¹ + 1 :=
    add_nonneg hlam_inv_nonneg zero_le_one
  have hfirst_nonneg :
      0 ≤ 4 * (lam⁻¹ + 1) :=
    mul_nonneg zero_le_four hinner_nonneg
  have hsecond_scale_nonneg :
      0 ≤ 4 * Real.pi :=
    mul_nonneg zero_le_four Real.pi_nonneg
  have hsecond_nonneg :
      0 ≤ 4 * Real.pi * lam⁻¹ :=
    mul_nonneg hsecond_scale_nonneg hlam_inv_nonneg
  exact
    Eq.subst
      (motive := fun r : ℝ => 0 ≤ r)
      (show
        4 * (lam⁻¹ + 1) + 4 * Real.pi * lam⁻¹ =
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h from rfl)
      (add_nonneg hfirst_nonneg hsecond_nonneg)

/-- The sum of curvature-scale shifted-correlation majorants over the Weyl
shift range is nonnegative. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_sum_nonneg
    {T : ℝ}
    {b H : ℕ}
    (hT : 1 ≤ T) :
    0 ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h := by
  exact Finset.sum_nonneg
    (fun h hh =>
      Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg hT
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh))

/-- Pointwise curvature-scale shifted-correlation estimates sum to an
envelope bound over the Weyl shift range. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_curvatureMajorants
    (φ : ℝ → ℝ)
    {a b H : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h)
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              T *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h)
            (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h
  exact Finset.sum_le_sum
    (fun h hh =>
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_curvatureScale_data
        φ hT ha
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
        (habh h hh)
        (hderiv_antitone h hh)
        (hderiv_lower h hh)
        (hinc_mono h hh)
        (hred_mono h hh)
        (hsep h hh))

/-- Canonical Weyl shift length at the square-root transition scale. -/
def Real.secondDerivativeVdc_weylShiftLength
    (T : ℝ) : ℕ :=
  ⌊Real.sqrt (1 + T)⌋₊

/-- The canonical Weyl shift length is positive for `1 ≤ T`. -/
theorem Real.secondDerivativeVdc_weylShiftLength_pos
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 < Real.secondDerivativeVdc_weylShiftLength T := by
  show 0 < ⌊Real.sqrt (1 + T)⌋₊
  have hone_le_arg : 1 ≤ 1 + T :=
    le_add_of_nonneg_right (le_trans zero_le_one hT)
  have hone_le_sqrt : (1 : ℝ) ≤ Real.sqrt (1 + T) :=
    (Real.one_le_sqrt).mpr hone_le_arg
  exact Nat.floor_pos.mpr hone_le_sqrt

/-- The canonical Weyl shift length is at least one for `1 ≤ T`. -/
theorem Real.one_le_secondDerivativeVdc_weylShiftLength
    {T : ℝ}
    (hT : 1 ≤ T) :
    1 ≤ Real.secondDerivativeVdc_weylShiftLength T :=
  Real.secondDerivativeVdc_weylShiftLength_pos hT

/-- The canonical Weyl shift length lies below the square-root transition
scale. -/
theorem Real.secondDerivativeVdc_weylShiftLength_le_sqrt
    {T : ℝ}
    (hT : 1 ≤ T) :
    ((Real.secondDerivativeVdc_weylShiftLength T : ℕ) : ℝ) ≤
      Real.sqrt (1 + T) := by
  show ((⌊Real.sqrt (1 + T)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (1 + T)
  exact Nat.floor_le (Real.sqrt_nonneg (1 + T))

/-- The square-root transition scale is below one plus the canonical Weyl
shift length. -/
theorem Real.sqrt_lt_secondDerivativeVdc_weylShiftLength_add_one
    (T : ℝ) :
    Real.sqrt (1 + T) <
      ((Real.secondDerivativeVdc_weylShiftLength T : ℕ) : ℝ) + 1 := by
  show Real.sqrt (1 + T) < ((⌊Real.sqrt (1 + T)⌋₊ : ℕ) : ℝ) + 1
  exact Nat.lt_floor_add_one (Real.sqrt (1 + T))

/-- The reciprocal of the positive canonical Weyl shift length is
nonnegative. -/
theorem Real.secondDerivativeVdc_weylShiftLength_inv_nonneg
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 ≤ (((Real.secondDerivativeVdc_weylShiftLength T : ℕ) : ℝ)⁻¹) := by
  have hpos_nat : 0 < Real.secondDerivativeVdc_weylShiftLength T :=
    Real.secondDerivativeVdc_weylShiftLength_pos hT
  have hpos_real :
      0 < ((Real.secondDerivativeVdc_weylShiftLength T : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hpos_nat
  exact inv_nonneg.mpr (le_of_lt hpos_real)

/-- In the long branch, the canonical Weyl shift length fits in the integer
block gap. -/
theorem Nat.secondDerivativeVdc_weylShiftLength_le_block_gap
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlong :
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    Real.secondDerivativeVdc_weylShiftLength T ≤ b - a := by
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength T
  have hH_le_sqrt :
      (H : ℝ) ≤ Real.sqrt (1 + T) :=
    Real.secondDerivativeVdc_weylShiftLength_le_sqrt hT
  have hsqrt_le_target :
      Real.sqrt (1 + T) ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) :=
    le_add_of_nonneg_left
      (Real.secondDerivativeVdc_endpointScale_nonneg (b := b) hT)
  have hH_lt_length :
      (H : ℝ) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
    lt_of_le_of_lt
      (le_trans hH_le_sqrt hsqrt_le_target)
      hlong
  have hH_add_lt :
      (H : ℝ) + (a : ℝ) < ((b + 1 : ℕ) : ℝ) :=
    lt_sub_iff_add_lt.mp hH_lt_length
  have hcast_add :
      ((H + a : ℕ) : ℝ) = (H : ℝ) + (a : ℝ) :=
    Nat.cast_add H a
  have hnat_lt_succ :
      H + a < b + 1 :=
    Nat.cast_lt.mp
      (Eq.subst
        (motive := fun r : ℝ => r < ((b + 1 : ℕ) : ℝ))
        hcast_add.symm
        hH_add_lt)
  have hH_add_le_b : H + a ≤ b :=
    Nat.lt_succ_iff.mp hnat_lt_succ
  exact Nat.le_sub_of_add_le hH_add_le_b

/-- In the square-root long branch, the canonical Weyl shift length fits in
the integer block gap. -/
theorem Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hlong_sqrt :
      Real.sqrt (1 + T) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    Real.secondDerivativeVdc_weylShiftLength T ≤ b - a := by
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength T
  have hH_le_sqrt :
      (H : ℝ) ≤ Real.sqrt (1 + T) :=
    Real.secondDerivativeVdc_weylShiftLength_le_sqrt hT
  have hH_lt_length :
      (H : ℝ) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)) :=
    lt_of_le_of_lt hH_le_sqrt hlong_sqrt
  have hH_add_lt :
      (H : ℝ) + (a : ℝ) < ((b + 1 : ℕ) : ℝ) :=
    lt_sub_iff_add_lt.mp hH_lt_length
  have hcast_add :
      ((H + a : ℕ) : ℝ) = (H : ℝ) + (a : ℝ) :=
    Nat.cast_add H a
  have hnat_lt_succ :
      H + a < b + 1 :=
    Nat.cast_lt.mp
      (Eq.subst
        (motive := fun r : ℝ => r < ((b + 1 : ℕ) : ℝ))
        hcast_add.symm
        hH_add_lt)
  have hH_add_le_b : H + a ≤ b :=
    Nat.lt_succ_iff.mp hnat_lt_succ
  exact Nat.le_sub_of_add_le hH_add_le_b

/-- In the square-root long branch, the canonical Weyl shift length is bounded
by the cardinality of the original integer block. -/
theorem Nat.secondDerivativeVdc_weylShiftLength_le_block_card_of_sqrt_long
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + T) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ))) :
    Real.secondDerivativeVdc_weylShiftLength T ≤ (Finset.Icc a b).card := by
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength T ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      hT hlong_sqrt
  have hgap_le_card : b - a ≤ (Finset.Icc a b).card := by
    have hcard : (Finset.Icc a b).card = b + 1 - a :=
      Nat.card_Icc a b
    have hgap_le_succ_gap : b - a ≤ b + 1 - a :=
      Nat.sub_le_sub_right (Nat.le_succ b) a
    exact
      Eq.subst
        (motive := fun n : ℕ => b - a ≤ n)
        hcard.symm
        hgap_le_succ_gap
  exact le_trans hgap hgap_le_card

/-- Curvature-majorant envelope bound at the canonical Weyl shift length in
the long branch. -/
theorem Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_curvatureMajorants_weylShiftLength
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (hlong :
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              T *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h)
            (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))) :
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b
        (Real.secondDerivativeVdc_weylShiftLength T) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength T),
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h := by
  have hgap :
      Real.secondDerivativeVdc_weylShiftLength T ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap hT hlong
  have habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          a ≤ b - h :=
    fun h hh =>
      Nat.realPhase_secondDerivative_vdc_lower_le_sub_shift hgap hh
  exact
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_curvatureMajorants
      φ hT ha habh hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep

/-- Substitution of the curvature-majorant envelope bound into the Weyl
envelope majorant at the canonical shift length. -/
theorem Real.secondDerivativeVdc_weylEnvelopeMajorant_le_of_curvatureMajorants_weylShiftLength
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (hlong :
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              T *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖)
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) a (b - h)
            (T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))) :
    Real.secondDerivativeVdc_weylEnvelopeMajorant a b
        (Real.secondDerivativeVdc_weylShiftLength T)
        (Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b
          (Real.secondDerivativeVdc_weylShiftLength T)) ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b
        (Real.secondDerivativeVdc_weylShiftLength T)
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength T),
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) := by
  have henvelope :
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope φ a b
          (Real.secondDerivativeVdc_weylShiftLength T) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength T),
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h :=
    Complex.realPhase_secondDerivative_vdc_shiftedCorrelationEnvelope_le_curvatureMajorants_weylShiftLength
      φ hT ha hlong hderiv_antitone hderiv_lower
      hinc_mono hred_mono hsep
  exact
    Real.secondDerivativeVdc_weylEnvelopeMajorant_mono
      (Real.one_le_secondDerivativeVdc_weylShiftLength hT)
      henvelope

/-- The endpoint scale is bounded by the endpoint-plus-square-root target. -/
theorem Real.secondDerivativeVdc_endpointScale_le_target
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    (((b + 1 : ℕ) : ℝ) / T) ≤
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  exact le_add_of_nonneg_right
    (Real.secondDerivativeVdc_sqrtScale_nonneg hT)

/-- The square-root scale is bounded by the endpoint-plus-square-root target. -/
theorem Real.secondDerivativeVdc_sqrtScale_le_target
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    Real.sqrt (1 + T) ≤
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  exact le_add_of_nonneg_left
    (Real.secondDerivativeVdc_endpointScale_nonneg (b := b) hT)

/-- The canonical Weyl shift length is bounded by the final
endpoint-plus-square-root target. -/
theorem Real.secondDerivativeVdc_weylShiftLength_le_target
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    ((Real.secondDerivativeVdc_weylShiftLength T : ℕ) : ℝ) ≤
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  exact le_trans
    (Real.secondDerivativeVdc_weylShiftLength_le_sqrt hT)
    (Real.secondDerivativeVdc_sqrtScale_le_target (b := b) hT)

/-- The long-branch target is strictly positive. -/
theorem Real.secondDerivativeVdc_target_pos
    {b : ℕ}
    {T : ℝ}
    (hT : 1 ≤ T) :
    0 < (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) := by
  have hsqrt_one :
      1 ≤ Real.sqrt (1 + T) := by
    have hone_le_arg : 1 ≤ 1 + T :=
      le_add_of_nonneg_right (le_trans zero_le_one hT)
    exact (Real.one_le_sqrt).mpr hone_le_arg
  have hone_le_target :
      1 ≤ (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) :=
    le_trans hsqrt_one
      (Real.secondDerivativeVdc_sqrtScale_le_target (b := b) hT)
  exact lt_of_lt_of_le zero_lt_one hone_le_target

/-- Nonempty endpoint data for one derivative-frequency packet.

This is the true local output of the derivative-window partition: the packet
has concrete endpoints, those endpoints are in the ambient real interval, the
curvature lower bound separates their derivatives, and the finite packet
cardinality is bounded by the endpoint span plus one. -/
theorem Complex.realPhase_secondDerivative_vdc_nonempty_derivPacket_endpoint_data
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty)
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hcont :
      ContinuousOn (fun z : ℝ => deriv φ z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hdiff :
      DifferentiableOn ℝ (fun z : ℝ => deriv φ z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))))
    (horientation :
      (MonotoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            0 ≤ deriv (deriv φ) z) ∨
      (AntitoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            deriv (deriv φ) z ≤ 0))
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) ≤
            ‖deriv (deriv φ) z‖) :
    ∃ p q : ℕ,
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ∧
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ∧
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      p ≤ q ∧
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        ‖deriv φ (q : ℝ) - deriv φ (p : ℝ)‖ ∧
      deriv φ q - deriv φ p < 1 ∧
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ))) := by
  let p : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).min' hp
  let q : ℕ :=
    (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).max' hp
  have hp_mem :
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_mem φ hp
  have hq_mem :
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_max_mem φ hp
  have hp_block_nat : p ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hp_mem
  have hq_block_nat : q ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hq_mem
  have hp_bounds_nat : a ≤ p ∧ p ≤ b :=
    Finset.mem_Icc.mp hp_block_nat
  have hq_bounds_nat : a ≤ q ∧ q ≤ b :=
    Finset.mem_Icc.mp hq_block_nat
  have hp_interval :
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
    exact And.intro
      (Nat.cast_le.mpr hp_bounds_nat.1)
      (Nat.cast_le.mpr
        (Nat.le_trans hp_bounds_nat.2 (Nat.le_succ b)))
  have hq_interval :
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
    exact And.intro
      (Nat.cast_le.mpr hq_bounds_nat.1)
      (Nat.cast_le.mpr
        (Nat.le_trans hq_bounds_nat.2 (Nat.le_succ b)))
  have hp_le_q : p ≤ q :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_min_le_of_mem
      φ hp hq_mem
  have hpq_real : (p : ℝ) ≤ (q : ℝ) :=
    Nat.cast_le.mpr hp_le_q
  have hseparation :
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ))) ≤
        ‖deriv φ (q : ℝ) - deriv φ (p : ℝ)‖ :=
    Complex.realPhase_secondDerivative_vdc_deriv_norm_separation
      φ hcont hdiff horientation hcurvature_lower
      hp_interval hq_interval hpq_real
  have hwindow :
      deriv φ q - deriv φ p < 1 :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_lt_one
      φ hp_mem hq_mem
  have hendpoint_card :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ)) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_card_le_endpoint_span
      φ hp
  exact Exists.intro p
    (Exists.intro q
        (And.intro hp_mem
        (And.intro hq_mem
          (And.intro hp_interval
            (And.intro hq_interval
              (And.intro hp_le_q
                (And.intro hseparation
                  (And.intro hwindow hendpoint_card))))))))

/-- Nonempty endpoint data for one derivative-frequency packet, with the
packet derivative spread recorded in absolute-value form. -/
theorem Complex.realPhase_secondDerivative_vdc_nonempty_derivPacket_endpoint_abs_data
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {T : ℝ}
    {m : ℤ}
    (hp :
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).Nonempty)
    (hT : 1 ≤ T)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hcont :
      ContinuousOn (fun z : ℝ => deriv φ z)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hdiff :
      DifferentiableOn ℝ (fun z : ℝ => deriv φ z)
        (interior (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ))))
    (horientation :
      (MonotoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            0 ≤ deriv (deriv φ) z) ∨
      (AntitoneOn (fun z : ℝ => deriv φ z)
          (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) ∧
        ∀ z : ℝ,
          z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
            deriv (deriv φ) z ≤ 0))
    (hcurvature_lower :
      ∀ z : ℝ,
        z ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          T *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) ≤
            ‖deriv (deriv φ) z‖) :
    ∃ p q : ℕ,
      p ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ∧
      q ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m ∧
      (p : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      (q : ℝ) ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) ∧
      p ≤ q ∧
      (T *
          ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ)))⁻¹) *
          ((q : ℝ) - (p : ℝ)) ≤
        ‖deriv φ (q : ℝ) - deriv φ (p : ℝ)‖ ∧
      ‖deriv φ (q : ℝ) - deriv φ (p : ℝ)‖ < 1 ∧
      ((Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card : ℝ) ≤
        (((q + 1 : ℕ) : ℝ) - (p : ℝ))) := by
  match
    Complex.realPhase_secondDerivative_vdc_nonempty_derivPacket_endpoint_data
      φ hp hT ha hab hcont hdiff horientation hcurvature_lower with
  | Exists.intro p hrest =>
    match hrest with
    | Exists.intro q hdata =>
      exact Exists.intro p
        (Exists.intro q
          (And.intro hdata.1
            (And.intro hdata.2.1
              (And.intro hdata.2.2.1
                (And.intro hdata.2.2.2.1
                  (And.intro hdata.2.2.2.2.1
                    (And.intro hdata.2.2.2.2.2.1
                      (And.intro
                        (Complex.realPhase_secondDerivative_vdc_derivPacket_deriv_sub_norm_lt_one
                          φ hdata.1 hdata.2.1)
                        hdata.2.2.2.2.2.2.2))))))))

end

end LFunctions
end Boundary

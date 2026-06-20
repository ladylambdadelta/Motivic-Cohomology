import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.PartialSums.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase

/-!
# Boundary logarithmic phase first-derivative estimates

This file owns the first-derivative/Euler-Maclaurin estimate surface consumed by
Boundary Euler-Abel transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The finite-difference/separation hypothesis needed by the proved
Kusmin-Landau first-derivative theorem for the logarithmic phase. -/
def logarithmicPhaseFiniteDifferenceHypothesis : Prop :=
  ∀ t : ℝ,
    1 ≤ ‖t‖ →
      ∀ {a b : ℕ},
        1 ≤ a →
          a ≤ b →
            Complex.realPhase_integerIncrementMonotoneOn
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
            Complex.realPhase_reducedIntegerIncrementMonotoneOn
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
            Complex.realPhase_integerIncrementSeparatedOn
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
              (‖t‖ / ((b + 1 : ℕ) : ℝ))

/-- Honest owner theorem available from the classical logarithmic-phase lane:
under the finite-difference/separation hypothesis, the positive-index
logarithmic-phase sums satisfy the proved first-derivative bound with an
existential constant.

This theorem is the real target for downstream rewiring. It deliberately does
not assert the stronger unconditional `8`-constant statement used by the old
circular wrapper chain. -/
theorem logarithmicPhase_positiveIndex_firstDerivative_bound_of_finiteDifference
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N‖ ≤
              A *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                  Real.log (2 + N) := by
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound
      hfiniteDifference

/-- The logarithmic-phase exponent is nonzero when `1 ≤ ‖t‖`. -/
theorem logarithmicPhase_complexExponent_ne_zero_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (-(t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hI_ne_zero : Complex.I ≠ 0 :=
    Complex.I_ne_zero
  have hneg_t_zero : -(t : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hI_ne_zero
  have ht_complex_zero : (t : ℂ) = 0 :=
    neg_eq_zero.mp hneg_t_zero
  have ht_real_zero : t = 0 :=
    Complex.ofReal_eq_zero.mp ht_complex_zero
  have hnorm_zero : ‖t‖ = 0 :=
    congrArg (fun x : ℝ => ‖x‖) ht_real_zero
  have hone_le_zero : (1 : ℝ) ≤ 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hnorm_zero
      ht
  exact not_lt_of_ge hone_le_zero zero_lt_one

/-- The zeroth logarithmic-phase sample vanishes for nonzero frequency. -/
theorem logarithmicPhase_zero_sample_eq_zero_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (0 : ℂ) ^ (-(t : ℂ) * Complex.I) = 0 := by
  exact
    Complex.zero_cpow
      (logarithmicPhase_complexExponent_ne_zero_of_one_le_norm t ht)

/-- The local `0..M` logarithmic-phase sum agrees with the positive-index
classical sum when the frequency is nonzero. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (M : ℕ) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M := by
  let term : ℕ → ℂ := fun k => (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  have hzero : term 0 = 0 :=
    logarithmicPhase_zero_sample_eq_zero_of_one_le_norm t ht
  have hlocal :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        ∑ k ∈ Finset.Icc 0 M, term k :=
    rfl
  have hclassical :
      Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        ∑ k ∈ Finset.Icc 1 M, term k :=
    rfl
  have hIcc_zero :
      (∑ k ∈ Finset.Icc 0 M, term k) =
        ∑ k ∈ Finset.Ico 0 (M + 1), term k :=
    congrArg
      (fun s : Finset ℕ => ∑ k ∈ s, term k)
      (Nat.Ico_succ_right 0 M).symm
  have hIcc_one :
      (∑ k ∈ Finset.Icc 1 M, term k) =
        ∑ k ∈ Finset.Ico 1 (M + 1), term k :=
    congrArg
      (fun s : Finset ℕ => ∑ k ∈ s, term k)
      (Nat.Ico_succ_right 1 M).symm
  have hpeel :
      (∑ k ∈ Finset.Ico 0 (M + 1), term k) =
        term 0 + ∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k :=
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos M) term
  have hpeel_one :
      (∑ k ∈ Finset.Ico 0 (M + 1), term k) =
        ∑ k ∈ Finset.Ico 1 (M + 1), term k := by
    calc
      (∑ k ∈ Finset.Ico 0 (M + 1), term k) =
          term 0 + ∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k := hpeel
      _ = 0 + ∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k := by
        exact congrArg
          (fun x : ℂ => x + ∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k)
          hzero
      _ = ∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k := by
        exact zero_add (∑ k ∈ Finset.Ico (0 + 1) (M + 1), term k)
      _ = ∑ k ∈ Finset.Ico 1 (M + 1), term k := by
        rfl
  calc
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        ∑ k ∈ Finset.Icc 0 M, term k := hlocal
    _ = ∑ k ∈ Finset.Ico 0 (M + 1), term k := hIcc_zero
    _ = ∑ k ∈ Finset.Ico 1 (M + 1), term k := hpeel_one
    _ = ∑ k ∈ Finset.Icc 1 M, term k := hIcc_one.symm
    _ = Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M :=
      hclassical.symm

/-- Honest local logarithmic-phase first-derivative estimate obtained from the
proved positive-index theorem under the finite-difference/separation
hypothesis. -/
theorem logarithmicPhase_localPartialSum_firstDerivative_bound_of_finiteDifference
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N‖ ≤
              A *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                  Real.log (2 + N) := by
  match logarithmicPhase_positiveIndex_firstDerivative_bound_of_finiteDifference
      hfiniteDifference with
  | ⟨A, hA, hbound⟩ =>
      exact
        ⟨A, hA,
          fun t ht N =>
            have hsum_eq :
                boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N =
                  Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N :=
              boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex
                t ht N
            Eq.subst
              (motive := fun z : ℂ =>
                ‖z‖ ≤
                  A *
                    (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                      Real.log (2 + N))
              hsum_eq.symm
              (hbound t ht N)⟩

/-- Concrete `40`-constant local logarithmic-phase first-derivative estimate.

The classical owner theorem is proved for positive-index sums.  The local
boundary sum includes the zeroth sample, which vanishes for `1 ≤ ‖t‖`, so the
same bound transfers across `boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex`.
-/
theorem logarithmicPhase_localPartialSum_firstDerivative_bound_40_of_finiteDifference
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N‖ ≤
      40 *
        (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + N) := by
  have hpositive :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N‖ ≤
        40 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) :=
    Complex.logarithmicPhase_dyadic_firstDerivative_sum_bound
      t ht hfiniteDifference N
  have hsum_eq :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N =
        Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex
      t ht N
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          40 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + N))
      hsum_eq.symm
      hpositive

/-- Standard first-derivative test for the concrete logarithmic phase, after
the finite-difference/separation arithmetic and phase derivative controls have
been isolated. -/
theorem finiteFirstDerivativeTest_exp_sum_norm_le
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    logarithmicPhase_localPartialSum_firstDerivative_bound_40_of_finiteDifference
      hfiniteDifference t ht ⌊x⌋₊

/-- Monotone-phase first-derivative test for the concrete logarithmic phase. -/
theorem monotonePhase_firstDerivativeTest_partialSum_bound
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    finiteFirstDerivativeTest_exp_sum_norm_le
      hfiniteDifference t ht hphase_deriv hphase_deriv_norm
      hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase, after
the phase derivative and its monotonicity have been isolated. -/
theorem firstDerivativeTest_logarithmicPhase_partialSum_bound_of_monotone_phase
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    monotonePhase_firstDerivativeTest_partialSum_bound
      hfiniteDifference t ht hphase_deriv hphase_deriv_norm
      hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase, after
the phase derivative and its monotonicity have been isolated. -/
theorem standardFirstDerivativeTest_logarithmicPhase_partialSum_bound_of_antitone
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    firstDerivativeTest_logarithmicPhase_partialSum_bound_of_monotone_phase
      hfiniteDifference t ht hphase_deriv hphase_deriv_norm
      hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase. -/
theorem standardFirstDerivativeTest_logarithmicPhase_partialSum_bound
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    standardFirstDerivativeTest_logarithmicPhase_partialSum_bound_of_antitone
      hfiniteDifference t ht hphase_deriv hphase_deriv_norm
      (logarithmicPhase_derivativeMagnitude_antitoneOn_positive t) hx

/-- Concrete first-derivative/Euler-Maclaurin estimate for the logarithmic
phase. -/
theorem firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    standardFirstDerivativeTest_logarithmicPhase_partialSum_bound
      hfiniteDifference t ht hphase_deriv hphase_deriv_norm hx

/-- Deep analytic owner estimate for logarithmic-phase partial sums. -/
theorem logarithmicPhasePartialSum_firstDerivative_bound
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
      hfiniteDifference t ht
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hu)
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hu)
      hx

/-- Standard first-derivative/Euler-Maclaurin estimate for the logarithmic
phase partial sums. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact logarithmicPhasePartialSum_firstDerivative_bound hfiniteDifference t ht hx

/-- First-derivative/Euler-Maclaurin owner estimate for the logarithmic phase
`u ↦ exp (-i t log u)`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
      hfiniteDifference t ht hx

/-- Euler-Maclaurin / van-der-Corput bound for the logarithmic-phase oscillator.

This is the canonical replacement for the false constant-ratio geometric route:
the proof studies the phase `x ↦ -t log x` and obtains a partial-sum bound
with the necessary long-range `x / |t|` term.  The latter term is unavoidable:
the primitive of `u^{-it}` has size comparable to `x / |t|` for large `x`;
cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_vdc
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
      hfiniteDifference t ht hx

/-- First conjunct of the finite Abel package: the endpoint partial sum at `M`
is exactly the first-derivative estimate at the real endpoint `M`. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      40 *
        ((((⌊((M : ℕ) : ℝ)⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊((M : ℕ) : ℝ)⌋₊)) := by
  have hreal :
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    logarithmicPhasePartialSum_firstDerivative_bound
      hfiniteDifference t ht hreal

/-- Sharper endpoint estimate in the logarithmic-phase partial-summation
package.

This is not obtained by multiplying the coarse primitive bound by the reciprocal
endpoint weights.  It is the endpoint part of the oscillatory
Euler-Maclaurin/partial-summation argument, where cancellation at the cutoff and
right endpoint is retained. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  have hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt (boundaryLineOnePointRealParam_cutoff_pos t)
  have hM_one : 1 ≤ M :=
    le_trans hcutoff_one hNM
  have hright :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ 2 :=
    logarithmicPhase_endpoint_trivial_bound t hM_one
  have hleft :
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤ 2 :=
    logarithmicPhase_endpoint_trivial_bound t hcutoff_one
  have hsum_le_four :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        4 := by
    have htwo_add_two : (2 : ℝ) + 2 = 4 := by
      rfl
    exact (add_le_add hright hleft).trans_eq htwo_add_two
  have hlog_two : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_add_le_three_add : 2 + ‖t‖ ≤ 3 + ‖t‖ := by
    exact add_le_add_right (show (2 : ℝ) ≤ 3 by
      calc
        (2 : ℝ) ≤ 2 + 1 := le_add_of_nonneg_right zero_le_one
        _ = 3 := rfl) ‖t‖
  have hlog_mono :
      Real.log (2 + ‖t‖) ≤ Real.log (3 + ‖t‖) := by
    have hpos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_one (one_le_two_add_norm t)
    exact Real.log_le_log hpos htwo_add_le_three_add
  have hlog_one : (1 : ℝ) ≤ Real.log (3 + ‖t‖) :=
    le_trans hlog_two hlog_mono
  have height_nonneg : 0 ≤ Real.log (3 + ‖t‖) :=
    le_trans zero_le_one hlog_one
  have hfour_le :
      (4 : ℝ) ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    have htwo_le_eight_log : (2 : ℝ) ≤ 8 * Real.log (3 + ‖t‖) := by
      have htwo_le_eight : (2 : ℝ) ≤ 8 := by
        calc
          (2 : ℝ) ≤ 2 + 6 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 6 by
            calc
              (0 : ℝ) ≤ 1 := zero_le_one
              _ ≤ 6 := by
                calc
                  (1 : ℝ) ≤ 1 + 5 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 5 by
                    calc
                      (0 : ℝ) ≤ 1 := zero_le_one
                      _ ≤ 5 := by
                        calc
                          (1 : ℝ) ≤ 1 + 4 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 4 by
                            calc
                              (0 : ℝ) ≤ 1 := zero_le_one
                              _ ≤ 4 := by
                                calc
                                  (1 : ℝ) ≤ 1 + 3 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 3 by
                                    calc
                                      (0 : ℝ) ≤ 1 := zero_le_one
                                      _ ≤ 3 := by
                                        calc
                                          (1 : ℝ) ≤ 1 + 2 := le_add_of_nonneg_right (le_of_lt two_pos)
                                          _ = 3 := rfl)
                                  _ = 4 := rfl)
                          _ = 5 := rfl)
                  _ = 6 := rfl)
          _ = 8 := rfl
      calc
        (2 : ℝ) ≤ 8 * 1 := by
          exact Eq.subst (motive := fun x : ℝ => 2 ≤ x) (mul_one (8 : ℝ)).symm htwo_le_eight
        _ ≤ 8 * Real.log (3 + ‖t‖) :=
          mul_le_mul_of_nonneg_left hlog_one
            (show (0 : ℝ) ≤ 8 by
              calc
                (0 : ℝ) ≤ 1 := zero_le_one
                _ ≤ 8 := le_trans zero_le_one htwo_le_eight)
    calc
      (4 : ℝ) = 2 + 2 := rfl
      _ ≤ 2 + 8 * Real.log (3 + ‖t‖) :=
        add_le_add_left htwo_le_eight_log 2
  exact le_trans hsum_le_four hfour_le

/-- Endpoint arithmetic after the logarithmic-phase first-derivative
Euler-Maclaurin estimate.

The two terms are the reciprocal endpoint contributions at the right endpoint
`M` and at the canonical cutoff `⌊2 + |t|⌋₊`.  The analytic input is only the
first-derivative primitive estimate; this theorem owns the subsequent
reciprocal-weight and cutoff arithmetic.  Cf. Apostol, *Introduction to
Analytic Number Theory*, partial summation, and Titchmarsh, Ch. 3. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound t ht hNM

end
end LFunctions
end Boundary

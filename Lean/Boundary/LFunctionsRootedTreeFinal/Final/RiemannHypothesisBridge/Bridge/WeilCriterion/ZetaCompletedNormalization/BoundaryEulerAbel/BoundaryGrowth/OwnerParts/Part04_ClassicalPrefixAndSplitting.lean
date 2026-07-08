import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.BoundaryGrowth.OwnerParts.Part03_AbelWeightsAndClassicalTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCanonicalPrefix

/-!
# Boundary growth owner part 4

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem boundaryGrowth_real_three_add_one_eq_four :
    ((3 : ℝ) + (1 : ℝ)) = 4 := by
  calc
    (3 : ℝ) + (1 : ℝ) =
        ((3 : ℕ) : ℝ) + (1 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (1 : ℝ))
        boundaryGrowth_natCast_three_eq_real_three.symm
    _ = ((3 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((3 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_one_eq_real_one.symm
    _ = (((3 : ℕ) + 1 : ℕ) : ℝ) := by
      exact (Nat.cast_add 3 1).symm
    _ = ((4 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((3 : ℕ) + 1) = 4 from rfl)
    _ = (4 : ℝ) := by
      exact boundaryGrowth_natCast_four_eq_real_four

theorem boundaryGrowth_real_four_add_one_eq_five :
    ((4 : ℝ) + (1 : ℝ)) = 5 := by
  calc
    (4 : ℝ) + (1 : ℝ) =
        ((4 : ℕ) : ℝ) + (1 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (1 : ℝ))
        boundaryGrowth_natCast_four_eq_real_four.symm
    _ = ((4 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((4 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_one_eq_real_one.symm
    _ = (((4 : ℕ) + 1 : ℕ) : ℝ) := by
      exact (Nat.cast_add 4 1).symm
    _ = ((5 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((4 : ℕ) + 1) = 5 from rfl)
    _ = (5 : ℝ) := by
      exact boundaryGrowth_natCast_five_eq_real_five

theorem boundaryGrowth_real_two_add_four_eq_six :
    ((2 : ℝ) + (4 : ℝ)) = 6 := by
  calc
    (2 : ℝ) + (4 : ℝ) =
        ((2 : ℕ) : ℝ) + (4 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (4 : ℝ))
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = ((2 : ℕ) : ℝ) + ((4 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((2 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_four_eq_real_four.symm
    _ = (((2 : ℕ) + 4 : ℕ) : ℝ) := by
      exact (Nat.cast_add 2 4).symm
    _ = ((6 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((2 : ℕ) + 4) = 6 from rfl)
    _ = (6 : ℝ) := by
      exact Nat.cast_ofNat

theorem boundaryGrowth_real_eighty_mul_five_eq_fourhundred :
    ((80 : ℝ) * (5 : ℝ)) = 400 := by
  calc
    (80 : ℝ) * (5 : ℝ) =
        ((80 : ℕ) : ℝ) * (5 : ℝ) := by
      exact congrArg (fun y : ℝ => y * (5 : ℝ))
        boundaryGrowth_natCast_eighty_eq_real_eighty.symm
    _ = ((80 : ℕ) : ℝ) * ((5 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((80 : ℕ) : ℝ) * y)
        boundaryGrowth_natCast_five_eq_real_five.symm
    _ = (((80 : ℕ) * 5 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 80 5).symm
    _ = ((400 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((80 : ℕ) * 5) = 400 from rfl)
    _ = (400 : ℝ) := by
      exact Nat.cast_ofNat

/-- Triangle assembly for the four post-cutoff Euler-Maclaurin components. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_components_norm_le_of_component_bounds
    {I L U R : ℂ}
    {A : ℝ}
    (hI : ‖I‖ ≤ (2 : ℝ))
    (hL : ‖L‖ ≤ (1 : ℝ))
    (hU : ‖U‖ ≤ (1 : ℝ))
    (hR : ‖R‖ ≤ 1 + A) :
    ‖I + L + U + R‖ ≤ 5 + A := by
  have htri₁ :
      ‖I + L‖ ≤ ‖I‖ + ‖L‖ :=
    norm_add_le I L
  have htri₂ :
      ‖I + L + U‖ ≤ ‖I + L‖ + ‖U‖ :=
    norm_add_le (I + L) U
  have htri₃ :
      ‖I + L + U + R‖ ≤ ‖I + L + U‖ + ‖R‖ :=
    norm_add_le (I + L + U) R
  have hpair :
      ‖I + L‖ ≤ (2 : ℝ) + 1 :=
    le_trans htri₁ (add_le_add hI hL)
  have htriple :
      ‖I + L + U‖ ≤ ((2 : ℝ) + 1) + 1 :=
    le_trans htri₂ (add_le_add hpair hU)
  have hquad :
      ‖I + L + U + R‖ ≤ (((2 : ℝ) + 1) + 1) + (1 + A) :=
    le_trans htri₃ (add_le_add htriple hR)
  have harith :
      (((2 : ℝ) + 1) + 1) + (1 + A) = 5 + A := by
    calc
      (((2 : ℝ) + 1) + 1) + (1 + A) =
          (((2 : ℝ) + 1) + 1 + 1) + A := by
        exact (add_assoc (((2 : ℝ) + 1) + 1) 1 A).symm
      _ = (((2 : ℝ) + 1) + (1 + 1)) + A := by
        exact congrArg (fun x : ℝ => x + A)
          (add_assoc ((2 : ℝ) + 1) 1 1)
      _ = (((2 : ℝ) + 1) + (2 : ℝ)) + A := by
        exact congrArg (fun x : ℝ => (((2 : ℝ) + 1) + x) + A)
          (one_add_one_eq_two : (1 : ℝ) + 1 = 2)
      _ = ((3 : ℝ) + 2) + A := by
        exact congrArg (fun x : ℝ => x + A)
          (congrArg (fun x : ℝ => x + (2 : ℝ))
            boundaryGrowth_real_two_add_one_eq_three)
      _ = (5 : ℝ) + A := by
        exact congrArg (fun x : ℝ => x + A)
          boundaryGrowth_real_three_add_two_eq_five
      _ = 5 + A := rfl
  exact Eq.subst
    (motive := fun r : ℝ => ‖I + L + U + R‖ ≤ r)
    harith
    hquad

/-- Classical Euler-Maclaurin component estimate for the ordinary post-cutoff
finite tail.

After the exact finite Euler-Maclaurin identity for
`∑_{N < n ≤ M} n^(-(1+it))`, the remaining analytic work is to bound the
oscillatory integral, the two half-endpoint corrections, and the Bernoulli
remainder uniformly from the cutoff `N = ⌊2 + |t|⌋₊` onward.  This is the
smallest honest post-cutoff tail input: it no longer mentions finite sums or
Abel partial summation, only the already-expanded Euler-Maclaurin terms. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_eulerMaclaurin_components_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-boundaryLineOnePointRealParam t))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))))))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-boundaryLineOnePointRealParam t))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-boundaryLineOnePointRealParam t))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))))
  have hI : ‖I‖ ≤ (2 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two
      t ht hM
  have hL : ‖L‖ ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_lowerHalfEndpoint_norm_le_one
      t
  have hU : ‖U‖ ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_upperHalfEndpoint_norm_le_one
      t hM
  have hR : ‖R‖ ≤ 1 + 16 * Real.log (3 + ‖t‖) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le
      t ht hM
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_components_norm_le_of_component_bounds
      (A := 16 * Real.log (3 + ‖t‖))
      hI hL hU hR

/-- Classical bounded post-cutoff oscillatory tail estimate for
`∑ n^{-1-it}` after `N = ⌊2 + |t|⌋₊`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_of_classical_postCutoff_tail
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  intro M hM
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hC_floor : ⌊(((C : ℕ) : ℝ))⌋₊ = C :=
    Nat.floor_natCast C
  have hM_floor : ⌊((M : ℕ) : ℝ)⌋₊ = M :=
    Nat.floor_natCast M
  have htail_to_eulerMaclaurin :
      (∑ k ∈ Finset.Ioc ⌊(((C : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
          (-(1 / 2 : ℂ) *
            ((((C : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-boundaryLineOnePointRealParam t *
                (((x : ℝ) : ℂ) ^
                  (-(boundaryLineOnePointRealParam t + 1))))) := by
    have hraw :
        (∑ k ∈ Finset.Ioc C M,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
          (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
            (-(1 / 2 : ℂ) *
              ((((C : ℕ) : ℝ) : ℂ) ^
                (-boundaryLineOnePointRealParam t))) +
            ((1 / 2 : ℂ) *
              ((((M : ℕ) : ℝ) : ℂ) ^
                (-boundaryLineOnePointRealParam t))) +
            (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-boundaryLineOnePointRealParam t *
                  (((x : ℝ) : ℂ) ^
                    (-(boundaryLineOnePointRealParam t + 1))))) :=
      boundaryLineOnePointRealParam_logarithmicPhase_weightedTail_eulerMaclaurin_identity
        t hM
    exact Eq.subst
      (motive := fun s : Finset ℕ =>
        (∑ k ∈ s,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
          (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
            (-(1 / 2 : ℂ) *
              ((((C : ℕ) : ℝ) : ℂ) ^
                (-boundaryLineOnePointRealParam t))) +
            ((1 / 2 : ℂ) *
              ((((M : ℕ) : ℝ) : ℂ) ^
                (-boundaryLineOnePointRealParam t))) +
            (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (-boundaryLineOnePointRealParam t *
                  (((x : ℝ) : ℂ) ^
                    (-(boundaryLineOnePointRealParam t + 1))))))
      (congrArg₂ Finset.Ioc hC_floor hM_floor).symm
      hraw
  have hcomponents :
      ‖(∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) +
          (-(1 / 2 : ℂ) *
            ((((C : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-boundaryLineOnePointRealParam t))) +
          (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-boundaryLineOnePointRealParam t *
                (((x : ℝ) : ℂ) ^
                  (-(boundaryLineOnePointRealParam t + 1)))))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_eulerMaclaurin_components_norm_le
      t ht hM
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    htail_to_eulerMaclaurin.symm
    hcomponents

/-- The classical prefix leaf is exactly the corresponding positive-index
logarithmic-phase prefix.

The zeroth local sample vanishes for `1 ≤ |t|`, so the remaining prefix problem
is the unconditional resonance-aware estimate for
`∑_{1 ≤ n ≤ floor(2 + |t|)} n^{-it}`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_eq_positiveIndex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ =
      Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊ := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_positiveIndex
      t ht ⌊2 + ‖t‖⌋₊

/-- Norm form of the positive-index reduction for the classical prefix leaf. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_eq_positiveIndex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊‖ =
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊‖ := by
  exact congrArg
    (fun z : ℂ => ‖z‖)
    (boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_eq_positiveIndex
      t ht)

/-- The classical prefix estimate is exactly the positive-index prefix
estimate transported across the zeroth-term reduction.

This is deliberately phrased with the positive-index estimate as an explicit
input.  The remaining analytic theorem must be an unconditional
resonance-aware estimate for the positive-index logarithmic phase sum; it is
not a finite-difference/no-resonance consequence. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_of_positiveIndex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (A : ℝ)
    (hpositive :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
          t ⌊2 + ‖t‖⌋₊‖ ≤
        A * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊)) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊‖ ≤
      A * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ A * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊))
    (boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_eq_positiveIndex
      t ht).symm
    hpositive

/-- At the canonical prefix cutoff, the first-derivative scale has bounded
linear part.

This is the real arithmetic sink needed after an unconditional
resonance-aware/stationary-phase estimate supplies the usual
`((N+1)/|t| + sqrt(1+|t|))` factor. -/
theorem boundaryLineOnePointRealParam_classicalPrefix_cutoff_linearScale_le_four
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖) ≤ (4 : ℝ) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have harg_nonneg : 0 ≤ 2 + ‖t‖ :=
    le_trans (show (0 : ℝ) ≤ 2 from zero_le_two)
      (le_add_of_nonneg_right (norm_nonneg t))
  have hfloor_le : ((C : ℕ) : ℝ) ≤ 2 + ‖t‖ :=
    Nat.floor_le harg_nonneg
  have hC_add_one :
      (((C + 1 : ℕ) : ℝ) : ℝ) ≤ 3 + ‖t‖ := by
    have hcast_add :
        (((C + 1 : ℕ) : ℝ) : ℝ) = ((C : ℕ) : ℝ) + 1 :=
      Eq.trans
        (Nat.cast_add C 1)
        (congrArg (fun r : ℝ => ((C : ℕ) : ℝ) + r)
          boundaryGrowth_natCast_one_eq_real_one)
    calc
      (((C + 1 : ℕ) : ℝ) : ℝ) = ((C : ℕ) : ℝ) + 1 :=
        hcast_add
      _ ≤ (2 + ‖t‖) + 1 :=
        add_le_add_right hfloor_le 1
      _ = 3 + ‖t‖ := by
        calc
          (2 + ‖t‖) + 1 = (2 + 1) + ‖t‖ := by
            exact add_right_comm (2 : ℝ) ‖t‖ 1
          _ = 3 + ‖t‖ := by
            exact congrArg (fun r : ℝ => r + ‖t‖)
              boundaryGrowth_real_two_add_one_eq_three
  have hthree_le_three_norm : (3 : ℝ) ≤ 3 * ‖t‖ := by
    calc
      (3 : ℝ) = 3 * (1 : ℝ) := by
        exact (mul_one (3 : ℝ)).symm
      _ ≤ 3 * ‖t‖ :=
        mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 3 from by exact zero_le_three)
  have hthree_add_le :
      (3 : ℝ) + ‖t‖ ≤ 4 * ‖t‖ := by
    calc
      (3 : ℝ) + ‖t‖ ≤ 3 * ‖t‖ + ‖t‖ :=
        add_le_add_right hthree_le_three_norm ‖t‖
      _ = 3 * ‖t‖ + 1 * ‖t‖ := by
        exact congrArg (fun r : ℝ => 3 * ‖t‖ + r) (one_mul ‖t‖).symm
      _ = (3 + 1) * ‖t‖ := by
        exact (add_mul (3 : ℝ) 1 ‖t‖).symm
      _ = 4 * ‖t‖ := by
        have hthree_add_one :
            (3 : ℝ) + 1 = 4 :=
          boundaryGrowth_real_three_add_one_eq_four
        exact congrArg (fun r : ℝ => r * ‖t‖) hthree_add_one
  have hnum_le : (((C + 1 : ℕ) : ℝ) : ℝ) ≤ 4 * ‖t‖ :=
    le_trans hC_add_one hthree_add_le
  have hdiv_le : (((C + 1 : ℕ) : ℝ) : ℝ) / ‖t‖ ≤ (4 * ‖t‖) / ‖t‖ :=
    div_le_div_of_nonneg_right hnum_le ht_pos.le
  have hright : (4 * ‖t‖) / ‖t‖ = (4 : ℝ) := by
    exact mul_div_cancel_right₀ (4 : ℝ) ht_pos.ne'
  exact Eq.subst
    (motive := fun r : ℝ => (((C + 1 : ℕ) : ℝ) : ℝ) / ‖t‖ ≤ r)
    hright
    hdiv_le

/-- At the canonical prefix cutoff, the standard first-derivative scale is
absorbed by `5 * sqrt(1 + |t|)`. -/
theorem boundaryLineOnePointRealParam_classicalPrefix_cutoff_vdcScale_le_five_sqrt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) ≤
      5 * Real.sqrt (1 + ‖t‖) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add
  have hlinear :
      (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖) ≤ (4 : ℝ) :=
    boundaryLineOnePointRealParam_classicalPrefix_cutoff_linearScale_le_four
      t ht
  have hfour_le_four_sqrt :
      (4 : ℝ) ≤ 4 * Real.sqrt (1 + ‖t‖) := by
    calc
      (4 : ℝ) = 4 * (1 : ℝ) := by
        exact (mul_one (4 : ℝ)).symm
      _ ≤ 4 * Real.sqrt (1 + ‖t‖) :=
        mul_le_mul_of_nonneg_left hsqrt_ge_one
          (show (0 : ℝ) ≤ 4 from by exact zero_le_four)
  have hlinear_sqrt :
      (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖) ≤
        4 * Real.sqrt (1 + ‖t‖) :=
    le_trans hlinear hfour_le_four_sqrt
  calc
    (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) ≤
        4 * Real.sqrt (1 + ‖t‖) + Real.sqrt (1 + ‖t‖) :=
      add_le_add_right hlinear_sqrt (Real.sqrt (1 + ‖t‖))
    _ = (4 + 1) * Real.sqrt (1 + ‖t‖) := by
      have hone_mul :
          Real.sqrt (1 + ‖t‖) = 1 * Real.sqrt (1 + ‖t‖) :=
        (one_mul (Real.sqrt (1 + ‖t‖))).symm
      exact Eq.trans
        (congrArg (fun r : ℝ => 4 * Real.sqrt (1 + ‖t‖) + r) hone_mul)
        (add_mul (4 : ℝ) 1 (Real.sqrt (1 + ‖t‖))).symm
    _ = 5 * Real.sqrt (1 + ‖t‖) := by
      have hfour_add_one :
          (4 : ℝ) + 1 = 5 :=
        boundaryGrowth_real_four_add_one_eq_five
      exact congrArg (fun r : ℝ => r * Real.sqrt (1 + ‖t‖))
        hfour_add_one

/-- The raw adjacent logarithmic increments are monotone on the classical
prefix block.  This isolates the non-modular part of the prefix cancellation
argument; the remaining difficulty is the resonance-aware reduced-increment
analysis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_rawIncrementMonotoneOn
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        1 ⌊2 + ‖t‖⌋₊ := by
  have hcutoff_pos :
      0 < ⌊2 + ‖t‖⌋₊ := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ‖t‖ :=
      one_le_two_add_norm t
    exact Nat.floor_pos.mpr hone_le_arg
  have hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  exact
    logarithmicPhase_integerIncrementMonotoneOn_of_logRatioMonotone_ownerGap
      t (Nat.le_refl 1) hcutoff_one

/-- On the classical prefix block, every raw adjacent logarithmic increment is
at least the endpoint derivative scale before reduction modulo `2π`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_integerIncrement_norm_ge_cutoffScale
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {n : ℕ}
    (hn : n ∈ Finset.Ico 1 ⌊2 + ‖t‖⌋₊) :
    ‖Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n‖ ≥
      ‖t‖ / (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ)) := by
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_integerIncrement_norm_ge_blockScale
      t (Nat.le_refl 1) hn

/-- If the boundary frequency is bounded, the finite prefix estimate follows
from the elementary cardinality bound.  This branch is genuinely finite; the
large-frequency branch still needs oscillatory cancellation. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_of_norm_le_four
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_four : ‖t‖ ≤ 4) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊‖ ≤
      8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have harg_le_six : (2 : ℝ) + ‖t‖ ≤ 6 := by
    calc
      (2 : ℝ) + ‖t‖ ≤ 2 + 4 :=
        add_le_add_left ht_four 2
      _ = 6 := by
        exact boundaryGrowth_real_two_add_four_eq_six
  have hC_le_six : C ≤ 6 := by
    have hfloor_mono :
        ⌊2 + ‖t‖⌋₊ ≤ ⌊(6 : ℝ)⌋₊ :=
      Nat.floor_mono harg_le_six
    have hfloor_six : ⌊(6 : ℝ)⌋₊ = 6 :=
      Nat.floor_natCast 6
    exact Eq.subst
      (motive := fun n : ℕ => C ≤ n)
      hfloor_six
      hfloor_mono
  have hC_add_one_le_eight_nat : C + 1 ≤ 8 := by
    have hC_add_one_le_seven : C + 1 ≤ 7 := by
      exact Nat.succ_le_succ hC_le_six
    have hseven_le_eight : 7 ≤ 8 :=
      Nat.le_of_lt (Nat.lt_succ_self 7)
    exact le_trans hC_add_one_le_seven hseven_le_eight
  have hC_add_one_le_eight : ((C + 1 : ℕ) : ℝ) ≤ 8 :=
    Nat.cast_le.mpr hC_add_one_le_eight_nat
  have hcard :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
        ((C + 1 : ℕ) : ℝ) :=
    have hraw :
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
          ((C : ℕ) : ℝ) + 1 :=
      logarithmicPhasePartialSum_norm_le_card t C
    have htarget :
        ((C : ℕ) : ℝ) + 1 = ((C + 1 : ℕ) : ℝ) :=
      (Eq.trans
        (Nat.cast_add C 1)
        (congrArg (fun r : ℝ => ((C : ℕ) : ℝ) + r)
          boundaryGrowth_natCast_one_eq_real_one)).symm
    Eq.subst
      (motive := fun r : ℝ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤ r)
      htarget
      hraw
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add
  have hnorm_le_C : ‖t‖ ≤ (C : ℝ) := by
    have hone_add_le_C :
        (1 : ℝ) + ‖t‖ ≤ (C : ℝ) :=
      boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
    have hnorm_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
      le_add_of_nonneg_left zero_le_one
    exact le_trans hnorm_le_one_add hone_add_le_C
  have hlog_ge_one : (1 : ℝ) ≤ Real.log (2 + C) := by
    have hbase : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
      one_le_log_two_add_norm_of_one_le_norm ht
    have harg_pos : (0 : ℝ) < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_one (one_le_two_add_norm t)
    have harg_le : 2 + ‖t‖ ≤ 2 + C :=
      add_le_add_left hnorm_le_C 2
    exact le_trans hbase (Real.log_le_log harg_pos harg_le)
  have hone_le_scale :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + C) :=
    mul_le_mul hsqrt_ge_one hlog_ge_one zero_le_one
      (Real.sqrt_nonneg (1 + ‖t‖))
  have height_le_target :
      (8 : ℝ) ≤ 8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) := by
    calc
      (8 : ℝ) = 8 * (1 : ℝ) := by
        exact (mul_one (8 : ℝ)).symm
      _ ≤ 8 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + C)) :=
        mul_le_mul_of_nonneg_left hone_le_scale
          (show (0 : ℝ) ≤ 8 from by exact Nat.cast_nonneg 8)
      _ = 8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) :=
        (mul_assoc 8 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + C))).symm
  exact le_trans hcard
    (le_trans hC_add_one_le_eight height_le_target)

/-- Scalar denominator comparison for the second-derivative scale on the
classical prefix window. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_curvatureDenominator_inv_le
    (t : ℝ)
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (1 : ℝ)
        (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))) :
      (((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
          (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))))⁻¹) ≤
        (x * x)⁻¹ := by
  let B : ℝ := (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_one hx.1
  have hB_pos : 0 < B :=
    Nat.cast_pos.mpr (Nat.succ_pos ⌊2 + ‖t‖⌋₊)
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx_pos
  have hB_nonneg : 0 ≤ B :=
    le_of_lt hB_pos
  have hx_le_B : x ≤ B :=
    hx.2
  have hxx_pos : 0 < x * x :=
    mul_pos hx_pos hx_pos
  have hxx_le_BB : x * x ≤ B * B :=
    mul_le_mul hx_le_B hx_le_B hx_nonneg hB_nonneg
  exact inv_le_inv₀ hxx_pos hxx_le_BB

/-- Curvature-scale comparison on the classical prefix window, with the
frequency factor restored. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_curvatureScale_le
    (t : ℝ)
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (1 : ℝ)
        (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))) :
      ‖t‖ *
          (((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
            (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))))⁻¹) ≤
        ‖t‖ * (x * x)⁻¹ := by
  exact mul_le_mul_of_nonneg_left
    (boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_curvatureDenominator_inv_le
      t hx)
    (norm_nonneg t)

/-- Curvature lower scale for the real logarithmic phase on the canonical
prefix window.  This is the concrete derivative estimate used by the
second-derivative van der Corput block argument. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_canonicalPrefix_curvature_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (1 : ℝ)
        (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))) :
      ‖t‖ *
          (((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
            (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ))))⁻¹) ≤
        ‖t‖ * (x * x)⁻¹ := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_curvatureScale_le
      t hx

/-- At the canonical prefix cutoff, the logarithmic normalization is at least
one. -/
theorem boundaryLineOnePointRealParam_classicalPrefix_cutoff_log_ge_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hnorm_le_C : ‖t‖ ≤ (C : ℝ) := by
    have hone_add_le_C :
        (1 : ℝ) + ‖t‖ ≤ (C : ℝ) :=
      boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
    have hnorm_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
      le_add_of_nonneg_left zero_le_one
    exact le_trans hnorm_le_one_add hone_add_le_C
  have hbase : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have harg_pos : 0 < 2 + ‖t‖ :=
    lt_of_lt_of_le zero_lt_one (one_le_two_add_norm t)
  have harg_le : 2 + ‖t‖ ≤ 2 + C :=
    add_le_add_left hnorm_le_C 2
  exact le_trans hbase (Real.log_le_log harg_pos harg_le)

/-- Canonical-prefix van der Corput scale estimate for the positive-index
logarithmic phase sum.

This is the true finite-prefix oscillatory sink: it must account for resonant
and nonresonant frequencies without assuming separated adjacent increments. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_vdcScale_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊‖ ≤
      80 * ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_curvatureBlock_norm_le
      t ht

/-- Canonical-prefix oscillatory estimate for the positive-index logarithmic
phase sum.

This is the precise remaining finite-prefix analytic sink: the bound is
unconditional in the frequency, so it cannot be obtained from the separated
finite-difference/no-resonance package. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊‖ ≤
      400 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  have hvdc :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
          t ⌊2 + ‖t‖⌋₊‖ ≤
        80 * ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_vdcScale_norm_le_ownerGap
      t ht
  have hscale :
      (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)) ≤
        5 * Real.sqrt (1 + ‖t‖) :=
    boundaryLineOnePointRealParam_classicalPrefix_cutoff_vdcScale_le_five_sqrt
      t ht
  have hlog_ge_one :
      (1 : ℝ) ≤ Real.log (2 + ⌊2 + ‖t‖⌋₊) :=
    boundaryLineOnePointRealParam_classicalPrefix_cutoff_log_ge_one t ht
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hsqrt_le_sqrt_log :
      Real.sqrt (1 + ‖t‖) ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
    calc
      Real.sqrt (1 + ‖t‖) = Real.sqrt (1 + ‖t‖) * 1 := by
        exact (mul_one (Real.sqrt (1 + ‖t‖))).symm
      _ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) :=
        mul_le_mul_of_nonneg_left hlog_ge_one hsqrt_nonneg
  have heighty_scale :
      80 * ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) ≤
        80 * (5 * Real.sqrt (1 + ‖t‖)) :=
    mul_le_mul_of_nonneg_left hscale (Nat.cast_nonneg 80)
  have heighty_five :
      80 * (5 * Real.sqrt (1 + ‖t‖)) =
        400 * Real.sqrt (1 + ‖t‖) := by
    calc
      80 * (5 * Real.sqrt (1 + ‖t‖)) =
          (80 * 5 : ℝ) * Real.sqrt (1 + ‖t‖) :=
        (mul_assoc (80 : ℝ) 5 (Real.sqrt (1 + ‖t‖))).symm
      _ = 400 * Real.sqrt (1 + ‖t‖) := by
        exact congrArg (fun r : ℝ => r * Real.sqrt (1 + ‖t‖))
          boundaryGrowth_real_eighty_mul_five_eq_fourhundred
  have hfourhundred_sqrt_le_target :
      400 * Real.sqrt (1 + ‖t‖) ≤
        400 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
    calc
      400 * Real.sqrt (1 + ‖t‖) =
          400 * (Real.sqrt (1 + ‖t‖) * 1) := by
        exact congrArg (fun r : ℝ => 400 * r)
          (mul_one (Real.sqrt (1 + ‖t‖))).symm
      _ ≤ 400 * (Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊)) :=
        mul_le_mul_of_nonneg_left
          (Eq.subst
            (motive := fun r : ℝ =>
              r ≤ Real.sqrt (1 + ‖t‖) *
                Real.log (2 + ⌊2 + ‖t‖⌋₊))
            (mul_one (Real.sqrt (1 + ‖t‖))).symm
            hsqrt_le_sqrt_log)
          (show (0 : ℝ) ≤ 400 from Nat.cast_nonneg 400)
      _ = 400 * Real.sqrt (1 + ‖t‖) *
          Real.log (2 + ⌊2 + ‖t‖⌋₊) :=
        (mul_assoc 400 (Real.sqrt (1 + ‖t‖))
          (Real.log (2 + ⌊2 + ‖t‖⌋₊))).symm
  exact le_trans hvdc
    (le_trans heighty_scale
      (le_trans (le_of_eq heighty_five) hfourhundred_sqrt_le_target))

/-- Finite prefix estimate for the unweighted logarithmic-phase partial sums up
to the natural cutoff `C = ⌊2 + |t|⌋₊`.

This is the finite initial segment in the Dirichlet/Abel proof of the public
partial-sum bound.  It is deliberately independent of the false finite
difference/no-resonance package: the prefix is handled by a direct finite
estimate at the cutoff. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊‖ ≤
      400 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_of_positiveIndex
      t ht
      400
      (Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_norm_le_ownerGap
        t ht)

/-- The finite prefix `[0, C]` is disjoint from the open-right tail `(C, M]`. -/
theorem boundaryGrowth_Icc_zero_disjoint_Ioc
    (C M : ℕ) :
    Disjoint (Finset.Icc 0 C) (Finset.Ioc C M) :=
  Finset.disjoint_left.mpr
    (fun n hn_prefix hn_tail =>
      have hn_le_C : n ≤ C :=
        (Finset.mem_Icc.mp hn_prefix).2
      have hC_lt_n : C < n :=
        (Finset.mem_Ioc.mp hn_tail).1
      have hC_lt_C : C < C :=
        Nat.lt_of_lt_of_le hC_lt_n hn_le_C
      Nat.lt_irrefl C hC_lt_C)

/-- The finite prefix `[0, C]` and the open-right tail `(C, M]` cover `[0, M]`
when `C ≤ M`. -/
theorem boundaryGrowth_Icc_zero_union_Ioc_eq_Icc
    (C M : ℕ)
    (hCM : C ≤ M) :
    Finset.Icc 0 C ∪ Finset.Ioc C M = Finset.Icc 0 M :=
  Finset.ext
    (fun n =>
      Iff.intro
        (fun hn_union =>
          match Finset.mem_union.mp hn_union with
          | Or.inl hn_prefix =>
              have hn_bounds : 0 ≤ n ∧ n ≤ C :=
                Finset.mem_Icc.mp hn_prefix
              have hn_le_M : n ≤ M :=
                Nat.le_trans hn_bounds.2 hCM
              Finset.mem_Icc.mpr ⟨hn_bounds.1, hn_le_M⟩
          | Or.inr hn_tail =>
              have hn_tail_bounds : C < n ∧ n ≤ M :=
                Finset.mem_Ioc.mp hn_tail
              have hzero_le_n : 0 ≤ n :=
                Nat.zero_le n
              Finset.mem_Icc.mpr ⟨hzero_le_n, hn_tail_bounds.2⟩)
          (fun hn_total =>
            have hn_total_bounds : 0 ≤ n ∧ n ≤ M :=
              Finset.mem_Icc.mp hn_total
            match Nat.le_or_gt n C with
            | Or.inl hn_le_C =>
                have hn_prefix : n ∈ Finset.Icc 0 C :=
                  Finset.mem_Icc.mpr ⟨hn_total_bounds.1, hn_le_C⟩
                Finset.mem_union.mpr (Or.inl hn_prefix)
            | Or.inr hC_lt_n =>
                have hn_tail : n ∈ Finset.Ioc C M :=
                  Finset.mem_Ioc.mpr ⟨hC_lt_n, hn_total_bounds.2⟩
              Finset.mem_union.mpr (Or.inr hn_tail)))

/-- Sum splitting for the finite prefix `[0, C]` and the open-right tail `(C, M]`. -/
theorem boundaryGrowth_sum_Icc_zero_eq_prefix_add_Ioc
    (f : ℕ → ℂ)
    (C M : ℕ)
    (hCM : C ≤ M) :
    (∑ n ∈ Finset.Icc 0 M, f n) =
      (∑ n ∈ Finset.Icc 0 C, f n) +
        ∑ n ∈ Finset.Ioc C M, f n :=
  have hdisjoint : Disjoint (Finset.Icc 0 C) (Finset.Ioc C M) :=
    boundaryGrowth_Icc_zero_disjoint_Ioc C M
  have hunion : Finset.Icc 0 C ∪ Finset.Ioc C M = Finset.Icc 0 M :=
    boundaryGrowth_Icc_zero_union_Ioc_eq_Icc C M hCM
  have hsum_union :
      (∑ n ∈ Finset.Icc 0 C ∪ Finset.Ioc C M, f n) =
        (∑ n ∈ Finset.Icc 0 C, f n) +
          ∑ n ∈ Finset.Ioc C M, f n :=
    Finset.sum_union hdisjoint
  Eq.trans
    (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hunion.symm)
    hsum_union

/-- Exact finite splitting of a logarithmic-phase partial sum at the canonical
post-cutoff endpoint. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_prefix_add_Ioc_tail_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ +
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℕ → ℂ := fun n => ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hsplit :
      (∑ n ∈ Finset.Icc 0 M, f n) =
        (∑ n ∈ Finset.Icc 0 C, f n) +
          ∑ n ∈ Finset.Ioc C M, f n :=
    boundaryGrowth_sum_Icc_zero_eq_prefix_add_Ioc f C M hM
  exact hsplit


end LFunctions
end Boundary

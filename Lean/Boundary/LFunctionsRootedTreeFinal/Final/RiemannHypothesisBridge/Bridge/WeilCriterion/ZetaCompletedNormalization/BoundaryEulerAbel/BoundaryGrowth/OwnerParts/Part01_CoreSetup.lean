import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Owner

/-!
# Boundary growth owner part 1

This file is a mechanical forward-order split of `BoundaryGrowth.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem boundaryGrowth_natCast_one_eq_real_one :
    (((1 : ℕ) : ℝ) = (1 : ℝ)) :=
  Nat.cast_one

theorem boundaryGrowth_natCast_two_eq_real_two :
    (((2 : ℕ) : ℝ) = (2 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_three_eq_real_three :
    (((3 : ℕ) : ℝ) = (3 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_four_eq_real_four :
    (((4 : ℕ) : ℝ) = (4 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_five_eq_real_five :
    (((5 : ℕ) : ℝ) = (5 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_sixteen_eq_real_sixteen :
    (((16 : ℕ) : ℝ) = (16 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_thirty_two_eq_real_thirty_two :
    (((32 : ℕ) : ℝ) = (32 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_thirty_six_eq_real_thirty_six :
    (((36 : ℕ) : ℝ) = (36 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_thirty_seven_eq_real_thirty_seven :
    (((37 : ℕ) : ℝ) = (37 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_thirty_eight_eq_real_thirty_eight :
    (((38 : ℕ) : ℝ) = (38 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_thirty_nine_eq_real_thirty_nine :
    (((39 : ℕ) : ℝ) = (39 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_forty_eq_real_forty :
    (((40 : ℕ) : ℝ) = (40 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_natCast_eighty_eq_real_eighty :
    (((80 : ℕ) : ℝ) = (80 : ℝ)) :=
  Nat.cast_ofNat

theorem boundaryGrowth_real_two_add_one_eq_three :
    ((2 : ℝ) + (1 : ℝ)) = 3 := by
  calc
    (2 : ℝ) + (1 : ℝ) =
        ((2 : ℕ) : ℝ) + (1 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (1 : ℝ))
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = ((2 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((2 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_one_eq_real_one.symm
    _ = (((2 : ℕ) + 1 : ℕ) : ℝ) := by
      exact (Nat.cast_add 2 1).symm
    _ = ((3 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((2 : ℕ) + 1) = 3 from rfl)
    _ = (3 : ℝ) := by
      exact boundaryGrowth_natCast_three_eq_real_three

theorem boundaryGrowth_real_two_mul_two_eq_four :
    ((2 : ℝ) * (2 : ℝ)) = 4 := by
  calc
    (2 : ℝ) * (2 : ℝ) =
        ((2 : ℕ) : ℝ) * (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y * (2 : ℝ))
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = ((2 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((2 : ℕ) : ℝ) * y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((2 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 2 2).symm
    _ = ((4 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((2 : ℕ) * 2) = 4 from rfl)
    _ = (4 : ℝ) := by
      exact boundaryGrowth_natCast_four_eq_real_four

theorem boundaryGrowth_real_two_add_two_eq_four :
    ((2 : ℝ) + (2 : ℝ)) = 4 := by
  calc
    (2 : ℝ) + (2 : ℝ) =
        ((2 : ℕ) : ℝ) + (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (2 : ℝ))
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = ((2 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((2 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((2 : ℕ) + 2 : ℕ) : ℝ) := by
      exact (Nat.cast_add 2 2).symm
    _ = ((4 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((2 : ℕ) + 2) = 4 from rfl)
    _ = (4 : ℝ) := by
      exact boundaryGrowth_natCast_four_eq_real_four

theorem boundaryGrowth_real_three_add_two_eq_five :
    ((3 : ℝ) + (2 : ℝ)) = 5 := by
  calc
    (3 : ℝ) + (2 : ℝ) =
        ((3 : ℕ) : ℝ) + (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (2 : ℝ))
        boundaryGrowth_natCast_three_eq_real_three.symm
    _ = ((3 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((3 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((3 : ℕ) + 2 : ℕ) : ℝ) := by
      exact (Nat.cast_add 3 2).symm
    _ = ((5 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((3 : ℕ) + 2) = 5 from rfl)
    _ = (5 : ℝ) := by
      exact boundaryGrowth_natCast_five_eq_real_five

theorem boundaryGrowth_real_sixteen_mul_two_eq_thirty_two :
    ((16 : ℝ) * (2 : ℝ)) = 32 := by
  calc
    (16 : ℝ) * (2 : ℝ) =
        ((16 : ℕ) : ℝ) * (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y * (2 : ℝ))
        boundaryGrowth_natCast_sixteen_eq_real_sixteen.symm
    _ = ((16 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((16 : ℕ) : ℝ) * y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((16 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 16 2).symm
    _ = ((32 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((16 : ℕ) * 2) = 32 from rfl)
    _ = (32 : ℝ) := by
      exact boundaryGrowth_natCast_thirty_two_eq_real_thirty_two

theorem boundaryGrowth_real_four_add_thirty_two_eq_thirty_six :
    ((4 : ℝ) + (32 : ℝ)) = 36 := by
  calc
    (4 : ℝ) + (32 : ℝ) =
        ((4 : ℕ) : ℝ) + (32 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (32 : ℝ))
        boundaryGrowth_natCast_four_eq_real_four.symm
    _ = ((4 : ℕ) : ℝ) + ((32 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((4 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_thirty_two_eq_real_thirty_two.symm
    _ = (((4 : ℕ) + 32 : ℕ) : ℝ) := by
      exact (Nat.cast_add 4 32).symm
    _ = ((36 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((4 : ℕ) + 32) = 36 from rfl)
    _ = (36 : ℝ) := by
      exact boundaryGrowth_natCast_thirty_six_eq_real_thirty_six

theorem boundaryGrowth_real_thirty_six_add_two_eq_thirty_eight :
    ((36 : ℝ) + (2 : ℝ)) = 38 := by
  calc
    (36 : ℝ) + (2 : ℝ) =
        ((36 : ℕ) : ℝ) + (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (2 : ℝ))
        boundaryGrowth_natCast_thirty_six_eq_real_thirty_six.symm
    _ = ((36 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((36 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((36 : ℕ) + 2 : ℕ) : ℝ) := by
      exact (Nat.cast_add 36 2).symm
    _ = ((38 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((36 : ℕ) + 2) = 38 from rfl)
    _ = (38 : ℝ) := by
      exact boundaryGrowth_natCast_thirty_eight_eq_real_thirty_eight

theorem boundaryGrowth_real_five_add_thirty_two_eq_thirty_seven :
    ((5 : ℝ) + (32 : ℝ)) = 37 := by
  calc
    (5 : ℝ) + (32 : ℝ) =
        ((5 : ℕ) : ℝ) + (32 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (32 : ℝ))
        boundaryGrowth_natCast_five_eq_real_five.symm
    _ = ((5 : ℕ) : ℝ) + ((32 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((5 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_thirty_two_eq_real_thirty_two.symm
    _ = (((5 : ℕ) + 32 : ℕ) : ℝ) := by
      exact (Nat.cast_add 5 32).symm
    _ = ((37 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((5 : ℕ) + 32) = 37 from rfl)
    _ = (37 : ℝ) := by
      exact boundaryGrowth_natCast_thirty_seven_eq_real_thirty_seven

theorem boundaryGrowth_real_thirty_seven_add_two_eq_thirty_nine :
    ((37 : ℝ) + (2 : ℝ)) = 39 := by
  calc
    (37 : ℝ) + (2 : ℝ) =
        ((37 : ℕ) : ℝ) + (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y + (2 : ℝ))
        boundaryGrowth_natCast_thirty_seven_eq_real_thirty_seven.symm
    _ = ((37 : ℕ) : ℝ) + ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((37 : ℕ) : ℝ) + y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((37 : ℕ) + 2 : ℕ) : ℝ) := by
      exact (Nat.cast_add 37 2).symm
    _ = ((39 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((37 : ℕ) + 2) = 39 from rfl)
    _ = (39 : ℝ) := by
      exact boundaryGrowth_natCast_thirty_nine_eq_real_thirty_nine

theorem boundaryGrowth_real_forty_mul_two_eq_eighty :
    ((40 : ℝ) * (2 : ℝ)) = 80 := by
  calc
    (40 : ℝ) * (2 : ℝ) =
        ((40 : ℕ) : ℝ) * (2 : ℝ) := by
      exact congrArg (fun y : ℝ => y * (2 : ℝ))
        boundaryGrowth_natCast_forty_eq_real_forty.symm
    _ = ((40 : ℕ) : ℝ) * ((2 : ℕ) : ℝ) := by
      exact congrArg (fun y : ℝ => ((40 : ℕ) : ℝ) * y)
        boundaryGrowth_natCast_two_eq_real_two.symm
    _ = (((40 : ℕ) * 2 : ℕ) : ℝ) := by
      exact (Nat.cast_mul 40 2).symm
    _ = ((80 : ℕ) : ℝ) := by
      exact congrArg (fun n : ℕ => (n : ℝ)) (show ((40 : ℕ) * 2) = 80 from rfl)
    _ = (80 : ℝ) := by
      exact boundaryGrowth_natCast_eighty_eq_real_eighty

theorem boundaryGrowth_complex_one_div_two_norm_le_one :
    ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  have hhalf_nonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) := by
    exact div_nonneg zero_le_one (show (0 : ℝ) ≤ 2 from zero_le_two)
  have hhalf_le_one : (1 / 2 : ℝ) ≤ (1 : ℝ) := by
    calc
      (1 / 2 : ℝ) ≤ (1 / 1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one
          (show (1 : ℝ) ≤ 2 from one_le_two)
      _ = (1 : ℝ) := by
        exact div_one 1
  have hnorm :
      ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
    calc
      ‖(1 / 2 : ℂ)‖ =
          ‖(((1 / 2 : ℝ) : ℂ))‖ := by
        rfl
      _ = |(1 / 2 : ℝ)| := by
        exact RCLike.norm_ofReal (1 / 2 : ℝ)
      _ = (1 / 2 : ℝ) := by
        exact abs_of_nonneg hhalf_nonneg
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ (1 : ℝ))
    hnorm.symm
    hhalf_le_one

theorem boundaryGrowth_complex_neg_one_div_two_norm_le_one :
    ‖-(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  have hnorm :
      ‖-(1 / 2 : ℂ)‖ = ‖(1 / 2 : ℂ)‖ :=
    norm_neg (1 / 2 : ℂ)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ (1 : ℝ))
    hnorm.symm
    boundaryGrowth_complex_one_div_two_norm_le_one

/-- The owner-level first-derivative partial-sum hypothesis with an explicit
constant. -/
def boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant
    (A : ℝ)
    (t : ℝ) : Prop :=
  ∀ {x : ℝ},
    (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        A * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)

/-- The owner-level first-derivative partial-sum hypothesis used in the
boundary-line Euler-Abel estimate.

The proved logarithmic-phase VDC chain uses a classical absolute constant in
the curvature-controlled prefix and then normalizes the post-cutoff
Euler-Abel terms to the public `x / |t|` surface.  The owner-level public
constant supported by the current proof chain is `500`.  The older
`8`-constant normalization is retained only in the finite scalar-majorant
helpers below, where it is explicitly requested as
`boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 8 t`.
-/
def boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound
    (t : ℝ) : Prop :=
  boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 500 t

/-- The owner-level finite post-cutoff Abel-tail boundedness hypothesis.

This is intentionally separate from the first-derivative partial-sum estimate:
the coarse finite majorant is not uniformly bounded by the fixed Abel-tail
constant, so downstream growth theorems must carry this true bounded-tail input
until the classical Abel-tail owner proves it. -/
def boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded
    (t : ℝ) : Prop :=
  ∀ M : ℕ,
    ⌊2 + ‖t‖⌋₊ ≤ M →
      ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t

/-- Combined boundary-line truncation hypotheses for a complex point on
`re = 1`. -/
def boundaryLineOneVerticalTruncationHypotheses
    (w : ℂ) : Prop :=
  boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound w.im ∧
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded w.im

/-- The currently proved owner-level Abel summation tail bound, stated with
the same cutoff quantifiers as `boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded`.

This is the honest output of the finite Abel decomposition: the right side is
the explicit endpoint-plus-integral majorant before the remaining uniform
constant comparison. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorantBounded
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 8 t) :
    ∀ M : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M := by
  exact
    fun M hcutoff =>
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
        t ht hpartial hcutoff

/-- Reduction of the fixed finite-tail boundedness hypothesis to the remaining
uniform Abel-tail majorant comparison. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_of_finiteAbelTailMajorant_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 8 t)
    (hmajorant :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
          boundaryLineOnePointRealParam_logarithmicPhaseFiniteAbelTailMajorant t M ≤
            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  intro M hcutoff
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailMajorantBounded
      t ht hpartial M hcutoff)
    (hmajorant M hcutoff)


end LFunctions
end Boundary

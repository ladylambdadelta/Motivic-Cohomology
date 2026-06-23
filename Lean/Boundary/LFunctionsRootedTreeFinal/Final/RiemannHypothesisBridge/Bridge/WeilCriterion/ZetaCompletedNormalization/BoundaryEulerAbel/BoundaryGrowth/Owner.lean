import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.AbelTransport.Owner

/-!
# Boundary zeta growth consequences

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.BoundaryEulerAbel.Owner`.  Declaration order is preserved.
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

The proved logarithmic-phase VDC chain gives an endpoint form with constant
`40` and the term `(⌊x⌋₊ + 1) / |t|`.  Normalizing this to the public
`x / |t|` surface costs exactly a factor of two: use
`⌊x⌋₊ + 1 ≤ x + 1` and `1 / |t| ≤ sqrt (1 + |t|)` when `1 ≤ |t|`.
Thus the owner-level public constant supported by the current proof chain is
`80`.  The older
`8`-constant normalization is retained only in the finite scalar-majorant
helpers below, where it is explicitly requested as
`boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 8 t`.
-/
def boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound
    (t : ℝ) : Prop :=
  boundaryLineOnePointRealParam_logarithmicPhasePartialSumBoundWithConstant 80 t

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

/-- Positive integer logarithmic step ratios decrease with the integer index. -/
theorem boundaryGrowth_logarithmicStepRatio_antitone_nat
    {m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
  have hm_pos_nat : 0 < m :=
    Nat.lt_of_succ_le hm
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le hm_pos_nat hmn
  have hm_pos : (0 : ℝ) < (m : ℝ) :=
    Nat.cast_pos.mpr hm_pos_nat
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hmn_real : (m : ℝ) ≤ (n : ℝ) :=
    Nat.cast_le.mpr hmn
  have hreciprocal : (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) :=
    one_div_le_one_div_of_le hm_pos hmn_real
  have hn_ratio :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        (1 : ℝ) + (1 : ℝ) / (n : ℝ) := by
    calc
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
          (((n : ℕ) : ℝ) + (1 : ℝ)) / (n : ℝ) := by
        exact congrArg (fun y : ℝ => y / (n : ℝ)) (Nat.cast_add n 1)
      _ = ((n : ℝ) / (n : ℝ)) + ((1 : ℝ) / (n : ℝ)) := by
        exact add_div (n : ℝ) (1 : ℝ) (n : ℝ)
      _ = (1 : ℝ) + ((1 : ℝ) / (n : ℝ)) := by
        exact congrArg (fun y : ℝ => y + ((1 : ℝ) / (n : ℝ)))
          (div_self (ne_of_gt hn_pos))
  have hm_ratio :
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
        (1 : ℝ) + (1 : ℝ) / (m : ℝ) := by
    calc
      (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
          (((m : ℕ) : ℝ) + (1 : ℝ)) / (m : ℝ) := by
        exact congrArg (fun y : ℝ => y / (m : ℝ)) (Nat.cast_add m 1)
      _ = ((m : ℝ) / (m : ℝ)) + ((1 : ℝ) / (m : ℝ)) := by
        exact add_div (m : ℝ) (1 : ℝ) (m : ℝ)
      _ = (1 : ℝ) + ((1 : ℝ) / (m : ℝ)) := by
        exact congrArg (fun y : ℝ => y + ((1 : ℝ) / (m : ℝ)))
          (div_self (ne_of_gt hm_pos))
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ (((m + 1 : ℕ) : ℝ) / (m : ℝ)))
    hn_ratio.symm
    (Eq.subst
      (motive := fun right : ℝ =>
        (1 : ℝ) + (1 : ℝ) / (n : ℝ) ≤ right)
      hm_ratio.symm
      (add_le_add_left hreciprocal 1))

/-- Logarithms of positive integer step ratios decrease with the integer index. -/
theorem boundaryGrowth_logarithmicStepLog_antitone_nat
    {m n : ℕ}
    (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
  have hm_pos_nat : 0 < m :=
    Nat.lt_of_succ_le hm
  have hn_pos_nat : 0 < n :=
    lt_of_lt_of_le hm_pos_nat hmn
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hn_succ_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos n)
  have hn_ratio_pos :
      (0 : ℝ) < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
    div_pos hn_succ_pos hn_pos
  exact
    Real.log_le_log
      hn_ratio_pos
      (boundaryGrowth_logarithmicStepRatio_antitone_nat hm hmn)

/-- Adjacent increments of the real logarithmic phase are the signed logarithmic
step ratios. -/
theorem boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
    (t : ℝ)
    {n : ℕ}
    (hn : 1 ≤ n) :
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
      -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hn_pos_nat : 0 < n :=
    Nat.lt_of_succ_le hn
  have hn_pos : (0 : ℝ) < (n : ℝ) :=
    Nat.cast_pos.mpr hn_pos_nat
  have hn_ne : (n : ℝ) ≠ 0 :=
    ne_of_gt hn_pos
  have hsucc_ne : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hlog_div :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) =
        Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) :=
    Real.log_div hsucc_ne hn_ne
  calc
    Complex.realPhase_integerIncrement
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
        (-t * Real.log ((n + 1 : ℕ) : ℝ)) -
          (-t * Real.log (n : ℝ)) := by
      rfl
    _ = -t * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) := by
      exact (mul_sub (-t) (Real.log ((n + 1 : ℕ) : ℝ)) (Real.log (n : ℝ))).symm
    _ = -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      exact congrArg (fun y : ℝ => -t * y) hlog_div.symm

/-- Raw adjacent logarithmic increments are monotone on each positive integer
block.  This elementary fact is not enough for the reduced finite-difference
package: reduction modulo `2π` can wind, and exact resonances can occur. -/
theorem logarithmicPhase_integerIncrementMonotoneOn_of_logRatioMonotone_ownerGap
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.realPhase_integerIncrementMonotoneOn
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b := by
  have hcases : 0 ≤ t ∨ t ≤ 0 :=
    le_total 0 t
  match hcases with
  | Or.inl ht_nonneg =>
      exact Or.inr
        (fun m hm n hn hmn =>
          have hm_ge_a : a ≤ m :=
            (Finset.mem_Ico.mp hm).1
          have hm_pos : 1 ≤ m :=
            le_trans ha hm_ge_a
          have hlog :
              Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicStepLog_antitone_nat hm_pos hmn
          have hscaled :
              -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr ht_nonneg)
          have hm_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m =
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hm_pos
          have hn_ge_a : a ≤ n :=
            le_trans hm_ge_a hmn
          have hn_pos : 1 ≤ n :=
            le_trans ha hn_ge_a
          have hn_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hn_pos
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n)
            hm_increment.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ right)
              hn_increment.symm
              hscaled))
  | Or.inr ht_nonpos =>
      exact Or.inl
        (fun m hm n hn hmn =>
          have hm_ge_a : a ≤ m :=
            (Finset.mem_Ico.mp hm).1
          have hm_pos : 1 ≤ m :=
            le_trans ha hm_ge_a
          have hlog :
              Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicStepLog_antitone_nat hm_pos hmn
          have hscaled :
              -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog (neg_nonneg.mpr ht_nonpos)
          have hm_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m =
                -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hm_pos
          have hn_ge_a : a ≤ n :=
            le_trans hm_ge_a hmn
          have hn_pos : 1 ≤ n :=
            le_trans ha hn_ge_a
          have hn_increment :
              Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) n =
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) :=
            boundaryGrowth_logarithmicPhase_integerIncrement_eq_neg_mul_logStep
              t hn_pos
          Eq.subst
            (motive := fun left : ℝ =>
              left ≤
                Complex.realPhase_integerIncrement
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) m)
            hn_increment.symm
            (Eq.subst
              (motive := fun right : ℝ =>
                -t * Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ right)
              hm_increment.symm
              hscaled))

/-- Endpoint-floor arithmetic for the public logarithmic-phase partial-sum
surface.

The VDC theorem supplies the factor
`40 * (((⌊x⌋₊ + 1) / |t| + sqrt (1 + |t|)) * log (2 + ⌊x⌋₊))`.
For `x ≥ ⌊2 + |t|⌋₊` and `1 ≤ |t|`, the endpoint shift is absorbed by
`1 / |t| ≤ sqrt (1 + |t|)`, while `log (2 + ⌊x⌋₊) ≤ log (2 + x)` follows
from `⌊x⌋₊ ≤ x`.  The only constant loss is therefore `40 -> 80`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_vdcEndpoint_le_public80
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) ≤
      80 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  let T : ℝ := ‖t‖
  let S : ℝ := Real.sqrt (1 + T)
  let Lfloor : ℝ := Real.log (2 + ⌊x⌋₊)
  let Lx : ℝ := Real.log (2 + x)
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one ht
  have hT_one : (1 : ℝ) ≤ T :=
    ht
  have hT_nonneg : 0 ≤ T :=
    le_of_lt hT_pos
  have hcutoff_nonneg : 0 ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    Nat.cast_nonneg ⌊2 + ‖t‖⌋₊
  have hx_nonneg : 0 ≤ x :=
    le_trans hcutoff_nonneg hx
  have hfloor_le_x : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hfloor_add_one_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℝ) ≤ x + 1 := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) : ℝ) =
          ((⌊x⌋₊ : ℕ) : ℝ) + 1 := by
        exact Nat.cast_add ⌊x⌋₊ 1
      _ ≤ x + 1 :=
        add_le_add_right hfloor_le_x 1
  have hone_div_le_one : (1 : ℝ) / T ≤ 1 := by
    calc
      (1 : ℝ) / T = 1 * T⁻¹ := by
        exact Eq.trans (one_div T) (one_mul T⁻¹).symm
      _ ≤ 1 * 1 :=
        mul_le_mul_of_nonneg_left
          (inv_le_one_of_one_le₀ hT_one)
          zero_le_one
      _ = 1 := by
        exact one_mul 1
  have hone_le_one_add_T : (1 : ℝ) ≤ 1 + T :=
    le_add_of_nonneg_right hT_nonneg
  have hone_le_S : (1 : ℝ) ≤ S := by
    exact Real.one_le_sqrt.mpr hone_le_one_add_T
  have hone_div_le_S : (1 : ℝ) / T ≤ S :=
    le_trans hone_div_le_one hone_le_S
  have hshift_div_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T) ≤ x / T + S := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T) ≤ (x + 1) / T :=
        div_le_div_of_nonneg_right hfloor_add_one_le (le_of_lt hT_pos)
      _ = x / T + 1 / T := by
        exact add_div x 1 T
      _ ≤ x / T + S :=
        add_le_add_left hone_div_le_S (x / T)
  have hvdc_factor_le :
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) ≤
        2 * (x / T + S) := by
    calc
      (((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) ≤
          (x / T + S) + S :=
        add_le_add_right hshift_div_le S
      _ ≤ (x / T + S) + (x / T + S) := by
        have hx_div_nonneg : 0 ≤ x / T :=
          div_nonneg hx_nonneg hT_nonneg
        have hS_le_sum : S ≤ x / T + S :=
          le_add_of_nonneg_left hx_div_nonneg
        exact add_le_add_left hS_le_sum (x / T + S)
      _ = 2 * (x / T + S) := by
        exact (two_mul (x / T + S)).symm
  have hlog_le : Lfloor ≤ Lx := by
    have hleft_pos : 0 < 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg ⌊x⌋₊))
    have harg_le : 2 + ((⌊x⌋₊ : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hfloor_le_x 2
    exact Real.log_le_log hleft_pos harg_le
  have hfactor_nonneg : 0 ≤ x / T + S := by
    exact add_nonneg (div_nonneg hx_nonneg hT_nonneg) (Real.sqrt_nonneg (1 + T))
  have hLfloor_nonneg : 0 ≤ Lfloor := by
    have hthree_le_arg : (3 : ℝ) ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) := by
      have hfloor_one : (1 : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
        have hcutoff_one : (1 : ℝ) ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
          Nat.cast_le.mpr (Nat.succ_le_of_lt (Nat.floor_pos.mpr (lt_of_lt_of_le zero_lt_two
            (le_add_of_nonneg_right (norm_nonneg t)))))
        have hx_one : (1 : ℝ) ≤ x :=
          le_trans hcutoff_one hx
        exact Nat.cast_le.mpr ((Nat.le_floor_iff hx_nonneg).mpr hx_one)
      calc
        (3 : ℝ) = 2 + 1 := by
          exact boundaryGrowth_real_two_add_one_eq_three.symm
        _ ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
          add_le_add_left hfloor_one 2
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((⌊x⌋₊ : ℕ) : ℝ) :=
      le_trans (show (1 : ℝ) ≤ 3 from one_le_three) hthree_le_arg
    exact Real.log_nonneg hone_le_arg
  have hmul_factor_log :
      ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) ≤
        (2 * (x / T + S)) * Lx := by
    exact mul_le_mul hvdc_factor_le hlog_le hLfloor_nonneg
      (mul_nonneg zero_le_two hfactor_nonneg)
  have hscaled :
      40 *
          ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) ≤
        40 * ((2 * (x / T + S)) * Lx) :=
    mul_le_mul_of_nonneg_left hmul_factor_log
      (show (0 : ℝ) ≤ 40 from Nat.cast_nonneg 40)
  calc
    40 *
        ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ⌊x⌋₊)) =
        40 *
          ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / T + S) * Lfloor) := rfl
    _ ≤ 40 * ((2 * (x / T + S)) * Lx) :=
      hscaled
    _ = 80 * ((x / T) + S) * Lx := by
      calc
        40 * ((2 * (x / T + S)) * Lx)
            = (40 * 2) * ((x / T + S) * Lx) := by
          exact Eq.trans
            (mul_assoc 40 (2 * (x / T + S)) Lx).symm
            (congrArg (fun y : ℝ => y * Lx)
              (mul_assoc 40 2 (x / T + S)))
        _ = 80 * ((x / T + S) * Lx) := by
          exact congrArg (fun y : ℝ => y * ((x / T + S) * Lx))
            boundaryGrowth_real_forty_mul_two_eq_eighty
        _ = 80 * (x / T + S) * Lx := by
          exact mul_assoc 80 (x / T + S) Lx
    _ = 80 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := rfl

/-- Endpoint-floor normalization from the proved VDC endpoint form to the
public first-derivative partial-sum bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_vdc_endpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hvdc :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            40 *
              ((((⌊x⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
                  Real.sqrt (1 + ‖t‖)) *
                Real.log (2 + ⌊x⌋₊))) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  intro x hx
  exact le_trans
    (hvdc hx)
    (boundaryLineOnePointRealParam_logarithmicPhase_vdcEndpoint_le_public80
      t ht hx)

/-- Conditional owner wrapper from the proved logarithmic-phase VDC estimate to
the public boundary-growth partial-sum hypothesis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_finiteDifference
    (hfiniteDifference : logarithmicPhaseFiniteDifferenceHypothesis)
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_vdc_endpoint
      t ht
      (fun hx =>
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_vdc
          hfiniteDifference t ht hx)

/-- Exact antiderivative identity for the post-cutoff main integral.

This is the fundamental theorem of calculus step for
`x ↦ x^(-1-it)` on the positive interval
`[⌊2 + |t|⌋₊, M]`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_intervalIntegral_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)) := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ =>
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t)))
      hle).symm

/-- Exponent endpoint normalization for the post-cutoff main-integral
antiderivative. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one
    (t : ℝ) :
    (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
      -(t : ℂ) * Complex.I := by
  have htail :
      (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
        -boundaryLineOnePointRealParam t :=
    boundaryLineOnePointRealParam_logarithmicPhase_tail_exponent_eq t
  calc
    (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        ((-1 : ℂ) + (-(t : ℂ) * Complex.I)) + (1 : ℂ) := by
      exact congrArg (fun z : ℂ => z + (1 : ℂ)) htail.symm
    _ = (-(t : ℂ) * Complex.I) + ((-1 : ℂ) + (1 : ℂ)) := by
      exact add_right_comm (-1 : ℂ) (-(t : ℂ) * Complex.I) (1 : ℂ)
    _ = (-(t : ℂ) * Complex.I) + (0 : ℂ) := by
      exact congrArg (fun z : ℂ => (-(t : ℂ) * Complex.I) + z) (neg_add_cancel (1 : ℂ))
    _ = -(t : ℂ) * Complex.I := by
      exact add_zero (-(t : ℂ) * Complex.I)

/-- The logarithmic-phase exponent is not the singular exponent `-1` on the
public range `1 ≤ ‖t‖`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_ne_neg_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    -boundaryLineOnePointRealParam t ≠ (-1 : ℂ) := by
  intro h
  have hadd :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        (-1 : ℂ) + (1 : ℂ) :=
    congrArg (fun z : ℂ => z + (1 : ℂ)) h
  have hleft :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        -(t : ℂ) * Complex.I :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one t
  have hright :
      (-1 : ℂ) + (1 : ℂ) = (0 : ℂ) :=
    neg_add_cancel (1 : ℂ)
  have htI_zero :
      -(t : ℂ) * Complex.I = (0 : ℂ) :=
    Eq.trans hleft.symm (Eq.trans hadd hright)
  have hneg_t_zero : -t = 0 := by
    have him_eq :
        (-(t : ℂ) * Complex.I).im = ((0 : ℂ) : ℂ).im :=
      congrArg Complex.im htI_zero
    have hleft_im :
        (-(t : ℂ) * Complex.I).im = -t := by
      calc
        (-(t : ℂ) * Complex.I).im =
            (-(t : ℂ)).re := by
          exact Complex.mul_I_im (-(t : ℂ))
        _ = -((t : ℂ).re) := by
          exact Complex.neg_re (t : ℂ)
        _ = -t := by
          exact congrArg Neg.neg (Complex.ofReal_re t)
    have hright_im :
        ((0 : ℂ) : ℂ).im = (0 : ℝ) :=
      Complex.zero_im
    exact Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have ht_zero : t = 0 := by
    calc
      t = -(-t) := by
        exact (neg_neg t).symm
      _ = -(0 : ℝ) := by
        exact congrArg Neg.neg hneg_t_zero
      _ = 0 := by
        exact neg_zero
  have hnorm_zero : ‖t‖ = (0 : ℝ) :=
    congrArg norm ht_zero
  have hzero_lt_one : (0 : ℝ) < 1 :=
    zero_lt_one
  have hnot : ¬ ((1 : ℝ) ≤ 0) :=
    not_le.mpr hzero_lt_one
  exact hnot (Eq.subst (motive := fun r : ℝ => (1 : ℝ) ≤ r) hnorm_zero ht)

/-- The positive post-cutoff interval avoids the origin. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (0 : ℝ) ∉
      [[(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)), (((M : ℕ) : ℝ))]] := by
  intro hzero_mem
  have hzero_pos :
      (0 : ℝ) < 0 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hzero_mem
  exact lt_irrefl (0 : ℝ) hzero_pos

/-- Direct `integral_cpow` evaluation before normalizing the endpoint exponent. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_rawCpowAntiderivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^
            ((-boundaryLineOnePointRealParam t) + (1 : ℂ))) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            ((-boundaryLineOnePointRealParam t) + (1 : ℂ)))) /
        ((-boundaryLineOnePointRealParam t) + (1 : ℂ)) := by
  exact
    integral_cpow
      (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (b := (((M : ℕ) : ℝ)))
      (r := -boundaryLineOnePointRealParam t)
      (Or.inr
        ⟨boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_ne_neg_one
            t ht,
          boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
            t hM⟩)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_antiderivativeDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I) := by
  have hraw :
      (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
        (((((M : ℕ) : ℝ) : ℂ) ^
              ((-boundaryLineOnePointRealParam t) + (1 : ℂ))) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              ((-boundaryLineOnePointRealParam t) + (1 : ℂ)))) /
          ((-boundaryLineOnePointRealParam t) + (1 : ℂ)) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_rawCpowAntiderivative
      t ht hM
  have hexp :
      (-boundaryLineOnePointRealParam t) + (1 : ℂ) =
        -(t : ℂ) * Complex.I :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_exponent_add_one t
  exact
    Eq.trans hraw
      (congrArg
        (fun z : ℂ =>
          let upper : ℂ := (((M : ℕ) : ℝ) : ℂ)
          let lower : ℂ := ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ))
          ((upper ^ z) - (lower ^ z)) / z)
        hexp)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_antiderivativeDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
      (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I) := by
  exact Eq.trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_intervalIntegral_ownerGap
      t hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_intervalIntegral_eq_antiderivativeDifference_ownerGap
      t ht hM)

/-- Endpoint norm estimate for the antiderivative difference. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_antiderivativeDifference_norm_le_two_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) /
        (-(t : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) := by
  let A : ℂ := (((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let B : ℂ :=
    ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let D : ℂ := -(t : ℂ) * Complex.I
  have hA : ‖A‖ ≤ (1 : ℝ) :=
    logarithmicPhase_nat_sample_norm_le_one t M
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    logarithmicPhase_nat_sample_norm_le_one t ⌊2 + ‖t‖⌋₊
  have hnum_triangle : ‖A - B‖ ≤ ‖A‖ + ‖B‖ :=
    norm_sub_le A B
  have hnum_add_le_two : ‖A‖ + ‖B‖ ≤ (2 : ℝ) := by
    calc
      ‖A‖ + ‖B‖ ≤ (1 : ℝ) + 1 :=
        add_le_add hA hB
      _ = (2 : ℝ) := by
        exact one_add_one_eq_two
  have hnum_le_two : ‖A - B‖ ≤ (2 : ℝ) :=
    le_trans hnum_triangle hnum_add_le_two
  have hD_norm : ‖D‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hquot_norm : ‖(A - B) / D‖ = ‖A - B‖ / ‖D‖ :=
    norm_div (A - B) D
  have hquot_le_two_div_normD : ‖(A - B) / D‖ ≤ (2 : ℝ) / ‖D‖ := by
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (2 : ℝ) / ‖D‖)
      hquot_norm.symm
      (div_le_div_of_nonneg_right hnum_le_two (norm_nonneg D))
  have htwo_div_norm_t_le_two : (2 : ℝ) / ‖t‖ ≤ (2 : ℝ) := by
    have hinv_le_one : ‖t‖⁻¹ ≤ (1 : ℝ) :=
      inv_le_one_of_one_le₀ ht
    calc
      (2 : ℝ) / ‖t‖ = 2 * ‖t‖⁻¹ := by
        exact Eq.trans (div_eq_mul_inv 2 ‖t‖) rfl
      _ ≤ 2 * 1 := by
        exact mul_le_mul_of_nonneg_left hinv_le_one
          (show (0 : ℝ) ≤ 2 from zero_le_two)
      _ = (2 : ℝ) := by
        exact mul_one 2
  have hquot_le_two : ‖(A - B) / D‖ ≤ (2 : ℝ) := by
    exact le_trans hquot_le_two_div_normD
      (Eq.subst
        (motive := fun r : ℝ => (2 : ℝ) / r ≤ (2 : ℝ))
        hD_norm.symm
        htwo_div_norm_t_le_two)
  exact hquot_le_two

/-- Owner sink for the antiderivative estimate
`∫ x^(-1-it) dx = (M^(-it) - N^(-it))/(-it)`.

The sharp elementary bound supplied by this identity is `2 / |t|`, hence `≤ 2`
on the public range `1 ≤ |t|`.  A unit bound would require a stronger lower
bound on `|t|` or extra arithmetic information about the two integer endpoint
phases. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
      (2 : ℝ) := by
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))) =
        (((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) /
          (-(t : ℂ) * Complex.I) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_eq_antiderivativeDifference_ownerGap
      t ht hM
  have hbound :
      ‖(((((M : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) /
          (-(t : ℂ) * Complex.I)‖ ≤
        (2 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_antiderivativeDifference_norm_le_two_ownerGap
      t ht hM
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ (2 : ℝ))
    hidentity.symm
    hbound

/-- Public main-integral component bound with the honest antiderivative
constant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-boundaryLineOnePointRealParam t))‖ ≤
      (2 : ℝ) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mainIntegral_norm_le_two_ownerGap
      t ht hM

/-- Lower half-endpoint component in the post-cutoff Euler-Maclaurin tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_lowerHalfEndpoint_norm_le_one
    (t : ℝ) :
    ‖(-(1 / 2 : ℂ) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t)))‖ ≤
      (1 : ℝ) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_tail_halfEndpoint_norm_le_one
      t
      (boundaryLineOnePointRealParam_cutoff_pos t)
      (-(1 / 2 : ℂ))
      boundaryGrowth_complex_neg_one_div_two_norm_le_one

/-- Upper half-endpoint component in the post-cutoff Euler-Maclaurin tail. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_upperHalfEndpoint_norm_le_one
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-boundaryLineOnePointRealParam t)))‖ ≤
      (1 : ℝ) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_tail_halfEndpoint_norm_le_one
      t
      hM_pos
      (1 / 2 : ℂ)
      boundaryGrowth_complex_one_div_two_norm_le_one

/-- Measure-to-interval transport for the real inverse-square majorant on the
post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_intervalIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      hle).symm

/-- Pointwise derivative of the inverse-square majorant antiderivative on the
positive half-line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_antiderivative_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => -((1 + ‖t‖) * y⁻¹))
      ((1 + ‖t‖) / x ^ 2)
      x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hinv :
      HasDerivAt
        (fun y : ℝ => y⁻¹)
        (-(x ^ 2)⁻¹)
        x :=
    hasDerivAt_inv hx_ne
  have hmul :
      HasDerivAt
        (fun y : ℝ => (1 + ‖t‖) * y⁻¹)
        ((1 + ‖t‖) * (-(x ^ 2)⁻¹))
        x :=
    hinv.const_mul (1 + ‖t‖)
  have hneg :
      HasDerivAt
        (fun y : ℝ => -((1 + ‖t‖) * y⁻¹))
        (-((1 + ‖t‖) * (-(x ^ 2)⁻¹)))
        x :=
    hmul.neg
  have halg :
      (-((1 + ‖t‖) * (-(x ^ 2)⁻¹))) =
        (1 + ‖t‖) / x ^ 2 := by
    calc
      (-((1 + ‖t‖) * (-(x ^ 2)⁻¹))) =
          -(-((1 + ‖t‖) * (x ^ 2)⁻¹)) := by
        exact
          congrArg
            (fun y : ℝ => -y)
            (mul_neg (1 + ‖t‖) ((x ^ 2)⁻¹))
      _ =
          (1 + ‖t‖) * (x ^ 2)⁻¹ := by
        exact neg_neg ((1 + ‖t‖) * (x ^ 2)⁻¹)
      _ = (1 + ‖t‖) / x ^ 2 := by
        exact (div_eq_mul_inv (1 + ‖t‖) (x ^ 2)).symm
  exact halg ▸ hneg

/-- The post-cutoff interval stays in the positive half-line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {x : ℝ}
    (hx :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ))) :
    0 < x := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hinterval :
      x ∈
        Set.Icc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) :=
    (Set.uIcc_of_le hle) ▸ hx
  have hleft_le_x :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    hinterval.1
  have hcutoff_pos_nat : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_pos_real :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos_nat
  exact lt_of_lt_of_le hcutoff_pos_real hleft_le_x

/-- Interval integrability of the inverse-square majorant on the positive
post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    IntervalIntegrable
      (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      volume
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ)) := by
  let a : ℝ := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
  let b : ℝ := (((M : ℕ) : ℝ))
  have hden_ne :
      ∀ x ∈ Set.uIcc a b, x ^ 2 ≠ 0 := by
    intro x hx
    have hx_pos :
        0 < x :=
      boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
        t
        hM
        hx
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    exact pow_ne_zero 2 hx_ne
  have hnum_cont :
      ContinuousOn
        (fun _x : ℝ => (1 + ‖t‖))
        (Set.uIcc a b) :=
    continuous_const.continuousOn
  have hden_cont :
      ContinuousOn
        (fun x : ℝ => x ^ 2)
        (Set.uIcc a b) :=
    (continuous_id.pow 2).continuousOn
  have hquot_cont :
      ContinuousOn
        (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
        (Set.uIcc a b) :=
    hnum_cont.div hden_cont hden_ne
  exact hquot_cont.intervalIntegrable

/-- Interval-integral FTC before endpoint algebra normalization. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_rawAntiderivative
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (-((1 + ‖t‖) * (((M : ℕ) : ℝ))⁻¹)) -
        (-((1 + ‖t‖) * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx =>
        boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_antiderivative_hasDerivAt
          t
          (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
            t hM hx))
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
        t hM)

/-- Endpoint algebra for the inverse-square antiderivative. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_rawAntiderivative_eq_endpointDifference
    (t : ℝ)
    {M : ℕ} :
    (-((1 + ‖t‖) * (((M : ℕ) : ℝ))⁻¹)) -
        (-((1 + ‖t‖) * (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  let c : ℝ := 1 + ‖t‖
  let a : ℝ := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹
  let b : ℝ := (((M : ℕ) : ℝ))⁻¹
  calc
    (-(c * b)) - (-(c * a)) = (-(c * b)) + (c * a) := by
      exact sub_neg_eq_add (-(c * b)) (c * a)
    _ = (c * a) + (-(c * b)) := by
      exact add_comm (-(c * b)) (c * a)
    _ = (c * a) - (c * b) := by
      exact (sub_eq_add_neg (c * a) (c * b)).symm
    _ = c * (a - b) := by
      exact (mul_sub c a b).symm

/-- Interval-integral FTC identity for the real inverse-square majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_endpointDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  exact Eq.trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_rawAntiderivative
      t hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_rawAntiderivative_eq_endpointDifference
      t)

/-- The boundary-line parameter has size at most the elementary scalar
`1 + |t|`. -/
theorem boundaryLineOnePointRealParam_norm_le_one_add_norm
    (t : ℝ) :
    ‖boundaryLineOnePointRealParam t‖ ≤ (1 : ℝ) + ‖t‖ := by
  have hparam :
      boundaryLineOnePointRealParam t = (1 : ℂ) + (t : ℂ) * Complex.I := by
    have hre :
        (boundaryLineOnePointRealParam t).re =
          ((1 : ℂ) + (t : ℂ) * Complex.I).re := by
      calc
        (boundaryLineOnePointRealParam t).re = (1 : ℝ) :=
          boundaryLineOnePointRealParam_re t
        _ = (1 : ℂ).re + (0 : ℝ) := by
          exact (add_zero (1 : ℝ)).symm
        _ = (1 : ℂ).re + (-(t : ℂ).im) := by
          exact congrArg (fun y : ℝ => (1 : ℂ).re + y)
            (Eq.trans neg_zero.symm
              (congrArg Neg.neg (Complex.ofReal_im t).symm))
        _ = (1 : ℂ).re + ((t : ℂ) * Complex.I).re := by
          exact congrArg (fun y : ℝ => (1 : ℂ).re + y)
            (Complex.mul_I_re (t : ℂ)).symm
        _ = ((1 : ℂ) + (t : ℂ) * Complex.I).re := by
          exact (Complex.add_re (1 : ℂ) ((t : ℂ) * Complex.I)).symm
    have him :
        (boundaryLineOnePointRealParam t).im =
          ((1 : ℂ) + (t : ℂ) * Complex.I).im := by
      calc
        (boundaryLineOnePointRealParam t).im = t :=
          boundaryLineOnePointRealParam_im t
        _ = (0 : ℝ) + t := by
          exact (zero_add t).symm
        _ = (1 : ℂ).im + (t : ℂ).re := by
          exact congrArg₂ (fun u v : ℝ => u + v)
            (Complex.ofReal_im 1).symm
            (Complex.ofReal_re t).symm
        _ = (1 : ℂ).im + ((t : ℂ) * Complex.I).im := by
          exact congrArg (fun y : ℝ => (1 : ℂ).im + y)
            (Complex.mul_I_im (t : ℂ)).symm
        _ = ((1 : ℂ) + (t : ℂ) * Complex.I).im := by
          exact (Complex.add_im (1 : ℂ) ((t : ℂ) * Complex.I)).symm
    exact Complex.ext hre him
  have htriangle :
      ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤
        ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ :=
    norm_add_le (1 : ℂ) ((t : ℂ) * Complex.I)
  have hone : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    norm_one
  have htI : ‖(t : ℂ) * Complex.I‖ = ‖t‖ := by
    have hmul :
        ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
      norm_mul (t : ℂ) Complex.I
    have hI : ‖Complex.I‖ = (1 : ℝ) :=
      RCLike.norm_I_of_ne_zero (K := ℂ) Complex.I_ne_zero
    have ht : ‖(t : ℂ)‖ = ‖t‖ :=
      RCLike.norm_ofReal t
    calc
      ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
        hmul
      _ = ‖(t : ℂ)‖ * (1 : ℝ) := by
        exact congrArg (fun y : ℝ => ‖(t : ℂ)‖ * y) hI
      _ = ‖(t : ℂ)‖ := by
        exact mul_one ‖(t : ℂ)‖
      _ = ‖t‖ :=
        ht
  have hright :
      ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ = (1 : ℝ) + ‖t‖ := by
    exact congrArg₂ HAdd.hAdd hone htI
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ (1 : ℝ) + ‖t‖)
    hparam.symm
    (Eq.subst
      (motive := fun r : ℝ => ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ ≤ r)
      hright
      htriangle)

/-- The post-cutoff `Ioc` interval lies above `1`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_le_of_mem_Ioc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {x : ℝ}
    (hx :
      x ∈
        Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ))) :
    (1 : ℝ) ≤ x := by
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hcutoff_le_x :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hcutoff_ge_one :
      (1 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
    have hcutoff_pos_nat : 0 < ⌊2 + ‖t‖⌋₊ :=
      boundaryLineOnePointRealParam_cutoff_pos t
    have hone_le_nat : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
      Nat.succ_le_of_lt hcutoff_pos_nat
    exact Nat.cast_le.mpr hone_le_nat
  exact le_trans hcutoff_ge_one hcutoff_le_x

/-- Positive real powers with exponent `-2` are inverse squares. -/
theorem boundaryGrowth_real_rpow_neg_two_eq_inv_sq
    {x : ℝ}
    (hx : 0 < x) :
    x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  have hneg :
      x ^ (-(2 : ℝ)) = (x ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (le_of_lt hx) 2
  have htwo :
      x ^ (2 : ℝ) = x ^ (2 : ℕ) :=
    Real.rpow_natCast x 2
  exact Eq.trans hneg (congrArg Inv.inv htwo)

/-- Pointwise norm of the Bernoulli derivative kernel before replacing
`x ^ (-2)` by the inverse-square scalar. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliKernel_norm_le_one_add_norm_mul_rpow
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
        (1 + ‖t‖) * x ^ (-(2 : ℝ)) := by
  intro x hx
  have hx_one :
      (1 : ℝ) ≤ x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_le_of_mem_Ioc
      t hM hx
  have hx_pos :
      0 < x :=
    lt_of_lt_of_le zero_lt_one hx_one
  have hB :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hparam :
      ‖boundaryLineOnePointRealParam t‖ ≤ (1 : ℝ) + ‖t‖ :=
    boundaryLineOnePointRealParam_norm_le_one_add_norm t
  have hre :
      (1 : ℝ) ≤ (boundaryLineOnePointRealParam t).re := by
    exact le_of_eq (boundaryLineOnePointRealParam_re t).symm
  have hcpow :
      ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤
        x ^ (-(1 + 1 : ℝ)) :=
    eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
      hx_pos hx_one (boundaryLineOnePointRealParam t) hre
  have hexponent :
      (-(1 + 1 : ℝ)) = (-(2 : ℝ)) := by
    exact congrArg Neg.neg (one_add_one_eq_two : (1 : ℝ) + 1 = 2)
  have hcpow_two :
      ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤
        x ^ (-(2 : ℝ)) :=
    Eq.subst
      (motive := fun e : ℝ =>
        ‖((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))‖ ≤ x ^ e)
      hexponent
      hcpow
  have hpow_nonneg :
      0 ≤ x ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hx_pos) (-(2 : ℝ))
  have hparam_nonneg :
      0 ≤ ‖boundaryLineOnePointRealParam t‖ :=
    norm_nonneg (boundaryLineOnePointRealParam t)
  have hinner_bound :
      ‖-boundaryLineOnePointRealParam t *
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))‖ ≤
        ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)) := by
    have hinner_norm :
        ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ =
          ‖boundaryLineOnePointRealParam t‖ *
            ‖((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))‖ := by
      have hmul :
          ‖-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1)))‖ =
            ‖-boundaryLineOnePointRealParam t‖ *
              ‖((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))‖ :=
        norm_mul
          (-boundaryLineOnePointRealParam t)
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))
      have hneg :
          ‖-boundaryLineOnePointRealParam t‖ =
            ‖boundaryLineOnePointRealParam t‖ :=
        norm_neg (boundaryLineOnePointRealParam t)
      exact Eq.trans hmul
        (congrArg
          (fun r : ℝ =>
            r *
              ‖((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))‖)
          hneg)
    have hproduct :
        ‖boundaryLineOnePointRealParam t‖ *
            ‖((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))‖ ≤
          ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)) :=
      mul_le_mul hparam hcpow_two
        (norm_nonneg
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1))))
        hparam_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)))
      hinner_norm.symm
      hproduct
  have houter_norm :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ =
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
          ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ :=
    norm_mul
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
      (-boundaryLineOnePointRealParam t *
        (((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))))
  have hproduct :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
          ‖-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1)))‖ ≤
        1 * (((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ))) :=
    mul_le_mul hB hinner_bound
      (norm_nonneg
        (-boundaryLineOnePointRealParam t *
          (((x : ℝ) : ℂ) ^
            (-(boundaryLineOnePointRealParam t + 1)))))
      (zero_le_one : (0 : ℝ) ≤ 1)
  exact Eq.subst
    (motive := fun r : ℝ =>
      r ≤ ((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ)))
    houter_norm.symm
    (Eq.subst
      (motive := fun r : ℝ =>
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1)))‖ ≤ r)
      (one_mul (((1 : ℝ) + ‖t‖) * x ^ (-(2 : ℝ))))
      hproduct)

/-- Scalar normalization for the pointwise Bernoulli derivative majorant on
the positive post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_add_norm_mul_rpow_le_realMajorant
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (1 + ‖t‖) * x ^ (-(2 : ℝ)) ≤
        (1 + ‖t‖) / x ^ 2 := by
  intro x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hrpow :
      x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ :=
    boundaryGrowth_real_rpow_neg_two_eq_inv_sq hx_pos
  have hdiv :
      (1 + ‖t‖) / x ^ 2 = (1 + ‖t‖) * (x ^ 2)⁻¹ :=
    div_eq_mul_inv (1 + ‖t‖) (x ^ 2)
  exact le_of_eq
    (Eq.trans
      (congrArg (fun y : ℝ => (1 + ‖t‖) * y) hrpow)
      hdiv.symm)

/-- Norm domination for the periodic-Bernoulli remainder by the elementary
real derivative majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_pointwise_norm_le_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
        (1 + ‖t‖) / x ^ 2 := by
  intro x hx
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliKernel_norm_le_one_add_norm_mul_rpow
      t hM x hx)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_one_add_norm_mul_rpow_le_realMajorant
      t hM x hx)

/-- Integrability of the scalar inverse-square majorant on the post-cutoff
`Ioc` interval, in the form required by Bochner norm domination. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_integrable_restrict_Ioc
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    Integrable
      (fun x : ℝ => (1 + ‖t‖) / x ^ 2)
      (volume.restrict
        (Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)))) := by
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegrable
        t hM)

/-- Bochner norm domination for the post-cutoff Bernoulli remainder over the
finite interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_core
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hpoint :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
          (1 + ‖t‖) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (-boundaryLineOnePointRealParam t *
        (((x : ℝ) : ℂ) ^
          (-(boundaryLineOnePointRealParam t + 1))))
  let g : ℝ → ℝ := fun x => (1 + ‖t‖) / x ^ 2
  have hg :
      Integrable g (volume.restrict s) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_integrable_restrict_Ioc
      t hM
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx => hpoint x hx)
  exact norm_integral_le_of_norm_le hg hbound

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hpoint :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-boundaryLineOnePointRealParam t *
              (((x : ℝ) : ℂ) ^
                (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
          (1 + ‖t‖) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_core
      t hM hpoint

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_realMajorant_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2 := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_integral_norm_le_of_pointwise_realMajorant_ownerGap
      t ht hM
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_pointwise_norm_le_realMajorant_ownerGap
        t ht hM)

/-- The canonical Abel cutoff is at least `1 + |t|` after coercion to `ℝ`. -/
theorem boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff
    (t : ℝ) :
    (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) := by
  have hsub_lt :
      (2 + ‖t‖ : ℝ) - 1 < ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor (2 + ‖t‖)
  have hone_add_eq :
      (1 : ℝ) + ‖t‖ = (2 + ‖t‖ : ℝ) - 1 := by
    calc
      (1 : ℝ) + ‖t‖ = (2 - 1) + ‖t‖ := by
        exact congrArg (fun y : ℝ => y + ‖t‖)
          (show (1 : ℝ) = 2 - 1 by
            exact eq_sub_iff_add_eq.mpr
              (one_add_one_eq_two : (1 : ℝ) + 1 = 2))
      _ = (2 + ‖t‖) - 1 := by
        exact (sub_add_eq_add_sub 2 1 ‖t‖).symm
  exact (le_of_eq hone_add_eq).trans hsub_lt.le

/-- Sharp real-variable cutoff estimate for the Bernoulli-remainder derivative
majorant.

This is the scalar calculus core: since
`⌊2 + |t|⌋₊ ≥ 1 + |t|`, the finite tail of `(1 + |t|) / x^2` from the
canonical cutoff is bounded by one. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_endpointDifference_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) =
      (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) := by
  have htransport :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) =
        ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_intervalIntegral
      t hM
  exact Eq.trans
    htransport
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_intervalIntegral_eq_endpointDifference_ownerGap
      t ht hM)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_cutoffRatio_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
      (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) := by
  have hM_nonneg : 0 ≤ (((M : ℕ) : ℝ) : ℝ) :=
    Nat.cast_nonneg M
  have hM_inv_nonneg : 0 ≤ ((((M : ℕ) : ℝ) : ℝ))⁻¹ :=
    inv_nonneg.mpr hM_nonneg
  have hdrop_upper_endpoint :
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    sub_le_self
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹)
      hM_inv_nonneg
  have hcoefficient_nonneg : 0 ≤ (1 : ℝ) + ‖t‖ :=
    add_nonneg zero_le_one (norm_nonneg t)
  exact
    mul_le_mul_of_nonneg_left
      hdrop_upper_endpoint
      hcoefficient_nonneg

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      1 := by
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have hone_add_norm_pos : 0 < (1 : ℝ) + ‖t‖ := by
    exact lt_of_lt_of_le
      zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg t))
  have hcutoff_pos : 0 < ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    lt_of_lt_of_le hone_add_norm_pos hcutoff_ge
  have hratio_le_one :
      ((1 : ℝ) + ‖t‖) / ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ 1 :=
    (div_le_one₀ hcutoff_pos).mpr hcutoff_ge
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    (div_eq_mul_inv ((1 : ℝ) + ‖t‖) ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
    hratio_le_one

/-- The post-cutoff reciprocal endpoint absorbs the logarithmic frequency.

This is the scalar endpoint estimate used by the reciprocal-drift component of
the finite normalized-kernel block decomposition. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      1 := by
  have hnorm_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
    le_add_of_nonneg_left zero_le_one
  have hcutoff_nonneg :
      0 ≤ ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg ⌊2 + ‖t‖⌋₊)
  have hmul :
      ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
        (1 + ‖t‖) * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) :=
    mul_le_mul_of_nonneg_right hnorm_le_one_add hcutoff_nonneg
  exact le_trans hmul
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
      t ht)

/-- The reciprocal-drift endpoint bound is dominated by the canonical
`2 sqrt(1 + |t|) log(2 + M)` post-cutoff scale. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_two_sqrt_log
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖t‖ * ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹) ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    one_le_mul hsqrt_ge_one hlog_lower_M
  have hscale_ge_one :
      (1 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    calc
      (1 : ℝ) ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
        le_trans hfactor_ge_one
          (mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 2 from one_le_two)
            (mul_nonneg
              (Real.sqrt_nonneg (1 + ‖t‖))
              (le_trans (show (0 : ℝ) ≤ 1 from zero_le_one) hlog_lower_M)))
      _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
        (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
      t ht)
    hscale_ge_one

/-- Nonnegativity of the Abel coefficient weight `|t| / (n - 1)` on the
post-cutoff right-endpoint range. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg
    (t : ℝ)
    (n : ℕ) :
    0 ≤ ‖t‖ / ((((n - 1 : ℕ) : ℕ) : ℝ)) := by
  exact div_nonneg (norm_nonneg t) (Nat.cast_nonneg (n - 1))

/-- Antitonicity of the Abel coefficient weight `|t| / (n - 1)` after the
canonical cutoff. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
    (t : ℝ)
    {k l : ℕ}
    (hk : ⌊2 + ‖t‖⌋₊ < k)
    (hkl : k ≤ l) :
    ‖t‖ / ((((l - 1 : ℕ) : ℕ) : ℝ)) ≤
      ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_k : 1 < k :=
    lt_of_le_of_lt hone_le_cutoff hk
  have hk_pred_pos_nat : 0 < k - 1 :=
    Nat.sub_pos_of_lt hone_lt_k
  have hk_pred_pos : 0 < (((k - 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hk_pred_pos_nat
  have hpred_le : k - 1 ≤ l - 1 :=
    Nat.sub_le_sub_right hkl 1
  have hpred_le_real :
      (((k - 1 : ℕ) : ℝ)) ≤ (((l - 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hpred_le
  exact
    div_le_div_of_nonneg_left
      (norm_nonneg t)
      hk_pred_pos
      hpred_le_real

/-- Finite variation of the Abel coefficient weight `|t| / (n - 1)` on the
post-cutoff right-endpoint range is at most one. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖t‖ / ((((M + 1 - 1 : ℕ) : ℕ) : ℝ))) +
        ∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) -
            ‖t‖ / (((((k + 1) - 1 : ℕ) : ℕ) : ℝ))) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let w : ℕ → ℝ := fun n => ‖t‖ / ((((n - 1 : ℕ) : ℕ) : ℝ))
  have htelescopes :
      w (M + 1) + ∑ k ∈ Finset.Ioc C M, (w k - w (k + 1)) =
        w (C + 1) :=
    finset_Ioc_adjacent_difference_telescope w C M hM
  have hC_succ :
      C + 1 - 1 = C :=
    Nat.add_sub_cancel C 1
  have hfirst :
      w (C + 1) = ‖t‖ * ((((C : ℕ) : ℝ))⁻¹) := by
    calc
      w (C + 1) =
          ‖t‖ / ((((C + 1 - 1 : ℕ) : ℕ) : ℝ)) := rfl
      _ = ‖t‖ / (((C : ℕ) : ℝ)) := by
        exact congrArg (fun n : ℕ => ‖t‖ / (((n : ℕ) : ℝ))) hC_succ
      _ = ‖t‖ * ((((C : ℕ) : ℝ))⁻¹) := by
        exact div_eq_mul_inv ‖t‖ (((C : ℕ) : ℝ))
  have hfirst_le_one :
      w (C + 1) ≤ 1 :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      hfirst.symm
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_cutoff_inv_le_one
        t ht)
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      htelescopes.symm
      hfirst_le_one

/-- One-step reciprocal-square domination by the adjacent reciprocal
difference.

This is the local scalar telescope used for the reciprocal-drift half of the
normalized Bernoulli block cancellation.  For the post-cutoff blocks the
left endpoint is at least two, so the inverse-square term at `m + 1` is
absorbed by `1 / m - 1 / (m + 1)`. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
    {m : ℕ}
    (hm : 0 < m) :
    (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ))) ≤
      (1 : ℝ) / ((m : ℕ) : ℝ) -
        (1 : ℝ) / (((m + 1 : ℕ) : ℝ)) := by
  let a : ℝ := ((m : ℕ) : ℝ)
  let b : ℝ := (((m + 1 : ℕ) : ℝ))
  have ha_pos : 0 < a :=
    Nat.cast_pos.mpr hm
  have hb_pos : 0 < b :=
    Nat.cast_pos.mpr (Nat.succ_pos m)
  have ha_le_b : a ≤ b :=
    Nat.cast_le.mpr (Nat.le_succ m)
  have hden_pos : 0 < a * b :=
    mul_pos ha_pos hb_pos
  have hsq_pos : 0 < b * b :=
    mul_pos hb_pos hb_pos
  have hden_le_sq : a * b ≤ b * b :=
    mul_le_mul_of_nonneg_right ha_le_b (le_of_lt hb_pos)
  have hinv_le :
      (1 : ℝ) / (b * b) ≤ (1 : ℝ) / (a * b) :=
    one_div_le_one_div_of_le hden_pos hden_le_sq
  have hdiff :
      (1 : ℝ) / a - (1 : ℝ) / b = (1 : ℝ) / (a * b) := by
    have hleft :
        (1 : ℝ) / a = b / (a * b) := by
      have hcancel : b / (a * b) = (1 : ℝ) / a := by
        calc
          b / (a * b) = b * (a * b)⁻¹ := by
            exact div_eq_mul_inv b (a * b)
          _ = b * (a⁻¹ * b⁻¹) := by
            exact congrArg (fun r : ℝ => b * r) (mul_inv_rev a b)
          _ = (b * b⁻¹) * a⁻¹ := by
            calc
              b * (a⁻¹ * b⁻¹) = b * (b⁻¹ * a⁻¹) := by
                exact congrArg (fun r : ℝ => b * r) (mul_comm a⁻¹ b⁻¹)
              _ = (b * b⁻¹) * a⁻¹ := by
                exact (mul_assoc b b⁻¹ a⁻¹).symm
          _ = 1 * a⁻¹ := by
            exact congrArg (fun r : ℝ => r * a⁻¹) (mul_inv_cancel₀ hb_pos.ne')
          _ = a⁻¹ := by
            exact one_mul a⁻¹
          _ = (1 : ℝ) / a := by
            exact (one_div a).symm
      exact hcancel.symm
    have hright :
        (1 : ℝ) / b = a / (a * b) := by
      have hcancel : a / (a * b) = (1 : ℝ) / b := by
        calc
          a / (a * b) = a * (a * b)⁻¹ := by
            exact div_eq_mul_inv a (a * b)
          _ = a * (b⁻¹ * a⁻¹) := by
            exact congrArg (fun r : ℝ => a * r)
              (Eq.trans (mul_inv_rev a b) (mul_comm a⁻¹ b⁻¹))
          _ = (a * a⁻¹) * b⁻¹ := by
            calc
              a * (b⁻¹ * a⁻¹) = a * (a⁻¹ * b⁻¹) := by
                exact congrArg (fun r : ℝ => a * r) (mul_comm b⁻¹ a⁻¹)
              _ = (a * a⁻¹) * b⁻¹ := by
                exact (mul_assoc a a⁻¹ b⁻¹).symm
          _ = 1 * b⁻¹ := by
            exact congrArg (fun r : ℝ => r * b⁻¹) (mul_inv_cancel₀ ha_pos.ne')
          _ = b⁻¹ := by
            exact one_mul b⁻¹
          _ = (1 : ℝ) / b := by
            exact (one_div b).symm
      exact hcancel.symm
    calc
      (1 : ℝ) / a - (1 : ℝ) / b =
          b / (a * b) - (1 : ℝ) / b := by
        exact congrArg (fun r : ℝ => r - (1 : ℝ) / b) hleft
      _ = b / (a * b) - a / (a * b) := by
        exact congrArg (fun r : ℝ => b / (a * b) - r) hright
      _ = (b - a) / (a * b) := by
        exact (sub_div b a (a * b)).symm
      _ = (1 : ℝ) / (a * b) := by
        have hsucc : b = a + 1 := by
          exact Nat.cast_add_one m
        have hsub_one : b - a = (1 : ℝ) := by
          calc
            b - a = (a + 1) - a := by
              exact congrArg (fun r : ℝ => r - a) hsucc
            _ = 1 := by
              exact add_sub_cancel_left a 1
        exact congrArg (fun r : ℝ => r / (a * b)) hsub_one
  exact Eq.subst
    (motive := fun r : ℝ => (1 : ℝ) / (b * b) ≤ r)
    hdiff.symm
    hinv_le

/-- Finite reciprocal-square tails are bounded by the first reciprocal via
the adjacent-difference telescope. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_Ioc_sum_le_reciprocal_start
    {C M : ℕ}
    (hC : 0 < C)
    (hM : C ≤ M) :
    (∑ k ∈ Finset.Ioc C M,
        (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / ((C : ℕ) : ℝ) := by
  let u : ℕ → ℝ := fun k : ℕ =>
    (1 : ℝ) / (((k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ)))
  let v : ℕ → ℝ := fun k : ℕ =>
    (1 : ℝ) / ((k : ℕ) : ℝ)
  have hpoint :
      ∀ k : ℕ, k ∈ Finset.Ioc C M → u k ≤ v k - v (k + 1) := by
    intro k hk
    have hC_lt_k : C < k :=
      (Finset.mem_Ioc.mp hk).left
    have hk_pos : 0 < k :=
      lt_of_lt_of_le hC (Nat.le_of_lt hC_lt_k)
    exact
      boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
        hk_pos
  have hsum :
      (∑ k ∈ Finset.Ioc C M, u k) ≤
        ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) :=
    Finset.sum_le_sum (fun k hk => hpoint k hk)
  have htelescopes :
      v (M + 1) + ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) =
        v (C + 1) :=
    finset_Ioc_adjacent_difference_telescope v C M hM
  have htail_nonneg :
      0 ≤ v (M + 1) := by
    have hsucc_pos : 0 < (M + 1 : ℕ) :=
      Nat.succ_pos M
    have hcast_pos : 0 < (((M + 1 : ℕ) : ℝ)) :=
      Nat.cast_pos.mpr hsucc_pos
    exact one_div_nonneg.mpr (le_of_lt hcast_pos)
  have htelescoped_le :
      ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) ≤ v (C + 1) := by
    calc
      ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) ≤
          v (M + 1) + ∑ k ∈ Finset.Ioc C M, (v k - v (k + 1)) :=
        le_add_of_nonneg_left htail_nonneg
      _ = v (C + 1) := htelescopes
  have hstart_le :
      v (C + 1) ≤ (1 : ℝ) / ((C : ℕ) : ℝ) := by
    have hC_cast_pos : 0 < ((C : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hC
    have hC_le_succ : ((C : ℕ) : ℝ) ≤ (((C + 1 : ℕ) : ℝ)) :=
      Nat.cast_le.mpr (Nat.le_succ C)
    exact one_div_le_one_div_of_le hC_cast_pos hC_le_succ
  exact le_trans hsum (le_trans htelescoped_le hstart_le)

/-- The predecessor of the canonical cutoff still absorbs the logarithmic
frequency.

This is the endpoint scalar estimate needed after the reciprocal-square
telescope is shifted to the right-endpoint local blocks: the block indexed by
`n` has left endpoint `n - 1`, so the reciprocal-square tail starts at
`⌊2 + |t|⌋₊ - 1`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_pred_cutoff_inv_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖t‖ * (((((⌊2 + ‖t‖⌋₊ - 1 : ℕ) : ℕ) : ℝ))⁻¹) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((C : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have htwo_le_one_add_norm :
      (2 : ℝ) ≤ (1 : ℝ) + ‖t‖ := by
    have htwo_eq : (2 : ℝ) = 1 + 1 :=
      (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ) + ‖t‖)
      htwo_eq
      (add_le_add_left ht 1)
  have htwo_le_C_real : (2 : ℝ) ≤ ((C : ℕ) : ℝ) :=
    le_trans htwo_le_one_add_norm hcutoff_ge
  have htwo_le_C_nat : 2 ≤ C := by
    have hcast :
        ((2 : ℕ) : ℝ) ≤ ((C : ℕ) : ℝ) :=
      htwo_le_C_real
    exact Nat.cast_le.mp hcast
  have hone_le_C_nat : 1 ≤ C :=
    le_trans
      (show 1 ≤ 2 from Nat.succ_le_succ (Nat.succ_le_succ Nat.zero_le))
      htwo_le_C_nat
  have hpred_cast :
      (((C - 1 : ℕ) : ℝ)) = ((C : ℕ) : ℝ) - 1 :=
    Nat.cast_sub hone_le_C_nat
  have hnorm_eq_sub :
      ‖t‖ = ((1 : ℝ) + ‖t‖) - 1 := by
    exact (add_sub_cancel_left 1 ‖t‖).symm
  have hnorm_le_pred :
      ‖t‖ ≤ (((C - 1 : ℕ) : ℝ)) := by
    have hsub_le :
        ((1 : ℝ) + ‖t‖) - 1 ≤ ((C : ℕ) : ℝ) - 1 :=
      sub_le_sub_right hcutoff_ge 1
    exact Eq.subst
      (motive := fun r : ℝ => ‖t‖ ≤ r)
      hpred_cast.symm
      (Eq.subst
        (motive := fun r : ℝ => r ≤ ((C : ℕ) : ℝ) - 1)
        hnorm_eq_sub.symm
        hsub_le)
  have hpred_pos :
      0 < (((C - 1 : ℕ) : ℝ)) :=
    lt_of_lt_of_le
      (lt_of_lt_of_le zero_lt_one ht)
      hnorm_le_pred
  have hratio :
      ‖t‖ / (((C - 1 : ℕ) : ℝ)) ≤ 1 :=
    (div_le_one₀ hpred_pos).mpr hnorm_le_pred
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    (div_eq_mul_inv ‖t‖ (((C - 1 : ℕ) : ℝ)))
    hratio

/-- Right-endpoint reciprocal-square tails are bounded by the reciprocal of
the predecessor of the first endpoint.

This is the shifted telescope used by the selected reciprocal-variation
estimate: for blocks `n ∈ (C,M]`, the reciprocal movement is controlled by
the square of the left endpoint `n - 1`. -/
theorem boundaryLineOnePointRealParam_reciprocalSquare_Ioc_pred_sum_le_reciprocal_pred_start
    {C M : ℕ}
    (hC : 1 < C)
    (hM : C ≤ M) :
    (∑ n ∈ Finset.Ioc C M,
        (1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) ≤
      (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) := by
  let u : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) /
      (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))
  let v : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) / (((n - 2 : ℕ) : ℝ))
  have hpoint :
      ∀ n : ℕ, n ∈ Finset.Ioc C M → u n ≤ v n - v (n + 1) := by
    intro n hn
    have hC_lt_n : C < n :=
      (Finset.mem_Ioc.mp hn).left
    have htwo_lt_n : 2 < n :=
      lt_of_lt_of_le
        (lt_of_lt_of_le (show 1 < C from hC) (Nat.le_of_lt hC_lt_n))
        (Nat.le_refl n)
    have hpred_pos : 0 < n - 2 :=
      Nat.sub_pos_of_lt htwo_lt_n
    have hsucc_pred :
        n - 2 + 1 = n - 1 := by
      exact Nat.succ_sub (Nat.succ_le_of_lt htwo_lt_n) 1
    have hsucc_right :
        n + 1 - 2 = n - 1 := by
      have htwo_le_n : 2 ≤ n :=
        Nat.le_of_lt htwo_lt_n
      calc
        n + 1 - 2 = n - 1 := by
          exact Nat.add_sub_add_right n 1 1
    have hraw :
        (1 : ℝ) /
            ((((n - 2) + 1 : ℕ) : ℝ) *
              ((((n - 2) + 1 : ℕ) : ℝ))) ≤
          (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)) :=
      boundaryLineOnePointRealParam_reciprocalSquare_le_adjacent_reciprocal_difference
        hpred_pos
    have hleft :
        (1 : ℝ) /
            ((((n - 2) + 1 : ℕ) : ℝ) *
              ((((n - 2) + 1 : ℕ) : ℝ))) =
          u n := by
      exact congrArg
        (fun k : ℕ =>
          (1 : ℝ) / (((k : ℕ) : ℝ) * (((k : ℕ) : ℝ))))
        hsucc_pred
    have hright :
        (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)) =
          v n - v (n + 1) := by
      exact congrArg
        (fun k : ℕ =>
          (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
            (1 : ℝ) / (((k : ℕ) : ℝ)))
        (Eq.trans hsucc_pred hsucc_right.symm)
    exact Eq.subst
      (motive := fun r : ℝ => u n ≤ r)
      hright
      (Eq.subst
        (motive := fun r : ℝ =>
          r ≤
            (1 : ℝ) / (((n - 2 : ℕ) : ℝ)) -
              (1 : ℝ) / (((((n - 2) + 1 : ℕ) : ℕ) : ℝ)))
        hleft
        hraw)
  have hsum :
      (∑ n ∈ Finset.Ioc C M, u n) ≤
        ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) :=
    Finset.sum_le_sum (fun n hn => hpoint n hn)
  have htelescopes :
      v (M + 1) + ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) =
        v (C + 1) :=
    finset_Ioc_adjacent_difference_telescope v C M hM
  have htail_nonneg :
      0 ≤ v (M + 1) := by
    exact one_div_nonneg.mpr (Nat.cast_nonneg (M + 1 - 2))
  have htelescoped_le :
      ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤ v (C + 1) := by
    calc
      ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤
          v (M + 1) + ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) :=
        le_add_of_nonneg_left htail_nonneg
      _ = v (C + 1) := htelescopes
  have hstart :
      v (C + 1) = (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) := by
    have hnat : C + 1 - 2 = C - 1 := by
      exact Nat.add_sub_add_right C 1 1
    exact congrArg
      (fun k : ℕ => (1 : ℝ) / (((k : ℕ) : ℝ)))
      hnat
  exact le_trans hsum
    (Eq.subst
      (motive := fun r : ℝ =>
        ∑ n ∈ Finset.Ioc C M, (v n - v (n + 1)) ≤ r)
      hstart
      htelescoped_le)

/-- Canonical post-cutoff reciprocal-variation scalar sum.

After multiplying the shifted reciprocal-square telescope by `|t|`, the
predecessor-cutoff endpoint estimate absorbs the whole selected local
reciprocal-variation contribution into `1`. -/
theorem boundaryLineOnePointRealParam_reciprocalVariation_selected_Ioc_sum_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ‖t‖ *
          ((1 : ℝ) /
            (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ))))) ≤
      1 := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let u : ℕ → ℝ := fun n : ℕ =>
    (1 : ℝ) /
      (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((C : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have htwo_le_one_add_norm :
      (2 : ℝ) ≤ (1 : ℝ) + ‖t‖ := by
    have htwo_eq : (2 : ℝ) = 1 + 1 :=
      (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ) + ‖t‖)
      htwo_eq
      (add_le_add_left ht 1)
  have htwo_le_C_real : (2 : ℝ) ≤ ((C : ℕ) : ℝ) :=
    le_trans htwo_le_one_add_norm hcutoff_ge
  have htwo_le_C_nat : 2 ≤ C := by
    have hcast :
        ((2 : ℕ) : ℝ) ≤ ((C : ℕ) : ℝ) :=
      htwo_le_C_real
    exact Nat.cast_le.mp hcast
  have hone_lt_C : 1 < C :=
    lt_of_lt_of_le (show 1 < 2 from Nat.lt.base 1) htwo_le_C_nat
  have hsum_u :
      (∑ n ∈ Finset.Ioc C M, u n) ≤
        (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_reciprocalSquare_Ioc_pred_sum_le_reciprocal_pred_start
      hone_lt_C hM
  have hsum_mul :
      (∑ n ∈ Finset.Ioc C M, ‖t‖ * u n) =
        ‖t‖ * (∑ n ∈ Finset.Ioc C M, u n) :=
    (Finset.mul_sum (Finset.Ioc C M) (fun n : ℕ => u n) ‖t‖).symm
  have hmul_le :
      ‖t‖ * (∑ n ∈ Finset.Ioc C M, u n) ≤
        ‖t‖ * ((1 : ℝ) / (((C - 1 : ℕ) : ℝ))) :=
    mul_le_mul_of_nonneg_left hsum_u (norm_nonneg t)
  have hendpoint :
      ‖t‖ * ((1 : ℝ) / (((C - 1 : ℕ) : ℝ))) ≤ 1 := by
    have hdiv :
        (1 : ℝ) / (((C - 1 : ℕ) : ℝ)) =
          ((((C - 1 : ℕ) : ℝ))⁻¹) := by
      exact one_div (((C - 1 : ℕ) : ℝ))
    exact Eq.subst
      (motive := fun r : ℝ => ‖t‖ * r ≤ 1)
      hdiv.symm
      (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_norm_mul_pred_cutoff_inv_le_one
        t ht)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 1)
    hsum_mul.symm
    (le_trans hmul_le hendpoint)

/-- Finite Abel/Dirichlet coefficient absorption for the phase-drift weight
`|t| / (n - 1)`.

If the unweighted phase-block partial sums are bounded by `B` on every
post-cutoff prefix, then weighting those blocks by the decreasing coefficient
`|t|/(n-1)` preserves the same bound. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (u : ℕ → ℂ)
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, u k‖ ≤ B) :
    ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) : ℝ) : ℂ) * u k)‖ ≤
      B := by
  exact
    abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
      (u := u)
      (w := fun k : ℕ => ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)))
      (N := ⌊2 + ‖t‖⌋₊)
      (M := M)
      (C := B)
      hM
      hpartial
      (fun k _hk =>
        boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg t k)
      (fun k l hk hkl =>
        boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
          t hk hkl)
      (boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
        t ht hM)

/-- Local-terminal finite Abel/Dirichlet coefficient absorption for the
phase-drift weight `|t| / (n - 1)`.

Only post-cutoff prefixes ending at `K ≤ M` are needed to bound the finite sum
up to `M`; this is the version used with a bound whose logarithmic scale
depends on the terminal endpoint `M`. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le_of_local
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (u : ℕ → ℂ)
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K, u k‖ ≤ B) :
    ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ)) : ℝ) : ℂ) * u k)‖ ≤
      B := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let w : ℕ → ℝ := fun k => ‖t‖ / ((((k - 1 : ℕ) : ℕ) : ℝ))
  have hC_nonneg : 0 ≤ B := by
    have hnorm_nonneg :
        0 ≤ ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_nonneg (∑ k ∈ Finset.Ioc N M, u k)
    exact le_trans hnorm_nonneg (hpartial M hM le_rfl)
  have hidentity :
      (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
        ((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) :=
    abel_positive_weighted_tail_finite_summation_by_parts hM
  have hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k := by
    intro k _hk
    exact boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_nonneg t k
  have hw_antitone :
      ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k := by
    intro k l hk hkl
    exact
      boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_antitone
        t hk hkl
  have hterminal_nonneg : 0 ≤ w (M + 1) :=
    hw_nonneg (M + 1) (Nat.lt_succ_of_le hM)
  have hterminal_norm :
      ‖((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k)‖ ≤
        w (M + 1) * B := by
    have hmul :
        ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k)‖ =
          ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_mul ((w (M + 1) : ℝ) : ℂ)
        (∑ k ∈ Finset.Ioc N M, u k)
    have hreal_norm :
        ‖((w (M + 1) : ℝ) : ℂ)‖ = w (M + 1) := by
      have hcomplex_real :
          ‖((w (M + 1) : ℝ) : ℂ)‖ = ‖w (M + 1)‖ :=
        RCLike.norm_ofReal (w (M + 1))
      have hreal_abs : ‖w (M + 1)‖ = w (M + 1) :=
        Real.norm_of_nonneg hterminal_nonneg
      exact Eq.trans hcomplex_real hreal_abs
    have hscaled :
        w (M + 1) * ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤
          w (M + 1) * B :=
      mul_le_mul_of_nonneg_left
        (hpartial M hM le_rfl)
        hterminal_nonneg
    have hleft_eq :
        ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ =
          w (M + 1) * ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      congrArg
        (fun a : ℝ => a * ‖∑ k ∈ Finset.Ioc N M, u k‖)
        hreal_norm
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ w (M + 1) * B)
      hmul.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ w (M + 1) * B)
        hleft_eq.symm
        hscaled)
  have hsum_norm :
      ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
    have hterm :
        ∀ k ∈ Finset.Ioc N M,
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
            (w k - w (k + 1)) * B := by
      intro k hk_mem
      have hk_tail : N < k :=
        (Finset.mem_Ioc.mp hk_mem).1
      have hk_le_M : k ≤ M :=
        (Finset.mem_Ioc.mp hk_mem).2
      have hdiff_nonneg : 0 ≤ w k - w (k + 1) :=
        abel_positive_weighted_tail_weight_difference_nonneg
          hw_antitone hk_tail
      have hmul :
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ =
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        norm_mul ((w k - w (k + 1) : ℝ) : ℂ)
          (∑ j ∈ Finset.Ioc N k, u j)
      have hreal_norm :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
            w k - w (k + 1) := by
        have hcomplex_real :
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
              ‖w k - w (k + 1)‖ :=
          RCLike.norm_ofReal (w k - w (k + 1))
        have hreal_abs : ‖w k - w (k + 1)‖ = w k - w (k + 1) :=
          Real.norm_of_nonneg hdiff_nonneg
        exact Eq.trans hcomplex_real hreal_abs
      have hscaled :
          (w k - w (k + 1)) *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ ≤
            (w k - w (k + 1)) * B :=
        mul_le_mul_of_nonneg_left
          (hpartial k (Nat.le_of_lt hk_tail) hk_le_M)
          hdiff_nonneg
      have hleft_eq :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ =
            (w k - w (k + 1)) *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        congrArg
          (fun a : ℝ => a * ‖∑ j ∈ Finset.Ioc N k, u j‖)
          hreal_norm
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * B)
        hmul.symm
        (Eq.subst
          (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * B)
          hleft_eq.symm
          hscaled)
    have hsum_le :
        ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
          ∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ :=
      norm_sum_le
        (Finset.Ioc N M)
        (fun k : ℕ =>
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)))
    have hsum_bound :
        (∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖) ≤
          ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * B :=
      Finset.sum_le_sum hterm
    have hfactor :
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * B) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
      exact (Finset.sum_mul (Finset.Ioc N M)
        (fun k : ℕ => w k - w (k + 1)) B).symm
    exact le_trans hsum_le (hsum_bound.trans_eq hfactor)
  have htriangle :
      ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        w (M + 1) * B +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B :=
    (norm_add_le
      (((w (M + 1) : ℝ) : ℂ) *
        (∑ k ∈ Finset.Ioc N M, u k))
      (∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j)))).trans
      (add_le_add hterminal_norm hsum_norm)
  have hw_variation :
      w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1 :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_variation_le_one
      t ht hM
  have hvariation_mul :
      w (M + 1) * B +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B ≤
        B := by
    have hfactor :
        w (M + 1) * B +
            (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B =
          (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B := by
      exact (add_mul (w (M + 1))
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) B).symm
    have hscaled :
        (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * B ≤
          1 * B :=
      mul_le_mul_of_nonneg_right hw_variation hC_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ B)
      hfactor.symm
      (hscaled.trans_eq (one_mul B))
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ B)
    hidentity.symm
    (le_trans htriangle hvariation_mul)

/-- The fixed complex direction of the phase-drift coefficient has unit norm. -/
theorem boundaryLineOnePointRealParam_phaseDrift_coefficientDirection_norm_eq_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ))‖ = (1 : ℝ) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let T : ℂ := ((‖t‖ : ℝ) : ℂ)
  have hA_norm : ‖A‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hT_norm : ‖T‖ = ‖t‖ := by
    exact Eq.trans (RCLike.norm_ofReal ‖t‖) (abs_of_nonneg (norm_nonneg t))
  have hnorm_div :
      ‖A / T‖ = ‖A‖ / ‖T‖ :=
    norm_div A T
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hquot :
      ‖A‖ / ‖T‖ = (1 : ℝ) := by
    calc
      ‖A‖ / ‖T‖ = ‖t‖ / ‖T‖ := by
        exact congrArg (fun r : ℝ => r / ‖T‖) hA_norm
      _ = ‖t‖ / ‖t‖ := by
        exact congrArg (fun r : ℝ => ‖t‖ / r) hT_norm
      _ = 1 := by
        exact div_self (ne_of_gt ht_pos)
  exact Eq.trans hnorm_div hquot

/-- Norm of the concrete phase-drift coefficient at a positive left endpoint. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_eq_weight
    (t : ℝ)
    {m : ℕ}
    (hm : 0 < m) :
    ‖((-(t : ℂ) * Complex.I) *
        (((((m : ℕ) : ℝ) : ℂ)⁻¹))‖ =
      ‖t‖ / (((m : ℕ) : ℝ)) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hmr_pos : 0 < mr :=
    Nat.cast_pos.mpr hm
  have hA_norm : ‖A‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hinv_norm : ‖((mr : ℂ)⁻¹)‖ = mr⁻¹ := by
    have hnorm_inv :
        ‖((mr : ℂ)⁻¹)‖ = (‖(mr : ℂ)‖)⁻¹ :=
      norm_inv (mr : ℂ)
    have hnorm_real :
        ‖(mr : ℂ)‖ = mr := by
      exact Eq.trans (RCLike.norm_ofReal mr) (abs_of_pos hmr_pos)
    exact Eq.trans hnorm_inv (congrArg Inv.inv hnorm_real)
  calc
    ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
        ‖A‖ * ‖((mr : ℂ)⁻¹)‖ := by
      exact norm_mul A ((mr : ℂ)⁻¹)
    _ = ‖t‖ * ‖((mr : ℂ)⁻¹)‖ := by
      exact congrArg (fun r : ℝ => r * ‖((mr : ℂ)⁻¹)‖) hA_norm
    _ = ‖t‖ * mr⁻¹ := by
      exact congrArg (fun r : ℝ => ‖t‖ * r) hinv_norm
    _ = ‖t‖ / mr := by
      exact (div_eq_mul_inv ‖t‖ mr).symm

/-- Right-endpoint form of the concrete phase-drift coefficient norm. -/
theorem boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_norm_eq_weight
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖((-(t : ℂ) * Complex.I) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))‖ =
      ‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hm_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt
      (lt_of_le_of_lt
        (Nat.succ_le_of_lt hcutoff_pos)
        hcutoff_lt_n)
  exact
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_eq_weight
      t hm_pos

/-- Factor the concrete phase-drift coefficient into a fixed unit direction
and the positive Abel weight `|t| / m`. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_eq_direction_mul_weight
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {m : ℕ}
    (hm : 0 < m) :
    ((-(t : ℂ) * Complex.I) *
        (((((m : ℕ) : ℝ) : ℂ)⁻¹))) =
      ((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)) *
        (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let T : ℂ := ((‖t‖ : ℝ) : ℂ)
  let R : ℂ := ((((m : ℕ) : ℝ) : ℂ))
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hT_ne : T ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ht_pos)
  have hR_ne : R ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Nat.cast_pos.mpr hm : 0 < ((m : ℕ) : ℝ)))
  have hweight :
      (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) = T / R := by
    exact Complex.ofReal_div ‖t‖ (((m : ℕ) : ℝ))
  have hcancel : T⁻¹ * T = (1 : ℂ) :=
    inv_mul_cancel₀ hT_ne
  calc
    A * R⁻¹ =
        (A * (1 : ℂ)) * R⁻¹ := by
      exact congrArg (fun z : ℂ => z * R⁻¹) (mul_one A).symm
    _ = (A * (T⁻¹ * T)) * R⁻¹ := by
      exact congrArg (fun z : ℂ => (A * z) * R⁻¹) hcancel.symm
    _ = ((A * T⁻¹) * T) * R⁻¹ := by
      exact congrArg (fun z : ℂ => z * R⁻¹) (mul_assoc A T⁻¹ T)
    _ = (A * T⁻¹) * (T * R⁻¹) := by
      exact (mul_assoc (A * T⁻¹) T R⁻¹).symm
    _ = (A / T) * (T / R) := by
      exact congrArg₂ (fun x y : ℂ => x * y)
        (div_eq_mul_inv A T).symm
        (div_eq_mul_inv T R).symm
    _ = (A / T) * (((‖t‖ / (((m : ℕ) : ℝ)) : ℝ) : ℂ)) := by
      exact congrArg (fun z : ℂ => (A / T) * z) hweight.symm

/-- Right-endpoint form of the phase-drift coefficient factorization. -/
theorem boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_eq_direction_mul_weight
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ((-(t : ℂ) * Complex.I) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))) =
      ((-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)) *
        (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hm_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  exact
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_eq_direction_mul_weight
      t ht hm_pos

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 + ‖t‖) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
      1 := by
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_cutoffRatio_ownerGap
      t ht hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_cutoffRatio_le_one_ownerGap
      t ht)

theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_one_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) ≤
      1 := by
  have hcalc :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) =
        (1 + ‖t‖) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareMajorant_eq_endpointDifference_ownerGap
      t ht hM
  have hendpoint :
      (1 + ‖t‖) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⁻¹ - (((M : ℕ) : ℝ))⁻¹) ≤
        1 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_inverseSquareEndpointDifference_le_one_ownerGap
      t ht hM
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 1)
    hcalc.symm
    hendpoint

/-- Real-variable cutoff estimate for the Bernoulli-remainder derivative
majorant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 + ‖t‖) / x ^ 2) ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  have hmajorant_le_one :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (1 + ‖t‖) / x ^ 2) ≤
        1 :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_one_ownerGap
      t ht hM
  have hlog_nonneg : 0 ≤ Real.log (3 + ‖t‖) := by
    have hone_le_arg : (1 : ℝ) ≤ 3 + ‖t‖ := by
      calc
        (1 : ℝ) ≤ 3 := by
          exact one_le_three
        _ ≤ 3 + ‖t‖ :=
          le_add_of_nonneg_right (norm_nonneg t)
    exact Real.log_nonneg hone_le_arg
  have htail_nonneg : 0 ≤ 16 * Real.log (3 + ‖t‖) :=
    mul_nonneg (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16) hlog_nonneg
  exact le_trans hmajorant_le_one
    (le_add_of_nonneg_right htail_nonneg)

/-- Owner sink for the first-periodic-Bernoulli remainder estimate after the
canonical cutoff. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  exact le_trans
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_realMajorant_ownerGap
      t ht hM)
    (boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_realMajorant_le_ownerGap
      t ht hM)

/-- Public Bernoulli-remainder component bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-boundaryLineOnePointRealParam t *
            (((x : ℝ) : ℂ) ^
              (-(boundaryLineOnePointRealParam t + 1))))‖ ≤
      1 + 16 * Real.log (3 + ‖t‖) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_bernoulliRemainder_norm_le_ownerGap
      t ht hM

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
            (-(boundaryLineOnePointRealParam t + 1))))
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
    (hpositive :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
          t ⌊2 + ‖t‖⌋₊‖ ≤
        8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊)) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊‖ ≤
      8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ 8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊))
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
      Nat.cast_add C 1
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
              (show (2 : ℝ) + 1 = 3 from rfl)
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
      _ = (3 + 1) * ‖t‖ := by
        exact (add_mul (3 : ℝ) 1 ‖t‖).symm
      _ = 4 * ‖t‖ := by
        exact congrArg (fun r : ℝ => r * ‖t‖)
          (show (3 : ℝ) + 1 = 4 from rfl)
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
      exact (add_mul (4 : ℝ) 1 (Real.sqrt (1 + ‖t‖))).symm
    _ = 5 * Real.sqrt (1 + ‖t‖) := by
      exact congrArg (fun r : ℝ => r * Real.sqrt (1 + ‖t‖))
        (show (4 : ℝ) + 1 = 5 from rfl)

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
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have harg_pos : (0 : ℝ) < 2 + ‖t‖ :=
      lt_of_lt_of_le htwo_pos (le_add_of_nonneg_right (norm_nonneg t))
    exact Nat.floor_pos.mpr harg_pos
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
        exact show (2 : ℝ) + 4 = 6 from rfl
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
    logarithmicPhasePartialSum_norm_le_card t C
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
    one_le_mul hsqrt_ge_one hlog_ge_one
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
    ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
        (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ)))⁻¹ ≤
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
        ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) *
          (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ)))⁻¹ ≤
      ‖t‖ * (x * x)⁻¹ := by
  exact mul_le_mul_of_nonneg_left
    (boundaryLineOnePointRealParam_logarithmicPhase_classicalPrefix_curvatureDenominator_inv_le
      t hx)
    (norm_nonneg t)

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
      (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖)) := by
  sorry

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
      8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  have hvdc :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
          t ⌊2 + ‖t‖⌋₊‖ ≤
        (((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)) :=
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
  have hfive_le_eight_log :
      5 * Real.sqrt (1 + ‖t‖) ≤
        8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
    have hfive_le_eight : (5 : ℝ) ≤ 8 :=
      Nat.cast_le.mpr (show (5 : ℕ) ≤ 8 from Nat.le_add_right 5 3)
    have hfive_sqrt_le_eight_sqrt :
        5 * Real.sqrt (1 + ‖t‖) ≤ 8 * Real.sqrt (1 + ‖t‖) :=
      mul_le_mul_of_nonneg_right hfive_le_eight hsqrt_nonneg
    have height_sqrt_le_target :
        8 * Real.sqrt (1 + ‖t‖) ≤
          8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
      calc
        8 * Real.sqrt (1 + ‖t‖) =
            8 * (Real.sqrt (1 + ‖t‖) * 1) := by
          exact congrArg (fun r : ℝ => 8 * r)
            (mul_one (Real.sqrt (1 + ‖t‖))).symm
        _ ≤ 8 * (Real.sqrt (1 + ‖t‖) *
            Real.log (2 + ⌊2 + ‖t‖⌋₊)) :=
          mul_le_mul_of_nonneg_left hsqrt_le_sqrt_log
            (show (0 : ℝ) ≤ 8 from Nat.cast_nonneg 8)
        _ = 8 * Real.sqrt (1 + ‖t‖) *
            Real.log (2 + ⌊2 + ‖t‖⌋₊) :=
          (mul_assoc 8 (Real.sqrt (1 + ‖t‖))
            (Real.log (2 + ⌊2 + ‖t‖⌋₊))).symm
    exact le_trans hfive_sqrt_le_eight_sqrt height_sqrt_le_target
  exact le_trans hvdc (le_trans hscale hfive_le_eight_log)

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
      8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + ⌊2 + ‖t‖⌋₊) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_of_positiveIndex
      t ht
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

/-- Pointwise normalization of the unweighted logarithmic-phase derivative on
the positive real axis.  This is the algebraic bridge from the standard
Euler-Maclaurin derivative `-z * x^-(z+1)` to the public
`((-it) / x) * x^(-it)` kernel. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_unweightedDerivative_standard_eq_normalized
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    -((t : ℂ) * Complex.I) *
        (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hx_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hexponent :
      (-(((t : ℂ) * Complex.I) + 1)) = a + (-1 : ℂ) := by
    calc
      (-(((t : ℂ) * Complex.I) + 1)) =
          -((t : ℂ) * Complex.I) + (-(1 : ℂ)) :=
        neg_add ((t : ℂ) * Complex.I) (1 : ℂ)
      _ = a + (-1 : ℂ) := rfl
  have hcpow_add :
      (((x : ℝ) : ℂ) ^ (a + (-1 : ℂ))) =
        (((x : ℝ) : ℂ) ^ a) * (((x : ℝ) : ℂ) ^ (-1 : ℂ)) :=
    Complex.cpow_add a (-1 : ℂ) hx_ne
  have hcpow_neg_one :
      (((x : ℝ) : ℂ) ^ (-1 : ℂ)) = (x : ℂ)⁻¹ :=
    Complex.cpow_neg_one (x : ℂ)
  have hstandard :
      -((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
        a * ((((x : ℝ) : ℂ) ^ a) * (x : ℂ)⁻¹) := by
    calc
      -((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) =
          a * (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))) := rfl
      _ = a * (((x : ℝ) : ℂ) ^ (a + (-1 : ℂ))) :=
        congrArg
          (fun y : ℂ => a * (((x : ℝ) : ℂ) ^ y))
          hexponent
      _ = a * ((((x : ℝ) : ℂ) ^ a) *
          (((x : ℝ) : ℂ) ^ (-1 : ℂ))) :=
        congrArg (fun y : ℂ => a * y) hcpow_add
      _ = a * ((((x : ℝ) : ℂ) ^ a) * (x : ℂ)⁻¹) :=
        congrArg
          (fun y : ℂ => a * ((((x : ℝ) : ℂ) ^ a) * y))
          hcpow_neg_one
  have hnormalized :
      a * ((((x : ℝ) : ℂ) ^ a) * (x : ℂ)⁻¹) =
        ((a / (x : ℂ)) * (((x : ℝ) : ℂ) ^ a)) := by
    have hdiv : a / (x : ℂ) = a * (x : ℂ)⁻¹ :=
      div_eq_mul_inv a (x : ℂ)
    calc
      a * ((((x : ℝ) : ℂ) ^ a) * (x : ℂ)⁻¹) =
          (a * (x : ℂ)⁻¹) * (((x : ℝ) : ℂ) ^ a) := by
        exact
          Eq.trans
            (mul_assoc a (((x : ℝ) : ℂ) ^ a) ((x : ℂ)⁻¹))
            (congrArg
              (fun y : ℂ => y * (((x : ℝ) : ℂ) ^ a))
              (mul_comm a ((x : ℂ)⁻¹)))
      _ = (a / (x : ℂ)) * (((x : ℝ) : ℂ) ^ a) :=
        congrArg
          (fun y : ℂ => y * (((x : ℝ) : ℂ) ^ a))
          hdiv.symm
  exact Eq.trans hstandard hnormalized

/-- Integral normalization for the unweighted Euler-Maclaurin Bernoulli
remainder on the finite post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_standard_eq_normalized
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (-((t : ℂ) * Complex.I) *
          (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ))
  have hcongr :
      EqOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (-((t : ℂ) * Complex.I) *
              (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1)))))
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        s := by
    intro x hx
    have hx_u :
        x ∈
          Set.uIcc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) := by
      have hle :
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
        Nat.cast_le.mpr hM
      have hx_icc :
          x ∈
            Set.Icc
              (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
              (((M : ℕ) : ℝ)) :=
        ⟨le_of_lt hx.1, hx.2⟩
      exact (Set.uIcc_of_le hle).symm ▸ hx_icc
    have hx_pos :
        0 < x :=
      boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
        t hM hx_u
    exact congrArg
      (fun y : ℂ => ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * y)
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum_unweightedDerivative_standard_eq_normalized
        t hx_pos)
  exact setIntegral_congr_fun measurableSet_Ioc hcongr

/-- Pointwise norm of the normalized unweighted logarithmic-phase derivative
kernel on the positive real axis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_normalizedDerivativeKernel_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ =
      ‖t‖ / x := by
  let K : ℂ := ((-(t : ℂ) * Complex.I) / (x : ℂ))
  have hphase :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx
  have hderiv :
      deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
        K * Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq
      t hx
  have hkernel_to_function :
      ‖K * (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ =
        ‖K * Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ := by
    exact congrArg (fun z : ℂ => ‖K * z‖) hphase.symm
  have hfunction_to_deriv :
      ‖K * Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ :=
    congrArg norm hderiv.symm
  have hderiv_norm :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx
  exact Eq.trans hkernel_to_function (Eq.trans hfunction_to_deriv hderiv_norm)

/-- Pointwise norm majorization for the first-periodic-Bernoulli normalized
unweighted logarithmic-phase derivative kernel on the post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖t‖ / x := by
  intro x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let K : ℂ :=
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hK :
      ‖K‖ = ‖t‖ / x :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_normalizedDerivativeKernel_norm_eq
      t hx_pos
  have hmul :
      ‖B * K‖ = ‖B‖ * ‖K‖ :=
    norm_mul B K
  have hproduct :
      ‖B‖ * ‖K‖ ≤ (1 : ℝ) * (‖t‖ / x) := by
    exact mul_le_mul hB (le_of_eq hK) (norm_nonneg K) (norm_nonneg B)
  exact
    Eq.subst
      (motive := fun r : ℝ => r ≤ ‖t‖ / x)
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖B‖ * ‖K‖ ≤ r)
        (one_mul (‖t‖ / x))
        hproduct)

/-- After the canonical cutoff, the first-periodic-Bernoulli normalized
unweighted logarithmic-phase derivative kernel is pointwise bounded by one. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_one
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        1 := by
  intro x hx
  have hnorm_div :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖t‖ / x :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
      t hM x hx
  have hx_u :
      x ∈
        Set.uIcc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
    have hle :
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
      Nat.cast_le.mpr hM
    have hx_icc :
        x ∈
          Set.Icc
            (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
            (((M : ℕ) : ℝ)) :=
      ⟨le_of_lt hx.1, hx.2⟩
    exact (Set.uIcc_of_le hle).symm ▸ hx_icc
  have hx_pos :
      0 < x :=
    boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_mem_interval_pos
      t hM hx_u
  have hx_ge_cutoff :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hcutoff_ge :
      (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t
  have ht_le_x :
      ‖t‖ ≤ x := by
    have ht_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
      le_add_of_nonneg_left zero_le_one
    exact le_trans ht_le_one_add (le_trans hcutoff_ge hx_ge_cutoff)
  have hdiv_le_one :
      ‖t‖ / x ≤ 1 :=
    (div_le_one₀ hx_pos).mpr ht_le_x
  exact le_trans hnorm_div hdiv_le_one

/-- Bochner norm domination for the normalized unweighted Bernoulli kernel by
the constant-one finite-interval majorant. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_constOneIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (1 : ℝ) := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let g : ℝ → ℝ := fun _x => (1 : ℝ)
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const (μ := volume) (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (b := (((M : ℕ) : ℝ))) (c := (1 : ℝ)))
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_one
          t hM x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Bochner norm domination for the normalized unweighted Bernoulli kernel by
the logarithmic absolute majorant `|t| / x`.

This is the sharp absolute-value estimate available before using cancellation
of the first-periodic Bernoulli factor.  The remaining defect theorem needs the
strictly stronger oscillatory improvement of this bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_normDivIntegral
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ‖t‖ / x := by
  let s : Set ℝ :=
    Set.Ioc
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
      (((M : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let g : ℝ → ℝ := fun x => ‖t‖ / x
  have hle :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (((M : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hM
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_real_pos :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  have hM_real_pos : (0 : ℝ) < (((M : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hM_pos
  have hg_interval :
      IntervalIntegrable g volume
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)) := by
    have hinv_interval :
        IntervalIntegrable (fun x : ℝ => x⁻¹) volume
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) := by
      have hzero_not_mem :
          (0 : ℝ) ∉
            Set.uIcc
              (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
              (((M : ℕ) : ℝ)) :=
        not_mem_uIcc_of_lt hcutoff_real_pos hM_real_pos
      exact (intervalIntegrable_inv_iff.mpr (Or.inr hzero_not_mem))
    have hconst_mul :
        IntervalIntegrable (fun x : ℝ => ‖t‖ * x⁻¹) volume
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)) :=
      hinv_interval.const_mul ‖t‖
    exact hconst_mul.congr
      (Filter.Eventually.of_forall
        (fun x =>
          (div_eq_mul_inv ‖t‖ x).symm))
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hg_interval
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_pointwise_norm_le_norm_div
          t hM x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- One-interval constant cancellation for the first-periodic Bernoulli factor.

This is the local cancellation input used by the finite-defect route: constants
may be subtracted from the slowly varying normalized kernel on each unit
interval without changing the Bernoulli integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_const_mul_integral_eq_zero
    (n : ℕ)
    (c : ℂ) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c) = 0 := by
  let s : Set ℝ :=
    Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  have hmul :
      (∫ x in s, B x * c) = (∫ x in s, B x) * c :=
    integral_mul_right c B
  have hzero :
      (∫ x in s, B x) = 0 :=
    eulerMaclaurinFirstPeriodicBernoulli_oneInterval_integral_eq_zero n
  calc
    (∫ x in s, B x * c) = (∫ x in s, B x) * c :=
      hmul
    _ = 0 * c := by
      exact congrArg (fun z : ℂ => z * c) hzero
    _ = 0 := by
      exact zero_mul c

/-- Exact local subtraction identity for the normalized-kernel variation
argument on a single unit interval.

After subtracting the left-endpoint value of the slowly varying factor, the
constant part vanishes by the Bernoulli zero-mean identity above.  The remaining
future estimate is therefore a genuine local-variation bound for
`K x - K n`, not an absolute-value estimate for `K x`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
    (n : ℕ)
    (K : ℝ → ℂ)
    (hBK :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
        (volume.restrict
          (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))))
    (hBc :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            K (((n : ℕ) : ℝ)))
        (volume.restrict
          (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
      (∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))) := by
  let s : Set ℝ :=
    Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let c : ℂ := K (((n : ℕ) : ℝ))
  have hpoint :
      (fun x : ℝ => B x * (K x - c)) =
        (fun x : ℝ => B x * K x - B x * c) := by
    funext x
    exact mul_sub (B x) (K x) c
  have hsub :
      (∫ x in s, B x * K x - B x * c) =
        (∫ x in s, B x * K x) - (∫ x in s, B x * c) :=
    integral_sub hBK hBc
  have hconst :
      (∫ x in s, B x * c) = 0 :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_const_mul_integral_eq_zero
      n c
  have hvariation :
      (∫ x in s, B x * (K x - c)) =
        (∫ x in s, B x * K x) := by
    calc
      (∫ x in s, B x * (K x - c)) =
          (∫ x in s, B x * K x - B x * c) := by
        exact congrArg (fun f : ℝ → ℂ => ∫ x in s, f x) hpoint
      _ = (∫ x in s, B x * K x) - (∫ x in s, B x * c) :=
        hsub
      _ = (∫ x in s, B x * K x) - 0 := by
        exact congrArg
          (fun z : ℂ => (∫ x in s, B x * K x) - z)
          hconst
      _ = (∫ x in s, B x * K x) := by
        exact sub_zero (∫ x in s, B x * K x)
  exact hvariation.symm

/-- Pointwise local-variation domination after subtracting the unit-interval
left endpoint.

Together with
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint`,
this reduces the finite-defect estimate to bounding the movement of the
normalized kernel itself on each unit interval. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_pointwise_norm_le
    (n : ℕ)
    (K : ℝ → ℂ) :
    ∀ x : ℝ,
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))‖ ≤
        ‖K x - K (((n : ℕ) : ℝ))‖ := by
  intro x
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let D : ℂ := K x - K (((n : ℕ) : ℝ))
  have hB : ‖B‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have hmul : ‖B * D‖ = ‖B‖ * ‖D‖ :=
    norm_mul B D
  have hprod : ‖B‖ * ‖D‖ ≤ (1 : ℝ) * ‖D‖ :=
    mul_le_mul hB (le_rfl : ‖D‖ ≤ ‖D‖) (norm_nonneg D) (norm_nonneg B)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ ‖D‖)
    hmul.symm
    (Eq.subst
      (motive := fun r : ℝ => ‖B‖ * ‖D‖ ≤ r)
      (one_mul ‖D‖)
      hprod)

/-- Pointwise movement bound for the normalized logarithmic-phase derivative
kernel on one interval.

The right side separates the elementary reciprocal drift from the genuinely
oscillatory phase drift.  Summing this estimate after the Bernoulli zero-mean
subtraction is the remaining finite-defect task. -/
theorem boundaryLineOnePointRealParam_normalizedKernel_movement_norm_le_reciprocal_add_phase
    (t x y : ℝ) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(x : ℂ)⁻¹ - (y : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(y : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
  let a : ℂ := -(t : ℂ) * Complex.I
  let bx : ℂ := (x : ℂ)⁻¹
  let by : ℂ := (y : ℂ)⁻¹
  let px : ℂ := (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let py : ℂ := (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hx_div : (-(t : ℂ) * Complex.I) / (x : ℂ) = a * bx :=
    div_eq_mul_inv a (x : ℂ)
  have hy_div : (-(t : ℂ) * Complex.I) / (y : ℂ) = a * by :=
    div_eq_mul_inv a (y : ℂ)
  have hdecomp :
      (a * bx) * px - (a * by) * py =
        a * ((bx - by) * px + by * (px - py)) := by
    calc
      (a * bx) * px - (a * by) * py =
          a * (bx * px) - a * (by * py) := by
        exact congrArg₂ Sub.sub
          (mul_assoc a bx px)
          (mul_assoc a by py)
      _ = a * (bx * px - by * py) := by
        exact (mul_sub a (bx * px) (by * py)).symm
      _ = a * (((bx - by) * px) + by * (px - py)) := by
        have hinner :
            bx * px - by * py =
              (bx - by) * px + by * (px - py) := by
          calc
            bx * px - by * py =
                (bx * px - by * px) + (by * px - by * py) := by
              have hcancel :
                  (bx * px - by * px) + (by * px - by * py) =
                    bx * px - by * py := by
                calc
                  (bx * px - by * px) + (by * px - by * py) =
                      (bx * px + -(by * px)) + (by * px + -(by * py)) := by
                    exact congrArg₂ Add.add
                      (sub_eq_add_neg (bx * px) (by * px))
                      (sub_eq_add_neg (by * px) (by * py))
                  _ = bx * px + (-(by * px) + (by * px + -(by * py))) := by
                    exact add_assoc (bx * px) (-(by * px)) (by * px + -(by * py))
                  _ = bx * px + ((-(by * px) + by * px) + -(by * py)) := by
                    exact congrArg (fun z : ℂ => bx * px + z)
                      (add_assoc (-(by * px)) (by * px) (-(by * py))).symm
                  _ = bx * px + (0 + -(by * py)) := by
                    exact congrArg
                      (fun z : ℂ => bx * px + (z + -(by * py)))
                      (neg_add_cancel (by * px))
                  _ = bx * px + -(by * py) := by
                    exact congrArg (fun z : ℂ => bx * px + z)
                      (zero_add (-(by * py)))
                  _ = bx * px - by * py := by
                    exact (sub_eq_add_neg (bx * px) (by * py)).symm
              exact hcancel.symm
            _ = ((bx - by) * px) + (by * px - by * py) := by
              exact congrArg (fun z : ℂ => z + (by * px - by * py))
                (sub_mul bx by px).symm
            _ = ((bx - by) * px) + by * (px - py) := by
              exact congrArg (fun z : ℂ => ((bx - by) * px) + z)
                (mul_sub by px py).symm
        exact congrArg (fun z : ℂ => a * z) hinner
  have htarget_eq :
      ((-(t : ℂ) * Complex.I) / (x : ℂ)) * px -
          ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py =
        a * ((bx - by) * px + by * (px - py)) := by
    calc
      ((-(t : ℂ) * Complex.I) / (x : ℂ)) * px -
          ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py =
          (a * bx) * px - ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py := by
        exact congrArg
          (fun z : ℂ => z * px - ((-(t : ℂ) * Complex.I) / (y : ℂ)) * py)
          hx_div
      _ = (a * bx) * px - (a * by) * py := by
        exact congrArg
          (fun z : ℂ => (a * bx) * px - z * py)
          hy_div
      _ = a * ((bx - by) * px + by * (px - py)) :=
        hdecomp
  have hnorm_decomp :
      ‖a * ((bx - by) * px + by * (px - py))‖ ≤
        ‖a‖ * (‖(bx - by) * px‖ + ‖by * (px - py)‖) := by
    calc
      ‖a * ((bx - by) * px + by * (px - py))‖ =
          ‖a‖ * ‖(bx - by) * px + by * (px - py)‖ := by
        exact norm_mul a ((bx - by) * px + by * (px - py))
      _ ≤ ‖a‖ * (‖(bx - by) * px‖ + ‖by * (px - py)‖) :=
        mul_le_mul_of_nonneg_left
          (norm_add_le ((bx - by) * px) (by * (px - py)))
          (norm_nonneg a)
  have hsplit :
      ‖a‖ * (‖(bx - by) * px‖ + ‖by * (px - py)‖) =
        ‖a‖ * ‖bx - by‖ * ‖px‖ + ‖a‖ * ‖by‖ * ‖px - py‖ := by
    calc
      ‖a‖ * (‖(bx - by) * px‖ + ‖by * (px - py)‖) =
          ‖a‖ * (‖bx - by‖ * ‖px‖ + ‖by‖ * ‖px - py‖) := by
        exact congrArg (fun z : ℝ => ‖a‖ * z)
          (congrArg₂ Add.add
            (norm_mul (bx - by) px)
            (norm_mul by (px - py)))
      _ = ‖a‖ * (‖bx - by‖ * ‖px‖) +
          ‖a‖ * (‖by‖ * ‖px - py‖) := by
        exact mul_add ‖a‖ (‖bx - by‖ * ‖px‖) (‖by‖ * ‖px - py‖)
      _ = ‖a‖ * ‖bx - by‖ * ‖px‖ + ‖a‖ * ‖by‖ * ‖px - py‖ := by
        exact congrArg₂ Add.add
          (mul_assoc ‖a‖ ‖bx - by‖ ‖px‖).symm
          (mul_assoc ‖a‖ ‖by‖ ‖px - py‖).symm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        ‖a‖ * ‖bx - by‖ * ‖px‖ +
          ‖a‖ * ‖by‖ * ‖px - py‖)
    htarget_eq.symm
    (le_trans hnorm_decomp
      (le_of_eq hsplit))

/-- Quantitative reciprocal drift on a single unit interval. -/
theorem boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(x : ℂ)⁻¹ - (((n : ℕ) : ℝ) : ℂ)⁻¹‖ ≤
      (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  have hnr_pos : 0 < nr :=
    Nat.cast_pos.mpr hn
  have hx_pos : 0 < x :=
    lt_trans hnr_pos hx.1
  have hx_ge : nr ≤ x :=
    le_of_lt hx.1
  have hx_le_succ : x ≤ (((n + 1 : ℕ) : ℝ)) :=
    hx.2
  have hsucc_eq : (((n + 1 : ℕ) : ℝ)) = nr + 1 :=
    Nat.cast_add_one n
  have hx_sub_le_one : x - nr ≤ 1 := by
    have hsub :
        x - nr ≤ (((n + 1 : ℕ) : ℝ)) - nr :=
      sub_le_sub_right hx_le_succ nr
    have hright :
        (((n + 1 : ℕ) : ℝ)) - nr = 1 := by
      calc
        (((n + 1 : ℕ) : ℝ)) - nr =
            (nr + 1) - nr := by
          exact congrArg (fun y : ℝ => y - nr) hsucc_eq
        _ = 1 := by
          exact add_sub_cancel_left nr 1
    exact Eq.subst
      (motive := fun r : ℝ => x - nr ≤ r)
      hright.symm
      hsub
  have hnr_sub_nonpos : nr - x ≤ 0 := by
    exact sub_nonpos.mpr hx_ge
  have hnum_abs :
      |nr - x| = x - nr := by
    calc
      |nr - x| = -(nr - x) :=
        abs_of_nonpos hnr_sub_nonpos
      _ = x - nr := by
        exact neg_sub nr x
  have hnum_le_one : |nr - x| ≤ 1 := by
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 1)
      hnum_abs.symm
      hx_sub_le_one
  have hx_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx_pos.ne'
  have hn_ne : ((nr : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnr_pos.ne'
  have hinv :
      (x : ℂ)⁻¹ - ((nr : ℝ) : ℂ)⁻¹ =
        (((nr : ℝ) : ℂ) - (x : ℂ)) / ((x : ℂ) * ((nr : ℝ) : ℂ)) :=
    inv_sub_inv hx_ne hn_ne
  have hnorm :
      ‖(x : ℂ)⁻¹ - ((nr : ℝ) : ℂ)⁻¹‖ =
        |nr - x| / (x * nr) := by
    have hnorm_div :
        ‖(((nr : ℝ) : ℂ) - (x : ℂ)) / ((x : ℂ) * ((nr : ℝ) : ℂ))‖ =
          ‖((nr : ℝ) : ℂ) - (x : ℂ)‖ /
            ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ :=
      norm_div (((nr : ℝ) : ℂ) - (x : ℂ)) ((x : ℂ) * ((nr : ℝ) : ℂ))
    have hnum :
        ‖((nr : ℝ) : ℂ) - (x : ℂ)‖ = |nr - x| := by
      have hsub :
          ((nr : ℝ) : ℂ) - (x : ℂ) = ((nr - x : ℝ) : ℂ) := by
        exact (Complex.ofReal_sub nr x).symm
      exact Eq.trans (congrArg norm hsub) (RCLike.norm_ofReal (nr - x))
    have hden :
        ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ = x * nr := by
      have hmul : ‖(x : ℂ) * ((nr : ℝ) : ℂ)‖ =
          ‖(x : ℂ)‖ * ‖((nr : ℝ) : ℂ)‖ :=
        norm_mul (x : ℂ) ((nr : ℝ) : ℂ)
      have hx_norm : ‖(x : ℂ)‖ = x := by
        exact Eq.trans (RCLike.norm_ofReal x) (abs_of_pos hx_pos)
      have hn_norm : ‖((nr : ℝ) : ℂ)‖ = nr := by
        exact Eq.trans (RCLike.norm_ofReal nr) (abs_of_pos hnr_pos)
      exact Eq.trans hmul
        (congrArg₂ (fun a b : ℝ => a * b) hx_norm hn_norm)
    exact Eq.trans (congrArg norm hinv)
      (Eq.trans hnorm_div
        (congrArg₂ (fun a b : ℝ => a / b) hnum hden))
  have hden_pos : 0 < x * nr :=
    mul_pos hx_pos hnr_pos
  have hnr_sq_pos : 0 < nr * nr :=
    mul_pos hnr_pos hnr_pos
  have hden_ge : nr * nr ≤ x * nr :=
    mul_le_mul_of_nonneg_right hx_ge (le_of_lt hnr_pos)
  have hquot_le :
      |nr - x| / (x * nr) ≤ (1 : ℝ) / (x * nr) :=
    div_le_div_of_nonneg_right hnum_le_one (le_of_lt hden_pos)
  have hone_div_le :
      (1 : ℝ) / (x * nr) ≤ (1 : ℝ) / (nr * nr) :=
    one_div_le_one_div_of_le hnr_sq_pos hden_ge
  exact Eq.subst
    (motive := fun r : ℝ =>
      r ≤ (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)))
    hnorm.symm
    (le_trans hquot_le hone_div_le)

/-- Quantitative phase drift on one unit interval after the logarithmic-phase
cutoff.

This is the local mean-value estimate for the genuinely oscillatory factor
`x^{-it}`.  It is kept separate from the reciprocal drift so the later finite
defect summation can use cancellation information interval by interval. -/
theorem boundaryLineOnePointRealParam_oneInterval_phase_drift_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      ‖t‖ / (((n : ℕ) : ℝ)) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  let phase : ℝ → ℂ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t
  let derivPhase : ℝ → ℂ := fun u =>
    (((-(t : ℂ) * Complex.I) / (u : ℂ)) * phase u)
  have hnr_pos : 0 < nr :=
    Nat.cast_pos.mpr hn
  have hx_pos : 0 < x :=
    lt_trans hnr_pos hx.1
  have hnr_le_x : nr ≤ x :=
    le_of_lt hx.1
  have hx_le_succ : x ≤ (((n + 1 : ℕ) : ℝ)) :=
    hx.2
  have hsucc_eq : (((n + 1 : ℕ) : ℝ)) = nr + 1 :=
    Nat.cast_add_one n
  have hx_sub_le_one : x - nr ≤ 1 := by
    have hsub :
        x - nr ≤ (((n + 1 : ℕ) : ℝ)) - nr :=
      sub_le_sub_right hx_le_succ nr
    have hright :
        (((n + 1 : ℕ) : ℝ)) - nr = 1 := by
      calc
        (((n + 1 : ℕ) : ℝ)) - nr =
            (nr + 1) - nr := by
          exact congrArg (fun y : ℝ => y - nr) hsucc_eq
        _ = 1 := by
          exact add_sub_cancel_left nr 1
    exact Eq.subst
      (motive := fun r : ℝ => x - nr ≤ r)
      hright.symm
      hsub
  have hnr_mem : nr ∈ Set.Icc nr x :=
    ⟨le_rfl, hnr_le_x⟩
  have hx_mem : x ∈ Set.Icc nr x :=
    ⟨hnr_le_x, le_rfl⟩
  have hderiv :
      ∀ u ∈ Set.Icc nr x,
        HasDerivWithinAt phase (derivPhase u) (Set.Icc nr x) u := by
    intro u hu
    have hu_pos : 0 < u :=
      lt_of_lt_of_le hnr_pos hu.1
    exact
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
        t hu_pos).hasDerivWithinAt
  have hderiv_bound :
      ∀ u ∈ Set.Icc nr x, ‖derivPhase u‖ ≤ ‖t‖ / nr := by
    intro u hu
    have hu_pos : 0 < u :=
      lt_of_lt_of_le hnr_pos hu.1
    have hnorm_eq : ‖derivPhase u‖ = ‖t‖ / u :=
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_norm_eq
        t hu_pos
    have hnum_nonneg : 0 ≤ ‖t‖ :=
      norm_nonneg t
    have hdiv_le : ‖t‖ / u ≤ ‖t‖ / nr :=
      div_le_div_of_nonneg_left hnum_nonneg hnr_pos hu.1
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ ‖t‖ / nr)
      hnorm_eq.symm
      hdiv_le
  have hmvt :
      ‖phase x - phase nr‖ ≤ (‖t‖ / nr) * ‖x - nr‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.Icc nr x)
      (f := phase)
      (f' := derivPhase)
      (C := ‖t‖ / nr)
      hderiv
      hderiv_bound
      (convex_Icc nr x)
      hnr_mem
      hx_mem
  have hdist_eq : ‖x - nr‖ = x - nr := by
    have hsub_nonneg : 0 ≤ x - nr :=
      sub_nonneg.mpr hnr_le_x
    exact Eq.trans (Real.norm_eq_abs (x - nr)) (abs_of_nonneg hsub_nonneg)
  have hscale_nonneg : 0 ≤ ‖t‖ / nr :=
    div_nonneg (norm_nonneg t) (le_of_lt hnr_pos)
  have hmvt_unit : ‖phase x - phase nr‖ ≤ ‖t‖ / nr := by
    have hscaled :
        (‖t‖ / nr) * ‖x - nr‖ ≤ (‖t‖ / nr) * 1 := by
      exact mul_le_mul_of_nonneg_left
        (Eq.subst
          (motive := fun r : ℝ => r ≤ 1)
          hdist_eq.symm
          hx_sub_le_one)
        hscale_nonneg
    exact le_trans hmvt
      (Eq.subst
        (motive := fun r : ℝ => (‖t‖ / nr) * ‖x - nr‖ ≤ r)
        (mul_one (‖t‖ / nr))
        hscaled)
  have hx_phase :
      phase x = ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx_pos
  have hn_phase :
      phase nr = ((nr : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hnr_pos
  have htarget_eq :
      ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((nr : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        phase x - phase nr := by
    exact congrArg₂ Sub.sub hx_phase.symm hn_phase.symm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖t‖ / (((n : ℕ) : ℝ)))
    htarget_eq.symm
    hmvt_unit

/-- One-interval movement bound for the normalized derivative kernel after
separating reciprocal drift and phase drift. -/
theorem boundaryLineOnePointRealParam_oneInterval_normalizedKernel_movement_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
          (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  have hsplit :
      ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / (nr : ℂ)) *
            (((nr : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
        ‖(-(t : ℂ) * Complex.I)‖ *
            ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖(-(t : ℂ) * Complex.I)‖ *
            ‖(nr : ℂ)⁻¹‖ *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
    boundaryLineOnePointRealParam_normalizedKernel_movement_norm_le_reciprocal_add_phase
      t x nr
  have ha_norm : ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hrecip :
      ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ ≤
        (1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
      hn hx
  have hphase :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ / (((n : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_phase_drift_norm_le t hn hx
  have hphase_norm_nonneg :
      0 ≤ ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
    norm_nonneg (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hfirst :
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
    have hmiddle :
        ‖t‖ * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ ≤
          ‖t‖ * ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hrecip (norm_nonneg t)
    have hproduct :
        ‖t‖ * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ :=
      mul_le_mul_of_nonneg_right hmiddle hphase_norm_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r * ‖(x : ℂ)⁻¹ - (nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖)
      ha_norm.symm
      hproduct
  have hsecond :
      ‖(-(t : ℂ) * Complex.I)‖ *
          ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        ‖t‖ * ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
          (‖t‖ / (((n : ℕ) : ℝ))) := by
    have hleft_nonneg : 0 ≤ ‖t‖ * ‖(nr : ℂ)⁻¹‖ :=
      mul_nonneg (norm_nonneg t) (norm_nonneg ((nr : ℂ)⁻¹))
    have hproduct :
        ‖t‖ * ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ * ‖(nr : ℂ)⁻¹‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hphase hleft_nonneg
    exact Eq.subst
      (motive := fun r : ℝ =>
        r * ‖(nr : ℂ)⁻¹‖ *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((nr : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          ‖t‖ * ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
            (‖t‖ / (((n : ℕ) : ℝ))))
      ha_norm.symm
      hproduct
  exact le_trans hsplit (add_le_add hfirst hsecond)

/-- Pointwise one-interval bound after subtracting the left-endpoint
normalized kernel using the Bernoulli zero-mean cancellation. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
            (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  let K : ℝ → ℂ := fun y =>
    (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
      (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hbernoulli :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((n : ℕ) : ℝ)))‖ ≤
        ‖K x - K (((n : ℕ) : ℝ))‖ :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_pointwise_norm_le
      n K x
  have hmovement :
      ‖K x - K (((n : ℕ) : ℝ))‖ ≤
        ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖t‖ *
            ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
              (‖t‖ / (((n : ℕ) : ℝ))) :=
    boundaryLineOnePointRealParam_oneInterval_normalizedKernel_movement_norm_le
      t hn hx
  exact le_trans hbernoulli hmovement

/-- Unit norm of the positive-real logarithmic phase written in complex-power
notation. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖((x : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) := by
  have hphase :
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        ((x : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t hx
  have hnorm :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        (1 : ℝ) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm t x
  exact Eq.trans (congrArg norm hphase.symm) hnorm

/-- Norm of the reciprocal of a positive real embedded in `ℂ`. -/
theorem boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv
    {x : ℝ}
    (hx : 0 < x) :
    ‖((x : ℂ)⁻¹)‖ = x⁻¹ := by
  have hnorm_inv :
      ‖((x : ℂ)⁻¹)‖ = (‖(x : ℂ)‖)⁻¹ :=
    norm_inv (x : ℂ)
  have hnorm_real :
      ‖(x : ℂ)‖ = x := by
    exact Eq.trans (RCLike.norm_ofReal x) (abs_of_pos hx)
  exact Eq.trans hnorm_inv (congrArg Inv.inv hnorm_real)

/-- Simplified pointwise one-interval bound for the Bernoulli-subtracted
normalized kernel.

This is the absolute local movement estimate.  The later finite-defect theorem
still needs the genuine oscillatory summation/blocking upgrade; this lemma
only supplies the correct local integrand bound after the Bernoulli zero-mean
subtraction. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le_scalarMovement
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n)
    {x : ℝ}
    (hx : x ∈ Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
            (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
        ‖t‖ *
          (((n : ℕ) : ℝ)⁻¹) *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
  let nr : ℝ := ((n : ℕ) : ℝ)
  have hnr_pos : 0 < nr :=
    Nat.cast_pos.mpr hn
  have hx_pos : 0 < x :=
    lt_trans hnr_pos hx.1
  have hraw :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
              (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
        ‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
              ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
          ‖t‖ *
            ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
              (‖t‖ / (((n : ℕ) : ℝ))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le
      t hn hx
  have hphase_norm :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
      t hx_pos
  have hinv_norm :
      ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ = nr⁻¹ :=
    boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv hnr_pos
  have hright :
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) =
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
        ‖t‖ *
          (((n : ℕ) : ℝ)⁻¹) *
            (‖t‖ / (((n : ℕ) : ℝ))) := by
    calc
      ‖t‖ *
          ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
            ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ +
        ‖t‖ *
          ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
            (‖t‖ / (((n : ℕ) : ℝ))) =
          ‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) *
                (1 : ℝ) +
            ‖t‖ *
              ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
                (‖t‖ / (((n : ℕ) : ℝ))) := by
        exact congrArg
          (fun y : ℝ =>
            ‖t‖ *
                ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) * y +
              ‖t‖ *
                ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
                  (‖t‖ / (((n : ℕ) : ℝ))))
          hphase_norm
      _ =
          ‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
            ‖t‖ *
              ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
                (‖t‖ / (((n : ℕ) : ℝ))) := by
        exact congrArg
          (fun y : ℝ =>
            y +
              ‖t‖ *
                ‖(((((n : ℕ) : ℝ) : ℂ)⁻¹)‖ *
                  (‖t‖ / (((n : ℕ) : ℝ))))
          (mul_one
            (‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ)))))
      _ =
          ‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
            ‖t‖ *
              (((n : ℕ) : ℝ)⁻¹) *
                (‖t‖ / (((n : ℕ) : ℝ))) := by
        exact congrArg
          (fun y : ℝ =>
            ‖t‖ *
                ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
              ‖t‖ * y * (‖t‖ / (((n : ℕ) : ℝ))))
          hinv_norm
  exact Eq.subst
    (motive := fun r : ℝ =>
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
              (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤ r)
    hright.symm
    hraw

/-- One-interval integral domination for the Bernoulli-subtracted normalized
kernel by the scalar movement majorant. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
              (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖ ≤
      ∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
          ‖t‖ *
            (((n : ℕ) : ℝ)⁻¹) *
              (‖t‖ / (((n : ℕ) : ℝ)))) := by
  let s : Set ℝ := Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
          (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
  let G : ℝ :=
    ‖t‖ *
        ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
      ‖t‖ *
        (((n : ℕ) : ℝ)⁻¹) *
          (‖t‖ / (((n : ℕ) : ℝ)))
  let g : ℝ → ℝ := fun _x => G
  have hle :
      (((n : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.le_succ n)
  have hg :
      Integrable g (volume.restrict s) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const (μ := volume) (a := (((n : ℕ) : ℝ)))
        (b := (((n + 1 : ℕ) : ℝ))) (c := G))
  have hbound :
      ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_pointwise_norm_le_scalarMovement
          t hn hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Every index in the post-cutoff open-right interval is positive. -/
theorem boundaryLineOnePointRealParam_postCutoff_Ioc_index_pos
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    0 < n := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  exact lt_trans hcutoff_pos hcutoff_lt_n

/-- Finite summation of the one-interval scalar movement bounds over the
post-cutoff interval.

This is the finite accumulation theorem produced directly by the one-interval
movement and Bernoulli cancellation lemmas.  The remaining hard step for the
visible selected endpoint/variation theorem is the oscillatory blocking
upgrade from this absolute scalar movement sum to the required
`4 * sqrt (1 + |t|) * log (2 + M)` finite-defect bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((( -(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) / ((((n : ℕ) : ℝ) : ℂ))) *
                (((((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) / (((n : ℕ) : ℝ) * ((n : ℕ) : ℝ))) +
            ‖t‖ *
              (((n : ℕ) : ℝ)⁻¹) *
                (‖t‖ / (((n : ℕ) : ℝ)))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t
          (boundaryLineOnePointRealParam_postCutoff_Ioc_index_pos t hn))

/-- Right-endpoint indexed form of the one-interval Bernoulli cancellation
movement estimate.

The global post-cutoff remainder is naturally indexed by right endpoints
`n ∈ (C,M]`; the contributing unit interval is therefore based at `n - 1`.
This is the local estimate in exactly that indexing. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))‖ ≤
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
          ‖t‖ *
            (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
              (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  let m : ℕ := n - 1
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hcutoff_lt_n
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
      t hm_pos

/-- Right-endpoint indexed local estimate over the literal interval `(n-1,n]`.

This is only the endpoint arithmetic transport of
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement`;
it keeps the finite-block cancellation statement aligned with the global
post-cutoff interval decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_subtracted_normalizedKernel_integral_norm_le_scalarMovement
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
            (((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))‖ ≤
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        (‖t‖ *
            ((1 : ℝ) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
          ‖t‖ *
            (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
              (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hsucc : n - 1 + 1 = n :=
    Nat.sub_add_cancel hn_pos
  exact
    Eq.subst
      (motive := fun q : ℕ =>
        ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))))
      hsucc
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
        t hn)

/-- Finite summation of the right-endpoint indexed local Bernoulli cancellation
movement estimates.

This is the source-level finite block estimate immediately upstream of the
normalized Bernoulli block-cancellation theorem. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_rightEndpointInterval_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n - 1 + 1 : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_rightEndpointInterval_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t hn)

/-- Finite summation of the literal `(n-1,n]` right-endpoint local cancellation
estimates.

This is the block-local norm estimate in the same indexing as the post-cutoff
Euler-Maclaurin finite defect. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖) ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_subtracted_normalizedKernel_integral_norm_le_scalarMovement
          t hn)

/-- Norm bound for the finite sum of right-endpoint local Bernoulli
cancellation blocks.

This is the assembled finite local-movement estimate.  It is the last purely
absolute estimate before the genuinely oscillatory block-cancellation
absorption needed for the `2 * sqrt (1 + |t|) * log (2 + M)` remainder bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ} :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  let F : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
          (((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))))
  let G : ℕ → ℝ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      (‖t‖ *
          ((1 : ℝ) /
            (((((n - 1 : ℕ) : ℕ) : ℝ)) *
              ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
        ‖t‖ *
          (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
            (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ)))))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, F n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) F
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, G n :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_integral_norm_le_scalarMovementSum
      t
  exact le_trans htriangle hlocal

/-- Natural right-endpoint unit intervals `(n-1,n]` are pairwise disjoint.

This is the measure-theoretic owner input needed to assemble the local
Bernoulli zero-mean blocks into the global post-cutoff remainder integral. -/
theorem boundaryGrowth_pairwiseDisjoint_Ioc_pred_self_natCast :
    Pairwise
      (Disjoint on
        (fun n : ℕ =>
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hmono : Monotone (fun n : ℕ => ((n : ℕ) : ℝ)) :=
    Nat.cast_mono
  exact hmono.pairwise_disjoint_on_Ioc_pred

/-- Finite-subset form of the disjointness of natural right-endpoint unit
intervals. -/
theorem boundaryGrowth_pairwiseDisjoint_finset_Ioc_pred_self_natCast
    (s : Finset ℕ) :
    Set.Pairwise (↑s : Set ℕ)
      (Disjoint on
        (fun n : ℕ =>
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  exact
    Set.Pairwise.mono
      (fun n _hn => Set.mem_univ n)
      boundaryGrowth_pairwiseDisjoint_Ioc_pred_self_natCast

/-- Finite set-integral decomposition over natural right-endpoint unit
intervals.

This is the measure-theoretic assembly lemma needed to replace the global
post-cutoff Bernoulli remainder integral by the finite sum of local
zero-mean blocks. -/
theorem boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
    (s : Finset ℕ)
    (f : ℝ → ℂ)
    (hf :
      ∀ n ∈ s,
        IntegrableOn f
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
          volume) :
    (∫ x in ⋃ n ∈ s,
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
      ∑ n ∈ s,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x := by
  exact
    integral_finset_biUnion
      s
      (fun n _hn => measurableSet_Ioc)
      (boundaryGrowth_pairwiseDisjoint_finset_Ioc_pred_self_natCast s)
      hf

/-- Membership in the natural right-endpoint interval `(n-1,n]` is equivalent
to having natural ceiling `n`. -/
theorem boundaryGrowth_mem_Ioc_pred_self_iff_natCeil_eq
    {n : ℕ}
    (hn : n ≠ 0)
    (x : ℝ) :
    x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) ↔
      Nat.ceil x = n := by
  have hpre :
      (Nat.ceil : ℝ → ℕ) ⁻¹' {n} =
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
    Nat.preimage_ceil_of_ne_zero hn
  have hmem :
      x ∈ (Nat.ceil : ℝ → ℕ) ⁻¹' {n} ↔
        x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
    congrArg (fun s : Set ℝ => x ∈ s) hpre
  exact Iff.intro
    (fun hx =>
      have hx_pre :
          x ∈ (Nat.ceil : ℝ → ℕ) ⁻¹' {n} :=
        hmem.mpr hx
      Set.mem_singleton_iff.mp hx_pre)
    (fun hx =>
      hmem.mp
        (Set.mem_singleton_iff.mpr hx))

/-- The finite union of natural right-endpoint intervals over `(C,M]` covers
exactly the real interval `(C,M]`. -/
theorem boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc
    (C M : ℕ) :
    (⋃ n ∈ Finset.Ioc C M,
        Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
      Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) := by
  exact Set.ext
    (fun x =>
      Iff.intro
        (fun hx =>
          match hx with
          | ⟨n, hn_mem, hx_interval⟩ =>
              have hC_lt_n : C < n :=
                (Finset.mem_Ioc.mp hn_mem).1
              have hn_le_M : n ≤ M :=
                (Finset.mem_Ioc.mp hn_mem).2
              have hC_le_pred : C ≤ n - 1 :=
                Nat.le_sub_one_of_lt hC_lt_n
              have hC_real_le_pred :
                  (((C : ℕ) : ℝ)) ≤ ((((n - 1 : ℕ) : ℕ) : ℝ)) :=
                Nat.cast_le.mpr hC_le_pred
              have hleft :
                  (((C : ℕ) : ℝ)) < x :=
                lt_of_le_of_lt hC_real_le_pred hx_interval.1
              have hright :
                  x ≤ (((M : ℕ) : ℝ)) :=
                le_trans hx_interval.2 (Nat.cast_le.mpr hn_le_M)
              ⟨hleft, hright⟩)
        (fun hx =>
          let n : ℕ := Nat.ceil x
          have hn_eq : Nat.ceil x = n := rfl
          have hC_lt_n : C < n := by
            exact Nat.lt_ceil.mpr hx.1
          have hn_le_M : n ≤ M := by
            exact Nat.ceil_le.mpr hx.2
          have hn_ne_zero : n ≠ 0 :=
            ne_of_gt (lt_of_le_of_lt (Nat.zero_le C) hC_lt_n)
          have hx_interval :
              x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)) :=
            (boundaryGrowth_mem_Ioc_pred_self_iff_natCeil_eq hn_ne_zero x).mpr
              hn_eq
          ⟨n, Finset.mem_Ioc.mpr ⟨hC_lt_n, hn_le_M⟩, hx_interval⟩))

/-- Exact finite-block decomposition of the global normalized Bernoulli
remainder into right-endpoint local zero-mean blocks, assuming the concrete
local integrability facts needed by the Bochner subtraction identity.

The remaining owner task after this lemma is to discharge these integrability
facts for the normalized kernel and then apply the oscillatory block estimate
to the displayed finite sum. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hBK :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hBc :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let K : ℝ → ℂ := fun x =>
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hcover :
      (⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
        Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) :=
    boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc C M
  have hdomain :
      (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) =
        ∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    congrArg
      (fun s : Set ℝ => ∫ x in s, f x)
      hcover.symm
  have hsplit :
      (∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
      (Finset.Ioc C M) f
      (fun n hn => hBK n hn)
  have hlocal :
      (∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ)))) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        have hC_lt_n : C < n :=
          (Finset.mem_Ioc.mp hn).1
        have hcutoff_pos : 0 < C :=
          boundaryLineOnePointRealParam_cutoff_pos t
        have hn_pos : 0 < n :=
          lt_trans hcutoff_pos hC_lt_n
        have hsucc : n - 1 + 1 = n :=
          Nat.sub_add_cancel hn_pos
        have hBK_local :
            Integrable
              (fun x : ℝ =>
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
              (volume.restrict
                (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                  ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)))) :=
          Eq.subst
            (motive := fun q : ℕ =>
              Integrable
                (fun x : ℝ =>
                  ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
                (volume.restrict
                  (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                    ((((q : ℕ) : ℕ) : ℝ)))))
            hsucc.symm
            (hBK n hn)
        have hBc_local :
            Integrable
              (fun x : ℝ =>
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  K (((n - 1 : ℕ) : ℝ)))
              (volume.restrict
                (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                  ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)))) :=
          Eq.subst
            (motive := fun q : ℕ =>
              Integrable
                (fun x : ℝ =>
                  ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                    K (((n - 1 : ℕ) : ℝ)))
                (volume.restrict
                  (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                    ((((q : ℕ) : ℕ) : ℝ)))))
            hsucc.symm
            (hBc n hn)
        have hraw :
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
              (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ))
                ((((n - 1 + 1 : ℕ) : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ))))) :=
          boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
            (n - 1)
            K
            hBK_local
            hBc_local
        Eq.subst
          (motive := fun q : ℕ =>
            (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) =
              (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ))))))
          hsucc
          hraw)
  calc
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x := rfl
    _ = ∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
      hdomain
    _ = ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
      hsplit
    _ = ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (K x - K (((((n - 1 : ℕ) : ℕ) : ℝ)))) :=
      hlocal
    _ = ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) := rfl

/-- Norm consequence of the global-to-local zero-mean block decomposition.

This is the exact bridge from the normalized Bernoulli remainder to the finite
sum of local scalar movement controls.  The remaining cancellation task is to
absorb that finite local expression into the sharper
`2 * sqrt (1 + |t|) * log (2 + M)` bound. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum_of_integrable
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hBK :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hBc :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        Integrable
          (fun x : ℝ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))
          (volume.restrict
            (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  have hdecomp :
      (∫ x in Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t hM hBK hBc
  have hsum :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_postCutoff_Ioc_pred_self_subtracted_normalizedKernel_sum_norm_le_scalarMovementSum
      t
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            (‖t‖ *
                ((1 : ℝ) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                    ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
              ‖t‖ *
                (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                  (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))))
    hdecomp.symm
    hsum

/-- Local integrability of the constant left-endpoint normalized kernel after
multiplication by the first periodic Bernoulli factor.

This discharges the constant half of the local zero-mean subtraction
integrability requirements in the global block decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) /
              (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  let c : ℂ :=
    (((-(t : ℂ) * Complex.I) /
        (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)))
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) := by
    exact Nat.cast_le.mpr (Nat.sub_le n 1)
  have hc_integrable :
      IntegrableOn
        (fun _x : ℝ => c)
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const
        (μ := volume)
        (a := ((((n - 1 : ℕ) : ℕ) : ℝ)))
        (b := (((n : ℕ) : ℝ)))
        (c := c))
  have hmul :
      IntegrableOn
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c)
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun _x : ℝ => c)
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hc_integrable
  exact hmul

/-- Local integrability of the nonconstant normalized logarithmic-phase kernel
on one post-cutoff unit block. -/
theorem boundaryLineOnePointRealParam_Ioc_pred_self_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hC_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hC_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_cpow :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hcont_inv :
      ContinuousOn
        (fun x : ℝ => (x : ℂ)⁻¹)
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuous_ofReal.continuousAt.inv
        (by
          exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx_pos))).continuousWithinAt
  have hconst_mul_inv :
      ContinuousOn
        (fun x : ℝ => (-(t : ℂ) * Complex.I) * (x : ℂ)⁻¹)
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :=
    continuousOn_const.mul hcont_inv
  have hdiv_eq :
      (fun x : ℝ => (-(t : ℂ) * Complex.I) / (x : ℂ)) =
        (fun x : ℝ => (-(t : ℂ) * Complex.I) * (x : ℂ)⁻¹) := by
    funext x
    exact div_eq_mul_inv (-(t : ℂ) * Complex.I) (x : ℂ)
  have hcont_kernel :
      ContinuousOn
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    exact
      Eq.subst
        (motive := fun φ : ℝ → ℂ =>
          ContinuousOn
            (fun x : ℝ =>
              φ x * (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
            (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))
        hdiv_eq.symm
        (hconst_mul_inv.mul hcont_cpow)
  have hinterval :
      IntervalIntegrable
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        volume
        ((((n - 1 : ℕ) : ℕ) : ℝ))
        (((n : ℕ) : ℝ)) :=
    hcont_kernel.intervalIntegrable
  exact
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hinterval

/-- Local integrability of the nonconstant normalized logarithmic-phase kernel
after multiplication by the first periodic Bernoulli factor. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hkernel :
      IntegrableOn
        (fun x : ℝ =>
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    boundaryLineOnePointRealParam_Ioc_pred_self_normalizedKernel_integrable
      t hn
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ =>
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hkernel

/-- Exact finite-block decomposition of the global normalized Bernoulli
remainder into right-endpoint local zero-mean blocks, with the concrete local
normalized-kernel integrability facts discharged. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)

/-- Norm form of the exact global-to-local oscillatory block decomposition for
the normalized Bernoulli remainder.

This keeps the cancellation problem on the finite complex block sum, before
passing to any absolute scalar movement envelope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_eq_sum_Ioc_pred_self_subtracted_norm
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ =
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ := by
  exact
    congrArg
      (fun z : ℂ => ‖z‖)
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted
        t hM)

/-- The normalized Bernoulli remainder cancellation estimate follows from the
corresponding finite oscillatory block-sum estimate.

This is the precise bridge from the true finite block cancellation theorem to
the selected endpoint/variation package. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_of_finiteOscillatoryBlockSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblocks :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_eq_sum_Ioc_pred_self_subtracted_norm
        t hM).symm
      hblocks

/-- The canonical post-cutoff scale dominates the unit bound used by the
summable reciprocal-drift part of the finite block decomposition. -/
theorem boundaryLineOnePointRealParam_one_le_two_sqrt_one_add_norm_mul_log_two_add_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hproduct_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    one_le_mul hsqrt_ge_one hlog_lower_M
  calc
    (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      hproduct_ge_one
    _ ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
      le_mul_of_one_le_left
        (mul_nonneg (Real.sqrt_nonneg (1 + ‖t‖))
          (le_trans (show (0 : ℝ) ≤ 1 from zero_le_one) hlog_lower_M))
        (show (1 : ℝ) ≤ 2 from one_le_two)
    _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
      (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm

/-- The canonical post-cutoff scale itself dominates the unit reciprocal-drift
bound. -/
theorem boundaryLineOnePointRealParam_one_le_sqrt_one_add_norm_mul_log_two_add_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  exact one_le_mul hsqrt_ge_one hlog_lower_M

/-- The reciprocal-drift unit contribution and one sharp phase contribution
fit inside the existing `2 * sqrt (1 + |t|) * log (2 + M)` block scale. -/
theorem boundaryLineOnePointRealParam_one_add_sqrt_log_le_two_sqrt_log_postCutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (1 : ℝ) + Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  have hone_le_A : (1 : ℝ) ≤ A :=
    boundaryLineOnePointRealParam_one_le_sqrt_one_add_norm_mul_log_two_add_postCutoff
      t ht hM
  have hsum : (1 : ℝ) + A ≤ A + A :=
    add_le_add_right hone_le_A A
  have htwo : A + A = 2 * A :=
    (two_mul A).symm
  exact Eq.subst
    (motive := fun r : ℝ => (1 : ℝ) + A ≤ r)
    htwo
    hsum

/-- Pointwise algebraic split of the local normalized-kernel defect into
reciprocal drift and phase drift.

This is the reusable owner-level algebra behind the finite block cancellation:
it separates the exact defect before any norm or scalar majorant is taken. -/
theorem boundaryLineOnePointRealParam_normalizedKernel_defect_eq_reciprocal_add_phase_pointwise
    (t : ℝ)
    (x : ℝ)
    (y : ℂ) :
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((-(t : ℂ) * Complex.I) / y) *
        (y ^ (-(t : ℂ) * Complex.I)))) =
      (-(t : ℂ) * Complex.I) *
        ((((x : ℂ)⁻¹ - y⁻¹) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          y⁻¹ *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (y ^ (-(t : ℂ) * Complex.I)))) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  let P : ℂ := (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let Q : ℂ := y ^ (-(t : ℂ) * Complex.I)
  have hx_div : (-(t : ℂ) * Complex.I) / (x : ℂ) = A * (x : ℂ)⁻¹ :=
    div_eq_mul_inv A (x : ℂ)
  have hy_div : (-(t : ℂ) * Complex.I) / y = A * y⁻¹ :=
    div_eq_mul_inv A y
  have hinner :
      ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) =
        (((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q) := by
    calc
      ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) =
          (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
            ((y⁻¹ * P) - (y⁻¹ * Q)) := by
        have hcancel :
            (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
                ((y⁻¹ * P) - (y⁻¹ * Q)) =
              ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) := by
          calc
            (((x : ℂ)⁻¹ * P) - (y⁻¹ * P)) +
                ((y⁻¹ * P) - (y⁻¹ * Q)) =
                (((x : ℂ)⁻¹ * P) + -(y⁻¹ * P)) +
                  ((y⁻¹ * P) + -(y⁻¹ * Q)) := by
              exact congrArg₂ Add.add
                (sub_eq_add_neg ((x : ℂ)⁻¹ * P) (y⁻¹ * P))
                (sub_eq_add_neg (y⁻¹ * P) (y⁻¹ * Q))
            _ = ((x : ℂ)⁻¹ * P) +
                  (-(y⁻¹ * P) + ((y⁻¹ * P) + -(y⁻¹ * Q))) := by
              exact add_assoc (((x : ℂ)⁻¹ * P)) (-(y⁻¹ * P))
                ((y⁻¹ * P) + -(y⁻¹ * Q))
            _ = ((x : ℂ)⁻¹ * P) +
                  ((-(y⁻¹ * P) + (y⁻¹ * P)) + -(y⁻¹ * Q)) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + z)
                (add_assoc (-(y⁻¹ * P)) (y⁻¹ * P) (-(y⁻¹ * Q))).symm
            _ = ((x : ℂ)⁻¹ * P) + (0 + -(y⁻¹ * Q)) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + (z + -(y⁻¹ * Q)))
                (neg_add_cancel (y⁻¹ * P))
            _ = ((x : ℂ)⁻¹ * P) + -(y⁻¹ * Q) := by
              exact congrArg
                (fun z : ℂ => ((x : ℂ)⁻¹ * P) + z)
                (zero_add (-(y⁻¹ * Q)))
            _ = ((x : ℂ)⁻¹ * P) - (y⁻¹ * Q) := by
              exact (sub_eq_add_neg ((x : ℂ)⁻¹ * P) (y⁻¹ * Q)).symm
        exact hcancel.symm
      _ = (((x : ℂ)⁻¹ - y⁻¹) * P) + ((y⁻¹ * P) - (y⁻¹ * Q)) := by
        exact congrArg (fun z : ℂ => z + ((y⁻¹ * P) - (y⁻¹ * Q)))
          (sub_mul ((x : ℂ)⁻¹) y⁻¹ P).symm
      _ = (((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q) := by
        exact congrArg
          (fun z : ℂ => (((x : ℂ)⁻¹ - y⁻¹) * P) + z)
          (mul_sub y⁻¹ P Q).symm
  calc
    (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((-(t : ℂ) * Complex.I) / y) *
        (y ^ (-(t : ℂ) * Complex.I)))) =
        (A * (x : ℂ)⁻¹) * P - (A * y⁻¹) * Q := by
      exact congrArg₂ Sub.sub
        (congrArg (fun z : ℂ => z * P) hx_div)
        (congrArg (fun z : ℂ => z * Q) hy_div)
    _ = A * (((x : ℂ)⁻¹ * P) - (y⁻¹ * Q)) := by
      exact (mul_sub A (((x : ℂ)⁻¹) * P) (y⁻¹ * Q)).symm
    _ = A * ((((x : ℂ)⁻¹ - y⁻¹) * P) + y⁻¹ * (P - Q)) := by
      exact congrArg (fun z : ℂ => A * z) hinner
    _ = (-(t : ℂ) * Complex.I) *
        ((((x : ℂ)⁻¹ - y⁻¹) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          y⁻¹ *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              (y ^ (-(t : ℂ) * Complex.I)))) := rfl

/-- Exact finite algebraic split of the oscillatory Bernoulli block sum into
reciprocal-drift and phase-drift pieces inside each local block.

This is the first Dirichlet/Abel block decomposition before taking norms: the
oscillatory factors remain inside the finite sum, so no cancellation has
been discarded into the scalar movement envelope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_eq_reciprocal_add_phaseBlocks
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) =
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) := by
  let A : ℂ := -(t : ℂ) * Complex.I
  have hlocal :
      ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I))))))) := by
    intro n _hn
    let y : ℂ := (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)
    let s : Set ℝ :=
      Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))
    let B : ℝ → ℂ := fun x =>
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
    let P : ℝ → ℂ := fun x =>
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
    let Py : ℂ := y ^ (-(t : ℂ) * Complex.I)
    have hpoint :
        (fun x : ℝ =>
          B x *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                P x) -
              (((-(t : ℂ) * Complex.I) / y) * Py)))) =
          (fun x : ℝ =>
            B x *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ - y⁻¹) * P x +
                  y⁻¹ * (P x - Py)))) := by
      funext x
      have hkernel :
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) * P x -
              (((-(t : ℂ) * Complex.I) / y) * Py)) =
            A * ((((x : ℂ)⁻¹ - y⁻¹) * P x) +
              y⁻¹ * (P x - Py)) :=
        boundaryLineOnePointRealParam_normalizedKernel_defect_eq_reciprocal_add_phase_pointwise
          t x y
      calc
        B x *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                P x) -
              (((-(t : ℂ) * Complex.I) / y) * Py))) =
            B x *
              (A * ((((x : ℂ)⁻¹ - y⁻¹) * P x) +
                y⁻¹ * (P x - Py))) := by
          exact congrArg (fun z : ℂ => B x * z) hkernel
    have hintegral :
        (∫ x in s,
          B x *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                P x) -
              (((-(t : ℂ) * Complex.I) / y) * Py)))) =
          (∫ x in s,
            B x *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ - y⁻¹) * P x +
                  y⁻¹ * (P x - Py)))) := by
      exact congrArg (fun f : ℝ → ℂ => ∫ x in s, f x) hpoint
    exact hintegral
  have hsum :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I))))))) := by
    exact Finset.sum_congr rfl hlocal
  exact hsum

/-- Pointwise distribution of the already-split normalized-kernel block into
the reciprocal-drift and phase-drift summands.

This is the algebraic local sink needed before the finite block sum can be
estimated by the reciprocal telescope plus the sharp Bernoulli phase
cancellation. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integrand_eq_reciprocal_add_phaseDrift
    (t : ℝ)
    (n : ℕ)
    (x : ℝ) :
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) =
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))) := by
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let A : ℂ := -(t : ℂ) * Complex.I
  let R : ℂ :=
    (((x : ℂ)⁻¹ -
        (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  let P : ℂ :=
    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
      ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I))))
  calc
    B * (A * (R + P)) = B * (A * R + A * P) := by
      exact congrArg (fun z : ℂ => B * z) (mul_add A R P)
    _ = B * (A * R) + B * (A * P) := by
      exact mul_add B (A * R) (A * P)
    _ =
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))) := rfl

/-- Local integral-level distribution of one split normalized-kernel block.

The only hypotheses are the concrete local integrability facts needed for
Bochner linearity of the reciprocal-drift and phase-drift summands. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integral_eq_reciprocal_add_phaseDrift
    (t : ℝ)
    (n : ℕ)
    (hrecip :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))))
    (hphase :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))
        (volume.restrict
          (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))))) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))) +
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) := by
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I)))))) := by
    funext x
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_splitBlock_integrand_eq_reciprocal_add_phaseDrift
        t n x
  have hintegral :
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) +
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) +
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((-(t : ℂ) * Complex.I) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                    ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                        (-(t : ℂ) * Complex.I)))))) := by
    exact congrArg
      (fun f : ℝ → ℂ =>
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x)
      hpoint
  exact Eq.trans hintegral
    (integral_add hrecip hphase)

/-- Pointwise reciprocal-drift bound on a selected right-endpoint block.

This is the local analytic input for the reciprocal-variation half of the
normalized Bernoulli block cancellation.  The oscillatory factor has unit norm,
the first periodic Bernoulli factor is bounded by one, and the reciprocal
movement is controlled by the square of the left endpoint. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_pointwise_norm_le
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M)
    {x : ℝ}
    (hx : x ∈ Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) :
    ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
        ((1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) := by
  let m : ℕ := n - 1
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hcutoff_lt_n
  have hn_eq : m + 1 = n :=
    Nat.sub_add_cancel (lt_trans hcutoff_pos hcutoff_lt_n)
  have hx_m :
      x ∈ Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)) := by
    exact Eq.subst
      (motive := fun q : ℕ =>
        x ∈ Set.Ioc (((m : ℕ) : ℝ)) (((q : ℕ) : ℝ)))
      hn_eq.symm
      hx
  have hB :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ (1 : ℝ) :=
    eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_finite x
  have ha :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hrecip :
      ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ ≤
        (1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ)) :=
    boundaryLineOnePointRealParam_oneInterval_reciprocal_movement_norm_le
      hm_pos hx_m
  have hx_pos : 0 < x :=
    lt_trans (Nat.cast_pos.mpr hm_pos) hx_m.1
  have hphase :
      ‖(((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_logarithmicPhase_cpow_norm_eq_one_of_pos
      t hx_pos
  have hraw :
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((m : ℕ) : ℝ) : ℂ)⁻¹) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
        ‖t‖ *
          ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
    calc
      ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((m : ℕ) : ℝ) : ℂ)⁻¹) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖(-(t : ℂ) * Complex.I)‖ *
              ‖((x : ℂ)⁻¹ -
                  (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
        calc
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖(-(t : ℂ) * Complex.I) *
                  (((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ := by
            exact norm_mul
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              ((-(t : ℂ) * Complex.I) *
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
          _ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                (‖(-(t : ℂ) * Complex.I)‖ *
                  ‖((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖) := by
            exact congrArg
              (fun r : ℝ =>
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ * r)
              (norm_mul (-(t : ℂ) * Complex.I)
                (((x : ℂ)⁻¹ -
                    (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
          _ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖(-(t : ℂ) * Complex.I)‖ *
                  ‖((x : ℂ)⁻¹ -
                      (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ := by
            exact (mul_assoc
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖
              ‖(-(t : ℂ) * Complex.I)‖
              ‖((x : ℂ)⁻¹ -
                  (((m : ℕ) : ℝ) : ℂ)⁻¹) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖).symm
      _ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖t‖ *
              (‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ * (1 : ℝ)) := by
        exact congrArg₂ HMul.hMul
          (congrArg (fun r : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ * r) ha)
          (Eq.trans
            (norm_mul
              ((x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹)
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
            (congrArg
              (fun r : ℝ =>
                ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ * r)
              hphase))
      _ =
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
            ‖t‖ *
              ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖ := by
        exact congrArg
          (fun r : ℝ =>
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
              ‖t‖ * r)
          (mul_one ‖(x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹‖)
      _ ≤
          (1 : ℝ) * ‖t‖ *
            ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul hB (le_rfl : ‖t‖ ≤ ‖t‖)
            (norm_nonneg t) (norm_nonneg ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)))
          hrecip
          (norm_nonneg ((x : ℂ)⁻¹ - (((m : ℕ) : ℝ) : ℂ)⁻¹))
          (mul_nonneg (norm_nonneg ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ))
            (norm_nonneg t))
      _ =
          ‖t‖ *
            ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
        exact congrArg
          (fun r : ℝ =>
            r * ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ))))
          (one_mul ‖t‖)
  exact hraw

/-- Lebesgue measure of a natural unit right-endpoint block is one. -/
theorem boundaryGrowth_volume_Ioc_nat_unit_toReal
    (n : ℕ) :
    (volume (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ)))).toReal =
      (1 : ℝ) := by
  have hvolume :
      volume (Set.Ioc (((n : ℕ) : ℝ)) (((n + 1 : ℕ) : ℝ))) =
        ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ))) :=
    Real.volume_Ioc
  have hlength :
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) = (1 : ℝ) := by
    have hsucc : (((n + 1 : ℕ) : ℝ)) = ((n : ℕ) : ℝ) + (1 : ℝ) :=
      Nat.cast_add_one n
    calc
      (((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ)) =
          (((n : ℕ) : ℝ) + (1 : ℝ)) - (((n : ℕ) : ℝ)) := by
        exact congrArg (fun r : ℝ => r - (((n : ℕ) : ℝ))) hsucc
      _ = (1 : ℝ) := by
        exact add_sub_cancel_left (((n : ℕ) : ℝ)) 1
  have hofReal :
      ENNReal.ofReal ((((n + 1 : ℕ) : ℝ)) - (((n : ℕ) : ℝ))) =
        ENNReal.ofReal (1 : ℝ) :=
    congrArg ENNReal.ofReal hlength
  have htoReal :
      (ENNReal.ofReal (1 : ℝ)).toReal = (1 : ℝ) :=
    ENNReal.toReal_ofReal zero_le_one
  exact Eq.trans
    (congrArg ENNReal.toReal (Eq.trans hvolume hofReal))
    htoReal

/-- Local reciprocal-drift block estimate in right-endpoint indexing. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlock_norm_le
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            (((x : ℂ)⁻¹ -
                (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      ‖t‖ *
        ((1 : ℝ) /
          (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ)))) := by
  let m : ℕ := n - 1
  let s : Set ℝ := Set.Ioc (((m : ℕ) : ℝ)) (((n : ℕ) : ℝ))
  let C : ℝ :=
    ‖t‖ *
      ((1 : ℝ) / (((m : ℕ) : ℝ) * ((m : ℕ) : ℝ)))
  let F : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((-(t : ℂ) * Complex.I) *
        (((x : ℂ)⁻¹ -
            (((m : ℕ) : ℝ) : ℂ)⁻¹) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hm_succ : m + 1 = n :=
    Nat.sub_add_cancel hn_pos
  have hmeasure :
      (volume s).toReal = (1 : ℝ) := by
    exact Eq.subst
      (motive := fun q : ℕ =>
        (volume (Set.Ioc (((m : ℕ) : ℝ)) (((q : ℕ) : ℝ)))).toReal =
          (1 : ℝ))
      hm_succ
      (boundaryGrowth_volume_Ioc_nat_unit_toReal m)
  have hbound :
      ∀ x ∈ s, ‖F x‖ ≤ C := by
    intro x hx
    exact
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDrift_pointwise_norm_le
        t hn hx
  have hset :
      ‖∫ x in s, F x‖ ≤ C * (volume s).toReal :=
    norm_setIntegral_le_of_norm_le_const'
      (measure_Ioc_lt_top : volume s < ∞)
      measurableSet_Ioc
      hbound
  have hcollapse :
      C * (volume s).toReal = C := by
    exact Eq.trans
      (congrArg (fun r : ℝ => C * r) hmeasure)
      (mul_one C)
  exact le_trans hset
    (le_of_eq hcollapse)

/-- Finite reciprocal-drift block sum bound for the selected normalized-kernel
decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlockSum_norm_le_one
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              (((x : ℂ)⁻¹ -
                  (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))‖ ≤
      1 := by
  let R : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          (((x : ℂ)⁻¹ -
              (((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
  let S : ℕ → ℝ := fun n =>
    ‖t‖ *
      ((1 : ℝ) /
        (((n - 1 : ℕ) : ℝ) * (((n - 1 : ℕ) : ℝ))))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, R n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖R n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) R
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖R n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, S n :=
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_reciprocalDriftBlock_norm_le
          t hn)
  have hscalar :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, S n) ≤ 1 :=
    boundaryLineOnePointRealParam_reciprocalVariation_selected_Ioc_sum_le_one
      t ht hM
  exact le_trans htriangle
    (le_trans hlocal hscalar)

/-- Local phase-drift block after pulling out the constant normalized
left-endpoint coefficient.

This is the algebraic owner form needed before applying finite
Dirichlet/Abel cancellation to the remaining Bernoulli-weighted phase
increments. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
    (t : ℝ)
    {n : ℕ} :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))))) =
      ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) *
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) := by
  let c : ℂ :=
    (-(t : ℂ) * Complex.I) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
  let s : Set ℝ :=
    Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))
  let F : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))
  have hpoint :
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        (fun x : ℝ => c * F x) := by
    funext x
    calc
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))) =
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (c *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))) := by
        exact congrArg
          (fun z : ℂ =>
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * z)
          (mul_assoc (-(t : ℂ) * Complex.I)
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))
      _ =
          c * (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) := by
        calc
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (c *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))) =
              (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * c) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))) := by
            exact mul_assoc
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              c
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))
          _ =
              (c * ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))) := by
            exact congrArg
              (fun z : ℂ =>
                z *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))
              (mul_comm ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) c)
          _ =
              c * (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))) := by
            exact (mul_assoc c
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))).symm
  have hintegral :
      (∫ x in s,
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        ∫ x in s, c * F x := by
    exact congrArg (fun G : ℝ → ℂ => ∫ x in s, G x) hpoint
  have hconst :
      (∫ x in s, c * F x) = c * ∫ x in s, F x :=
    integral_const_mul c F
  exact Eq.trans hintegral hconst

/-- The constant coefficient in each factored phase-drift block is bounded by
one after the canonical cutoff. -/
theorem boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_le_one
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖((-(t : ℂ) * Complex.I) *
        ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))‖ ≤ (1 : ℝ) := by
  let m : ℕ := n - 1
  let mr : ℝ := ((m : ℕ) : ℝ)
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_le_m : ⌊2 + ‖t‖⌋₊ ≤ m :=
    Nat.le_sub_one_of_lt hcutoff_lt_n
  have hnorm_le_mr :
      ‖t‖ ≤ mr := by
    exact le_trans
      (le_trans
        (le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 from zero_le_one))
        (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t))
      (Nat.cast_le.mpr hcutoff_le_m)
  have hm_pos_nat : 0 < m :=
    lt_of_lt_of_le
      (boundaryLineOnePointRealParam_cutoff_pos t)
      hcutoff_le_m
  have hmr_pos : 0 < mr :=
    Nat.cast_pos.mpr hm_pos_nat
  have hnum :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hinv :
      ‖((mr : ℂ)⁻¹)‖ = mr⁻¹ :=
    boundaryLineOnePointRealParam_complex_inv_ofReal_norm_eq_inv hmr_pos
  have hmul :
      ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
        ‖t‖ * mr⁻¹ := by
    calc
      ‖((-(t : ℂ) * Complex.I) * ((mr : ℂ)⁻¹))‖ =
          ‖(-(t : ℂ) * Complex.I)‖ * ‖((mr : ℂ)⁻¹)‖ := by
        exact norm_mul (-(t : ℂ) * Complex.I) ((mr : ℂ)⁻¹)
      _ = ‖t‖ * ‖((mr : ℂ)⁻¹)‖ := by
        exact congrArg (fun r : ℝ => r * ‖((mr : ℂ)⁻¹)‖) hnum
      _ = ‖t‖ * mr⁻¹ := by
        exact congrArg (fun r : ℝ => ‖t‖ * r) hinv
  have hratio :
      ‖t‖ * mr⁻¹ ≤ (1 : ℝ) := by
    have hdiv : ‖t‖ / mr ≤ (1 : ℝ) :=
      (div_le_one₀ hmr_pos).mpr hnorm_le_mr
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      (div_eq_mul_inv ‖t‖ mr)
      hdiv
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ (1 : ℝ))
    hmul.symm
    hratio

/-- Local phase-drift block norm after removing the harmless cutoff-normalized
left-endpoint coefficient. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_norm_le_phaseIncrementIntegral_norm
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))))))‖ ≤
      ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))‖ := by
  let c : ℂ :=
    (-(t : ℂ) * Complex.I) *
      ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹))
  let J : ℂ :=
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))
  have hfactor :
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))) =
        c * J :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
      t
  have hc : ‖c‖ ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_phaseDrift_leftEndpointCoefficient_norm_le_one
      t hn
  have hnorm :
      ‖c * J‖ ≤ ‖J‖ := by
    calc
      ‖c * J‖ = ‖c‖ * ‖J‖ := by
        exact norm_mul c J
      _ ≤ (1 : ℝ) * ‖J‖ := by
        exact mul_le_mul hc (le_rfl : ‖J‖ ≤ ‖J‖) (norm_nonneg J) (norm_nonneg c)
      _ = ‖J‖ := by
        exact one_mul ‖J‖
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖J‖)
    hfactor.symm
    hnorm

/-- Finite phase-drift block sum after coefficient removal.

This is the summed non-circular reduction of the phase-drift part: the
remaining estimate is exactly the finite Dirichlet/Abel cancellation for the
Bernoulli-weighted phase-increment integrals. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_phaseIncrementIntegralNormSum
    (t : ℝ)
    {M : ℕ} :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ‖∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))‖ := by
  let F : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((-(t : ℂ) * Complex.I) *
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))))
  let G : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))
  have htriangle :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, F n‖ ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖ :=
    norm_sum_le (Finset.Ioc ⌊2 + ‖t‖⌋₊ M) F
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖F n‖) ≤
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, ‖G n‖ :=
    Finset.sum_le_sum
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_norm_le_phaseIncrementIntegral_norm
          t hn)
  exact le_trans htriangle hlocal

/-- Local Bernoulli zero-mean cancellation for phase increments.

On each post-cutoff unit block, subtracting the left-endpoint phase does not
change the first-periodic-Bernoulli integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_phaseIntegral
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let m : ℕ := n - 1
  let K : ℝ → ℂ := fun x =>
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hn_pos : 0 < n :=
    lt_trans hcutoff_pos hcutoff_lt_n
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hm_pos : 0 < m :=
    Nat.sub_pos_of_lt hone_lt_n
  have hsucc : m + 1 = n :=
    Nat.sub_add_cancel hn_pos
  have hle :
      (((m : ℕ) : ℝ)) ≤ (((m + 1 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.le_succ m)
  have hcont_phase :
      ContinuousOn K (Set.Icc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hm_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hphase_integrable :
      IntegrableOn K
        (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      hcont_phase.intervalIntegrable
  have hBK :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x)
        (volume.restrict
          (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))) :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      K
      (((m : ℕ) : ℝ))
      (((m + 1 : ℕ) : ℝ))
      hphase_integrable
  let c : ℂ := K (((m : ℕ) : ℝ))
  have hc_integrable :
      IntegrableOn
        (fun _x : ℝ => c)
        (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      (intervalIntegrable_const
        (μ := volume)
        (a := (((m : ℕ) : ℝ)))
        (b := (((m + 1 : ℕ) : ℝ)))
        (c := c))
  have hBc :
      Integrable
        (fun x : ℝ =>
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            K (((m : ℕ) : ℝ)))
        (volume.restrict
          (Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)))) :=
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun _x : ℝ => c)
      (((m : ℕ) : ℝ))
      (((m + 1 : ℕ) : ℝ))
      hc_integrable
  have hraw :
      (∫ x in Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (K x - K (((m : ℕ) : ℝ)))) =
        (∫ x in Set.Ioc (((m : ℕ) : ℝ)) (((m + 1 : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) * K x) :=
    (boundaryLineOnePointRealParam_firstPeriodicBernoulli_oneInterval_subtract_leftEndpoint
      m K hBK hBc).symm
  exact
    Eq.subst
      (motive := fun q : ℕ =>
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) =
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((q : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))))
      hsucc
      hraw

/-- Pointwise Taylor-linear decomposition of one logarithmic phase increment.

The first term is the resonance-bearing derivative at the left endpoint; the
second term is the nonlinear local remainder.  This is the source object needed
for the unconditional Dirichlet/Abel block cancellation, before any absolute
movement estimate is taken. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_phaseIncrement_eq_linear_add_remainder
    (t : ℝ)
    (x a : ℝ) :
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
          ((x : ℂ) - (a : ℂ)) +
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) - (a : ℂ))) := by
  let P : ℂ :=
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
        ((x : ℂ) - (a : ℂ))
  calc
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        P := rfl
    _ = L + (P - L) := by
      exact (add_sub_cancel' L P).symm
    _ =
      (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
          ((x : ℂ) - (a : ℂ)) +
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
            (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
            ((x : ℂ) - (a : ℂ))) := rfl

/-- Integral form of the local Taylor-linear phase-block decomposition.

This keeps the first-periodic Bernoulli weight inside the local block while
exposing the derivative-at-left-endpoint main term and the nonlinear remainder.
The later cancellation theorem can now attack the main term by finite
Dirichlet/Abel summation and the remainder by a genuinely smaller local
estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_add_remainder
    (t : ℝ)
    (n : ℕ) :
    (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((((-(t : ℂ) * Complex.I) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) *
              ((x : ℂ) -
                (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))) +
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)) -
              ((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))))) := by
  let a : ℝ := ((((n - 1 : ℕ) : ℕ) : ℝ))
  let s : Set ℝ := Set.Ioc a (((n : ℕ) : ℝ))
  let B : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let F : ℝ → ℂ := fun x =>
    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℝ → ℂ := fun x =>
    (((-(t : ℂ) * Complex.I) / (a : ℂ)) *
        (((a : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) *
        ((x : ℂ) - (a : ℂ))
  have hpoint :
      (fun x : ℝ => B x * F x) =
        (fun x : ℝ => B x * (L x + (F x - L x))) := by
    funext x
    have hphase :
        F x = L x + (F x - L x) :=
      boundaryLineOnePointRealParam_logarithmicPhase_phaseIncrement_eq_linear_add_remainder
        t x a
    exact congrArg (fun z : ℂ => B x * z) hphase
  exact congrArg (fun f : ℝ → ℂ => ∫ x in s, f x) hpoint

/-- Finite post-cutoff sum form of the Taylor-linear phase-block decomposition.

This is the source-level bridge from the current phase-increment block object to
the two pieces used in the eventual resonance-aware estimate: the
left-endpoint derivative main term and the nonlinear Taylor remainder. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_linear_add_remainder
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) *
                ((x : ℂ) -
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ))) +
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)) -
                ((((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))) *
                  ((x : ℂ) -
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)))))) := by
  exact Finset.sum_congr rfl
    (fun n _hn =>
      boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_linear_add_remainder
        t n)

/-- Local integrability of the Bernoulli-weighted logarithmic phase on one
post-cutoff unit block. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_phase_integrable
    (t : ℝ)
    {M n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M) :
    Integrable
      (fun x : ℝ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (volume.restrict
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))) := by
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn).1
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_lt_n : 1 < n :=
    lt_of_le_of_lt hone_le_cutoff hcutoff_lt_n
  have hn_pred_pos : 0 < n - 1 :=
    Nat.sub_pos_of_lt hone_lt_n
  have hle :
      ((((n - 1 : ℕ) : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) :=
    Nat.cast_le.mpr (Nat.sub_le n 1)
  have hcont_phase :
      ContinuousOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Icc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) := by
    intro x hx
    have hx_pos : 0 < x :=
      lt_of_lt_of_le (Nat.cast_pos.mpr hn_pred_pos) hx.1
    exact
      (Complex.continuousAt_ofReal_cpow_const x (-(t : ℂ) * Complex.I)
        (Or.inr (ne_of_gt hx_pos))).continuousWithinAt
  have hphase_integrable :
      IntegrableOn
        (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)))
        volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp
      hcont_phase.intervalIntegrable
  exact
    eulerMaclaurin_bernoulli_mul_integrableOn_Ioc
      (fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      ((((n - 1 : ℕ) : ℕ) : ℝ))
      (((n : ℕ) : ℝ))
      hphase_integrable

/-- Global assembly of the finite Bernoulli-weighted phase-integral blocks.

This is the finite complex object produced after local phase-increment
cancellation; the remaining analytic step is the Dirichlet/Abel bound for this
single post-cutoff oscillatory integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIntegralBlockSum_eq_global
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℝ → ℂ := fun x =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hcover :
      (⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ))) =
        Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)) :=
    boundaryGrowth_biUnion_Ioc_pred_self_natCast_eq_Ioc C M
  have hsplit :
      (∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x) =
        ∑ n ∈ Finset.Ioc C M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    boundaryGrowth_integral_finset_biUnion_Ioc_pred_self_natCast
      (Finset.Ioc C M)
      f
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_phase_integrable
          t hn)
  have hdomain :
      (∫ x in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)), f x) =
        ∫ x in ⋃ n ∈ Finset.Ioc C M,
          Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)), f x :=
    congrArg
      (fun s : Set ℝ => ∫ x in s, f x)
      hcover.symm
  exact
    Eq.symm
      (Eq.trans hdomain hsplit)

/-- Global Bernoulli-weighted phase integral as the finite sum of local
zero-mean phase-increment blocks.

This is the non-absolute cancellation form needed by the Dirichlet/Abel
blocking estimate: each local integral has had its left-endpoint phase removed
using the one-interval Bernoulli zero-mean identity, while the total remains the
single global oscillatory phase integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
    (t : ℝ)
    {M : ℕ} :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  have hlocal :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementIntegral_eq_phaseIntegral
          t hn)
  exact Eq.trans hlocal
    (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIntegralBlockSum_eq_global
      t)

/-- Quantitative transfer from the global Bernoulli-weighted phase integral to
the finite zero-mean phase-increment block sum.

This is the exact non-absolute bridge needed after the global
Dirichlet/Abel/stationary-phase estimate for
`∫ B₁(x) x^{-it}` is proved: no local scalar movement envelope is used. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_of_globalPhaseIntegral
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t).symm
      hphase

/-- Monotonicity of the logarithmic terminal scale on natural endpoints. -/
theorem boundaryLineOnePointRealParam_log_two_add_nat_mono
    {K M : ℕ}
    (hKM : K ≤ M) :
    Real.log (2 + K) ≤ Real.log (2 + M) := by
  have hleft_pos : 0 < (2 : ℝ) + K :=
    lt_of_lt_of_le zero_lt_two
      (le_add_of_nonneg_right (Nat.cast_nonneg K))
  have harg_le : (2 : ℝ) + K ≤ (2 : ℝ) + M :=
    add_le_add_left (Nat.cast_le.mpr hKM) 2
  exact Real.log_le_log hleft_pos harg_le

/-- Local-terminal phase-increment partial-sum bound from the corresponding
global Bernoulli-weighted phase-integral estimates and endpoint monotonicity. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ∀ K : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ K →
      K ≤ M →
        ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))‖ ≤
          2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  intro K hK hKM
  have hlocal :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_norm_le_of_globalPhaseIntegral
      t (hphase K hK hKM)
  have hscale_nonneg :
      0 ≤ 2 * Real.sqrt (1 + ‖t‖) :=
    mul_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two)
      (Real.sqrt_nonneg (1 + ‖t‖))
  have hlog_le :
      Real.log (2 + K) ≤ Real.log (2 + M) :=
    boundaryLineOnePointRealParam_log_two_add_nat_mono hKM
  exact le_trans hlocal
    (mul_le_mul_of_nonneg_left hlog_le hscale_nonneg)

/-- Finite Abel/Dirichlet absorption for the concrete phase-drift block sum.

This is the coefficient-summation step for the actual phase-drift blocks:
`(-it)/(n-1)` is factored into a fixed unit complex direction and the positive
decreasing weight `|t|/(n-1)`, then finite Abel summation is applied to the
unweighted phase-increment block sequence. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    {B : ℝ}
    (hpartial :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
            ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤ B := by
  let D : ℂ := (-(t : ℂ) * Complex.I) / ((‖t‖ : ℝ) : ℂ)
  let U : ℕ → ℂ := fun n =>
    ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))
  let W : ℕ → ℂ := fun n =>
    (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ) * U n)
  have hblock :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
        D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n := by
    have hlocal :
        ∀ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) =
            D * W n := by
      intro n hn
      have hfactor :
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I))))))) =
            ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) * U n :=
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlock_eq_const_mul_phaseIncrementIntegral
          t
      have hcoeff :
          ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) =
            D * (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ) :=
        boundaryLineOnePointRealParam_phaseDrift_rightEndpointCoefficient_eq_direction_mul_weight
          t ht hn
      calc
        (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((-(t : ℂ) * Complex.I) *
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))) =
            ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹)) * U n :=
          hfactor
        _ = (D * (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) * U n := by
          exact congrArg (fun z : ℂ => z * U n) hcoeff
        _ = D * W n := by
          exact (mul_assoc D (((‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))) : ℝ) : ℂ)) (U n)).symm
    have hsum :
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((-(t : ℂ) * Complex.I) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
                  ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                    ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                      (-(t : ℂ) * Complex.I)))))))) =
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, D * W n :=
      Finset.sum_congr rfl hlocal
    exact Eq.trans hsum (Finset.mul_sum.symm)
  have hweighted :
      ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W k‖ ≤ B :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientWeight_finite_sum_norm_le_of_local
      t ht hM U hpartial
  have hD_norm : ‖D‖ = (1 : ℝ) :=
    boundaryLineOnePointRealParam_phaseDrift_coefficientDirection_norm_eq_one
      t ht
  have hmul_bound :
      ‖D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ ≤ B := by
    calc
      ‖D * ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ =
          ‖D‖ * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact norm_mul D (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n)
      _ = (1 : ℝ) * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact congrArg
          (fun r : ℝ => r * ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖)
          hD_norm
      _ = ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖ := by
        exact one_mul ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M, W n‖
      _ ≤ B := hweighted
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ B)
      hblock.symm
      hmul_bound

/-- Concrete phase-drift block bound from terminal-local global phase-integral
estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_globalPhaseIntegral_family
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
      t ht hM
      (B := 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family
        t hphase)

/-- Sharp local-terminal phase-increment partial-sum bound from the
corresponding sharp global Bernoulli-weighted phase-integral estimates.

This is the constant-correct version needed for the selected
normalized-kernel cancellation: the phase-drift side must consume only one
copy of `sqrt (1 + |t|) log (2 + M)`, leaving the other copy to absorb the
reciprocal-drift telescope. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family_sharp
    (t : ℝ)
    {M : ℕ}
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ∀ K : ℕ,
      ⌊2 + ‖t‖⌋₊ ≤ K →
      K ≤ M →
        ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))‖ ≤
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  intro K hK hKM
  have hlocal :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ K,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
              ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))))‖ ≤
        Real.sqrt (1 + ‖t‖) * Real.log (2 + K) :=
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + K))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrementBlockSum_eq_globalPhaseIntegral
        t).symm
      (hphase K hK hKM)
  have hscale_nonneg :
      0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hlog_le :
      Real.log (2 + K) ≤ Real.log (2 + M) :=
    boundaryLineOnePointRealParam_log_two_add_nat_mono hKM
  exact le_trans hlocal
    (mul_le_mul_of_nonneg_left hlog_le hscale_nonneg)

/-- Sharp finite Abel/Dirichlet phase-drift block bound from sharp
terminal-local global phase-integral estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_globalPhaseIntegral_family_sharp
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hphase :
      ∀ K : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ K →
        K ≤ M →
          ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((K : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            Real.sqrt (1 + ‖t‖) * Real.log (2 + K)) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          ((-(t : ℂ) * Complex.I) *
            ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ)⁻¹) *
              ((((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I)))))))‖ ≤
      Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseDriftBlockSum_norm_le_of_phaseIncrement_partial_sums
      t ht hM
      (B := Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_phaseIncrement_partial_sums_norm_le_of_globalPhaseIntegral_family_sharp
        t hphase)

/-- Norm consequence of the global-to-local zero-mean block decomposition,
with the local normalized-kernel integrability obligations discharged. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc
        (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          (‖t‖ *
              ((1 : ℝ) /
                (((((n - 1 : ℕ) : ℕ) : ℝ)) *
                  ((((n - 1 : ℕ) : ℕ) : ℝ)))) +
            ‖t‖ *
              (((((n - 1 : ℕ) : ℕ) : ℝ))⁻¹) *
                (‖t‖ / (((((n - 1 : ℕ) : ℕ) : ℝ))))) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_norm_le_scalarMovementSum_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)

/-- Finite first-order Euler-Maclaurin identity for the unweighted
logarithmic-phase post-cutoff tail, normalized to the derivative kernel used by
the boundary-line Dirichlet package. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hstandard :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (-((t : ℂ) * Complex.I) *
                (((x : ℝ) : ℂ) ^
                  (-(((t : ℂ) * Complex.I) + 1))))) :=
    eulerMaclaurin_firstOrder_cpow_neg_finite_postCutoffTail_identity_standard
      ((t : ℂ) * Complex.I)
      ⌊2 + ‖t‖⌋₊
      M
      hcutoff_pos
      hM
  have hremainder :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (-((t : ℂ) * Complex.I) *
            (((x : ℝ) : ℂ) ^ (-(((t : ℂ) * Complex.I) + 1))))) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_standard_eq_normalized
      t hM
  exact Eq.trans hstandard
    (congrArg
      (fun R : ℂ =>
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          R)
      hremainder)

/-- Solved-for normalized Bernoulli remainder in the boundary-line finite
Euler-Maclaurin identity.

This is the boundary-growth specialization of the finite Bernoulli
integration-by-parts primitive: the normalized remainder is exactly the
post-cutoff finite sum minus the main integral and the two half-endpoint terms. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) -
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hem :
      S = I + L + U + R :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
      t hM
  have hpeel_I :
      I + L + U + R - I = L + U + R := by
    calc
      I + L + U + R - I =
          (I + (L + U + R)) - I := by
        exact congrArg (fun z : ℂ => z - I)
          (Eq.trans
            (add_assoc (I + L) U R)
            (Eq.trans
              (add_assoc I L (U + R))
              (congrArg (fun z : ℂ => I + z) (add_assoc L U R).symm)))
      _ = L + U + R := by
        exact add_sub_cancel_left I (L + U + R)
  have hpeel_L :
      (L + U + R) - L = U + R := by
    calc
      (L + U + R) - L =
          (L + (U + R)) - L := by
        exact congrArg (fun z : ℂ => z - L)
          (add_assoc L U R)
      _ = U + R := by
        exact add_sub_cancel_left L (U + R)
  have hpeel_U :
      (U + R) - U = R := by
    calc
      (U + R) - U = R + U - U := by
        exact congrArg (fun z : ℂ => z - U) (add_comm U R)
      _ = R := by
        exact add_sub_cancel_right R U
  have hraw :
      (I + L + U + R) - I - L - U = R := by
    calc
      (I + L + U + R) - I - L - U =
          (L + U + R) - L - U := by
        exact congrArg (fun z : ℂ => z - L - U) hpeel_I
      _ = (U + R) - U := by
        exact congrArg (fun z : ℂ => z - U) hpeel_L
      _ = R := hpeel_U
  have hsolved :
      R = S - I - L - U := by
    calc
      R = (I + L + U + R) - I - L - U := hraw.symm
      _ = S - I - L - U := by
        exact congrArg (fun z : ℂ => z - I - L - U) hem.symm
  exact hsolved

/-- Exact post-cutoff Euler-Maclaurin decomposition for the unweighted
logarithmic-phase tail.

The existing post-cutoff Abel theorem controls the weighted tail
`n⁻¹ n^{-it}`.  The public partial-sum bound needs this separate unweighted
identity for `n^{-it}`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_eulerMaclaurin_decomposition_ownerGap
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
        (-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hsplit :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ +
          ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq_prefix_add_Ioc_tail_ownerGap
      t hM
  have htail :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_tail_eulerMaclaurin_normalizedDerivative_ownerGap
      t hM
  exact Eq.trans hsplit (congrArg
    (fun z : ℂ =>
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊2 + ‖t‖⌋₊ + z)
    htail)

/-- Positive integer endpoint norm for the unweighted antiderivative
`x^(1-it)`. -/
theorem logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖(n : ℂ) ^ (((-(t : ℂ) * Complex.I) + (1 : ℂ)))‖ =
      (n : ℝ) := by
  have hnorm :
      ‖(n : ℂ) ^ (((-(t : ℂ) * Complex.I) + (1 : ℂ)))‖ =
        (n : ℝ) ^
          (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) :=
    Complex.norm_natCast_cpow_of_pos hn
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)))
  have hre :
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) = (1 : ℝ) := by
    calc
      (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) =
          (-(t : ℂ) * Complex.I).re + ((1 : ℂ) : ℂ).re := by
        exact Complex.add_re (-(t : ℂ) * Complex.I) (1 : ℂ)
      _ = 0 + ((1 : ℂ) : ℂ).re := by
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).re)
          (Complex.mul_I_re (-(t : ℂ)))
      _ = 0 + 1 := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re 1)
      _ = 1 := by
        exact zero_add 1
  have hpow_one :
      (n : ℝ) ^
          (((-(t : ℂ) * Complex.I) + (1 : ℂ)).re) =
        (n : ℝ) := by
    exact Eq.trans
      (congrArg (fun r : ℝ => (n : ℝ) ^ r) hre)
      (Real.rpow_one (n : ℝ))
  exact Eq.trans hnorm hpow_one

/-- The denominator `1 - it` dominates the vertical frequency. -/
theorem logarithmicPhase_norm_le_one_minus_it_norm
    (t : ℝ) :
    ‖t‖ ≤ ‖((-(t : ℂ) * Complex.I) + (1 : ℂ))‖ := by
  let D : ℂ := (-(t : ℂ) * Complex.I) + (1 : ℂ)
  have hD_im : D.im = -t := by
    calc
      D.im = (-(t : ℂ) * Complex.I).im + ((1 : ℂ) : ℂ).im := by
        exact Complex.add_im (-(t : ℂ) * Complex.I) (1 : ℂ)
      _ = (-(t : ℂ)).re + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).im)
          (Complex.mul_I_im (-(t : ℂ)))
      _ = -((t : ℂ).re) + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => r + ((1 : ℂ) : ℂ).im)
          (Complex.neg_re (t : ℂ))
      _ = -t + ((1 : ℂ) : ℂ).im := by
        exact congrArg (fun r : ℝ => -r + ((1 : ℂ) : ℂ).im)
          (Complex.ofReal_re t)
      _ = -t + 0 := by
        exact congrArg (fun r : ℝ => -t + r) (Complex.ofReal_im 1)
      _ = -t := by
        exact add_zero (-t)
  have habs_im_le_abs : |D.im| ≤ Complex.abs D :=
    Complex.abs_im_le_abs D
  have hnorm_eq_abs : ‖D‖ = Complex.abs D :=
    Complex.norm_eq_abs D
  have hfreq :
      ‖t‖ = |D.im| := by
    have hnorm_real : ‖t‖ = |t| :=
      Real.norm_eq_abs t
    have habs_neg : |-t| = |t| :=
      abs_neg t
    exact Eq.trans hnorm_real
      (Eq.trans habs_neg.symm (congrArg abs hD_im.symm))
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ ‖D‖)
    hfreq
    (Eq.subst
      (motive := fun r : ℝ => |D.im| ≤ r)
      hnorm_eq_abs.symm
      habs_im_le_abs)

/-- Main-integral estimate in the unweighted post-cutoff Dirichlet package.

The `M / |t|` term is the unavoidable primitive size of `x^{-it}`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_mainIntegral_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
        Real.log (2 + M) := by
  have hraw :
      (∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        (((((M : ℕ) : ℝ) : ℂ) ^ ((-(t : ℂ) * Complex.I) + (1 : ℂ))) -
            (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              ((-(t : ℂ) * Complex.I) + (1 : ℂ)))) /
          ((-(t : ℂ) * Complex.I) + (1 : ℂ)) := by
    exact
      integral_cpow
        (a := (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
        (b := (((M : ℕ) : ℝ)))
        (r := (-(t : ℂ) * Complex.I))
        (Or.inr
          ⟨by
            intro hsing
            have hsing_add :
                (-(t : ℂ) * Complex.I) + (1 : ℂ) =
                  (-1 : ℂ) + (1 : ℂ) :=
              congrArg (fun z : ℂ => z + (1 : ℂ)) hsing
            have hleft :
                (-(t : ℂ) * Complex.I) + (1 : ℂ) =
                  (1 : ℂ) + (-(t : ℂ) * Complex.I) :=
              add_comm (-(t : ℂ) * Complex.I) (1 : ℂ)
            have hright :
                (-1 : ℂ) + (1 : ℂ) = (0 : ℂ) :=
              neg_add_cancel (1 : ℂ)
            have hone_minus_it_zero :
                (1 : ℂ) + (-(t : ℂ) * Complex.I) = (0 : ℂ) :=
              Eq.trans hleft.symm (Eq.trans hsing_add hright)
            have hre :
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re =
                  ((0 : ℂ) : ℂ).re :=
              congrArg Complex.re hone_minus_it_zero
            have hleft_re :
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re = (1 : ℝ) := by
              calc
                ((1 : ℂ) + (-(t : ℂ) * Complex.I)).re =
                    ((1 : ℂ) : ℂ).re + (-(t : ℂ) * Complex.I).re := by
                  exact Complex.add_re (1 : ℂ) (-(t : ℂ) * Complex.I)
                _ = 1 + (-(t : ℂ) * Complex.I).re := by
                  exact congrArg (fun r : ℝ => r + (-(t : ℂ) * Complex.I).re)
                    (Complex.ofReal_re 1)
                _ = 1 + 0 := by
                  exact congrArg (fun r : ℝ => 1 + r)
                    (Complex.mul_I_re (-(t : ℂ)))
                _ = 1 := by
                  exact add_zero 1
            have hright_re :
                ((0 : ℂ) : ℂ).re = (0 : ℝ) :=
              Complex.zero_re
            have hone_eq_zero : (1 : ℝ) = 0 :=
              Eq.trans hleft_re.symm (Eq.trans hre hright_re)
            exact one_ne_zero hone_eq_zero,
            boundaryLineOnePointRealParam_logarithmicPhase_postCutoff_zero_not_mem_uIcc
              t hM⟩)
  have htransport :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∫ x in (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))..(((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    (intervalIntegral.integral_of_le
      (f := fun x : ℝ => (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (Nat.cast_le.mpr hM)).symm
  let U : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ) ^ ((-(t : ℂ) * Complex.I) + (1 : ℂ)))
  let L : ℂ :=
    (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
      ((-(t : ℂ) * Complex.I) + (1 : ℂ))))
  let D : ℂ := (-(t : ℂ) * Complex.I) + (1 : ℂ)
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        (U - L) / D :=
    Eq.trans htransport hraw
  have hU_norm : ‖U‖ ≤ (M : ℝ) := by
    have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
      boundaryLineOnePointRealParam_cutoff_pos t
    have hM_pos : 0 < M :=
      lt_of_lt_of_le hcutoff_pos hM
    exact le_of_eq
      (logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat t hM_pos)
  have hL_norm : ‖L‖ ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
    exact le_of_eq
      (logarithmicPhase_nat_sample_one_minus_it_norm_eq_nat t
        (boundaryLineOnePointRealParam_cutoff_pos t))
  have hcutoff_le_M :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ (M : ℝ) :=
    Nat.cast_le.mpr hM
  have hnum_le :
      ‖U - L‖ ≤ (2 : ℝ) * (M : ℝ) := by
    have htriangle : ‖U - L‖ ≤ ‖U‖ + ‖L‖ :=
      norm_sub_le U L
    have hendpoints : ‖U‖ + ‖L‖ ≤ (M : ℝ) + (M : ℝ) :=
      add_le_add hU_norm (le_trans hL_norm hcutoff_le_M)
    have htwice : (M : ℝ) + (M : ℝ) = (2 : ℝ) * (M : ℝ) := by
      exact (two_mul (M : ℝ)).symm
    exact le_trans htriangle
      (Eq.subst
        (motive := fun r : ℝ => ‖U‖ + ‖L‖ ≤ r)
        htwice
        hendpoints)
  have hD_norm_ge_t : ‖t‖ ≤ ‖D‖ := by
    exact logarithmicPhase_norm_le_one_minus_it_norm t
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one ht) hD_norm_ge_t
  have hquot_le :
      ‖(U - L) / D‖ ≤ ((2 : ℝ) * (M : ℝ)) / ‖D‖ := by
    have hquot_norm : ‖(U - L) / D‖ = ‖U - L‖ / ‖D‖ :=
      norm_div (U - L) D
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ ((2 : ℝ) * (M : ℝ)) / ‖D‖)
      hquot_norm.symm
      (div_le_div_of_nonneg_right hnum_le (le_of_lt hD_pos))
  have hquot_le_t :
      ((2 : ℝ) * (M : ℝ)) / ‖D‖ ≤ ((2 : ℝ) * (M : ℝ)) / ‖t‖ := by
    have hnum_nonneg : 0 ≤ (2 : ℝ) * (M : ℝ) :=
      mul_nonneg zero_le_two (Nat.cast_nonneg M)
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_le_div_of_nonneg_left hnum_nonneg ht_pos hD_norm_ge_t
  have hmain_le :
      ‖(U - L) / D‖ ≤ (2 : ℝ) * ((M : ℝ) / ‖t‖) :=
    have hmul_div :
        ((2 : ℝ) * (M : ℝ)) / ‖t‖ =
          (2 : ℝ) * ((M : ℝ) / ‖t‖) :=
      mul_div_assoc (2 : ℝ) (M : ℝ) ‖t‖
    le_trans hquot_le
      (Eq.subst
        (motive := fun r : ℝ => ((2 : ℝ) * (M : ℝ)) / ‖D‖ ≤ r)
        hmul_div
        hquot_le_t)
  have hlog_lower : (1 : ℝ) ≤ Real.log (2 + M) := by
    have hM_ge_one_add_norm :
        (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
      le_trans
        (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
        (Nat.cast_le.mpr hM)
    have harg_le :
        2 + ‖t‖ ≤ (2 : ℝ) + M := by
      have hone_add_one :
          (1 : ℝ) + 1 = 2 :=
        one_add_one_eq_two
      have htwo_add_norm :
          2 + ‖t‖ = 1 + (1 + ‖t‖) := by
        calc
          2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
            exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
          _ = 1 + (1 + ‖t‖) := by
            exact add_assoc (1 : ℝ) 1 ‖t‖
      calc
        2 + ‖t‖ = 1 + (1 + ‖t‖) :=
          htwo_add_norm
        _ ≤ 1 + (M : ℝ) :=
          add_le_add_left hM_ge_one_add_norm 1
        _ ≤ 2 + (M : ℝ) :=
          add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
    have harg_pos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    exact le_trans
      (one_le_log_two_add_norm_of_one_le_norm ht)
      (Real.log_le_log harg_pos harg_le)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hbase_le :
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) := by
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right hsqrt_nonneg)
      zero_le_two
  have htarget_ge_base :
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) := by
    have hleft_nonneg :
        0 ≤ 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
      mul_nonneg zero_le_two
        (add_nonneg
          (div_nonneg (Nat.cast_nonneg M) (norm_nonneg t))
          hsqrt_nonneg)
    calc
      (2 : ℝ) * ((M : ℝ) / ‖t‖) ≤
          2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) :=
        hbase_le
      _ = 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) * 1 := by
        exact (mul_one
          (2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))).symm
      _ ≤ 2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) :=
        mul_le_mul_of_nonneg_left hlog_lower hleft_nonneg
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤
        2 * ((M : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M))
    hidentity.symm
    (le_trans hmain_le htarget_ge_base)

/-- Endpoint estimate for the two half-boundary terms in the unweighted
post-cutoff Euler-Maclaurin decomposition. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(-(1 / 2 : ℂ) *
        ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  have hL : ‖L‖ ≤ (1 : ℝ) :=
    let ε : ℂ := -(1 / 2 : ℂ)
    let P : ℂ :=
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
    have hmul : ‖ε * P‖ = ‖ε‖ * ‖P‖ :=
      norm_mul ε P
    have hε : ‖ε‖ ≤ (1 : ℝ) :=
      boundaryGrowth_complex_neg_one_div_two_norm_le_one
    have hP : ‖P‖ ≤ (1 : ℝ) :=
      logarithmicPhase_nat_sample_norm_le_one t ⌊2 + ‖t‖⌋₊
    have hprod : ‖ε‖ * ‖P‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hε hP (norm_nonneg P) (norm_nonneg ε)
    have hone_mul : (1 : ℝ) * (1 : ℝ) = (1 : ℝ) :=
      one_mul (1 : ℝ)
    Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖ε‖ * ‖P‖ ≤ r)
        hone_mul
        hprod)
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hM_pos : 0 < M :=
    lt_of_lt_of_le hcutoff_pos hM
  have hU : ‖U‖ ≤ (1 : ℝ) :=
    let ε : ℂ := (1 / 2 : ℂ)
    let P : ℂ :=
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
    have hmul : ‖ε * P‖ = ‖ε‖ * ‖P‖ :=
      norm_mul ε P
    have hε : ‖ε‖ ≤ (1 : ℝ) :=
      boundaryGrowth_complex_one_div_two_norm_le_one
    have hP : ‖P‖ ≤ (1 : ℝ) :=
      logarithmicPhase_nat_sample_norm_le_one t M
    have hprod : ‖ε‖ * ‖P‖ ≤ (1 : ℝ) * (1 : ℝ) :=
      mul_le_mul hε hP (norm_nonneg P) (norm_nonneg ε)
    have hone_mul : (1 : ℝ) * (1 : ℝ) = (1 : ℝ) :=
      one_mul (1 : ℝ)
    Eq.subst
      (motive := fun r : ℝ => r ≤ (1 : ℝ))
      hmul.symm
      (Eq.subst
        (motive := fun r : ℝ => ‖ε‖ * ‖P‖ ≤ r)
        hone_mul
        hprod)
  have hsum : ‖L + U‖ ≤ (2 : ℝ) := by
    have htriangle : ‖L + U‖ ≤ ‖L‖ + ‖U‖ :=
      norm_add_le L U
    have hadd : ‖L‖ + ‖U‖ ≤ (2 : ℝ) := by
      calc
        ‖L‖ + ‖U‖ ≤ (1 : ℝ) + 1 :=
          add_le_add hL hU
        _ = (2 : ℝ) :=
          one_add_one_eq_two
    exact le_trans htriangle hadd
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_le_one_add_norm : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Real.one_le_sqrt.mpr hone_le_one_add_norm
  have hM_ge_one_add_norm :
      (1 : ℝ) + ‖t‖ ≤ (M : ℝ) :=
    le_trans
      (boundaryLineOnePointRealParam_postCutoff_one_add_norm_le_cutoff t)
      (Nat.cast_le.mpr hM)
  have harg_le :
      2 + ‖t‖ ≤ (2 : ℝ) + M := by
    have hone_add_one :
        (1 : ℝ) + 1 = 2 :=
      one_add_one_eq_two
    have htwo_add_norm :
        2 + ‖t‖ = 1 + (1 + ‖t‖) := by
      calc
        2 + ‖t‖ = ((1 : ℝ) + 1) + ‖t‖ := by
          exact congrArg (fun x : ℝ => x + ‖t‖) hone_add_one.symm
        _ = 1 + (1 + ‖t‖) := by
          exact add_assoc (1 : ℝ) 1 ‖t‖
    calc
      2 + ‖t‖ = 1 + (1 + ‖t‖) :=
        htwo_add_norm
      _ ≤ 1 + (M : ℝ) :=
        add_le_add_left hM_ge_one_add_norm 1
      _ ≤ 2 + (M : ℝ) :=
        add_le_add_right (show (1 : ℝ) ≤ 2 from one_le_two) (M : ℝ)
  have hlog_lower_norm : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hlog_lower_M : (1 : ℝ) ≤ Real.log (2 + M) := by
    have harg_pos : 0 < 2 + ‖t‖ := by
      exact lt_of_lt_of_le zero_lt_two
        (le_add_of_nonneg_right (norm_nonneg t))
    have hlog_le :
        Real.log (2 + ‖t‖) ≤ Real.log (2 + M) :=
      Real.log_le_log harg_pos harg_le
    exact le_trans hlog_lower_norm hlog_le
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    one_le_mul hsqrt_ge_one hlog_lower_M
  have hrhs_ge_two :
      (2 : ℝ) ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * (Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one zero_le_two
      _ = 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
        (mul_assoc 2 (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
  exact le_trans hsum hrhs_ge_two

/-- Exact selected endpoint/variation split from the solved-form finite
Bernoulli integration-by-parts identity.

The endpoint term is the negative of the two half-endpoint corrections, and
the variation term is the finite oscillatory defect `tail sum - main integral`.
This is the canonical split needed by the quantitative owner theorem below. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_exactSplit_endpointBound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      C =
        -((-(1 / 2 : ℂ) *
            ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I)))) ∧
      V =
        (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let C : ℂ := -(L + U)
  let V : ℂ := S - I
  have hsolved :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        S - I - L - U :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
      t hM
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V := by
    have halg :
        S - I - L - U = C + V := by
      calc
        S - I - L - U =
            (S - I) - (L + U) := by
          exact (sub_sub (S - I) L U).symm
        _ = (S - I) + -(L + U) := by
          exact sub_eq_add_neg (S - I) (L + U)
        _ = -(L + U) + (S - I) := by
          exact add_comm (S - I) (-(L + U))
        _ = C + V := rfl
    exact Eq.trans hsolved halg
  have hendpoint_raw :
      ‖L + U‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
      t ht hM
  have hendpoint :
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    have hnorm : ‖C‖ = ‖L + U‖ :=
      norm_neg (L + U)
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hnorm.symm
      hendpoint_raw
  exact
    Exists.intro C
      (Exists.intro V
        ⟨hidentity, rfl, rfl, hendpoint⟩)

/-- Exact reconstruction of the finite oscillatory defect from the two
Euler-Maclaurin half-endpoints and the normalized Bernoulli remainder.

This is the first non-circular source step toward the post-cutoff defect
estimate: the remaining analytic work is to bound the normalized Bernoulli
remainder itself. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_eq_endpoints_add_normalizedRemainder
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
      ((-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))) +
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  let S : ℂ :=
    ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
      (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)
  let I : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    -(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let U : ℂ :=
    (1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hR :
      R = S - I - L - U :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_remainderIntegral_eq_tail_sub_integral_sub_endpoints
      t hM
  have halg :
      S - I = (L + U) + R := by
    have hsub_pair :
        S - I - L - U = (S - I) - (L + U) :=
      (sub_sub (S - I) L U).symm
    have hR_pair :
        R = (S - I) - (L + U) :=
      Eq.trans hR hsub_pair
    calc
      S - I =
          ((S - I) - (L + U)) + (L + U) := by
        exact (sub_add_cancel (S - I) (L + U)).symm
      _ = (L + U) + ((S - I) - (L + U)) := by
        exact add_comm ((S - I) - (L + U)) (L + U)
      _ = (L + U) + R := by
        exact congrArg (fun z : ℂ => (L + U) + z) hR_pair.symm
  exact halg

/-- Triangle inequality form of the exact post-cutoff defect reconstruction.

This reduces the finite oscillatory defect estimate to two genuine pieces:
the already proved endpoint estimate and the remaining normalized Bernoulli
remainder estimate. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_norm_le_endpoints_add_normalizedRemainder
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      ‖((-(1 / 2 : ℂ) *
          ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))))‖ +
        ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ := by
  let E : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hdefect :
      (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        E + R :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_eq_endpoints_add_normalizedRemainder
      t hM
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖E‖ + ‖R‖)
    hdefect.symm
    (norm_add_le E R)

/-- Absorption of the normalized Bernoulli remainder cancellation estimate into
the finite post-cutoff oscillatory defect bound.

This is the exact owner-level bridge needed by the selected endpoint/variation
theorem: after the Euler-Maclaurin endpoint terms are bounded by
`2 * sqrt(1 + |t|) * log(2 + M)`, it remains only to prove the genuine
oscillatory blocking estimate for the normalized Bernoulli remainder with the
same `2 * sqrt(1 + |t|) * log(2 + M)` scale. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_finiteDefect_norm_le_of_normalizedRemainder_blockCancellation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  let E : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I))) +
      ((1 / 2 : ℂ) *
        ((((M : ℕ) : ℝ) : ℂ) ^
          (-(t : ℂ) * Complex.I)))
  let R : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        ‖E‖ + ‖R‖ :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_defect_norm_le_endpoints_add_normalizedRemainder
      t hM
  have hendpoint :
      ‖E‖ ≤ 2 * A :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
      t ht hM
  have hremainder :
      ‖R‖ ≤ 2 * A :=
    hblock
  have hsum :
      ‖E‖ + ‖R‖ ≤ 2 * A + 2 * A :=
    add_le_add hendpoint hremainder
  have htwo_two :
      2 * A + 2 * A = 4 * A := by
    calc
      2 * A + 2 * A = ((2 : ℝ) + 2) * A := by
        exact (add_mul (2 : ℝ) 2 A).symm
      _ = 4 * A := by
        exact congrArg (fun c : ℝ => c * A)
          (show (2 : ℝ) + 2 = 4 from rfl)
  exact le_trans hdefect
    (Eq.subst
      (motive := fun r : ℝ => ‖E‖ + ‖R‖ ≤ r)
      htwo_two
      hsum)

/-- Quantitative selected endpoint/variation package reduced to the true
finite oscillatory defect estimate.

The exact split theorem above identifies the variation term as
`tail sum - main integral`.  Thus the only remaining analytic input is the
displayed defect bound; no scalar Bernoulli majorant is used here. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_finiteDefect
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_exactSplit_endpointBound
      t ht hM with
  | ⟨C, V, hidentity, _hC_eq, hV_eq, hC_bound⟩ =>
      have hV_bound :
          ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
        exact Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
          hV_eq.symm
          hdefect
      exact Exists.intro C
        (Exists.intro V
          ⟨hidentity, hC_bound, hV_bound⟩)

/-- Canonical fixed-interval endpoint/variation package reduced to the
normalized Bernoulli block-cancellation estimate.

This is the exact bridge from the true oscillatory cancellation theorem to the
selected endpoint/variation surface. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_blockCancellation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hdefect :
      ‖(∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            (((n : ℕ) : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)) -
          (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_finiteDefect_norm_le_of_normalizedRemainder_blockCancellation
      t ht hM hblock
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_finiteDefect
      t ht hM hdefect

/-- Finite oscillatory zero-mean block estimate for the normalized Bernoulli
kernel after the canonical cutoff.

This is the precise finite-block analytic sink left after the global normalized
kernel has been decomposed into right-endpoint zero-mean unit blocks. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
              (((-(t : ℂ) * Complex.I) /
                  (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))))))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  sorry

/-- Transport of a finite zero-mean block estimate back to the global normalized
Bernoulli kernel integral. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_blockCancellation_of_finiteOscillatoryBlockSum
    (t : ℝ)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hblock :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hdecomp :
      (∫ x in Set.Ioc
          (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))
          (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I)))))) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_integral_eq_sum_Ioc_pred_self_subtracted_of_integrable
      t
      hM
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_normalizedKernel_integrable
          t hn)
      (fun n hn =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_Ioc_pred_self_leftEndpoint_normalizedKernel_integrable
          t hn)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hdecomp.symm
      hblock

/-- Normalized Bernoulli block-cancellation estimate on the canonical
post-cutoff interval.

This is the exact oscillatory remainder sink needed by the selected
endpoint/variation package.  It is stronger than the already-assembled `6A`
absolute endpoint-plus-variation consequence and supplies the `2A` cancellation
input required for the finite-defect estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_blockCancellation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  have hblock :
      ‖∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
          ∫ x in Set.Ioc ((((n - 1 : ℕ) : ℕ) : ℝ)) (((n : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                  (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) -
                (((-(t : ℂ) * Complex.I) /
                    (((((n - 1 : ℕ) : ℕ) : ℝ)) : ℂ)) *
                  ((((((n - 1 : ℕ) : ℕ) : ℝ) : ℂ) ^
                    (-(t : ℂ) * Complex.I))))))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_finiteOscillatoryBlockSum_norm_le_ownerGap
      t ht hM
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_blockCancellation_of_finiteOscillatoryBlockSum
      t hM hblock

/-- Canonical fixed-interval integration-by-parts decomposition together with
the endpoint and reciprocal-variation estimates for the selected terms. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_of_blockCancellation
      t ht hM
      (boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_blockCancellation_ownerGap
        t ht hM)

/-- Exact zero-endpoint decomposition for the normalized Bernoulli kernel,
with the endpoint estimate proved directly.

This peels the endpoint part of the fixed-interval integration-by-parts
package.  The remaining analytic content in the full package is the
reciprocal-variation estimate for the selected variation term. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_zeroEndpoint_decomposition_endpointBound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        (0 : ℂ) + V ∧
      ‖(0 : ℂ)‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let V : ℂ :=
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        (0 : ℂ) + V :=
    (zero_add V).symm
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hM_nonneg : 0 ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_nonneg M
  have hlog_nonneg : 0 ≤ Real.log (2 + M) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((M : ℕ) : ℝ) :=
      le_trans one_le_two (le_add_of_nonneg_right hM_nonneg)
    exact Real.log_nonneg hone_le_arg
  have hproduct_nonneg :
      0 ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two) hsqrt_nonneg)
      hlog_nonneg
  have hendpoint :
      ‖(0 : ℂ)‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      hproduct_nonneg
  exact Exists.intro V ⟨hidentity, hendpoint⟩

/-- Endpoint-only existential consequence for the fixed-interval normalized
Bernoulli kernel.

This does not claim the full selected endpoint/variation integration-by-parts
construction; it only discharges the endpoint-bound projection by taking the
endpoint component to be zero.  The full owner theorem above still owns the
genuine reciprocal-variation estimate. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_endpointBound_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_zeroEndpoint_decomposition_endpointBound
      t ht hM with
  | ⟨V, hidentity, hendpoint⟩ =>
      exact Exists.intro (0 : ℂ) (Exists.intro V ⟨hidentity, hendpoint⟩)

/-- Canonical fixed-interval integration-by-parts decomposition for the
first-periodic-Bernoulli normalized kernel.

This is the genuine real-variable summation-by-parts input: on the finite
post-cutoff interval with the canonical logarithmic-phase cutoff as left
endpoint, the normalized kernel is decomposed into endpoint and
reciprocal-variation pieces. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_bounds_ownerIntegrationByParts
      t ht hM

/-- Endpoint bound for the endpoint term selected by the canonical fixed-interval
integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_endpoint_norm_le_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hendpoint

/-- Variation bound for the variation term selected by the canonical
fixed-interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_variation_norm_le_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hvariation

/-- Canonical fixed-interval integration-by-parts package for the
first-periodic-Bernoulli normalized kernel, assembled from its selected
decomposition and the two selected endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_decomposition_ownerIntegrationByParts
      t ht hM

/-- Existential projection of the selected endpoint/variation
integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_decomposition_ownerIntegrationByParts
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V := by
  match
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
      t ht hM with
  | ⟨C, V, hidentity, _hendpoint, _hvariation⟩ =>
      exact Exists.intro C (Exists.intro V hidentity)

/-- Exact endpoint estimate for the endpoint selected by the canonical fixed
interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpoint_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hendpoint

/-- Endpoint estimate for the selected endpoint term in the canonical fixed
interval integration-by-parts decomposition of the first-periodic-Bernoulli
normalized kernel. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_endpointTerm_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hendpoint :
      ‖C‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖C‖ ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpoint_norm_le_ownerDirichletBoundedVariation
      t ht hM C V hidentity hendpoint

/-- Exact reciprocal-variation estimate for the variation term selected by the
canonical fixed-interval integration-by-parts decomposition. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedVariation_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (_hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact hvariation

/-- Reciprocal-variation estimate for the selected variation term in the
canonical fixed interval integration-by-parts decomposition of the
first-periodic-Bernoulli normalized kernel. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_variationTerm_norm_le_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (C V : ℂ)
    (hidentity :
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V)
    (hvariation :
      ‖V‖ ≤
        4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M)) :
    ‖V‖ ≤
      4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedVariation_norm_le_ownerDirichletBoundedVariation
      t ht hM C V hidentity hvariation

/-- Core canonical fixed-interval Dirichlet bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This is now the package wrapper over the integration-by-parts decomposition
and the two selected endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_selectedEndpointVariation_ownerIntegrationByParts
      t ht hM

/-- Canonical fixed-interval bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This is now only the public fixed-interval wrapper.  The actual
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_core_ownerDirichletBoundedVariation
      t ht hM

/-- Cutoff-normalized bounded-variation package for the
first-periodic-Bernoulli normalized kernel.

This theorem is only the cutoff-normalization wrapper.  The actual
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_cutoffNormalized_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N M : ℕ}
    (hN : N = ⌊2 + ‖t‖⌋₊)
    (hM : N ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun K : ℕ =>
        K ≤ M →
          ∃ C V : ℂ,
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
              C + V ∧
            ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
            ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hN.symm
      (fun hM_canonical =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalFixedInterval_ownerDirichletBoundedVariation
          t ht hM_canonical)
      hM

/-- Canonical-cutoff bounded-variation package for the first-periodic-Bernoulli
normalized kernel.

This is now the canonical wrapper over the cutoff-normalized
summation-by-parts leaf. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_cutoffNormalized_ownerDirichletBoundedVariation
      t ht rfl hM

/-- Canonical-cutoff bounded-variation package for the first-periodic-Bernoulli
normalized kernel.

This theorem is now only the public endpoint/variation surface.  The real
Dirichlet/Abel bounded-variation construction is owned by
`boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation`. -/
theorem boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_endpointVariation_canonicalCutoff_ownerBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_canonicalCutoff_ownerDirichletBoundedVariation
      t ht hM

/-- Generic owner wrapper for the first-periodic-Bernoulli normalized-kernel
endpoint/variation decomposition after the canonical logarithmic-phase cutoff.

This transports the canonical-cutoff bounded-variation package through an
explicit lower-endpoint equality. -/
theorem boundaryLineOnePointRealParam_periodicBernoulli_normalizedKernel_endpointVariation_ownerBoundedVariation
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {N M : ℕ}
    (hN : N = ⌊2 + ‖t‖⌋₊)
    (hM : N ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((N : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    Eq.subst
      (motive := fun K : ℕ =>
        K ≤ M →
          ∃ C V : ℂ,
            (∫ x in Set.Ioc (((K : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                    (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
              C + V ∧
            ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
            ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M))
      hN.symm
      (fun hM_canonical =>
        boundaryLineOnePointRealParam_firstPeriodicBernoulli_normalizedKernel_endpointVariation_canonicalCutoff_ownerBoundedVariation
          t ht hM_canonical)
      hM

/-- Generic owner leaf for the first-periodic-Bernoulli normalized-kernel
endpoint/variation decomposition after the canonical logarithmic-phase cutoff.

This is the true summation-by-parts step for the normalized kernel
`((-it) / x) x^{-it}`.  The lower endpoint is the canonical cutoff and the
upper endpoint is finite; the proof must construct the endpoint term `C` and
the reciprocal-variation term `V` from the periodic Bernoulli primitive. -/
theorem boundaryLineOnePointRealParam_postCutoff_periodicBernoulli_normalizedKernel_endpointVariation_ownerDirichlet
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_periodicBernoulli_normalizedKernel_endpointVariation_ownerBoundedVariation
      t
      ht
      (N := ⌊2 + ‖t‖⌋₊)
      (M := M)
      rfl
      hM

/-- Owner leaf for the normalized-kernel first-periodic-Bernoulli
integration-by-parts package.

This is the exact missing oscillatory step: the normalized derivative kernel
`((-it) / x) x^{-it}` is paired with the first periodic Bernoulli factor and
split into an endpoint contribution `C` and a reciprocal-variation contribution
`V`, with the two estimates kept separate. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_normalizedKernel_periodicBernoulli_endpointVariation_package_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_postCutoff_periodicBernoulli_normalizedKernel_endpointVariation_ownerDirichlet
      t ht hM

/-- Oscillatory Bernoulli-periodic decomposition for the unweighted post-cutoff
Euler-Maclaurin remainder.

This is the exact normalized-kernel endpoint/variation step: after the
standard Euler-Maclaurin remainder has been transported to the public
`(-it / x) x^{-it}` derivative kernel, the first-periodic Bernoulli factor is
integrated by parts into a boundary term and a reciprocal-variation term. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_normalizedKernel_endpointVariation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_normalizedKernel_periodicBernoulli_endpointVariation_package_ownerGap
      t ht hM

/-- Public Bernoulli-periodic decomposition wrapper for the unweighted
post-cutoff Euler-Maclaurin remainder.

The absolute-value estimate is too large here.  The required proof is the
Dirichlet/Abel cancellation argument for the periodic Bernoulli factor, split
into a boundary part `C` and a variation part `V` after summation by parts on
the post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_periodicOscillatoryDecomposition_endpointVariation_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∃ C V : ℂ,
      (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
              (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
        C + V ∧
      ‖C‖ ≤ 2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ∧
      ‖V‖ ≤ 4 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_normalizedKernel_endpointVariation_ownerGap
      t ht hM

/-- Scalar constant bookkeeping for the Bernoulli-remainder endpoint and
variation pieces. -/
theorem boundaryGrowth_two_four_scale_le_six_scale_ownerGap
    (A : ℝ) :
    (2 : ℝ) * A + 4 * A ≤ 6 * A := by
  have hfactor :
      (2 : ℝ) * A + 4 * A = ((2 : ℝ) + 4) * A :=
    (add_mul (2 : ℝ) 4 A).symm
  have htwo_four :
      ((2 : ℝ) + 4) * A = 6 * A :=
    congrArg (fun c : ℝ => c * A) (show (2 : ℝ) + 4 = 6 from rfl)
  exact le_of_eq (Eq.trans hfactor htwo_four)

/-- Final constant algebra after the Bernoulli-periodic cancellation and
endpoint/variation estimates. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_from_periodicOscillatoryDecomposition
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  let A : ℝ := Real.sqrt (1 + ‖t‖) * Real.log (2 + M)
  have hdecomp :
      ∃ C V : ℂ,
        (∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
                (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
          C + V ∧
        ‖C‖ ≤ 2 * A ∧
        ‖V‖ ≤ 4 * A :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_periodicOscillatoryDecomposition_endpointVariation_ownerGap
      t ht hM
  match hdecomp with
  | ⟨C, V, hsplit, hC, hV⟩ =>
      have hsum :
          ‖C + V‖ ≤ (2 : ℝ) * A + 4 * A :=
        le_trans (norm_add_le C V) (add_le_add hC hV)
      have hscale :
          (2 : ℝ) * A + 4 * A ≤ 6 * A :=
        boundaryGrowth_two_four_scale_le_six_scale_ownerGap A
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ 6 * A)
          hsplit.symm
          (le_trans hsum hscale)

/-- Bernoulli-remainder estimate for the unweighted post-cutoff
Euler-Maclaurin decomposition.

This is the summation-by-parts/Dirichlet-test content that replaces the
insufficient monotone-increment sink: the derivative factor is integrated only
after the oscillatory decomposition has been made at the owner level. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            (((x : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
      6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_from_periodicOscillatoryDecomposition
      t ht hM

/-- Exact finite endpoint bookkeeping and public normalization for the
unweighted Dirichlet/Euler-Maclaurin package.

This assembles the finite prefix, the exact post-cutoff identity, the main
integral estimate, the two endpoint terms, and the Bernoulli remainder into the
`80`-constant public partial-sum surface. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_classicalDirichletAbel_package_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  intro x hx
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  let M : ℕ := ⌊x⌋₊
  let A : ℝ := (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)
  have hC_nonneg : 0 ≤ ((C : ℕ) : ℝ) :=
    Nat.cast_nonneg C
  have hx_nonneg : 0 ≤ x :=
    le_trans hC_nonneg hx
  have hM : C ≤ M :=
    Nat.le_floor_iff hx_nonneg |>.mpr hx
  have hM_le_x : ((M : ℕ) : ℝ) ≤ x :=
    Nat.floor_le hx_nonneg
  have hprefix :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
        8 * Real.sqrt (1 + ‖t‖) * Real.log (2 + C) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_classicalPrefix_norm_le_ownerGap
      t ht
  have hdecomp :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
          (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
          (-(1 / 2 : ℂ) *
            ((((C : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          ((1 / 2 : ℂ) *
            ((((M : ℕ) : ℝ) : ℂ) ^
              (-(t : ℂ) * Complex.I))) +
          (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
            ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
              (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_eulerMaclaurin_decomposition_ownerGap
      t hM
  have hmain :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_mainIntegral_norm_le_ownerGap
      t ht hM
  have hendpoints :
      ‖(-(1 / 2 : ℂ) *
          ((((C : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))‖ ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_endpoints_norm_le_ownerGap
      t ht hM
  have hremainder :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        6 * Real.sqrt (1 + ‖t‖) * Real.log (2 + M) :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_postCutoff_bernoulliRemainder_norm_le_ownerGap
      t ht hM
  have hlog_C_le : Real.log (2 + C) ≤ Real.log (2 + x) := by
    have hleft_pos : 0 < 2 + ((C : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hC_nonneg)
    have harg_le : 2 + ((C : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hx 2
    exact Real.log_le_log hleft_pos harg_le
  have hlog_M_le : Real.log (2 + M) ≤ Real.log (2 + x) := by
    have hleft_pos : 0 < 2 + ((M : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg M))
    have harg_le : 2 + ((M : ℕ) : ℝ) ≤ 2 + x :=
      add_le_add_left hM_le_x 2
    exact Real.log_le_log hleft_pos harg_le
  have hlog_C_nonneg : 0 ≤ Real.log (2 + C) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((C : ℕ) : ℝ) :=
      le_trans one_le_two (le_add_of_nonneg_right hC_nonneg)
    exact Real.log_nonneg hone_le_arg
  have hlog_M_nonneg : 0 ≤ Real.log (2 + M) := by
    have hone_le_arg : (1 : ℝ) ≤ 2 + ((M : ℕ) : ℝ) :=
      le_trans one_le_two
        (le_add_of_nonneg_right (Nat.cast_nonneg M))
    exact Real.log_nonneg hone_le_arg
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + ‖t‖) :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hfactor_nonneg : 0 ≤ x / ‖t‖ + Real.sqrt (1 + ‖t‖) :=
    add_nonneg
      (div_nonneg hx_nonneg (norm_nonneg t))
      hsqrt_nonneg
  have hA_nonneg : 0 ≤ A := by
    have hlog_x_nonneg : 0 ≤ Real.log (2 + x) :=
      Real.log_nonneg
        (le_trans one_le_two
          (le_add_of_nonneg_right hx_nonneg))
    exact mul_nonneg hfactor_nonneg hlog_x_nonneg
  have hsqrt_le_factor :
      Real.sqrt (1 + ‖t‖) ≤ x / ‖t‖ + Real.sqrt (1 + ‖t‖) :=
    le_add_of_nonneg_left
      (div_nonneg hx_nonneg (norm_nonneg t))
  have hMfactor_le :
      ((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖) ≤
        x / ‖t‖ + Real.sqrt (1 + ‖t‖) := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact add_le_add_right
      (div_le_div_of_nonneg_right hM_le_x (le_of_lt ht_pos))
      (Real.sqrt (1 + ‖t‖))
  have hprefix_A :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C‖ ≤
        8 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + C) ≤ A := by
      exact
        Eq.subst
          (motive := fun r : ℝ =>
            Real.sqrt (1 + ‖t‖) * Real.log (2 + C) ≤ r)
          (show
            (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
          (mul_le_mul hsqrt_le_factor hlog_C_le hlog_C_nonneg hfactor_nonneg)
    exact le_trans hprefix
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 8 * A)
        (mul_assoc (8 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + C))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 8 from Nat.cast_nonneg 8)))
  have hmain_A :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        2 * A := by
    have hscale :
        (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
              Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hMfactor_le hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hmain
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 2 * A)
        (mul_assoc
          (2 : ℝ)
          (((M : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
          (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 2 from zero_le_two)))
  have hendpoints_A :
      ‖(-(1 / 2 : ℂ) *
          ((((C : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I))) +
        ((1 / 2 : ℂ) *
          ((((M : ℕ) : ℝ) : ℂ) ^
            (-(t : ℂ) * Complex.I)))‖ ≤
        2 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hsqrt_le_factor hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hendpoints
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 2 * A)
        (mul_assoc (2 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 2 from zero_le_two)))
  have hremainder_A :
      ‖∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
          ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
            (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))‖ ≤
        6 * A := by
    have hscale :
        Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ A :=
      Eq.subst
        (motive := fun r : ℝ =>
          Real.sqrt (1 + ‖t‖) * Real.log (2 + M) ≤ r)
        (show
          (x / ‖t‖ + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) = A from rfl)
        (mul_le_mul hsqrt_le_factor hlog_M_le hlog_M_nonneg hfactor_nonneg)
    exact le_trans hremainder
      (Eq.subst
        (motive := fun r : ℝ => r ≤ 6 * A)
        (mul_assoc (6 : ℝ) (Real.sqrt (1 + ‖t‖)) (Real.log (2 + M))).symm
        (mul_le_mul_of_nonneg_left hscale
          (show (0 : ℝ) ≤ 6 from Nat.cast_nonneg 6)))
  let P : ℂ := boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C
  let I : ℂ :=
    ∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))
  let L : ℂ :=
    (-(1 / 2 : ℂ) *
      ((((C : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)))
  let U : ℂ :=
    ((1 / 2 : ℂ) *
      ((((M : ℕ) : ℝ) : ℂ) ^
        (-(t : ℂ) * Complex.I)))
  let E : ℂ :=
    L + U
  let R : ℂ :=
    ∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
      ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
        (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
          (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))
  have hsum_bound :
      ‖P + I + E + R‖ ≤ (8 * A + 2 * A) + 2 * A + 6 * A := by
    have hfirst : ‖P + I‖ ≤ 8 * A + 2 * A :=
      le_trans (norm_add_le P I) (add_le_add hprefix_A hmain_A)
    have hsecond : ‖P + I + E‖ ≤ (8 * A + 2 * A) + 2 * A :=
      le_trans (norm_add_le (P + I) E) (add_le_add hfirst hendpoints_A)
    exact
      le_trans (norm_add_le (P + I + E) R)
        (add_le_add hsecond hremainder_A)
  have hconstant :
      (8 * A + 2 * A) + 2 * A + 6 * A ≤ 80 * A := by
    have hleft_eq : (8 * A + 2 * A) + 2 * A + 6 * A = 18 * A := by
      calc
        (8 * A + 2 * A) + 2 * A + 6 * A =
            ((8 + 2) * A + 2 * A) + 6 * A := by
          exact congrArg (fun y : ℝ => (y + 2 * A) + 6 * A)
            (add_mul 8 2 A).symm
        _ = (((8 + 2) + 2) * A) + 6 * A := by
          exact congrArg (fun y : ℝ => y + 6 * A)
            (add_mul (8 + 2) 2 A).symm
        _ = (((8 + 2) + 2) + 6) * A := by
          exact (add_mul ((8 + 2) + 2) 6 A).symm
        _ = 18 * A := by
          exact congrArg (fun y : ℝ => y * A) rfl
    have heighteen_le_eighty : (18 : ℝ) ≤ 80 :=
      Nat.cast_le.mpr
        (show (18 : ℕ) ≤ 80 from Nat.le_add_right 18 62)
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 80 * A)
      hleft_eq.symm
      (mul_le_mul_of_nonneg_right heighteen_le_eighty hA_nonneg)
  have htarget :
      ‖P + I + E + R‖ ≤ 80 * A :=
    le_trans hsum_bound hconstant
  have hgrouped :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
        P + I + E + R := by
    have hright_group :
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
            (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
            (-(1 / 2 : ℂ) *
              ((((C : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) +
            ((1 / 2 : ℂ) *
              ((((M : ℕ) : ℝ) : ℂ) ^
                (-(t : ℂ) * Complex.I))) +
            (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
              ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
                (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                  (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
          P + I + E + R := by
      exact
        calc
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C +
              (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I))) +
              (-(1 / 2 : ℂ) *
                ((((C : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) +
              ((1 / 2 : ℂ) *
                ((((M : ℕ) : ℝ) : ℂ) ^
                  (-(t : ℂ) * Complex.I))) +
              (∫ y in Set.Ioc (((C : ℕ) : ℝ)) (((M : ℕ) : ℝ)),
                ((eulerMaclaurinFirstPeriodicBernoulli y : ℝ) : ℂ) *
                  (((-(t : ℂ) * Complex.I) / (y : ℂ)) *
                    (((y : ℝ) : ℂ) ^ (-(t : ℂ) * Complex.I)))) =
            (P + I + L + U) + R := rfl
          _ = (P + I + (L + U)) + R := by
            exact congrArg (fun z : ℂ => z + R)
              (add_assoc (P + I) L U)
          _ = P + I + E + R := rfl
    exact Eq.trans hdecomp hright_group
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 80 * A)
      hgrouped.symm
      htarget

/-- Owner gap: unconditional logarithmic-phase partial sums on the boundary
line.

The former route through `logarithmicPhaseFiniteDifferenceHypothesis` was not
an honest owner proof: unrestricted real frequencies have exact resonances
among adjacent logarithmic increments, e.g. `t = -2π / log 2` makes the first
increment an integral multiple of `2π`.  The unconditional boundary-line
estimate must instead be proved by the classical Dirichlet/Abel or
Euler-Maclaurin argument for `∑ n^{-it}` with cutoff comparable to `|t|`;
cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5.
-/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_classicalDirichletAbel_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_of_classicalDirichletAbel_package_ownerGap
      t ht

/-- Owner gap: logarithmic-phase partial sums on the boundary line.

Proof chain:
classical Dirichlet/Abel oscillatory estimate for `∑ n^{-it}`
-> cutoff normalization at `⌊2 + |t|⌋₊`
-> this `80`-constant public boundary hypothesis.
-/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_classicalDirichletAbel_ownerGap
      t ht

/-- Owner gap: uniformly bounded finite post-cutoff Abel tails on the
boundary line.

This is the direct classical bounded-partial-sums input needed by Abel
transport.  The explicit finite Abel majorant above is useful for finite
decompositions, but its endpoint form is not uniformly absorbed by the fixed
Abel-tail constant. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_of_classical_postCutoff_tail
      t ht

/-- Owner package for the real-parameter boundary-line truncation hypotheses. -/
theorem boundaryLineOnePointRealParam_verticalTruncationHypotheses_ownerGap
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t ∧
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t := by
  have hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t :=
    boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound_ownerGap t ht
  exact
    ⟨hpartial,
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded_ownerGap t ht⟩

theorem eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (_hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
      t ht hfinite
  exact boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    t htail

/-- The exact Abel/Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`. -/
theorem eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    t ht hpartial hfinite

/-- Public Abel/Euler-Maclaurin zeta-tail root.  The proof is now only name
transport from the canonical Euler-Maclaurin tail estimate at the exact cutoff. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    t ht hpartial hfinite

/-- Triangle-inequality split of `ζ(1+it)` into its Abel/Euler-Maclaurin tail
and finite Dirichlet truncation. -/
theorem boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation
    (t : ℝ) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
  let S : ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
      (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
  have hsplit :
      riemannZeta (boundaryLineOnePointRealParam t) =
        (riemannZeta (boundaryLineOnePointRealParam t) - S) + S := by
    exact (sub_add_cancel (riemannZeta (boundaryLineOnePointRealParam t)) S).symm
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ ‖riemannZeta (boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
    hsplit.symm
    (norm_add_le (riemannZeta (boundaryLineOnePointRealParam t) - S) S)

/-- The analytic tail estimate and finite harmonic majorant give the intermediate
explicit-tail boundary estimate. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  have hsplit :
      ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
        ‖riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ :=
    boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation t
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
      t ht hpartial hfinite
  have hfinite :
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        1 + Real.log (2 + ‖t‖) :=
    boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log t
  have htail_plus_finite :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
          (1 + Real.log (2 + ‖t‖)) :=
    add_le_add htail hfinite
  exact le_trans hsplit htail_plus_finite

/-- On the large vertical range, the intermediate `2 + log` bound is absorbed by
`3 * log`. -/
theorem two_add_log_two_add_norm_le_three_mul_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    2 + Real.log (2 + ‖t‖) ≤
      3 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hlog_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_le_twoL : (2 : ℝ) ≤ 2 * L := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * L :=
        mul_le_mul_of_nonneg_left hlog_one zero_le_two
  calc
    2 + Real.log (2 + ‖t‖) = 2 + L := rfl
    _ ≤ 2 * L + L :=
      add_le_add_right htwo_le_twoL L
    _ = 2 * L + 1 * L := by
      exact congrArg (fun x : ℝ => 2 * L + x) (one_mul L).symm
    _ = (2 + 1) * L := by
      exact (add_mul 2 1 L).symm
    _ = 3 * L := by
      exact congrArg (fun x : ℝ => x * L) boundaryGrowth_real_two_add_one_eq_three
    _ = 3 * Real.log (2 + ‖t‖) := rfl

/-- The enlarged logarithmic argument `3 + |t|` is absorbed by twice the
canonical boundary-line logarithm. -/
theorem log_three_add_norm_le_two_mul_log_two_add_norm
    (t : ℝ) :
    Real.log (3 + ‖t‖) ≤
      2 * Real.log (2 + ‖t‖) := by
  let x : ℝ := ‖t‖
  have hx_nonneg : 0 ≤ x :=
    norm_nonneg t
  have hleft_pos : 0 < 3 + x := by
    have hthree_pos : (0 : ℝ) < 3 :=
      three_pos
    exact lt_of_lt_of_le hthree_pos (le_add_of_nonneg_right hx_nonneg)
  have hright_pos : 0 < 2 * (2 + x) := by
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have harg_pos : 0 < 2 + x :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg)
    exact mul_pos htwo_pos harg_pos
  have harg_ne : (2 : ℝ) + x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg))
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have harg_ge_two : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx_nonneg
  have hthree_le :
      3 + x ≤ 2 * (2 + x) := by
    have hx_le_two_x : x ≤ 2 * x := by
      calc
        x = 1 * x := by
          exact (one_mul x).symm
        _ ≤ 2 * x :=
          mul_le_mul_of_nonneg_right one_le_two hx_nonneg
    calc
      3 + x ≤ 4 + 2 * x :=
        add_le_add
          (Nat.cast_le.mpr (show (3 : ℕ) ≤ 4 from Nat.le_succ 3))
          hx_le_two_x
      _ = 2 * 2 + 2 * x := by
        exact congrArg (fun y : ℝ => y + 2 * x)
          boundaryGrowth_real_two_mul_two_eq_four.symm
      _ = 2 * (2 + x) := by
        exact (left_distrib 2 2 x).symm
  have hlog_le :
      Real.log (3 + x) ≤ Real.log (2 * (2 + x)) :=
    Real.log_le_log hleft_pos hthree_le
  have hlog_mul :
      Real.log (2 * (2 + x)) =
        Real.log 2 + Real.log (2 + x) :=
    Real.log_mul htwo_ne harg_ne
  have hlog_two_le :
      Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hsum_le :
      Real.log 2 + Real.log (2 + x) ≤
        Real.log (2 + x) + Real.log (2 + x) :=
    add_le_add_right hlog_two_le (Real.log (2 + x))
  calc
    Real.log (3 + ‖t‖) = Real.log (3 + x) := rfl
    _ ≤ Real.log (2 * (2 + x)) :=
      hlog_le
    _ = Real.log 2 + Real.log (2 + x) :=
      hlog_mul
    _ ≤ Real.log (2 + x) + Real.log (2 + x) :=
      hsum_le
    _ = 2 * Real.log (2 + x) := by
      exact (two_mul (Real.log (2 + x))).symm
    _ = 2 * Real.log (2 + ‖t‖) := rfl

/-- The explicit Abel-tail constant plus finite-truncation logarithmic term is
absorbed by an absolute multiple of the canonical logarithm. -/
theorem boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      39 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hL_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hL_nonneg : 0 ≤ L :=
    le_trans zero_le_one hL_one
  have hfive_le : (5 : ℝ) ≤ 5 * L := by
    calc
      (5 : ℝ) = 5 * 1 := by
        exact (mul_one 5).symm
      _ ≤ 5 * L :=
        mul_le_mul_of_nonneg_left hL_one
          (show (0 : ℝ) ≤ 5 from Nat.cast_nonneg 5)
  have hone_le : (1 : ℝ) ≤ L :=
    hL_one
  have hlog_three :
      Real.log (3 + ‖t‖) ≤ 2 * L := by
    exact log_three_add_norm_le_two_mul_log_two_add_norm t
  have hsixteen_log :
      16 * Real.log (3 + ‖t‖) ≤ 32 * L := by
    calc
      16 * Real.log (3 + ‖t‖) ≤ 16 * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog_three
          (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16)
      _ = (16 * 2) * L := by
        exact (mul_assoc 16 2 L).symm
      _ = 32 * L := by
        exact congrArg (fun x : ℝ => x * L)
          boundaryGrowth_real_sixteen_mul_two_eq_thirty_two
  have htail :
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
        37 * L := by
    calc
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
          5 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 5 * L + 32 * L :=
        add_le_add hfive_le hsixteen_log
      _ = (5 + 32) * L := by
        exact (add_mul 5 32 L).symm
      _ = 37 * L := by
        exact congrArg (fun x : ℝ => x * L)
          boundaryGrowth_real_five_add_thirty_two_eq_thirty_seven
  have hfinite :
      1 + Real.log (2 + ‖t‖) ≤ 2 * L := by
    calc
      1 + Real.log (2 + ‖t‖) = 1 + L := rfl
      _ ≤ L + L :=
        add_le_add_right hone_le L
      _ = 2 * L := by
        exact (two_mul L).symm
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      37 * L + 2 * L :=
        add_le_add htail hfinite
    _ = (37 + 2) * L := by
      exact (add_mul 37 2 L).symm
    _ = 39 * L := by
      exact congrArg (fun x : ℝ => x * L)
        boundaryGrowth_real_thirty_seven_add_two_eq_thirty_nine
    _ = 39 * Real.log (2 + ‖t‖) := rfl

/-- The finite truncation plus the Abel/Euler-Maclaurin tail gives the logarithmic
boundary estimate with the explicit Abel-tail constant still visible. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t)
    (hfinite :
      boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  exact
    abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
      t ht hpartial hfinite

/-- The exact analytic Abel/Euler-Maclaurin tail estimate on `ζ(1 + it)`.

Intended proof chain:
Dirichlet truncation at `N = ⌊2 + |t|⌋₊`, Abel summation for the oscillatory tail
`∑ n^{-1-it}`, Euler-Maclaurin control of the endpoint remainder, the harmonic
majorant for the finite part, and the standard logarithmic normalization; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact Exists.intro 39
    (And.intro
      (Nat.cast_pos.mpr (show (0 : ℕ) < 39 from Nat.succ_pos 38))
      (fun t ht hpartial hfinite =>
        let hexplicit :
            ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
              boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                (1 + Real.log (2 + ‖t‖)) :=
          abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
            t ht hpartial hfinite
        let habsorb :
            boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
                (1 + Real.log (2 + ‖t‖)) ≤
              39 * Real.log (2 + ‖t‖) :=
          boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log ht
        le_trans hexplicit habsorb))

/-- Euler-Maclaurin/Abel-truncation boundary estimate for the Riemann zeta function on
`1 + it`.

This is the canonical classical number-theoretic input: truncate the Dirichlet
series at height comparable to `|t|`, control the tail by Euler-Maclaurin or Abel
summation, and derive the standard logarithmic bound; cf. Titchmarsh, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic

/-- The historical owner-root spelling for the boundary-line logarithmic zeta estimate.

The proof is only name transport from the canonical Abel/Euler-Maclaurin theorem on
`ζ(1 + it)`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of raw zeta on `1 + it`.

This is the smallest analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and derive the standard `O(log (2 + |t|))` boundary-line bound; cf. Titchmarsh,
The Theory of the Riemann Zeta-function, §3.5. -/
theorem classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of zeta on the line `1 + it`.

This is only the definitional transport from the raw boundary-line zeta value to the
local real-parameter name. -/
theorem classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        boundaryLineOnePointRealParam_logarithmicPhasePartialSumBound t →
        boundaryLineOnePointRealParam_logarithmicPhaseFiniteTailBounded t →
        ‖boundaryLineOneZetaRealParam t‖ ≤ A * Real.log (2 + ‖t‖) := by
  exact Exists.elim
    classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun t ht hpartial hfinite =>
            Eq.subst
              (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖t‖))
              (show ‖riemannZeta (boundaryLineOnePointRealParam t)‖ =
                  ‖boundaryLineOneZetaRealParam t‖ from rfl)
              (hA.right t ht hpartial hfinite))))

/-- A logarithmic zeta estimate on `re = 1` gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim hzeta
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im =>
            let hpole_norm :
                ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
              boundaryLine_one_sub_one_norm_le_vertical_height hw_re
            let hzeta_norm :
                ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
              hA.right w hw_re hw_im
            let hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
            let hmul :
                ‖w - 1‖ * ‖riemannZeta w‖ ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
              mul_le_mul hpole_norm hzeta_norm (norm_nonneg (riemannZeta w)) hheight_nonneg
            let htarget_eq :
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                  A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
              calc
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                    ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
                  exact (mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))).symm
                _ =
                    (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
                  exact congrArg
                    (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
                    (mul_comm (1 + ‖w.im‖) A)
                _ =
                    A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
                  exact rfl
            let hnorm_eq :
                ‖(w - 1) * riemannZeta w‖ = ‖w - 1‖ * ‖riemannZeta w‖ :=
              norm_mul (w - 1) (riemannZeta w)
            Eq.subst
              (motive := fun x : ℝ =>
                ‖(w - 1) * riemannZeta w‖ ≤ x)
              htarget_eq
              (Eq.subst
                (motive := fun x : ℝ => x ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
                hnorm_eq.symm
                hmul))))

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, proved
by Euler-Maclaurin/Abel truncation.

This is the exact analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and derive the standard `O(log (2 + |t|))` boundary-line bound. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim
    classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im htrunc =>
            Eq.subst
              (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖w.im‖))
              (norm_riemannZeta_boundaryLine_one_eq_norm_realParam hw_re).symm
              (hA.right w.im hw_im htrunc.left htrunc.right))))

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, in the
standard partial-summation/truncation form. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, obtained from the raw boundary-line zeta estimate and the elementary
pole-clearing factor. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact Exists.elim
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation
    (fun A hA =>
      Exists.intro A
        (And.intro hA.left
          (fun w hw_re hw_im htrunc =>
            let hpole_norm :
                ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
              boundaryLine_one_sub_one_norm_le_vertical_height hw_re
            let hzeta_norm :
                ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
              hA.right w hw_re hw_im htrunc
            let hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
            let hmul :
                ‖w - 1‖ * ‖riemannZeta w‖ ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
              mul_le_mul hpole_norm hzeta_norm (norm_nonneg (riemannZeta w)) hheight_nonneg
            let htarget_eq :
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                  A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
              calc
                (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
                    ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
                  exact (mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))).symm
                _ = (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
                  exact congrArg
                    (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
                    (mul_comm (1 + ‖w.im‖) A)
                _ = A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
                  rfl
            let hnorm_eq :
                ‖(w - 1) * riemannZeta w‖ =
                  ‖w - 1‖ * ‖riemannZeta w‖ :=
              norm_mul (w - 1) (riemannZeta w)
            Eq.subst
              (motive := fun x : ℝ =>
                ‖(w - 1) * riemannZeta w‖ ≤ x)
              htarget_eq
              (Eq.subst
                (motive := fun x : ℝ => x ≤
                  (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
                hnorm_eq.symm
                hmul))))

/-- The logarithmic boundary-line zeta estimate gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_of_zeta_log
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound hzeta

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.  This is the standard boundary-line zeta estimate in the form needed before
coarsening to a finite polynomial envelope. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation

/-- A conditional log-linear vertical-height boundary estimate gives the coarser
conditional polynomial envelope used by the normalization chain. -/
theorem boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    {f : ℂ → ℂ}
    (P : ℂ → Prop)
    (hlog :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          P w →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        P w →
        ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m := by
  exact Exists.elim hlog
    (fun A hA =>
      Exists.intro (2 * A)
        (Exists.intro 2
          (And.intro
            (mul_pos two_pos hA.left)
            (fun w hw_re hw_im hP =>
              let H : ℝ := 1 + ‖w.im‖
              let hH_nonneg : 0 ≤ H :=
                le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
              let hlog_arg_pos : 0 < 2 + ‖w.im‖ :=
                add_pos_of_pos_of_nonneg zero_lt_two (norm_nonneg w.im)
              let hlog_le_arg :
                  Real.log (2 + ‖w.im‖) ≤ 2 + ‖w.im‖ :=
                Real.log_le_self hlog_arg_pos.le
              let hnorm_le_two_norm : ‖w.im‖ ≤ 2 * ‖w.im‖ := by
                calc
                  ‖w.im‖ = 1 * ‖w.im‖ := by
                    exact (one_mul ‖w.im‖).symm
                  _ ≤ 2 * ‖w.im‖ :=
                    mul_le_mul_of_nonneg_right one_le_two (norm_nonneg w.im)
              let harg_le_twoH : 2 + ‖w.im‖ ≤ 2 * H := by
                calc
                  2 + ‖w.im‖ ≤ 2 + 2 * ‖w.im‖ :=
                    add_le_add_left hnorm_le_two_norm 2
                  _ = 2 * (1 + ‖w.im‖) := by
                    calc
                      2 + 2 * ‖w.im‖ = 2 * 1 + 2 * ‖w.im‖ := by
                        exact congrArg (fun y : ℝ => y + 2 * ‖w.im‖)
                          (mul_one 2).symm
                      _ = 2 * (1 + ‖w.im‖) :=
                        (left_distrib 2 1 ‖w.im‖).symm
                  _ = 2 * H := rfl
              let hlog_le_twoH :
                  Real.log (2 + ‖w.im‖) ≤ 2 * H :=
                le_trans hlog_le_arg harg_le_twoH
              let hleft_nonneg : 0 ≤ A * H :=
                mul_nonneg (le_of_lt hA.left) hH_nonneg
              let hmul_log_le :
                  A * H * Real.log (2 + ‖w.im‖) ≤ A * H * (2 * H) :=
                mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
              let htarget_eq :
                  A * H * (2 * H) = (2 * A) * H ^ (2 : ℕ) := by
                calc
                  A * H * (2 * H) = (A * H * 2) * H := by
                    exact (mul_assoc (A * H) 2 H).symm
                  _ = (2 * (A * H)) * H := by
                    exact congrArg (fun x : ℝ => x * H) (mul_comm (A * H) 2)
                  _ = ((2 * A) * H) * H := by
                    exact congrArg (fun x : ℝ => x * H) (mul_assoc 2 A H).symm
                  _ = (2 * A) * (H * H) := by
                    exact mul_assoc (2 * A) H H
                  _ = (2 * A) * H ^ (2 : ℕ) := by
                    exact congrArg (fun x : ℝ => (2 * A) * x) (pow_two H).symm
              le_trans (hA.right w hw_re hw_im hP)
                (Eq.subst
                  (motive := fun x : ℝ =>
                    A * H * Real.log (2 + ‖w.im‖) ≤ x)
                  htarget_eq
                  hmul_log_le)))))

/-- A conditional polynomial vertical-height boundary estimate gives the
conditional exponential finite-order envelope in the same vertical-height
variable. -/
theorem boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound_of_condition
    {f : ℂ → ℂ}
    (P : ℂ → Prop)
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          P w →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        P w →
        ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact match hpoly with
    | ⟨A, m, hA_pos, hbound⟩ =>
      ⟨A, 1, m, hA_pos, zero_lt_one, fun w hw_re hw_im hP => by
        let H : ℝ := (1 + ‖w.im‖) ^ m
        have hH_nonneg : 0 ≤ H :=
          pow_nonneg
            (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im)))
            m
        have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
          have hone_mul : (1 : ℝ) * H = H := by
            exact one_mul H
          have hH_le_H_add_one : H ≤ H + 1 :=
            le_add_of_nonneg_right zero_le_one
          have hH_add_one_le_exp : H + 1 ≤ Real.exp H :=
            Real.add_one_le_exp H
          have hH_le_exp_H : H ≤ Real.exp H :=
            le_trans hH_le_H_add_one hH_add_one_le_exp
          exact Eq.subst
            (motive := fun x : ℝ => H ≤ Real.exp x)
            hone_mul.symm
            hH_le_exp_H
        have hscaled :
            A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
          mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
        exact le_trans (hbound w hw_re hw_im hP) hscaled⟩

/-- Standard polynomial vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.

This is the classical boundary-line estimate for the removable meromorphic factor
`(s - 1)ζ(s)`, stated before conversion to the coarser finite-order envelope. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  exact boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    boundaryLineOneVerticalTruncationHypotheses
    classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, converted from the polynomial boundary-line estimate.

This is the zeta-side finite-order theorem that must come from boundary-line estimates
for the pole-cleared meromorphic zeta function, not from the false far-right `re = 2`
Dirichlet-series route. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound_of_condition
    boundaryLineOneVerticalTruncationHypotheses
    riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard

/-- The standard vertical-height finite-order estimate for `(s - 1)ζ(s)` on `re = 1`
implies the complex-height envelope consumed by the strip-normalization chain. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    (hvertical :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          boundaryLineOneVerticalTruncationHypotheses w →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim hvertical
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im htrunc =>
                          le_trans (hdata.right.right w hw_re hw_im htrunc)
                            (finiteOrder_vertical_envelope_le_complex_envelope
                              (le_of_lt hdata.left)
                              (le_of_lt hdata.right.left))))))))))

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, in the complex-height envelope used downstream. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard

/-- The removable pole-cleared boundary-line estimate implies the raw
`(s - 1)ζ(s)` boundary-line estimate on the vertical tail.

The vertical-tail hypothesis excludes the removable point `1`, so the raw product and
`poleClearedRiemannZeta` agree there. -/
theorem riemannZeta_boundaryLine_one_raw_growth_bound_of_poleCleared_growth_bound
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim hpole
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im =>
                          let hw_ne_one : w ≠ 1 :=
                            fun hw =>
                              have him_zero : w.im = 0 := by
                                calc
                                  w.im = (1 : ℂ).im := by
                                    exact congrArg Complex.im hw
                                  _ = 0 := by
                                    exact Complex.one_im
                              have him_norm_zero : ‖w.im‖ = 0 := by
                                calc
                                  ‖w.im‖ = ‖(0 : ℝ)‖ := by
                                    exact congrArg norm him_zero
                                  _ = 0 := by
                                    exact norm_zero
                              have hone_le_zero : (1 : ℝ) ≤ 0 :=
                                Eq.subst
                                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                                  him_norm_zero
                                  hw_im
                              not_lt_of_ge hone_le_zero zero_lt_one
                          let hpole_eq :
                              poleClearedRiemannZeta w =
                                (w - 1) * riemannZeta w :=
                            poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                          Eq.subst
                            (motive := fun x : ℂ =>
                              ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                            hpole_eq
                            (hdata.right.right w hw_re hw_im)))))))))

/-- Pole-cleared zeta has finite-order vertical growth on the boundary line `re = 1`.

This is the smallest zeta-side analytic primitive needed on the reflected left boundary:
reflection sends `re z = 0` to `re (1 - z) = 1`, not to the `re = 2`
Dirichlet-series boundary. -/
theorem poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        boundaryLineOneVerticalTruncationHypotheses w →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact Exists.elim riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard
    (fun A hA_tail =>
      Exists.elim hA_tail
        (fun B hB_tail =>
          Exists.elim hB_tail
            (fun m hdata =>
              Exists.intro A
                (Exists.intro B
                  (Exists.intro m
                    (And.intro hdata.left
                      (And.intro hdata.right.left
                        (fun w hw_re hw_im htrunc =>
                          let hw_ne_one : w ≠ 1 :=
                            fun hw =>
                              have him_zero : w.im = 0 := by
                                calc
                                  w.im = (1 : ℂ).im := by
                                    exact congrArg Complex.im hw
                                  _ = 0 := by
                                    exact Complex.one_im
                              have him_norm_zero : ‖w.im‖ = 0 := by
                                calc
                                  ‖w.im‖ = ‖(0 : ℝ)‖ := by
                                    exact congrArg norm him_zero
                                  _ = 0 := by
                                    exact norm_zero
                              have hone_le_zero : (1 : ℝ) ≤ 0 :=
                                Eq.subst
                                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                                  him_norm_zero
                                  hw_im
                              not_lt_of_ge hone_le_zero zero_lt_one
                          let hpole_eq :
                              poleClearedRiemannZeta w =
                                (w - 1) * riemannZeta w :=
                            poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                          Eq.subst
                            (motive := fun x : ℂ =>
                              ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                            hpole_eq.symm
                            (hdata.right.right w hw_re hw_im htrunc)))))))))


end
end LFunctions
end Boundary

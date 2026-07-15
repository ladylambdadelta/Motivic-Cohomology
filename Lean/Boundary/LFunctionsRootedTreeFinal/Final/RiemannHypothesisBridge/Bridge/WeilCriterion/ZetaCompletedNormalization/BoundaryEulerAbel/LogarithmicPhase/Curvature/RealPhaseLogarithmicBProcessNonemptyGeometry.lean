import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessActiveArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSupportComparability

/-!
# Geometry of a nonempty balanced active family

The additive `2` in the coarse integer-cardinality bound is harmless only after
the nonempty regime is understood.  A negative integer mode satisfies
`1 <= -m`.  Hence its stationary center is at most `‖t‖`, since the angular
denominator is at least one.  Membership of a balanced interior mode then
forces `a <= ‖t‖`; dyadic comparability forces `b <= 2‖t‖`.

If no interior mode exists, the balanced interior budget is exactly zero.  The
two alternatives are exposed here for the scalar arithmetic owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Int.one_le_neg_of_neg
    {m : ℤ} (hm : m < 0) :
    (1 : ℤ) ≤ -m := by
  have hnegPos : (0 : ℤ) < -m := Int.neg_pos.mpr hm
  exact Int.add_one_le_iff.mpr hnegPos

theorem Real.one_le_neg_intCast_of_neg
    {m : ℤ} (hm : m < 0) :
    (1 : ℝ) ≤ -(m : ℝ) := by
  have hint := Int.one_le_neg_of_neg hm
  have hcast : ((1 : ℤ) : ℝ) ≤ ((-m : ℤ) : ℝ) :=
    Int.cast_le.mpr hint
  have hone : (((1 : ℤ) : ℝ)) = 1 := Int.cast_one
  have hneg : (((-m : ℤ) : ℝ)) = -(m : ℝ) := Int.cast_neg m
  exact Eq.mp
    (congrArg₂ (fun left right : ℝ => left ≤ right) hone hneg)
    hcast

theorem Real.one_le_two_mul_pi :
    (1 : ℝ) ≤ 2 * Real.pi := by
  have hthreePi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have honePi : (1 : ℝ) ≤ Real.pi :=
    le_of_lt (lt_trans (Nat.one_lt_ofNat : (1 : ℝ) < 3) hthreePi)
  have htwo : (1 : ℝ) ≤ 2 := one_le_two
  have hscaled := mul_le_mul htwo honePi zero_le_one zero_le_two
  exact le_trans (le_of_eq (one_mul 1).symm) hscaled

theorem Complex.one_le_logarithmicPhaseAngularDenominator
    {m : ℤ} (hm : m < 0) :
    (1 : ℝ) ≤ 2 * Real.pi * (-(m : ℝ)) := by
  have htwoPi := Real.one_le_two_mul_pi
  have hmReal := Real.one_le_neg_intCast_of_neg hm
  have htwoPiNonneg : 0 ≤ 2 * Real.pi :=
    Complex.two_mul_pi_pos.le
  have hproduct :=
    mul_le_mul htwoPi hmReal zero_le_one htwoPiNonneg
  exact le_trans (le_of_eq (one_mul 1).symm) hproduct

theorem Complex.logarithmicPhaseFourierStationaryPoint_le_norm
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤ ‖t‖ := by
  unfold Complex.logarithmicPhaseFourierStationaryPoint
  have hdenominator :=
    Complex.one_le_logarithmicPhaseAngularDenominator hm
  have hdenominatorPos :
      0 < 2 * Real.pi * (-(m : ℝ)) :=
    lt_of_lt_of_le zero_lt_one hdenominator
  have hnormNonneg : 0 ≤ ‖t‖ := norm_nonneg t
  have htarget :
      ‖t‖ ≤ ‖t‖ * (2 * Real.pi * (-(m : ℝ))) := by
    have hscaled := mul_le_mul_of_nonneg_left hdenominator hnormNonneg
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤ ‖t‖ * (2 * Real.pi * (-(m : ℝ))))
      (mul_one ‖t‖)
      hscaled
  exact (div_le_iff₀ hdenominatorPos).mpr htarget

theorem Complex.logarithmicPhaseBProcess_blockLeft_le_center_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    (a : ℝ) ≤ Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hradius :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmem.2.1
  exact le_trans hmem.2.2.1 (sub_le_self _ hradius)

theorem Complex.logarithmicPhaseBProcess_blockLeft_le_norm_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    (a : ℝ) ≤ ‖t‖ := by
  have hmemData :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  exact le_trans
    (Complex.logarithmicPhaseBProcess_blockLeft_le_center_of_mem
      t ht hm)
    (Complex.logarithmicPhaseFourierStationaryPoint_le_norm
      t hmemData.2.1)

theorem Complex.logarithmicPhaseBProcess_natBlockLeft_le_norm_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b : ℕ} {m : ℤ}
    (hm : m ∈
      Complex.logarithmicPhasePoissonBProcessInteriorModes t (a : ℤ) (b : ℤ)) :
    (a : ℝ) ≤ ‖t‖ := by
  have hbound :=
    Complex.logarithmicPhaseBProcess_blockLeft_le_norm_of_mem
      t ht hm
  exact hbound

theorem Real.natCast_blockRight_le_two_mul_blockLeft
    {a b : ℕ} (hcomparable : b + 1 ≤ 2 * a) :
    (b : ℝ) ≤ 2 * (a : ℝ) := by
  have hbLe : b ≤ 2 * a :=
    le_trans (Nat.le_succ b) hcomparable
  have hcast : (b : ℝ) ≤ ((2 * a : ℕ) : ℝ) :=
    Nat.cast_le.mpr hbLe
  have hcastProduct : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) := by
    exact Nat.cast_mul 2 a
  exact Eq.subst
    (motive := fun value : ℝ => (b : ℝ) ≤ value)
    hcastProduct
    hcast

theorem Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_mem
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b : ℕ} {m : ℤ}
    (hcomparable : b + 1 ≤ 2 * a)
    (hm : m ∈
      Complex.logarithmicPhasePoissonBProcessInteriorModes t (a : ℤ) (b : ℤ)) :
    (b : ℝ) ≤ 2 * ‖t‖ := by
  have hba := Real.natCast_blockRight_le_two_mul_blockLeft hcomparable
  have hat :=
    Complex.logarithmicPhaseBProcess_natBlockLeft_le_norm_of_mem
      t ht hm
  have hscaled := mul_le_mul_of_nonneg_left hat zero_le_two
  exact le_trans hba hscaled

theorem Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_nonempty
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a b : ℕ}
    (hcomparable : b + 1 ≤ 2 * a)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) ≤ 2 * ‖t‖ := by
  exact
    Complex.logarithmicPhaseBProcess_natBlockRight_le_two_mul_norm_of_mem
      t ht hcomparable hnonempty.choose_spec

theorem Complex.logarithmicPhaseBProcessInteriorBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty :
      Complex.logarithmicPhasePoissonBProcessInteriorModes t a b = ∅) :
    Complex.logarithmicPhaseBProcessInteriorBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseBProcessInteriorBudget
  unfold Complex.logarithmicPhaseBProcessInteriorCrossingBudget
  unfold Complex.logarithmicPhaseBProcessInteriorLeftTailBudget
  unfold Complex.logarithmicPhaseBProcessInteriorCentralBudget
  unfold Complex.logarithmicPhaseBProcessInteriorRightTailBudget
  have hcrossing :
      (∑ _m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        (4 / 3 : ℝ)) = 0 := by
    exact Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ _m ∈ modes, (4 / 3 : ℝ)) = 0)
      hempty.symm
      (Finset.sum_empty)
  have hleft :
      (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        Complex.logarithmicPhaseBProcessLeftTailBudget t m) = 0 := by
    exact Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ m ∈ modes,
          Complex.logarithmicPhaseBProcessLeftTailBudget t m) = 0)
      hempty.symm
      (Finset.sum_empty)
  have hcentral :
      (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        Complex.logarithmicPhaseBProcessWindowWidth t m) = 0 := by
    exact Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ m ∈ modes,
          Complex.logarithmicPhaseBProcessWindowWidth t m) = 0)
      hempty.symm
      (Finset.sum_empty)
  have hright :
      (∑ m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b,
        Complex.logarithmicPhaseBProcessRightTailBudget t m) = 0 := by
    exact Eq.subst
      (motive := fun modes : Finset ℤ =>
        (∑ m ∈ modes,
          Complex.logarithmicPhaseBProcessRightTailBudget t m) = 0)
      hempty.symm
      (Finset.sum_empty)
  exact
    (congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          hcrossing hleft)
        hcentral)
      hright).trans
      ((add_zero ((0 : ℝ) + 0 + 0)).trans
        ((add_zero ((0 : ℝ) + 0)).trans
          (add_zero (0 : ℝ))))

theorem Complex.logarithmicPhasePoissonBProcessInteriorModes_empty_or_nonempty
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonBProcessInteriorModes t a b = ∅ ∨
      (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b).Nonempty := by
  exact Finset.eq_empty_or_nonempty
    (Complex.logarithmicPhasePoissonBProcessInteriorModes t a b)

end

end LFunctions
end Boundary

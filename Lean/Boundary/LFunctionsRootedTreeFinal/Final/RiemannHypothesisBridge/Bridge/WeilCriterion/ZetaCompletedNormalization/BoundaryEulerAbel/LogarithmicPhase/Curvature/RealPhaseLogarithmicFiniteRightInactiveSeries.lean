import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ZeroBasedShiftedReciprocalPower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveSeriesBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteRightInactiveReindex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveMajorantSum

/-!
# Shifted reciprocal series for finite right-inactive modes

The reverse-frequency index is injected into the zero-based shifted series.
The ceiling residual is strictly positive, and each inverse power of the
actual derivative gap is exactly the corresponding zero-based series term.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFiniteRightThreshold_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b := by
  unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  exact div_pos hnorm (mul_pos Complex.two_mul_pi_pos hright)

theorem Complex.logarithmicPhaseFiniteRightTop_add_one_eq_ceil
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 =
      ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ := by
  unfold Complex.logarithmicPhaseFiniteRightFrequencyTop
  have hceilPos :
      0 < ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ :=
    Nat.ceil_pos.mpr
      (Complex.logarithmicPhaseFiniteRightThreshold_pos t ht a b ha hab)
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hceilPos)

theorem Complex.logarithmicPhaseFiniteRightTop_lt_threshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ) <
      Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b := by
  have hadd :=
    Complex.logarithmicPhaseFiniteRightTop_add_one_eq_ceil
      t ht a b ha hab
  have hceil :
      Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 ≤
        ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ :=
    le_of_eq hadd
  exact Nat.add_one_le_ceil_iff.mp hceil

theorem Complex.logarithmicPhaseFiniteRightResidual_eq_angular_difference
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteRightResidual t b =
      (2 * Real.pi) *
        (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b -
          (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)) := by
  unfold Complex.logarithmicPhaseFiniteRightResidual
  unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
  have htwoPiNe : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Complex.two_mul_pi_pos
  have hfirst :
      (2 * Real.pi) *
          (‖t‖ /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportRight b)) =
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b := by
    calc
      (2 * Real.pi) *
          (‖t‖ /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportRight b)) =
          (2 * Real.pi * ‖t‖) /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportRight b) :=
        (mul_div_assoc _ _ _).symm
      _ = ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b := by
        exact mul_div_mul_left ‖t‖
          (Complex.logarithmicPhaseQuantitativeSupportRight b) htwoPiNe
  have hreplace := congrArg
      (fun value : ℝ => value -
        (2 * Real.pi) *
          (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ))
      hfirst.symm
  have hexpand := mul_sub (2 * Real.pi)
    (‖t‖ /
      (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportRight b))
    (Complex.logarithmicPhaseFiniteRightFrequencyTop t b : ℝ)
  exact Eq.trans hreplace hexpand.symm

theorem Complex.logarithmicPhaseFiniteRightResidual_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightResidual t b := by
  have hdifference := sub_pos.mpr
    (Complex.logarithmicPhaseFiniteRightTop_lt_threshold
      t ht a b ha hab)
  have hproduct := mul_pos Complex.two_mul_pi_pos hdifference
  exact Eq.subst
    (motive := fun value : ℝ => 0 < value)
    (Complex.logarithmicPhaseFiniteRightResidual_eq_angular_difference
      t a b ha hab).symm hproduct

theorem Complex.finiteRight_inverseSquare_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2 =
      Real.zeroBasedShiftedInverseSquareTerm
        (Complex.logarithmicPhaseFiniteRightResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightReverseIndex m) := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 2)
    (Complex.logarithmicPhaseFiniteRightResidual_add_step_index
      t ht a b ha hab m)

theorem Complex.finiteRight_inverseCube_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3 =
      Real.zeroBasedShiftedInverseCubeTerm
        (Complex.logarithmicPhaseFiniteRightResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightReverseIndex m) := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 3)
    (Complex.logarithmicPhaseFiniteRightResidual_add_step_index
      t ht a b ha hab m)

theorem Complex.finiteRight_inverseFourth_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4 =
      Real.zeroBasedShiftedInverseFourthTerm
        (Complex.logarithmicPhaseFiniteRightResidual t b)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteRightReverseIndex m) := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 4)
    (Complex.logarithmicPhaseFiniteRightResidual_add_step_index
      t ht a b ha hab m)

theorem Complex.sum_finiteRight_inverseSquare_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2) ≤
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m =>
    1 / (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 2
  let g := Real.zeroBasedShiftedInverseSquareTerm
    (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteRightResidual_pos t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseSquareTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 2)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteRightReverseIndex m) :=
    fun m => le_of_eq
      (Complex.finiteRight_inverseSquare_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g
    Complex.logarithmicPhaseFiniteRightReverseIndex
    (Complex.logarithmicPhaseFiniteRightReverseIndex_injective
      t ht a b ha hab)
    hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseSquareTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  have hbudget := Real.tsum_zeroBasedShiftedInverseSquareTerm_le_budget
    _ _ hresidual Complex.two_mul_pi_pos
  exact le_trans hsum hbudget

theorem Complex.sum_finiteRight_inverseCube_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3) ≤
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 3
  let g := Real.zeroBasedShiftedInverseCubeTerm
    (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteRightResidual_pos t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseCubeTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 3)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteRightReverseIndex m) :=
    fun m => le_of_eq
      (Complex.finiteRight_inverseCube_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g Complex.logarithmicPhaseFiniteRightReverseIndex
    (Complex.logarithmicPhaseFiniteRightReverseIndex_injective
      t ht a b ha hab) hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseCubeTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseCubeTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteRight_inverseFourth_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      1 / (Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4) ≤
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b)) ^ 4
  let g := Real.zeroBasedShiftedInverseFourthTerm
    (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteRightResidual_pos t ht a b ha hab
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseFourthTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 4)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteRightReverseIndex m) :=
    fun m => le_of_eq
      (Complex.finiteRight_inverseFourth_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g Complex.logarithmicPhaseFiniteRightReverseIndex
    (Complex.logarithmicPhaseFiniteRightReverseIndex_injective
      t ht a b ha hab) hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseFourthTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseFourthTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

/-! ## The complete finite right-inactive packet budget -/

def Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedSquareCoefficient *
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi)

theorem Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hresidual :=
    Complex.logarithmicPhaseFiniteRightResidual_pos t ht a b ha hab
  have hsquare :=
    Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg t a hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
      t a b hab hleft
  have hfourth :=
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
      t a b hab hleft
  have hsquareBudget :=
    Real.zeroBasedShiftedInverseSquareBudget_nonneg
      _ _ hresidual.le Complex.two_mul_pi_pos.le
  have hcubeBudget :=
    Real.zeroBasedShiftedInverseCubeBudget_nonneg
      _ _ hresidual.le Complex.two_mul_pi_pos.le
  have hfourthBudget :=
    Real.zeroBasedShiftedInverseFourthBudget_nonneg
      _ _ hresidual.le Complex.two_mul_pi_pos.le
  unfold Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg
        (mul_nonneg hsquare hsquareBudget)
        (mul_nonneg hcurvature hcubeBudget))
      (mul_nonneg hthird hcubeBudget))
    (mul_nonneg hfourth hfourthBudget)

theorem Complex.sum_finiteRight_closedMajorant_le_seriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseRightInactiveGap t m
          (Complex.logarithmicPhaseQuantitativeSupportRight b))) ≤
      Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hsquare := Complex.sum_finiteRight_inverseSquare_le_zeroBasedBudget
    t ht a b ha hab
  have hcube := Complex.sum_finiteRight_inverseCube_le_zeroBasedBudget
    t ht a b ha hab
  have hfourth := Complex.sum_finiteRight_inverseFourth_le_zeroBasedBudget
    t ht a b ha hab
  unfold Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget
  exact Complex.sum_adaptedClosedMajorant_le_fourPowerBudget
    t a b
    (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
    (fun m => Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b))
    (Real.zeroBasedShiftedInverseSquareBudget
      (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseCubeBudget
      (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseFourthBudget
      (Complex.logarithmicPhaseFiniteRightResidual t b) (2 * Real.pi))
    hleft hab hsquare hcube hfourth

theorem Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget_le_seriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteRightInactiveSeriesBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeRightInactiveBudget
  have hpacket := Finset.sum_le_sum (fun m hm => by
    have hgap :=
      Complex.logarithmicPhaseRightInactiveGap_ge_curvature_third
        t ht a b ha hab hm
    have hgapPos := lt_of_lt_of_le
      (Complex.logarithmicPhaseFiniteRightInactiveGap_pos
        t ht a b ha hab) hgap
    have hstrict :
        2 * Real.pi * (-(m : ℝ)) <
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
      sub_pos.mp hgapPos
    have hcanonical := Complex.norm_logarithmicPhaseRightInactiveModePacket_le
      t a b m ha hab hstrict
    unfold Complex.logarithmicPhaseRightInactiveClosedMajorant at hcanonical
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseRightInactiveGap t m
              (Complex.logarithmicPhaseQuantitativeSupportRight b)))
      hparameter.symm hcanonical)
  exact le_trans hpacket
    (Complex.sum_finiteRight_closedMajorant_le_seriesBudget
      t ht a b ha hab)

end

end LFunctions
end Boundary

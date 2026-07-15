import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveSeriesBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ZeroBasedShiftedReciprocalPower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactivePacketBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveMajorantSum

/-!
# Shifted reciprocal series for finite left-inactive modes

Write `q = -m`.  Left inactivity places the integer `q` strictly above
`‖t‖ / (2*pi*L)`, where `L` is the quantitative left endpoint.  The first
possible integer is therefore `floor(threshold)+1`.  Subtracting that integer
gives an injective natural index, while the derivative gap becomes an exact
positive residual plus `2*pi` times that index.  This retains all reciprocal
powers in the phase-adapted majorant and avoids a cardinality-times-worst-gap
estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftFrequencyThreshold
    (t : ℝ) (a : ℤ) : ℝ :=
  ‖t‖ /
    (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportLeft a)

def Complex.logarithmicPhaseFiniteLeftFrequencyBase
    (t : ℝ) (a : ℤ) : ℤ :=
  ⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ + 1

def Complex.logarithmicPhaseFiniteLeftResidual
    (t : ℝ) (a : ℤ) : ℝ :=
  2 * Real.pi *
      (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) -
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a

def Complex.logarithmicPhaseFiniteLeftForwardIndex
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) : ℕ :=
  (-(m : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a).toNat

theorem Complex.logarithmicPhaseFiniteLeftThreshold_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a := by
  unfold Complex.logarithmicPhaseFiniteLeftFrequencyThreshold
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hleft := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  exact div_pos hnorm (mul_pos Complex.two_mul_pi_pos hleft)

theorem Complex.logarithmicPhaseFiniteLeftBase_gt_threshold
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a <
      (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteLeftFrequencyBase
  have hraw := Int.lt_floor_add_one
    (Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a)
  have hcastAdd := Int.cast_add
    (R := ℝ)
    ⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ 1
  have hcastOne : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
  have htransport :
      ((⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ + 1 : ℤ) : ℝ) =
        (⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ : ℝ) + 1 :=
    Eq.trans hcastAdd
      (congrArg
        (fun value : ℝ =>
          (⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ : ℝ) + value)
        hcastOne)
  exact Eq.subst
    (motive := fun value : ℝ =>
      Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a < value)
    htransport.symm hraw

theorem Complex.logarithmicPhaseFiniteLeftResidual_eq_angular_difference
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    Complex.logarithmicPhaseFiniteLeftResidual t a =
      (2 * Real.pi) *
        ((Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) -
          Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a) := by
  unfold Complex.logarithmicPhaseFiniteLeftResidual
  unfold Complex.logarithmicPhaseFiniteLeftFrequencyThreshold
  have htwoPiNe : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Complex.two_mul_pi_pos
  have hcancel :
      (2 * Real.pi) *
          (‖t‖ /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportLeft a)) =
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a := by
    calc
      (2 * Real.pi) *
          (‖t‖ /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportLeft a)) =
          (2 * Real.pi * ‖t‖) /
            (2 * Real.pi *
              Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
        (mul_div_assoc _ _ _).symm
      _ = ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a :=
        mul_div_mul_left ‖t‖
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) htwoPiNe
  have hexpand := mul_sub (2 * Real.pi)
    (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)
    (‖t‖ /
      (2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportLeft a))
  exact Eq.trans
    (congrArg
      (fun value : ℝ =>
        (2 * Real.pi) *
            (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) -
          value)
      hcancel.symm)
    hexpand.symm

theorem Complex.logarithmicPhaseFiniteLeftResidual_pos
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftResidual t a := by
  have hdifference := sub_pos.mpr
    (Complex.logarithmicPhaseFiniteLeftBase_gt_threshold t a)
  have hproduct := mul_pos Complex.two_mul_pi_pos hdifference
  exact Eq.subst
    (motive := fun value : ℝ => 0 < value)
    (Complex.logarithmicPhaseFiniteLeftResidual_eq_angular_difference
      t a ha).symm hproduct

theorem Complex.logarithmicPhaseFiniteLeft_mode_frequency_gt_threshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a <
      ((-(m : ℤ) : ℤ) : ℝ) := by
  have hgapLower :=
    Complex.logarithmicPhaseLeftInactiveGap_ge_curvature_third
      t ht a b ha hab m.property
  have hgapPos := lt_of_lt_of_le
    (Complex.logarithmicPhaseFiniteLeftInactiveGap_pos t ht a ha)
    hgapLower
  unfold Complex.logarithmicPhaseLeftInactiveGap at hgapPos
  unfold Complex.logarithmicPhaseFiniteLeftFrequencyThreshold
  have hgapStrict :
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
        2 * Real.pi * (-((m : ℤ) : ℝ)) :=
    sub_pos.mp hgapPos
  have hproductOrder :
      2 * Real.pi * (-((m : ℤ) : ℝ)) =
        -((m : ℤ) : ℝ) * (2 * Real.pi) :=
    mul_comm _ _
  have hgapOrdered :
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
        -((m : ℤ) : ℝ) * (2 * Real.pi) :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a < value)
      hproductOrder hgapStrict
  have hdivide :
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) /
          (2 * Real.pi) <
        -((m : ℤ) : ℝ) :=
    (div_lt_iff₀ Complex.two_mul_pi_pos).mpr hgapOrdered
  have hquotientOrder :
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) /
          (2 * Real.pi) =
        ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    (div_div ‖t‖
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)
      (2 * Real.pi)).trans
      (congrArg (fun value : ℝ => ‖t‖ / value)
        (mul_comm
          (Complex.logarithmicPhaseQuantitativeSupportLeft a)
          (2 * Real.pi)))
  have hthresholdReal :
      ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) <
        -((m : ℤ) : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value < -((m : ℤ) : ℝ))
      hquotientOrder hdivide
  have hcastNeg : ((-(m : ℤ) : ℤ) : ℝ) = -((m : ℤ) : ℝ) :=
    Int.cast_neg (m : ℤ)
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) < value)
    hcastNeg.symm hthresholdReal

theorem Complex.logarithmicPhaseFiniteLeftBase_le_mode_frequency
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftFrequencyBase t a ≤ -(m : ℤ) := by
  have hthreshold :=
    Complex.logarithmicPhaseFiniteLeft_mode_frequency_gt_threshold
      t ht a b ha hab m
  unfold Complex.logarithmicPhaseFiniteLeftFrequencyBase
  have hfloor :
      ⌊Complex.logarithmicPhaseFiniteLeftFrequencyThreshold t a⌋ <
        -(m : ℤ) :=
    Int.floor_lt.mpr hthreshold
  exact Int.add_one_le_iff.mpr hfloor

theorem Complex.logarithmicPhaseFiniteLeftForwardIndex_cast
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    (Complex.logarithmicPhaseFiniteLeftForwardIndex m : ℤ) =
      -(m : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a := by
  unfold Complex.logarithmicPhaseFiniteLeftForwardIndex
  have hnonneg := sub_nonneg.mpr
    (Complex.logarithmicPhaseFiniteLeftBase_le_mode_frequency
      t ht a b ha hab m)
  exact Int.toNat_of_nonneg hnonneg

theorem Complex.logarithmicPhaseFiniteLeftForwardIndex_injective
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Function.Injective
      (Complex.logarithmicPhaseFiniteLeftForwardIndex
        (t := t) (a := a) (b := b)) := by
  intro m₁ m₂ hindex
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hindex
  have hcast₁ := Complex.logarithmicPhaseFiniteLeftForwardIndex_cast
    t ht a b ha hab m₁
  have hcast₂ := Complex.logarithmicPhaseFiniteLeftForwardIndex_cast
    t ht a b ha hab m₂
  have hdifference :
      -(m₁ : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a =
        -(m₂ : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a :=
    Eq.trans hcast₁.symm (Eq.trans hcast hcast₂)
  have hadd := congrArg
    (fun value : ℤ =>
      value + Complex.logarithmicPhaseFiniteLeftFrequencyBase t a)
    hdifference
  have hcancel₁ :
      (-(m₁ : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a) +
          Complex.logarithmicPhaseFiniteLeftFrequencyBase t a = -(m₁ : ℤ) :=
    sub_add_cancel _ _
  have hcancel₂ :
      (-(m₂ : ℤ) - Complex.logarithmicPhaseFiniteLeftFrequencyBase t a) +
          Complex.logarithmicPhaseFiniteLeftFrequencyBase t a = -(m₂ : ℤ) :=
    sub_add_cancel _ _
  have hnegative : -(m₁ : ℤ) = -(m₂ : ℤ) :=
    Eq.trans hcancel₁.symm (Eq.trans hadd hcancel₂)
  have hvalue : (m₁ : ℤ) = (m₂ : ℤ) :=
    neg_injective hnegative
  exact Subtype.ext hvalue

theorem Complex.logarithmicPhaseFiniteLeftResidual_add_step_index
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftResidual t a +
        (2 * Real.pi) *
          (Complex.logarithmicPhaseFiniteLeftForwardIndex m : ℝ) =
      Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  have hindexInt := Complex.logarithmicPhaseFiniteLeftForwardIndex_cast
    t ht a b ha hab m
  have hindexReal :
      (Complex.logarithmicPhaseFiniteLeftForwardIndex m : ℝ) =
        ((-(m : ℤ) -
          Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℤ) : ℝ) := by
    exact congrArg (fun z : ℤ => (z : ℝ)) hindexInt
  unfold Complex.logarithmicPhaseFiniteLeftResidual
  unfold Complex.logarithmicPhaseLeftInactiveGap
  have hcastNeg : ((-(m : ℤ) : ℤ) : ℝ) = -((m : ℤ) : ℝ) :=
    Int.cast_neg (m : ℤ)
  have hindexNormalized :
      (Complex.logarithmicPhaseFiniteLeftForwardIndex m : ℝ) =
        -((m : ℤ) : ℝ) -
          (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) :=
    Eq.trans hindexReal
      (Eq.trans (Int.cast_sub _ _)
        (congrArg
          (fun value : ℝ => value -
            (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ))
          hcastNeg))
  exact Eq.subst
    (motive := fun value : ℝ =>
      2 * Real.pi *
            (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a +
          (2 * Real.pi) * value =
        2 * Real.pi * (-((m : ℤ) : ℝ)) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a)
    hindexNormalized.symm
    (by
      calc
        2 * Real.pi *
              (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) -
            ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a +
            (2 * Real.pi) *
              (-((m : ℤ) : ℝ) -
                (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)) =
            (2 * Real.pi *
                (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) +
              2 * Real.pi *
                (-((m : ℤ) : ℝ) -
                  (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ))) -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a :=
          sub_add_eq_add_sub _ _ _
        _ = 2 * Real.pi * (-((m : ℤ) : ℝ)) -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a := by
          have hdistribute := mul_sub (2 * Real.pi)
            (-((m : ℤ) : ℝ))
            (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)
          have hcancel :
              2 * Real.pi *
                    (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) +
                  (2 * Real.pi * (-((m : ℤ) : ℝ)) -
                    2 * Real.pi *
                      (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)) =
                2 * Real.pi * (-((m : ℤ) : ℝ)) := by
            exact Eq.trans
              (add_comm
                (2 * Real.pi *
                  (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ))
                (2 * Real.pi * (-((m : ℤ) : ℝ)) -
                  2 * Real.pi *
                    (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)))
              (sub_add_cancel
                (2 * Real.pi * (-((m : ℤ) : ℝ)))
                (2 * Real.pi *
                  (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ)))
          exact congrArg
            (fun value : ℝ => value -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a)
            (Eq.trans
              (congrArg
                (fun value : ℝ =>
                  2 * Real.pi *
                      (Complex.logarithmicPhaseFiniteLeftFrequencyBase t a : ℝ) +
                    value)
                hdistribute)
              hcancel))

theorem Complex.finiteLeft_inverseSquare_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 =
      Real.zeroBasedShiftedInverseSquareTerm
        (Complex.logarithmicPhaseFiniteLeftResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftForwardIndex m) := by
  unfold Real.zeroBasedShiftedInverseSquareTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 2)
    (Complex.logarithmicPhaseFiniteLeftResidual_add_step_index
      t ht a b ha hab m).symm

theorem Complex.finiteLeft_inverseCube_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3 =
      Real.zeroBasedShiftedInverseCubeTerm
        (Complex.logarithmicPhaseFiniteLeftResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftForwardIndex m) := by
  unfold Real.zeroBasedShiftedInverseCubeTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 3)
    (Complex.logarithmicPhaseFiniteLeftResidual_add_step_index
      t ht a b ha hab m).symm

theorem Complex.finiteLeft_inverseFourth_eq_zeroBasedTerm
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    1 / (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4 =
      Real.zeroBasedShiftedInverseFourthTerm
        (Complex.logarithmicPhaseFiniteLeftResidual t a)
        (2 * Real.pi)
        (Complex.logarithmicPhaseFiniteLeftForwardIndex m) := by
  unfold Real.zeroBasedShiftedInverseFourthTerm
  exact congrArg (fun value : ℝ => 1 / value ^ 4)
    (Complex.logarithmicPhaseFiniteLeftResidual_add_step_index
      t ht a b ha hab m).symm

theorem Complex.sum_finiteLeft_inverseSquare_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2) ≤
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2
  let g := Real.zeroBasedShiftedInverseSquareTerm
    (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteLeftResidual_pos t a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseSquareTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 2)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteLeftForwardIndex m) :=
    fun m => le_of_eq
      (Complex.finiteLeft_inverseSquare_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g Complex.logarithmicPhaseFiniteLeftForwardIndex
    (Complex.logarithmicPhaseFiniteLeftForwardIndex_injective
      t ht a b ha hab) hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseSquareTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseSquareTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteLeft_inverseCube_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3) ≤
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 3
  let g := Real.zeroBasedShiftedInverseCubeTerm
    (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteLeftResidual_pos t a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseCubeTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 3)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteLeftForwardIndex m) :=
    fun m => le_of_eq
      (Complex.finiteLeft_inverseCube_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g Complex.logarithmicPhaseFiniteLeftForwardIndex
    (Complex.logarithmicPhaseFiniteLeftForwardIndex_injective
      t ht a b ha hab) hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseCubeTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseCubeTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

theorem Complex.sum_finiteLeft_inverseFourth_le_zeroBasedBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      1 / (Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4) ≤
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) := by
  let modes := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let f : ℤ → ℝ := fun m => 1 /
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 4
  let g := Real.zeroBasedShiftedInverseFourthTerm
    (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi)
  have hresidual :=
    Complex.logarithmicPhaseFiniteLeftResidual_pos t a ha
  have hgNonneg : ∀ n : ℕ, 0 ≤ g n := fun n => by
    unfold g
    unfold Real.zeroBasedShiftedInverseFourthTerm
    have hbase := add_nonneg hresidual.le
      (mul_nonneg Complex.two_mul_pi_pos.le (Nat.cast_nonneg n))
    exact div_nonneg zero_le_one (pow_nonneg hbase 4)
  have hpoint : ∀ m : {m : ℤ // m ∈ modes},
      f m ≤ g (Complex.logarithmicPhaseFiniteLeftForwardIndex m) :=
    fun m => le_of_eq
      (Complex.finiteLeft_inverseFourth_eq_zeroBasedTerm
        t ht a b ha hab m)
  have hsum := Finset.sum_le_tsum_of_subtype_injection
    modes f g Complex.logarithmicPhaseFiniteLeftForwardIndex
    (Complex.logarithmicPhaseFiniteLeftForwardIndex_injective
      t ht a b ha hab) hpoint hgNonneg
    (Real.summable_zeroBasedShiftedInverseFourthTerm
      _ _ hresidual Complex.two_mul_pi_pos)
  exact le_trans hsum
    (Real.tsum_zeroBasedShiftedInverseFourthTerm_le_budget
      _ _ hresidual Complex.two_mul_pi_pos)

def Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedSquareCoefficient *
      Real.zeroBasedShiftedInverseSquareBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
      Real.zeroBasedShiftedInverseCubeBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi) +
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
      Real.zeroBasedShiftedInverseFourthBudget
        (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi)

theorem Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget_nonneg
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hresidual :=
    (Complex.logarithmicPhaseFiniteLeftResidual_pos t a ha).le
  have hsquareBudget := Real.zeroBasedShiftedInverseSquareBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hcubeBudget := Real.zeroBasedShiftedInverseCubeBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hfourthBudget := Real.zeroBasedShiftedInverseFourthBudget_nonneg
    _ _ hresidual Complex.two_mul_pi_pos.le
  have hc₁ := Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg
  have hc₂ :=
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg t a hleft
  have hc₃ := Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
    t a b hab hleft
  have hc₄ := Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
    t a b hab hleft
  unfold Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget
  exact add_nonneg
    (add_nonneg
      (add_nonneg (mul_nonneg hc₁ hsquareBudget)
        (mul_nonneg hc₂ hcubeBudget))
      (mul_nonneg hc₃ hcubeBudget))
    (mul_nonneg hc₄ hfourthBudget)

theorem Complex.sum_finiteLeft_closedMajorant_le_seriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (Complex.logarithmicPhaseLeftInactiveGap t m
          (Complex.logarithmicPhaseQuantitativeSupportLeft a))) ≤
      Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hsquare := Complex.sum_finiteLeft_inverseSquare_le_zeroBasedBudget
    t ht a b ha hab
  have hcube := Complex.sum_finiteLeft_inverseCube_le_zeroBasedBudget
    t ht a b ha hab
  have hfourth := Complex.sum_finiteLeft_inverseFourth_le_zeroBasedBudget
    t ht a b ha hab
  unfold Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget
  exact Complex.sum_adaptedClosedMajorant_le_fourPowerBudget
    t a b
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
    (fun m => Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))
    (Real.zeroBasedShiftedInverseSquareBudget
      (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseCubeBudget
      (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi))
    (Real.zeroBasedShiftedInverseFourthBudget
      (Complex.logarithmicPhaseFiniteLeftResidual t a) (2 * Real.pi))
    hleft hab hsquare hcube hfourth

theorem Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget_le_seriesBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget t a b ≤
      Complex.logarithmicPhaseFiniteLeftInactiveSeriesBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessQuantitativeLeftInactiveBudget
  have hpacket := Finset.sum_le_sum (fun m hm => by
    have hgap := Complex.logarithmicPhaseLeftInactiveGap_ge_curvature_third
      t ht a b ha hab hm
    have hgapPos := lt_of_lt_of_le
      (Complex.logarithmicPhaseFiniteLeftInactiveGap_pos t ht a ha) hgap
    have hstrict :
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
          2 * Real.pi * (-(m : ℝ)) := sub_pos.mp hgapPos
    have hcanonical := Complex.norm_logarithmicPhaseLeftInactiveModePacket_le
      t a b m ha hab hstrict
    unfold Complex.logarithmicPhaseLeftInactiveClosedMajorant at hcanonical
    have hparameter :=
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_eq_norm_parameter_of_nonneg
        t ht_nonneg a b m
    exact Eq.subst
      (motive := fun value : ℝ =>
        value ≤
          Complex.logarithmicPhaseAdaptedClosedMajorant t a b
            (Complex.logarithmicPhaseLeftInactiveGap t m
              (Complex.logarithmicPhaseQuantitativeSupportLeft a)))
      hparameter.symm hcanonical)
  exact le_trans hpacket
    (Complex.sum_finiteLeft_closedMajorant_le_seriesBudget
      t ht a b ha hab)

end

end LFunctions
end Boundary

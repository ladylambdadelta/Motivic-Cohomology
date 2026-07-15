import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteLeftInactiveSeries
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteRightInactiveSeries

/-!
# Full-support protected residuals for finite inactive frequencies

The inactive classes are separated from the quantitative support because their
stationary centers lie beyond the larger compact cutoff support.  Reindexing at
the quantitative endpoint alone forgets this fact and may create a fictitious
near-zero first gap.  Here the integer base and top are instead determined by
the full-support thresholds.  The resulting residuals are the actual
quantitative derivative gaps at those extremal integer frequencies and retain
the geometric one-third separation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftFullSupportThreshold
    (t : ℝ) (a : ℤ) : ℝ :=
  ‖t‖ / (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)

def Complex.logarithmicPhaseFiniteLeftProtectedBase
    (t : ℝ) (a : ℤ) : ℤ :=
  ⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ + 1

def Complex.logarithmicPhaseFiniteLeftProtectedResidual
    (t : ℝ) (a : ℤ) : ℝ :=
  2 * Real.pi *
      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) -
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a

def Complex.logarithmicPhaseFiniteRightFullSupportThreshold
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ / (2 * Real.pi * ((b : ℝ) + 2 / 3))

def Complex.logarithmicPhaseFiniteRightProtectedTop
    (t : ℝ) (b : ℤ) : ℕ :=
  ⌈Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b⌉₊ - 1

def Complex.logarithmicPhaseFiniteRightProtectedResidual
    (t : ℝ) (b : ℤ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
    2 * Real.pi *
      (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)

theorem Complex.logarithmicPhaseFiniteLeftFullSupportThreshold_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a := by
  unfold Complex.logarithmicPhaseFiniteLeftFullSupportThreshold
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hfull := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  exact div_pos hnorm (mul_pos Complex.two_mul_pi_pos hfull)

theorem Complex.logarithmicPhaseFiniteLeftProtectedBase_gt_fullThreshold
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a <
      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) := by
  unfold Complex.logarithmicPhaseFiniteLeftProtectedBase
  have hraw := Int.lt_floor_add_one
    (Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a)
  have hcastAdd := Int.cast_add
    (R := ℝ)
    ⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ 1
  have hcastOne : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
  have htransport :
      ((⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ + 1 : ℤ) : ℝ) =
        (⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ : ℝ) + 1 :=
    Eq.trans hcastAdd
      (congrArg
        (fun value : ℝ =>
          (⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ : ℝ) + value)
        hcastOne)
  exact Eq.subst
    (motive := fun value : ℝ =>
      Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a < value)
    htransport.symm hraw

theorem Complex.logarithmicPhaseFiniteLeftProtectedBase_frequency_gap_pos
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 <
      2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) -
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a := by
  have hthreshold :=
    Complex.logarithmicPhaseFiniteLeftProtectedBase_gt_fullThreshold t a
  unfold Complex.logarithmicPhaseFiniteLeftFullSupportThreshold at hthreshold
  have hfull := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hdenominator := mul_pos Complex.two_mul_pi_pos hfull
  have hscaled := (div_lt_iff₀ hdenominator).mp hthreshold
  have hreorder :
      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) *
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) =
        (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)) *
            Real.integerBlockCutoffSupportLeftEndpoint a := by
    calc
      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) *
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) =
        ((Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) *
          (2 * Real.pi)) * Real.integerBlockCutoffSupportLeftEndpoint a :=
        (mul_assoc _ _ _).symm
      _ = (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)) *
            Real.integerBlockCutoffSupportLeftEndpoint a :=
        congrArg
          (fun value : ℝ =>
            value * Real.integerBlockCutoffSupportLeftEndpoint a)
          (mul_comm _ _)
  have hscaledNormalized :
      ‖t‖ <
        (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)) *
            Real.integerBlockCutoffSupportLeftEndpoint a :=
    Eq.subst (motive := fun value : ℝ => ‖t‖ < value) hreorder hscaled
  have hstrict :
      ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a <
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) :=
    (div_lt_iff₀ hfull).mpr hscaledNormalized
  exact sub_pos.mpr hstrict

theorem Complex.logarithmicPhaseFiniteLeftProtectedResidual_ge_fullGap
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    2 * Real.pi *
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) -
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a ≤
      Complex.logarithmicPhaseFiniteLeftProtectedResidual t a := by
  unfold Complex.logarithmicPhaseFiniteLeftProtectedResidual
  have hfull := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hquant := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hendpoint :
      Real.integerBlockCutoffSupportLeftEndpoint a <
        Complex.logarithmicPhaseQuantitativeSupportLeft a := by
    have hdifference := Real.quantitativeLeft_sub_fullLeft_eq_one_third a
    have hthird : (0 : ℝ) < 1 / 3 :=
      div_pos zero_lt_one zero_lt_three
    exact sub_pos.mp (Eq.subst
      (motive := fun value : ℝ => 0 < value)
      hdifference.symm hthird)
  have hdivision := div_le_div_of_nonneg_left
    (norm_nonneg t) hfull hendpoint.le
  exact sub_le_sub_left hdivision
    (2 * Real.pi *
      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ))

theorem Complex.logarithmicPhaseFiniteLeftProtectedResidual_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftProtectedResidual t a := by
  have hfullGap :=
    Complex.logarithmicPhaseFiniteLeftProtectedBase_frequency_gap_pos
      t a ha
  have hcomparison :=
    Complex.logarithmicPhaseFiniteLeftProtectedResidual_ge_fullGap
      t a ha
  exact lt_of_lt_of_le hfullGap hcomparison

theorem Complex.logarithmicPhaseFiniteRightFullSupportThreshold_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b := by
  unfold Complex.logarithmicPhaseFiniteRightFullSupportThreshold
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hbCast : ((1 : ℤ) : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr (le_trans ha hab)
  have hcastOne : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
  have hbReal : (1 : ℝ) ≤ (b : ℝ) :=
    Eq.subst (motive := fun value : ℝ => value ≤ (b : ℝ)) hcastOne hbCast
  have htwoThirds : (0 : ℝ) < 2 / 3 :=
    div_pos zero_lt_two zero_lt_three
  have hright := lt_of_lt_of_le (add_pos zero_lt_one htwoThirds) (add_le_add_right hbReal _)
  exact div_pos hnorm (mul_pos Complex.two_mul_pi_pos hright)

theorem Complex.logarithmicPhaseFiniteRightProtectedTop_add_one_eq_ceil
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteRightProtectedTop t b + 1 =
      ⌈Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b⌉₊ := by
  unfold Complex.logarithmicPhaseFiniteRightProtectedTop
  have hceilPos :
      0 < ⌈Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b⌉₊ :=
    Nat.ceil_pos.mpr
      (Complex.logarithmicPhaseFiniteRightFullSupportThreshold_pos
        t ht a b ha hab)
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hceilPos)

theorem Complex.logarithmicPhaseFiniteRightProtectedTop_lt_fullThreshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) <
      Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b := by
  have hadd :=
    Complex.logarithmicPhaseFiniteRightProtectedTop_add_one_eq_ceil
      t ht a b ha hab
  have hceil :
      Complex.logarithmicPhaseFiniteRightProtectedTop t b + 1 ≤
        ⌈Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b⌉₊ :=
    le_of_eq hadd
  exact Nat.add_one_le_ceil_iff.mp hceil

theorem Complex.logarithmicPhaseFiniteRightProtectedResidual_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightProtectedResidual t b := by
  unfold Complex.logarithmicPhaseFiniteRightProtectedResidual
  have htop :=
    Complex.logarithmicPhaseFiniteRightProtectedTop_lt_fullThreshold
      t ht a b ha hab
  unfold Complex.logarithmicPhaseFiniteRightFullSupportThreshold at htop
  have hrightQuant :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hrightFull :
      Complex.logarithmicPhaseQuantitativeSupportRight b <
        (b : ℝ) + 2 / 3 := by
    have hdifference := Real.fullRight_sub_quantitativeRight_eq_one_third b
    have hthird : (0 : ℝ) < 1 / 3 :=
      div_pos zero_lt_one zero_lt_three
    exact sub_pos.mp (Eq.subst
      (motive := fun value : ℝ => 0 < value)
      hdifference.symm hthird)
  have hnorm := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdivision := div_lt_div_of_pos_left hnorm hrightQuant hrightFull
  have hfullPos := lt_trans hrightQuant hrightFull
  have hdenominator := mul_pos Complex.two_mul_pi_pos hfullPos
  have hscaled := (lt_div_iff₀ hdenominator).mp htop
  have hreorder :
      (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) *
          (2 * Real.pi * ((b : ℝ) + 2 / 3)) =
        (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) *
            ((b : ℝ) + 2 / 3) := by
    calc
      (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) *
          (2 * Real.pi * ((b : ℝ) + 2 / 3)) =
        ((Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) *
          (2 * Real.pi)) * ((b : ℝ) + 2 / 3) :=
        (mul_assoc _ _ _).symm
      _ = (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) *
            ((b : ℝ) + 2 / 3) :=
        congrArg (fun value : ℝ => value * ((b : ℝ) + 2 / 3))
          (mul_comm _ _)
  have hscaledNormalized :
      (2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) *
          ((b : ℝ) + 2 / 3) < ‖t‖ :=
    Eq.subst (motive := fun value : ℝ => value < ‖t‖) hreorder hscaled
  have hfullBound :
      2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) <
        ‖t‖ / ((b : ℝ) + 2 / 3) := by
    exact (lt_div_iff₀ hfullPos).mpr hscaledNormalized
  exact sub_pos.mpr (lt_trans hfullBound hdivision)

def Complex.logarithmicPhaseFiniteLeftProtectedIndex
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) : ℕ :=
  (-(m : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a).toNat

def Complex.logarithmicPhaseFiniteRightProtectedIndex
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) : ℕ :=
  (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
    (-(m : ℤ)).toNat)

theorem Complex.stationaryPoint_lt_left_iff_frequency_gt
    (t : ℝ) (m : ℤ) (left : ℝ)
    (ht : 1 ≤ ‖t‖) (hm : m < 0) (hleft : 0 < left) :
    Complex.logarithmicPhaseFourierStationaryPoint t m < left ↔
      ‖t‖ / (2 * Real.pi * left) < -(m : ℝ) := by
  have hfrequency : 0 < -(m : ℝ) := by
    have hmReal : ((m : ℤ) : ℝ) < 0 := Int.cast_lt_zero.mpr hm
    exact neg_pos.mpr hmReal
  have hangular : 0 < 2 * Real.pi := Complex.two_mul_pi_pos
  have hdenominator : 0 < 2 * Real.pi * -(m : ℝ) :=
    mul_pos hangular hfrequency
  constructor
  · intro hcenter
    unfold Complex.logarithmicPhaseFourierStationaryPoint at hcenter
    have hproduct := (div_lt_iff₀ hdenominator).mp hcenter
    have hreorder :
        left * (2 * Real.pi * -(m : ℝ)) =
          -(m : ℝ) * (2 * Real.pi * left) := by
      calc
        left * (2 * Real.pi * -(m : ℝ)) =
            (left * (2 * Real.pi)) * -(m : ℝ) :=
          (mul_assoc _ _ _).symm
        _ = -(m : ℝ) * (left * (2 * Real.pi)) := mul_comm _ _
        _ = -(m : ℝ) * (2 * Real.pi * left) :=
          congrArg (fun value : ℝ => -(m : ℝ) * value)
            (mul_comm _ _)
    have htargetProduct :
        ‖t‖ < -(m : ℝ) * (2 * Real.pi * left) :=
      Eq.subst (motive := fun value : ℝ => ‖t‖ < value) hreorder hproduct
    exact (div_lt_iff₀ (mul_pos hangular hleft)).mpr htargetProduct
  · intro hfrequencyBound
    unfold Complex.logarithmicPhaseFourierStationaryPoint
    have hproduct :=
      (div_lt_iff₀ (mul_pos hangular hleft)).mp hfrequencyBound
    have hreorder :
        -(m : ℝ) * (2 * Real.pi * left) =
          left * (2 * Real.pi * -(m : ℝ)) := by
      calc
        -(m : ℝ) * (2 * Real.pi * left) =
            -(m : ℝ) * (left * (2 * Real.pi)) :=
          congrArg (fun value : ℝ => -(m : ℝ) * value)
            (mul_comm _ _)
        _ = (left * (2 * Real.pi)) * -(m : ℝ) := mul_comm _ _
        _ = left * (2 * Real.pi * -(m : ℝ)) := mul_assoc _ _ _
    have htargetProduct :
        ‖t‖ < left * (2 * Real.pi * -(m : ℝ)) :=
      Eq.subst (motive := fun value : ℝ => ‖t‖ < value) hreorder hproduct
    exact (div_lt_iff₀ hdenominator).mpr htargetProduct

theorem Complex.right_lt_stationaryPoint_iff_frequency_lt
    (t : ℝ) (m : ℤ) (right : ℝ)
    (ht : 1 ≤ ‖t‖) (hm : m < 0) (hright : 0 < right) :
    right < Complex.logarithmicPhaseFourierStationaryPoint t m ↔
      -(m : ℝ) < ‖t‖ / (2 * Real.pi * right) := by
  have hfrequency : 0 < -(m : ℝ) :=
    neg_pos.mpr (Int.cast_lt_zero.mpr hm)
  have hangular : 0 < 2 * Real.pi := Complex.two_mul_pi_pos
  have hdenominator : 0 < 2 * Real.pi * -(m : ℝ) :=
    mul_pos hangular hfrequency
  constructor
  · intro hcenter
    unfold Complex.logarithmicPhaseFourierStationaryPoint at hcenter
    have hproduct := (lt_div_iff₀ hdenominator).mp hcenter
    have hreorder :
        right * (2 * Real.pi * -(m : ℝ)) =
          -(m : ℝ) * (2 * Real.pi * right) := by
      calc
        right * (2 * Real.pi * -(m : ℝ)) =
            (right * (2 * Real.pi)) * -(m : ℝ) :=
          (mul_assoc _ _ _).symm
        _ = -(m : ℝ) * (right * (2 * Real.pi)) := mul_comm _ _
        _ = -(m : ℝ) * (2 * Real.pi * right) :=
          congrArg (fun value : ℝ => -(m : ℝ) * value)
            (mul_comm _ _)
    have htargetProduct :
        -(m : ℝ) * (2 * Real.pi * right) < ‖t‖ :=
      Eq.subst (motive := fun value : ℝ => value < ‖t‖) hreorder hproduct
    exact (lt_div_iff₀ (mul_pos hangular hright)).mpr htargetProduct
  · intro hfrequencyBound
    unfold Complex.logarithmicPhaseFourierStationaryPoint
    have hproduct :=
      (lt_div_iff₀ (mul_pos hangular hright)).mp hfrequencyBound
    have hreorder :
        -(m : ℝ) * (2 * Real.pi * right) =
          right * (2 * Real.pi * -(m : ℝ)) := by
      calc
        -(m : ℝ) * (2 * Real.pi * right) =
            -(m : ℝ) * (right * (2 * Real.pi)) :=
          congrArg (fun value : ℝ => -(m : ℝ) * value)
            (mul_comm _ _)
        _ = (right * (2 * Real.pi)) * -(m : ℝ) := mul_comm _ _
        _ = right * (2 * Real.pi * -(m : ℝ)) := mul_assoc _ _ _
    have htargetProduct :
        right * (2 * Real.pi * -(m : ℝ)) < ‖t‖ :=
      Eq.subst (motive := fun value : ℝ => value < ‖t‖) hreorder hproduct
    exact (lt_div_iff₀ hdenominator).mpr htargetProduct

theorem Complex.logarithmicPhaseFiniteLeftProtectedBase_le_mode
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftProtectedBase t a ≤ -(m : ℤ) := by
  have hcenter :=
    Complex.logarithmicPhasePoissonLeftInactive_center_lt_fullSupport
      t a b hab m.property
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp m.property).2.1
  have hfull := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hfrequency :
      Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a <
        (-(m : ℤ) : ℝ) := by
    unfold Complex.logarithmicPhaseFiniteLeftFullSupportThreshold
    have hcross := Complex.stationaryPoint_lt_left_iff_frequency_gt
      t m (Real.integerBlockCutoffSupportLeftEndpoint a)
      ht hmNeg hfull
    exact hcross.mp hcenter
  unfold Complex.logarithmicPhaseFiniteLeftProtectedBase
  have hcastNeg : ((-(m : ℤ) : ℤ) : ℝ) = -((m : ℤ) : ℝ) :=
    Int.cast_neg (m : ℤ)
  have hfrequencyCast :
      Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a <
        ((-(m : ℤ) : ℤ) : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a < value)
      hcastNeg.symm hfrequency
  have hfloor :
      ⌊Complex.logarithmicPhaseFiniteLeftFullSupportThreshold t a⌋ <
        -(m : ℤ) :=
    Int.floor_lt.mpr hfrequencyCast
  exact Int.add_one_le_iff.mpr hfloor

theorem Complex.logarithmicPhaseFiniteRight_mode_le_protectedTop
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    (-(m : ℤ)).toNat ≤
      Complex.logarithmicPhaseFiniteRightProtectedTop t b := by
  have hmData :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp m.property
  have hmNeg := hmData.2.1
  have hcenter :=
    Complex.logarithmicPhasePoissonRightInactive_fullSupport_lt_center
      t a b hab m.property
  have hright : 0 < (b : ℝ) + 2 / 3 := by
    have hbCast : ((1 : ℤ) : ℝ) ≤ (b : ℝ) :=
      Int.cast_le.mpr (le_trans ha hab)
    have hcastOne : ((1 : ℤ) : ℝ) = (1 : ℝ) := Int.cast_one
    have hb : (1 : ℝ) ≤ (b : ℝ) :=
      Eq.subst (motive := fun value : ℝ => value ≤ (b : ℝ)) hcastOne hbCast
    have hthird : (0 : ℝ) < 2 / 3 :=
      div_pos zero_lt_two zero_lt_three
    exact lt_of_lt_of_le (add_pos zero_lt_one hthird)
      (add_le_add_right hb _)
  have hcross := Complex.right_lt_stationaryPoint_iff_frequency_lt
    t m ((b : ℝ) + 2 / 3) ht hmNeg hright
  have hfrequency := hcross.mp hcenter
  have hceil : (-(m : ℤ)).toNat + 1 ≤
      ⌈Complex.logarithmicPhaseFiniteRightFullSupportThreshold t b⌉₊ := by
    have hmNatCast : ((-(m : ℤ)).toNat : ℝ) = (-(m : ℤ) : ℝ) := by
      have hmode := Complex.logarithmicPhaseFiniteRightModeNat_real_cast m
      unfold Complex.logarithmicPhaseFiniteRightModeNat at hmode
      exact hmode
    exact Nat.add_one_le_ceil_iff.mpr
      (Eq.subst (motive := fun value : ℝ => value < _)
        hmNatCast.symm hfrequency)
  have htop :=
    Complex.logarithmicPhaseFiniteRightProtectedTop_add_one_eq_ceil
      t ht a b ha hab
  have hsuccessors :
      (-(m : ℤ)).toNat + 1 ≤
        Complex.logarithmicPhaseFiniteRightProtectedTop t b + 1 :=
    Eq.subst (motive := fun value : ℕ => _ ≤ value) htop.symm hceil
  exact Nat.succ_le_succ_iff.mp hsuccessors

theorem Complex.logarithmicPhaseFiniteLeftProtectedIndex_cast
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    (Complex.logarithmicPhaseFiniteLeftProtectedIndex m : ℤ) =
      -(m : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a := by
  unfold Complex.logarithmicPhaseFiniteLeftProtectedIndex
  exact Int.toNat_of_nonneg (sub_nonneg.mpr
    (Complex.logarithmicPhaseFiniteLeftProtectedBase_le_mode
      t ht a b ha hab m))

theorem Complex.logarithmicPhaseFiniteLeftProtectedIndex_injective
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Function.Injective
      (Complex.logarithmicPhaseFiniteLeftProtectedIndex
        (t := t) (a := a) (b := b)) := by
  intro m₁ m₂ hindex
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hindex
  have h₁ := Complex.logarithmicPhaseFiniteLeftProtectedIndex_cast
    t ht a b ha hab m₁
  have h₂ := Complex.logarithmicPhaseFiniteLeftProtectedIndex_cast
    t ht a b ha hab m₂
  have hdifference :
      -(m₁ : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a =
        -(m₂ : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a :=
    Eq.trans h₁.symm (Eq.trans hcast h₂)
  have hadd := congrArg
    (fun value : ℤ =>
      value + Complex.logarithmicPhaseFiniteLeftProtectedBase t a)
    hdifference
  have hcancel₁ :
      (-(m₁ : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a) +
          Complex.logarithmicPhaseFiniteLeftProtectedBase t a = -(m₁ : ℤ) :=
    sub_add_cancel _ _
  have hcancel₂ :
      (-(m₂ : ℤ) - Complex.logarithmicPhaseFiniteLeftProtectedBase t a) +
          Complex.logarithmicPhaseFiniteLeftProtectedBase t a = -(m₂ : ℤ) :=
    sub_add_cancel _ _
  have hnegative : -(m₁ : ℤ) = -(m₂ : ℤ) :=
    Eq.trans hcancel₁.symm (Eq.trans hadd hcancel₂)
  exact Subtype.ext (neg_injective hnegative)

theorem Complex.logarithmicPhaseFiniteLeftProtectedResidual_add_step
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftProtectedResidual t a +
        (2 * Real.pi) *
          (Complex.logarithmicPhaseFiniteLeftProtectedIndex m : ℝ) =
      Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  have hindexInt := Complex.logarithmicPhaseFiniteLeftProtectedIndex_cast
    t ht a b ha hab m
  have hindexReal :
      (Complex.logarithmicPhaseFiniteLeftProtectedIndex m : ℝ) =
        ((-(m : ℤ) -
          Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℤ) : ℝ) :=
    congrArg (fun z : ℤ => (z : ℝ)) hindexInt
  unfold Complex.logarithmicPhaseFiniteLeftProtectedResidual
  unfold Complex.logarithmicPhaseLeftInactiveGap
  have hcastNeg : ((-(m : ℤ) : ℤ) : ℝ) = -((m : ℤ) : ℝ) :=
    Int.cast_neg (m : ℤ)
  have hindexNormalized :
      (Complex.logarithmicPhaseFiniteLeftProtectedIndex m : ℝ) =
        -((m : ℤ) : ℝ) -
          (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) :=
    Eq.trans hindexReal
      (Eq.trans (Int.cast_sub _ _)
        (congrArg
          (fun value : ℝ => value -
            (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ))
          hcastNeg))
  exact Eq.subst
    (motive := fun value : ℝ =>
      2 * Real.pi *
            (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a +
          2 * Real.pi * value =
        2 * Real.pi * (-((m : ℤ) : ℝ)) -
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a)
    hindexNormalized.symm
    (by
      calc
        2 * Real.pi *
              (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) -
            ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a +
            2 * Real.pi *
              (-((m : ℤ) : ℝ) -
                (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)) =
            (2 * Real.pi *
                (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) +
              2 * Real.pi *
                (-((m : ℤ) : ℝ) -
                  (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ))) -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a :=
          sub_add_eq_add_sub _ _ _
        _ = 2 * Real.pi * (-((m : ℤ) : ℝ)) -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a := by
          have hdistribute := mul_sub (2 * Real.pi)
            (-((m : ℤ) : ℝ))
            (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)
          have hcancel :
              2 * Real.pi *
                    (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) +
                  (2 * Real.pi * (-((m : ℤ) : ℝ)) -
                    2 * Real.pi *
                      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)) =
                2 * Real.pi * (-((m : ℤ) : ℝ)) := by
            exact Eq.trans
              (add_comm _ _)
              (sub_add_cancel
                (2 * Real.pi * (-((m : ℤ) : ℝ)))
                (2 * Real.pi *
                  (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ)))
          exact congrArg
            (fun value : ℝ => value -
              ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a)
            (Eq.trans
              (congrArg
                (fun value : ℝ =>
                  2 * Real.pi *
                      (Complex.logarithmicPhaseFiniteLeftProtectedBase t a : ℝ) + value)
                hdistribute)
              hcancel))

theorem Complex.logarithmicPhaseFiniteRightProtectedIndex_add_mode_eq_top
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteRightProtectedIndex m +
        (-(m : ℤ)).toNat =
      Complex.logarithmicPhaseFiniteRightProtectedTop t b := by
  unfold Complex.logarithmicPhaseFiniteRightProtectedIndex
  exact Nat.sub_add_cancel
    (Complex.logarithmicPhaseFiniteRight_mode_le_protectedTop
      t ht a b ha hab m)

theorem Complex.logarithmicPhaseFiniteRightProtectedIndex_injective
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Function.Injective
      (Complex.logarithmicPhaseFiniteRightProtectedIndex
        (t := t) (a := a) (b := b)) := by
  intro m₁ m₂ hindex
  have hmTop := Complex.logarithmicPhaseFiniteRight_mode_le_protectedTop
    t ht a b ha hab m₁
  have hnTop := Complex.logarithmicPhaseFiniteRight_mode_le_protectedTop
    t ht a b ha hab m₂
  unfold Complex.logarithmicPhaseFiniteRightProtectedIndex at hindex
  have hmRecover := Nat.sub_add_cancel hmTop
  have hnRecover := Nat.sub_add_cancel hnTop
  have hmNat : (-(m₁ : ℤ)).toNat = (-(m₂ : ℤ)).toNat := by
    have hsum :
        (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
            (-(m₁ : ℤ)).toNat) + (-(m₁ : ℤ)).toNat =
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
            (-(m₂ : ℤ)).toNat) + (-(m₂ : ℤ)).toNat :=
      hmRecover.trans hnRecover.symm
    have hsameLeft :
        (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
            (-(m₂ : ℤ)).toNat) + (-(m₁ : ℤ)).toNat =
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
            (-(m₂ : ℤ)).toNat) + (-(m₂ : ℤ)).toNat :=
      Eq.subst
        (motive := fun value : ℕ =>
          value + (-(m₁ : ℤ)).toNat =
            (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
              (-(m₂ : ℤ)).toNat) + (-(m₂ : ℤ)).toNat)
        hindex hsum
    exact Nat.add_left_cancel hsameLeft
  have hmCast := Complex.logarithmicPhaseFiniteRightModeNat_cast m₁
  have hnCast := Complex.logarithmicPhaseFiniteRightModeNat_cast m₂
  unfold Complex.logarithmicPhaseFiniteRightModeNat at hmCast hnCast
  have hnegative : -(m₁ : ℤ) = -(m₂ : ℤ) :=
    hmCast.symm.trans
      ((congrArg (fun value : ℕ => (value : ℤ)) hmNat).trans hnCast)
  exact Subtype.ext (neg_injective hnegative)

theorem Complex.logarithmicPhaseFiniteRightProtectedResidual_add_step
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteRightProtectedResidual t b +
        (2 * Real.pi) *
          (Complex.logarithmicPhaseFiniteRightProtectedIndex m : ℝ) =
      Complex.logarithmicPhaseRightInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportRight b) := by
  have hmTop := Complex.logarithmicPhaseFiniteRight_mode_le_protectedTop
    t ht a b ha hab m
  have hcastSub :
      ((Complex.logarithmicPhaseFiniteRightProtectedTop t b -
        (-(m : ℤ)).toNat : ℕ) : ℝ) =
      (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) -
        ((-(m : ℤ)).toNat : ℝ) :=
    Nat.cast_sub hmTop
  have hmode := Complex.logarithmicPhaseFiniteRightModeNat_real_cast m
  unfold Complex.logarithmicPhaseFiniteRightModeNat at hmode
  unfold Complex.logarithmicPhaseFiniteRightProtectedResidual
  unfold Complex.logarithmicPhaseRightInactiveGap
  unfold Complex.logarithmicPhaseFiniteRightProtectedIndex
  calc
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
          2 * Real.pi *
            (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) +
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b -
            (-(m : ℤ)).toNat : ℕ) =
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
        2 * Real.pi *
          (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) +
        2 * Real.pi *
          ((Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ) -
            ((-(m : ℤ)).toNat : ℝ)) := by
      exact congrArg
        (fun value : ℝ =>
          (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
            2 * Real.pi *
              (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) +
            2 * Real.pi * value)
        hcastSub
    _ = ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
          2 * Real.pi * ((-(m : ℤ)).toNat : ℝ) := by
      exact Eq.trans
        (congrArg
          (fun value : ℝ =>
            (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
              2 * Real.pi *
                (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)) + value)
          (mul_sub (2 * Real.pi)
            (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ)
            ((-(m : ℤ)).toNat : ℝ)))
        (sub_add_sub_cancel _
          (2 * Real.pi *
            (Complex.logarithmicPhaseFiniteRightProtectedTop t b : ℝ))
          (2 * Real.pi * ((-(m : ℤ)).toNat : ℝ)))
    _ = ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
          2 * Real.pi * (-((m : ℤ) : ℝ)) :=
      congrArg
        (fun value : ℝ =>
          ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b -
            2 * Real.pi * value)
        hmode

end

end LFunctions
end Boundary

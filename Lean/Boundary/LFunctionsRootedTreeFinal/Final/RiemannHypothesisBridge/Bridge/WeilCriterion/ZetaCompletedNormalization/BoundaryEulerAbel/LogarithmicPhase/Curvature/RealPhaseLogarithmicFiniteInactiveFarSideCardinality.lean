import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarReciprocalArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteRightInactiveReindex

/-!
# Side-specific cardinality of finite far modes

The left family may use the enclosing mode range because its per-mode endpoint
is the lower endpoint.  The right family requires its sharper natural
frequency top.  This owner supplies that asymmetric cardinality closure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteRightModeIndexFin
    {t : ℝ} {a b : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b}) :
    Fin (Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1) :=
  ⟨Complex.logarithmicPhaseFiniteRightModeNat m,
    Nat.lt_succ_of_le
      (Complex.logarithmicPhaseFiniteRightModeNat_le_top
        t ht a b ha hab m)⟩

theorem Complex.logarithmicPhaseFiniteRightModeIndexFin_injective
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Function.Injective
      (Complex.logarithmicPhaseFiniteRightModeIndexFin ht ha hab) := by
  intro m n hfin
  have hnat :
      Complex.logarithmicPhaseFiniteRightModeNat m =
        Complex.logarithmicPhaseFiniteRightModeNat n :=
    congrArg Fin.val hfin
  have hmCast := Complex.logarithmicPhaseFiniteRightModeNat_cast m
  have hnCast := Complex.logarithmicPhaseFiniteRightModeNat_cast n
  have hneg : -(m : ℤ) = -(n : ℤ) :=
    hmCast.symm.trans
      ((congrArg (fun value : ℕ => (value : ℤ)) hnat).trans hnCast)
  exact Subtype.ext (neg_injective hneg)

theorem Complex.logarithmicPhasePoissonRightInactive_card_le_frequencyTop_add_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (Complex.logarithmicPhasePoissonRightInactiveModes t a b).card ≤
      Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 := by
  have hinjective :=
    Complex.logarithmicPhaseFiniteRightModeIndexFin_injective
      t ht a b ha hab
  have hcard := Fintype.card_le_of_injective
    (Complex.logarithmicPhaseFiniteRightModeIndexFin ht ha hab)
    hinjective
  have hcodomain :
      Fintype.card
          (Fin (Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1)) =
        Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 :=
    Fintype.card_fin
      (Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1)
  have hcardRight :
      Fintype.card
          {m : ℤ //
            m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b} ≤
        Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 :=
    Eq.subst
      (motive := fun value : ℕ =>
        Fintype.card
            {m : ℤ //
              m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b} ≤
          value)
      hcodomain
      hcard
  have hdomain :
      Fintype.card
          {m : ℤ //
            m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b} =
        (Complex.logarithmicPhasePoissonRightInactiveModes t a b).card :=
    Fintype.card_coe
      (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
  exact Eq.subst
    (motive := fun value : ℕ =>
      value ≤ Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1)
    hdomain
    hcardRight

theorem Complex.logarithmicPhaseFiniteRightFar_card_le_frequencyTop_add_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteRightFarModes t a b).card ≤
      Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteRightFarModes_card_le_rightInactive
      t a b)
    (Complex.logarithmicPhasePoissonRightInactive_card_le_frequencyTop_add_one
      t ht a b ha hab)

theorem Complex.logarithmicPhaseFiniteRightFrequencyTop_add_one_le_ceil
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ) (hb : 1 ≤ b) :
    Complex.logarithmicPhaseFiniteRightFrequencyTop t b + 1 ≤
      ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ := by
  have hright :
      0 < Complex.logarithmicPhaseQuantitativeSupportRight b :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos b b hb (le_refl b)
  have hdenominator :
      0 < 2 * Real.pi * Complex.logarithmicPhaseQuantitativeSupportRight b :=
    mul_pos Complex.two_mul_pi_pos hright
  have hnorm : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hthreshold :
      0 < Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b := by
    unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
    exact div_pos hnorm hdenominator
  have hceil :
      1 ≤ ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ :=
    (Nat.ceil_pos.mpr hthreshold)
  unfold Complex.logarithmicPhaseFiniteRightFrequencyTop
  exact le_of_eq (Nat.sub_add_cancel hceil)

theorem Complex.logarithmicPhaseFiniteRightFar_card_le_ceil_threshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteRightFarModes t a b).card ≤
      ⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteRightFar_card_le_frequencyTop_add_one
      t ht a b ha hab)
    (Complex.logarithmicPhaseFiniteRightFrequencyTop_add_one_le_ceil
      t ht b (le_trans ha hab))

theorem Real.natCeil_le_add_one
    (x : ℝ) (hx : 0 ≤ x) :
    (⌈x⌉₊ : ℝ) ≤ x + 1 := by
  have hlt := Nat.ceil_lt_add_one hx
  exact le_of_lt hlt

theorem Complex.logarithmicPhaseFiniteRightFrequencyThreshold_nonneg
    (t : ℝ) (b : ℤ) (hb : 1 ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b := by
  unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos b b hb (le_refl b)
  have hdenom := mul_pos Complex.two_mul_pi_pos hright
  exact div_nonneg (norm_nonneg t) hdenom.le

theorem Complex.logarithmicPhaseFiniteRightFar_card_real_le_threshold_add_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b + 1 := by
  have hnat :=
    Complex.logarithmicPhaseFiniteRightFar_card_le_ceil_threshold
      t ht a b ha hab
  have hcast :
      ((Complex.logarithmicPhaseFiniteRightFarModes t a b).card : ℝ) ≤
        (⌈Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b⌉₊ : ℝ) :=
    Nat.cast_le.mpr hnat
  have hb : 1 ≤ b := le_trans ha hab
  exact le_trans hcast
    (Real.natCeil_le_add_one
      (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b)
      (Complex.logarithmicPhaseFiniteRightFrequencyThreshold_nonneg t b hb))

theorem Complex.logarithmicPhaseFiniteLeftFar_card_real_le_modeRangeMajorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hsubset := Finset.Subset.trans
    (Complex.logarithmicPhaseFiniteLeftFarModes_subset_leftInactive t a b)
    (Complex.logarithmicPhasePoissonLeftInactiveModes_subset_inRangeInactive
      t a b)
  have hcardNat := Finset.card_le_card hsubset
  have hcardReal :
      ((Complex.logarithmicPhaseFiniteLeftFarModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) :=
    Nat.cast_le.mpr hcardNat
  exact le_trans hcardReal
    (Complex.logarithmicPhaseInRangeInactive_card_real_le_majorant
      t a b ha)

theorem Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant_nonneg
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 ≤ Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a := by
  unfold Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
  have hzeroOne : (0 : ℤ) ≤ 1 :=
    Int.ofNat_le.mpr (Nat.zero_le 1)
  have haReal : 0 ≤ (a : ℝ) :=
    Int.cast_nonneg.mpr (le_trans hzeroOne ha)
  have hproduct := mul_nonneg haReal
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hquotient := div_nonneg hproduct (norm_nonneg t)
  exact mul_nonneg (Nat.cast_nonneg 2) hquotient

theorem Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant_nonneg
    (t : ℝ) (b : ℤ) (hb : 1 ≤ b) :
    0 ≤ Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b := by
  unfold Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
  have hzeroOne : (0 : ℤ) ≤ 1 :=
    Int.ofNat_le.mpr (Nat.zero_le 1)
  have hbReal : 0 ≤ (b : ℝ) :=
    Int.cast_nonneg.mpr (le_trans hzeroOne hb)
  have hproduct := mul_nonneg hbReal
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hquotient := div_nonneg hproduct (norm_nonneg t)
  exact mul_nonneg (Nat.cast_nonneg 2) hquotient

theorem Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant_le_sideMajorants
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant t a b ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a *
          Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a +
        (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b + 1) *
          Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b := by
  have hleftCard :=
    Complex.logarithmicPhaseFiniteLeftFar_card_real_le_modeRangeMajorant
      t a b ha
  have hrightCard :=
    Complex.logarithmicPhaseFiniteRightFar_card_real_le_threshold_add_one
      t ht a b ha hab
  have hb : 1 ≤ b := le_trans ha hab
  have hleftScale := mul_le_mul_of_nonneg_right hleftCard
    (Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant_nonneg
      t a ha)
  have hrightScale := mul_le_mul_of_nonneg_right hrightCard
    (Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant_nonneg
      t b hb)
  unfold Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant
  exact add_le_add hleftScale hrightScale

theorem Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_sideMajorants
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget t a b ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a *
          Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant t a +
        (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t b + 1) *
          Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant t b := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_cardinalityMajorant
      t ht a b ha hab)
    (Complex.logarithmicPhaseFiniteFarCardinalityReciprocalMajorant_le_sideMajorants
      t ht a b ha hab)

end

end LFunctions
end Boundary

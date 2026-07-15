import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveWindowPartition

/-!
# Cardinality one for the full finite left-inactive family

The Poisson mode range ends at the floor of the negative left-support
frequency.  Left inactivity requires the reflected positive integer frequency
to lie strictly beyond the corresponding real threshold.  Hence at most the
single ceiling integer can occur.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFullLeftFrequencyThreshold
    (t : ℝ) (a : ℤ) : ℝ :=
  ‖t‖ /
    (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)

def Complex.logarithmicPhaseFiniteLeftModeNat
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) : ℕ :=
  Int.toNat (-(m : ℤ))

theorem Complex.logarithmicPhaseFiniteLeftModeNat_cast
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    ((Complex.logarithmicPhaseFiniteLeftModeNat m : ℕ) : ℤ) = -(m : ℤ) := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b (m : ℤ)).mp m.property).2.1
  unfold Complex.logarithmicPhaseFiniteLeftModeNat
  exact Int.toNat_of_nonneg (neg_nonneg.mpr hmNeg.le)

theorem Complex.logarithmicPhaseFiniteLeftModeNat_real_cast
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    (Complex.logarithmicPhaseFiniteLeftModeNat m : ℝ) =
      -((m : ℤ) : ℝ) := by
  have hcast := congrArg (fun value : ℤ => (value : ℝ))
    (Complex.logarithmicPhaseFiniteLeftModeNat_cast m)
  exact hcast.trans (Int.cast_neg (m : ℤ))

theorem Complex.logarithmicPhaseFiniteLeftModeNat_pos
    {t : ℝ} {a b : ℤ}
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    0 < Complex.logarithmicPhaseFiniteLeftModeNat m := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b (m : ℤ)).mp m.property).2.1
  have hcast := Complex.logarithmicPhaseFiniteLeftModeNat_cast m
  exact Int.ofNat_pos.mp
    (Eq.subst (motive := fun value : ℤ => 0 < value)
      hcast.symm (neg_pos.mpr hmNeg))

theorem Complex.logarithmicPhaseFiniteLeftModeNat_gt_fullThreshold
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hab : a ≤ b)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFullLeftFrequencyThreshold t a <
      (Complex.logarithmicPhaseFiniteLeftModeNat m : ℝ) := by
  have hcenter :=
    Complex.logarithmicPhasePoissonLeftInactive_center_lt_fullSupport
      t a b hab m.property
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b (m : ℤ)).mp m.property).2.1
  have hsupportPos :
      0 < Real.integerBlockCutoffSupportLeftEndpoint a := by
    have hcenterPos :=
      Complex.logarithmicPhaseFourierStationaryPoint_pos t
        ht hmNeg
    exact lt_of_lt_of_le hcenterPos hcenter.le
  have hangular := Complex.logarithmicPhaseAngular_eq_norm_div_center
    t ht hmNeg
  have hnormPos : 0 < ‖t‖ :=
    Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hmNeg
  have hfrequencyAtCenter :
      ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a <
        ‖t‖ / Complex.logarithmicPhaseFourierStationaryPoint t (m : ℤ) :=
    div_lt_div_of_pos_left hnormPos hcenterPos hcenter
  have hfrequency :
      ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a <
        2 * Real.pi * (-((m : ℤ) : ℝ)) := by
    exact Eq.subst
      (motive := fun value : ℝ =>
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a < value)
      hangular.symm hfrequencyAtCenter
  have hfrequencyReordered :
      ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a <
        (-((m : ℤ) : ℝ)) * (2 * Real.pi) :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a < value)
      (mul_comm (2 * Real.pi) (-((m : ℤ) : ℝ)))
      hfrequency
  have hdivide :
      (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi) <
        -((m : ℤ) : ℝ) :=
    (div_lt_iff₀ Complex.two_mul_pi_pos).mpr hfrequencyReordered
  have hthresholdIdentity :
      ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) =
        (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi) :=
    div_mul_eq_div_div_swap ‖t‖ (2 * Real.pi)
      (Real.integerBlockCutoffSupportLeftEndpoint a)
  unfold Complex.logarithmicPhaseFullLeftFrequencyThreshold
  exact Eq.subst
    (motive := fun value : ℝ =>
      value < Complex.logarithmicPhaseFiniteLeftModeNat m)
    hthresholdIdentity.symm
    (Eq.subst
      (motive := fun value : ℝ =>
        (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
            (2 * Real.pi) < value)
      (Complex.logarithmicPhaseFiniteLeftModeNat_real_cast m).symm
      hdivide)

theorem Complex.logarithmicPhaseFiniteLeftModeNat_le_ceilThreshold
    (t : ℝ) (a b : ℤ)
    (m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b}) :
    Complex.logarithmicPhaseFiniteLeftModeNat m ≤
      ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉₊ := by
  have hinactive :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b (m : ℤ)).mp m.property).1
  have hmodeRange := Finset.mem_sdiff.mp hinactive |>.1
  have hrange :=
    (Complex.mem_logarithmicPhasePoissonModeRange_iff
      t a (m : ℤ)).mp hmodeRange
  have hfloor := hrange.1
  have hnegFloor := neg_le_neg hfloor
  have hceilIdentity :
      -Complex.logarithmicPhasePoissonModeRangeLower t a =
        ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉ := by
    have hthresholdIdentity :
        ‖t‖ /
            (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) =
          (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
            (2 * Real.pi) :=
      div_mul_eq_div_div_swap ‖t‖ (2 * Real.pi)
        (Real.integerBlockCutoffSupportLeftEndpoint a)
    have hnegativeNumerator :
        (-‖t‖) / Real.integerBlockCutoffSupportLeftEndpoint a =
          -(‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) :=
      neg_div (Real.integerBlockCutoffSupportLeftEndpoint a) ‖t‖
    have hnegativeQuotient :
        ((-‖t‖) / Real.integerBlockCutoffSupportLeftEndpoint a) /
            (2 * Real.pi) =
          -(Complex.logarithmicPhaseFullLeftFrequencyThreshold t a) := by
      unfold Complex.logarithmicPhaseFullLeftFrequencyThreshold
      exact Eq.trans
        (congrArg (fun value : ℝ => value / (2 * Real.pi))
          hnegativeNumerator)
        (Eq.trans
          (neg_div
            (2 * Real.pi)
            (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a))
          (congrArg Neg.neg hthresholdIdentity.symm))
    have hfloorNeg :
        ⌊-(Complex.logarithmicPhaseFullLeftFrequencyThreshold t a)⌋ =
          -⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉ :=
      Int.floor_neg
    unfold Complex.logarithmicPhasePoissonModeRangeLower
    exact Eq.trans
      (congrArg Neg.neg (congrArg Int.floor hnegativeQuotient))
      (Eq.trans
        (congrArg Neg.neg hfloorNeg)
        (neg_neg
          ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉))
  have hmodeCast := Complex.logarithmicPhaseFiniteLeftModeNat_cast m
  have hint :
      (Complex.logarithmicPhaseFiniteLeftModeNat m : ℤ) ≤
        ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉ := by
    exact Eq.subst (motive := fun value : ℤ => value ≤ _)
      hmodeCast.symm
      (Eq.subst (motive := fun value : ℤ => -(m : ℤ) ≤ value)
        hceilIdentity hnegFloor)
  have htoNat := Int.toNat_le_toNat hint
  have hleftToNat :=
    Int.toNat_natCast (Complex.logarithmicPhaseFiniteLeftModeNat m)
  have hrightToNat :=
    Int.ceil_toNat (Complex.logarithmicPhaseFullLeftFrequencyThreshold t a)
  have hleftTarget :
      Complex.logarithmicPhaseFiniteLeftModeNat m ≤
        Int.toNat
          ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉ :=
    Eq.subst
      (motive := fun value : ℕ =>
        value ≤ Int.toNat
          ⌈Complex.logarithmicPhaseFullLeftFrequencyThreshold t a⌉)
      hleftToNat htoNat
  exact Eq.subst
    (motive := fun value : ℕ =>
      Complex.logarithmicPhaseFiniteLeftModeNat m ≤ value)
    hrightToNat hleftTarget

theorem Nat.gt_real_and_le_ceil_unique
    {x : ℝ} {p q : ℕ}
    (hp : x < (p : ℝ)) (hpceil : p ≤ ⌈x⌉₊)
    (hq : x < (q : ℝ)) (hqceil : q ≤ ⌈x⌉₊) :
    p = q := by
  have hceilLeP := Nat.ceil_le.mpr hp.le
  have hceilLeQ := Nat.ceil_le.mpr hq.le
  exact le_antisymm
    (le_trans hpceil hceilLeQ)
    (le_trans hqceil hceilLeP)

theorem Complex.logarithmicPhasePoissonLeftInactive_card_le_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hab : a ≤ b) :
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b).card ≤ 1 := by
  exact Finset.card_le_one.mpr (fun m hm n hn => by
    let msub : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b} := ⟨m, hm⟩
    let nsub : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b} := ⟨n, hn⟩
    have hnat := Nat.gt_real_and_le_ceil_unique
      (Complex.logarithmicPhaseFiniteLeftModeNat_gt_fullThreshold
        t ht a b hab msub)
      (Complex.logarithmicPhaseFiniteLeftModeNat_le_ceilThreshold
        t a b msub)
      (Complex.logarithmicPhaseFiniteLeftModeNat_gt_fullThreshold
        t ht a b hab nsub)
      (Complex.logarithmicPhaseFiniteLeftModeNat_le_ceilThreshold
        t a b nsub)
    have hcast := congrArg (fun value : ℕ => (value : ℤ)) hnat
    have hmCast := Complex.logarithmicPhaseFiniteLeftModeNat_cast msub
    have hnCast := Complex.logarithmicPhaseFiniteLeftModeNat_cast nsub
    exact neg_injective (hmCast.symm.trans (hcast.trans hnCast)))

theorem Complex.logarithmicPhaseFiniteLeftFar_card_le_one
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hab : a ≤ b) :
    (Complex.logarithmicPhaseFiniteLeftFarModes t a b).card ≤ 1 := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteLeftFarModes_card_le_leftInactive t a b)
    (Complex.logarithmicPhasePoissonLeftInactive_card_le_one t ht a b hab)

end

end LFunctions
end Boundary

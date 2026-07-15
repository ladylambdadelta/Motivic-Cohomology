import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarEndpointCancellation

/-!
# Regime closure for finite far reciprocal packets

The right family closes directly from its side threshold.  The left family is
split at `‖t‖ = 3a`: balanced-radius cancellation controls the high-frequency
regime, while the first negative angular frequency controls the low-frequency
regime.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftFarLowFrequency
    (t : ℝ) (a : ℕ) : Prop :=
  ‖t‖ ≤ 3 * (a : ℝ)

def Complex.logarithmicPhaseFiniteLeftFarHighFrequency
    (t : ℝ) (a : ℕ) : Prop :=
  3 * (a : ℝ) ≤ ‖t‖

theorem Complex.logarithmicPhaseFiniteLeftFar_frequency_regime
    (t : ℝ) (a : ℕ) :
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a ∨
      Complex.logarithmicPhaseFiniteLeftFarHighFrequency t a := by
  exact le_total ‖t‖ (3 * (a : ℝ))

theorem Real.add_one_mul
    (x y : ℝ) :
    (x + 1) * y = x * y + y := by
  exact Eq.trans (add_mul x 1 y)
    (congrArg (fun value : ℝ => x * y + value) (one_mul y))

theorem Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_threshold_add_one_mul
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t (b : ℤ) + 1) *
        Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
          t (b : ℤ) := by
  have ha : 1 ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hcard :=
    Complex.logarithmicPhaseFiniteRightFar_card_real_le_threshold_add_one
      t ht (a : ℤ) (b : ℤ) ha hab
  have hperNonneg :=
    Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant_nonneg
      t (b : ℤ) (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_one_le_b hgeometry))
  have hscaled := mul_le_mul_of_nonneg_right hcard hperNonneg
  exact le_trans
    (Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_card_mul
      t ht (a : ℤ) (b : ℤ) ha hab)
    hscaled

theorem Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale_of_nonempty
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hne : (Complex.logarithmicPhaseFiniteRightFarModes
      t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (7 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  obtain ⟨m, hm⟩ := hne
  have hbase :=
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_threshold_add_one_mul
      t ht a b hgeometry
  have hexpand := Real.add_one_mul
    (Complex.logarithmicPhaseFiniteRightFrequencyThreshold t (b : ℤ))
    (Complex.logarithmicPhaseFiniteRightFarPerModeReciprocalMajorant
      t (b : ℤ))
  have hmain := Complex.rightThreshold_mul_endpointScale_le_two_scale
    t ht b
  have hremainder :=
    Complex.logarithmicPhaseFiniteRightFar_perModeMajorant_le_one_third_scale
      ht hm
  have hsum := add_le_add hmain hremainder
  have hnormalize :
      2 * Complex.logarithmicPhaseBProcessScale t +
          (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t =
        (7 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans
      (add_mul 2 (1 / 3 : ℝ)
        (Complex.logarithmicPhaseBProcessScale t)).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        (show (2 : ℝ) + 1 / 3 = 7 / 3 from by
          have hthree : (3 : ℝ) ≠ 0 :=
            ne_of_gt (show (0 : ℝ) < 3 from zero_lt_three)
          apply (eq_div_iff hthree).mpr
          have htwoThree : (2 : ℝ) * 3 = 6 :=
            (Nat.cast_mul 2 3).symm.trans
              (congrArg Nat.cast (show 2 * 3 = 6 from rfl))
          have honeThird : (1 / 3 : ℝ) * 3 = 1 :=
            div_mul_cancel₀ 1 hthree
          have hsixOne : (6 : ℝ) + 1 = 7 := by
            have h6 : ((6 : ℕ) : ℝ) = (6 : ℝ) := rfl
            have h1 : ((1 : ℕ) : ℝ) = (1 : ℝ) := Nat.cast_one
            have hadd := @Nat.cast_add ℝ _ 6 1
            have hcast : ((6 + 1 : ℕ) : ℝ) = (7 : ℝ) :=
              congrArg Nat.cast (show (6 : ℕ) + 1 = 7 from rfl)
            exact Eq.trans
              (Eq.trans
                (congrArg₂ (· + ·) h6.symm h1.symm)
                hadd.symm)
              hcast
          calc
            (2 + 1 / 3 : ℝ) * 3 = 2 * 3 + (1 / 3 : ℝ) * 3 :=
              add_mul 2 (1 / 3) 3
            _ = 6 + 1 := congrArg₂ (· + ·) htwoThree honeThird
            _ = 7 := hsixOne))
  exact le_trans hbase
    (Eq.subst (motive := fun value : ℝ => value ≤ _)
      hexpand.symm (le_trans hsum (le_of_eq hnormalize)))

theorem Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (7 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  match Finset.eq_empty_or_nonempty
      (Complex.logarithmicPhaseFiniteRightFarModes
        t (a : ℤ) (b : ℤ)) with
  | Or.inl hempty =>
      have hzero :=
        Complex.logarithmicPhaseFiniteRightFarBudget_eq_zero_of_empty
          t (a : ℤ) (b : ℤ) hempty
      have hrightNonneg :
          0 ≤ (7 / 3 : ℝ) *
            Complex.logarithmicPhaseBProcessScale t :=
        mul_nonneg (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 3))
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst (motive := fun value : ℝ => value ≤ _) hzero.symm
        hrightNonneg
  | Or.inr hne =>
      exact
        Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale_of_nonempty
          t ht a b hgeometry hne

theorem Complex.logarithmicPhaseFiniteLeftFarHighFrequency_endpointScale_le_two_thirds_scale
    {t : ℝ} {a : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hhigh : Complex.logarithmicPhaseFiniteLeftFarHighFrequency t a) :
    Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
        t (a : ℤ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteLeftFarHighFrequency at hhigh
  unfold Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdivide :
      (a : ℝ) / ‖t‖ ≤ 1 / 3 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have hhigh' : (a : ℝ) * 3 ≤ ‖t‖ :=
      Eq.mp
        (congrArg (fun value : ℝ => value ≤ ‖t‖)
          (mul_comm (3 : ℝ) (a : ℝ))) hhigh
    have hthird : (a : ℝ) ≤ ‖t‖ / 3 :=
      (le_div_iff₀ hthreePos).mpr hhigh'
    have hcomm : ‖t‖ / 3 = (1 / 3 : ℝ) * ‖t‖ := by
      calc
        ‖t‖ / 3 = ‖t‖ * (3 : ℝ)⁻¹ := div_eq_mul_inv ‖t‖ 3
        _ = (3 : ℝ)⁻¹ * ‖t‖ := mul_comm _ _
        _ = (1 / 3 : ℝ) * ‖t‖ :=
          congrArg (fun value : ℝ => value * ‖t‖)
            (Eq.trans (one_mul ((3 : ℝ)⁻¹)).symm
              (div_eq_mul_inv (1 : ℝ) 3).symm)
    have hthird' : (a : ℝ) ≤ (1 / 3 : ℝ) * ‖t‖ :=
      Eq.subst hcomm hthird
    exact (div_le_iff₀ hnormPos).mpr hthird'
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hmul := mul_le_mul_of_nonneg_right hdivide hscaleNonneg
  have htwice := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg 2)
  have hleftNormalize :
      2 * ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) =
        2 * (((a : ℝ) / ‖t‖) *
          Complex.logarithmicPhaseBProcessScale t) := by
    have hbase :
        (a : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
          ((a : ℝ) / ‖t‖) * Complex.logarithmicPhaseBProcessScale t := by
      calc
        (a : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
            (a : ℝ) *
              (Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
          mul_div_assoc (a : ℝ)
            (Complex.logarithmicPhaseBProcessScale t) ‖t‖
        _ = (a : ℝ) *
              (Complex.logarithmicPhaseBProcessScale t * ‖t‖⁻¹) :=
          congrArg (fun value : ℝ => (a : ℝ) * value)
            (div_eq_mul_inv
              (Complex.logarithmicPhaseBProcessScale t) ‖t‖)
        _ = ((a : ℝ) * ‖t‖⁻¹) *
              Complex.logarithmicPhaseBProcessScale t := by
          calc
            (a : ℝ) *
                (Complex.logarithmicPhaseBProcessScale t * ‖t‖⁻¹) =
              ((a : ℝ) * Complex.logarithmicPhaseBProcessScale t) *
                ‖t‖⁻¹ := (mul_assoc _ _ _).symm
            _ = (Complex.logarithmicPhaseBProcessScale t * (a : ℝ)) *
                ‖t‖⁻¹ := congrArg (fun value : ℝ => value * ‖t‖⁻¹)
                  (mul_comm (a : ℝ) (Complex.logarithmicPhaseBProcessScale t))
            _ = (Complex.logarithmicPhaseBProcessScale t) *
                ((a : ℝ) * ‖t‖⁻¹) := mul_assoc _ _ _
            _ = ((a : ℝ) * ‖t‖⁻¹) *
                Complex.logarithmicPhaseBProcessScale t := mul_comm _ _
        _ = ((a : ℝ) / ‖t‖) *
              Complex.logarithmicPhaseBProcessScale t := by
          exact congrArg (fun value : ℝ => value *
              Complex.logarithmicPhaseBProcessScale t)
            (div_eq_mul_inv (a : ℝ) ‖t‖).symm
    exact congrArg (fun value : ℝ => 2 * value) hbase
  have hrightNormalize :
      2 * ((1 / 3 : ℝ) *
          Complex.logarithmicPhaseBProcessScale t) =
        (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 2 (1 / 3 : ℝ) _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        (show (2 : ℝ) * (1 / 3) = 2 / 3 from
          (mul_one_div (2 : ℝ) (3 : ℝ))))
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hleftNormalize.symm
    (le_trans htwice (le_of_eq hrightNormalize))

theorem Complex.logarithmicPhaseFiniteLeftFarHighFrequency_sideMajorant_le_twenty_two_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hhigh : Complex.logarithmicPhaseFiniteLeftFarHighFrequency t a) :
    Complex.logarithmicPhaseModeRangeCardMajorant t (a : ℤ) *
        Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
          t (a : ℤ) ≤
      (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseModeRangeCardMajorant
  have hexpand := add_mul 2
    (‖t‖ /
      (2 * Real.pi *
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)))
    (Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant
      t (a : ℤ))
  have hper :=
    Complex.logarithmicPhaseFiniteLeftFarHighFrequency_endpointScale_le_two_thirds_scale
      ht hhigh
  have htwo := mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg 2)
  have hmain :=
    Complex.leftFrequencyTerm_mul_endpointScale_le_six_scale
      ht hgeometry
  have hsum := add_le_add htwo hmain
  have hnormalize :
      2 * ((2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t) +
          6 * Complex.logarithmicPhaseBProcessScale t =
        (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    have hfirst :
        2 * ((2 / 3 : ℝ) *
            Complex.logarithmicPhaseBProcessScale t) =
          (4 / 3 : ℝ) *
            Complex.logarithmicPhaseBProcessScale t := by
      exact Eq.trans (mul_assoc 2 (2 / 3 : ℝ) _).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          (show (2 : ℝ) * (2 / 3) = 4 / 3 from by
            have hthree : (3 : ℝ) ≠ 0 :=
              ne_of_gt (show (0 : ℝ) < 3 from zero_lt_three)
            apply (eq_div_iff hthree).mpr
            have htwoTwo : (2 : ℝ) * 2 = 4 :=
              (Nat.cast_mul 2 2).symm.trans
                (congrArg Nat.cast (show 2 * 2 = 4 from rfl))
            calc
              2 * (2 / 3) * 3 = 2 * ((2 / 3 : ℝ) * 3) :=
                mul_assoc 2 (2 / 3) 3
              _ = 2 * 2 := congrArg (fun z : ℝ => 2 * z)
                (div_mul_cancel₀ 2 hthree)
              _ = 4 := htwoTwo))
    have hsecond :
        (4 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t +
            6 * Complex.logarithmicPhaseBProcessScale t =
          (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
      Eq.trans
        (add_mul (4 / 3 : ℝ) 6
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          (show (4 / 3 : ℝ) + 6 = 22 / 3 from by
            have hthree : (3 : ℝ) ≠ 0 :=
              ne_of_gt (show (0 : ℝ) < 3 from zero_lt_three)
            apply (eq_div_iff hthree).mpr
            have hfourSix : (4 : ℝ) + 6 * 3 = 22 := by
              have hsixThree : (6 : ℝ) * 3 = 18 :=
                (Nat.cast_mul 6 3).symm.trans
                  (congrArg Nat.cast (show 6 * 3 = 18 from rfl))
              exact Eq.trans
                (congrArg (fun z : ℝ => (4 : ℝ) + z) hsixThree)
                ((Nat.cast_add 4 18).symm.trans
                  (congrArg Nat.cast (show 4 + 18 = 22 from rfl)))
            calc
              (4 / 3 + 6 : ℝ) * 3 = (4 / 3 : ℝ) * 3 + 6 * 3 :=
                add_mul (4 / 3) 6 3
              _ = 4 + 6 * 3 := congrArg₂ (· + ·)
                (div_mul_cancel₀ 4 hthree) (Eq.refl ((6 : ℝ) * 3))
              _ = 22 := hfourSix))
    calc
      2 * ((2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t) +
          6 * Complex.logarithmicPhaseBProcessScale t =
        (4 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t +
          6 * Complex.logarithmicPhaseBProcessScale t :=
            congrArg
              (fun value : ℝ =>
                value + 6 * Complex.logarithmicPhaseBProcessScale t)
              hfirst
      _ = (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := hsecond
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hexpand.symm (le_trans hsum (le_of_eq hnormalize))

end

end LFunctions
end Boundary

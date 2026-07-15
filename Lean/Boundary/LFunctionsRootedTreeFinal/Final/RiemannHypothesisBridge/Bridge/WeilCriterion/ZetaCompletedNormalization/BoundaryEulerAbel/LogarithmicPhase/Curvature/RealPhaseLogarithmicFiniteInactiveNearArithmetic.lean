import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearQuantitativeBudget

/-!
# Arithmetic closure for near finite inactive packets

The only nonzero clipped tail points inward.  Mode-dependent endpoint bounds
control it by `7/6*S` on the left and `1/3*S` on the right.  Together with the
exact crossing and radius estimates, cardinality one gives a total near budget
of at most `7/2*S`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem near_real_nat_add
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem near_real_nat_mul
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem near_two_sixths_eq_one_third :
    (2 / 6 : ℝ) = 1 / 3 := by
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hleft : (2 : ℝ) * 3 = 6 := near_real_nat_mul 2 3 6 rfl
  have hright : (1 : ℝ) * 6 = 6 := one_mul (6 : ℝ)
  exact (div_eq_div_iff hsixNe hthreeNe).mpr
    (Eq.trans hleft hright.symm)

private theorem near_two_mul_seven_twelfths_eq_seven_sixths :
    (2 : ℝ) * (7 / 12) = 7 / 6 := by
  have htwelveNe : (12 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 11))
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have hfourteen : (2 : ℝ) * 7 = 14 := near_real_nat_mul 2 7 14 rfl
  have hleft : (14 : ℝ) * 6 = 84 := near_real_nat_mul 14 6 84 rfl
  have hright : (7 : ℝ) * 12 = 84 := near_real_nat_mul 7 12 84 rfl
  have hfraction : (14 / 12 : ℝ) = 7 / 6 :=
    (div_eq_div_iff htwelveNe hsixNe).mpr (Eq.trans hleft hright.symm)
  exact Eq.trans (mul_div_assoc 2 7 12).symm
    (Eq.trans (congrArg (fun numerator : ℝ => numerator / 12) hfourteen)
      hfraction)

private theorem near_left_packet_coefficients_eq_thirteen_sixths :
    (2 / 3 : ℝ) + 0 + 1 / 3 + 7 / 6 = 13 / 6 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have htwoThirds : (2 / 3 : ℝ) = 4 / 6 := by
    have hleft : (2 : ℝ) * 6 = 12 := near_real_nat_mul 2 6 12 rfl
    have hright : (4 : ℝ) * 3 = 12 := near_real_nat_mul 4 3 12 rfl
    exact (div_eq_div_iff hthreeNe hsixNe).mpr
      (Eq.trans hleft hright.symm)
  have honeThird : (1 / 3 : ℝ) = 2 / 6 := by
    have hleft : (1 : ℝ) * 6 = 6 := one_mul (6 : ℝ)
    have hright : (2 : ℝ) * 3 = 6 := near_real_nat_mul 2 3 6 rfl
    exact (div_eq_div_iff hthreeNe hsixNe).mpr
      (Eq.trans hleft hright.symm)
  have hfourAddTwo : (4 : ℝ) + 2 = 6 := near_real_nat_add 4 2 6 rfl
  have hsixAddSeven : (6 : ℝ) + 7 = 13 := near_real_nat_add 6 7 13 rfl
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 1 / 3 + 7 / 6)
      (add_zero (2 / 3 : ℝ)))
    (Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          htwoThirds honeThird)
        rfl)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 7 / 6)
          (Eq.trans (div_add_div_same 4 2 6)
            (congrArg (fun numerator : ℝ => numerator / 6) hfourAddTwo)))
        (Eq.trans (div_add_div_same 6 7 6)
          (congrArg (fun numerator : ℝ => numerator / 6) hsixAddSeven))))

private theorem near_right_packet_coefficients_eq_four_thirds :
    (2 / 3 : ℝ) + 1 / 3 + 1 / 3 + 0 = 4 / 3 := by
  have htwoAddOneCast := near_real_nat_add 2 1 3 rfl
  have htwoAddOne : (2 : ℝ) + 1 = 3 :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (Nat.cast_eq_ofNat (n := 2)).symm
        (Nat.cast_one (R := ℝ)).symm)
      (Eq.trans htwoAddOneCast (Nat.cast_eq_ofNat (n := 3)))
  have hthreeAddOneCast := near_real_nat_add 3 1 4 rfl
  have hthreeAddOne : (3 : ℝ) + 1 = 4 :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (Nat.cast_eq_ofNat (n := 3)).symm
        (Nat.cast_one (R := ℝ)).symm)
      (Eq.trans hthreeAddOneCast (Nat.cast_eq_ofNat (n := 4)))
  exact Eq.trans (add_zero _)
    (Eq.trans
      (congrArg (fun value : ℝ => value + 1 / 3)
        (Eq.trans (div_add_div_same 2 1 3)
          (congrArg (fun numerator : ℝ => numerator / 3) htwoAddOne)))
      (Eq.trans (div_add_div_same 3 1 3)
        (congrArg (fun numerator : ℝ => numerator / 3) hthreeAddOne)))

private theorem near_thirteen_sixths_add_four_thirds_eq_seven_halves :
    (13 / 6 : ℝ) + 4 / 3 = 7 / 2 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have htwoNe : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have hfourThirds : (4 / 3 : ℝ) = 8 / 6 := by
    have hleft : (4 : ℝ) * 6 = 24 := near_real_nat_mul 4 6 24 rfl
    have hright : (8 : ℝ) * 3 = 24 := near_real_nat_mul 8 3 24 rfl
    exact (div_eq_div_iff hthreeNe hsixNe).mpr
      (Eq.trans hleft hright.symm)
  have hthirteenAddEight : (13 : ℝ) + 8 = 21 :=
    near_real_nat_add 13 8 21 rfl
  have hleft : (21 : ℝ) * 2 = 42 := near_real_nat_mul 21 2 42 rfl
  have hright : (7 : ℝ) * 6 = 42 := near_real_nat_mul 7 6 42 rfl
  have htwentyOneSixths : (21 / 6 : ℝ) = 7 / 2 :=
    (div_eq_div_iff hsixNe htwoNe).mpr (Eq.trans hleft hright.symm)
  exact Eq.trans (congrArg (fun value : ℝ => 13 / 6 + value) hfourThirds)
    (Eq.trans (div_add_div_same 13 8 6)
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 6) hthirteenAddEight)
        htwentyOneSixths))

theorem Complex.logarithmicPhaseFiniteLeftNear_clippedRightTail_le_seven_sixths_scale
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedRightTailBudget
        t (b : ℤ) m ≤
      (7 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hblockRight :=
        Complex.logarithmicPhaseFiniteLeftNear_blockRight_le_seven_twelfths_norm
          ht hgeometry hm
      have hwindowRight := le_trans hraw hblockRight
      have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
      have hmul := mul_le_mul_of_nonneg_right hwindowRight hscaleNonneg
      have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
      have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
      have hscaled := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg 2)
      have hnormalize :
          2 * (((7 / 12 : ℝ) * ‖t‖) *
              Complex.logarithmicPhaseBProcessScale t / ‖t‖) =
            (7 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
        have hcancel :
            (((7 / 12 : ℝ) * ‖t‖) *
                Complex.logarithmicPhaseBProcessScale t) / ‖t‖ =
              (7 / 12 : ℝ) *
                Complex.logarithmicPhaseBProcessScale t := by
          calc
            (((7 / 12 : ℝ) * ‖t‖) *
                Complex.logarithmicPhaseBProcessScale t) / ‖t‖ =
                ((7 / 12 : ℝ) *
                  Complex.logarithmicPhaseBProcessScale t) * ‖t‖ / ‖t‖ := by
              exact congrArg (fun value : ℝ => value / ‖t‖)
                (Eq.trans (mul_assoc (7 / 12) ‖t‖ _)
                  (Eq.trans
                    (congrArg (fun value : ℝ => (7 / 12) * value)
                      (mul_comm ‖t‖ _))
                    (mul_assoc (7 / 12) _ ‖t‖).symm))
            _ = (7 / 12 : ℝ) *
                Complex.logarithmicPhaseBProcessScale t :=
              mul_div_cancel_right₀ _ (ne_of_gt hnormPos)
        exact Eq.trans
          (congrArg (fun value : ℝ => 2 * value) hcancel)
          (Eq.trans (mul_assoc 2 (7 / 12) _).symm
            (congrArg
              (fun coefficient : ℝ => coefficient *
                Complex.logarithmicPhaseBProcessScale t)
              near_two_mul_seven_twelfths_eq_seven_sixths))
      have hmNeg :=
        (((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
          t (a : ℤ) (b : ℤ) m).mp
          ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
            t (a : ℤ) (b : ℤ) m).mp hm).1).2.1)
      have htailRaw :
          Complex.logarithmicPhaseBProcessRightTailBudget t m ≤
            (7 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        Eq.subst
          (motive := fun value : ℝ => value ≤ _)
          (Complex.logarithmicPhaseBProcessRightTailBudget_eq
            t ht hmNeg).symm
          (le_trans hscaled (le_of_eq hnormalize))
      exact Eq.subst
        (motive := fun value : ℝ => value ≤ _)
        (if_pos hraw).symm htailRaw
  | Or.inr hzero =>
      have hnonneg :
          0 ≤ (7 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        mul_nonneg
          (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 6))
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst
        (motive := fun value : ℝ => value ≤ _)
        (if_neg hzero).symm hnonneg

theorem Complex.logarithmicPhaseFiniteRightNear_clippedLeftTail_le_one_third_scale
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget
        t (a : ℤ) m ≤
      (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hraw =>
      have hnear :=
        ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
          t (a : ℤ) (b : ℤ) m).mp hm).2
      have hbase :=
        Complex.logarithmicPhaseFiniteRightNear_blockRight_le_norm_div_six hm
      have hwindow := le_trans hnear hbase
      have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
      have hmul := mul_le_mul_of_nonneg_right hwindow hscaleNonneg
      have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
      have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
      have hscaled := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg 2)
      have hnormalize :
          2 * ((‖t‖ / 6) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) =
            (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
        have hcancel :
            ((‖t‖ / 6) * Complex.logarithmicPhaseBProcessScale t) / ‖t‖ =
              Complex.logarithmicPhaseBProcessScale t / 6 := by
          have hreorder :
              (‖t‖ / 6) * Complex.logarithmicPhaseBProcessScale t =
                (Complex.logarithmicPhaseBProcessScale t / 6) * ‖t‖ := by
            calc
              (‖t‖ / 6) * Complex.logarithmicPhaseBProcessScale t =
                  (‖t‖ * (6 : ℝ)⁻¹) *
                    Complex.logarithmicPhaseBProcessScale t :=
                congrArg
                  (fun value : ℝ =>
                    value * Complex.logarithmicPhaseBProcessScale t)
                  (div_eq_mul_inv ‖t‖ 6)
              _ = ‖t‖ * ((6 : ℝ)⁻¹ *
                    Complex.logarithmicPhaseBProcessScale t) :=
                mul_assoc ‖t‖ (6 : ℝ)⁻¹ _
              _ = ‖t‖ * (Complex.logarithmicPhaseBProcessScale t *
                    (6 : ℝ)⁻¹) := by
                exact congrArg (fun value : ℝ => ‖t‖ * value)
                  (mul_comm (6 : ℝ)⁻¹
                    (Complex.logarithmicPhaseBProcessScale t))
              _ = (‖t‖ * Complex.logarithmicPhaseBProcessScale t) *
                    (6 : ℝ)⁻¹ :=
                (mul_assoc ‖t‖
                  (Complex.logarithmicPhaseBProcessScale t) (6 : ℝ)⁻¹).symm
              _ = (Complex.logarithmicPhaseBProcessScale t * ‖t‖) *
                    (6 : ℝ)⁻¹ := by
                exact congrArg (fun value : ℝ => value * (6 : ℝ)⁻¹)
                  (mul_comm ‖t‖
                    (Complex.logarithmicPhaseBProcessScale t))
              _ = Complex.logarithmicPhaseBProcessScale t *
                    (‖t‖ * (6 : ℝ)⁻¹) :=
                mul_assoc
                  (Complex.logarithmicPhaseBProcessScale t) ‖t‖ (6 : ℝ)⁻¹
              _ = Complex.logarithmicPhaseBProcessScale t *
                    ((6 : ℝ)⁻¹ * ‖t‖) := by
                exact congrArg
                  (fun value : ℝ =>
                    Complex.logarithmicPhaseBProcessScale t * value)
                  (mul_comm ‖t‖ (6 : ℝ)⁻¹)
              _ = (Complex.logarithmicPhaseBProcessScale t *
                    (6 : ℝ)⁻¹) * ‖t‖ :=
                (mul_assoc
                  (Complex.logarithmicPhaseBProcessScale t) (6 : ℝ)⁻¹ ‖t‖).symm
              _ = (Complex.logarithmicPhaseBProcessScale t / 6) * ‖t‖ :=
                congrArg (fun value : ℝ => value * ‖t‖)
                  (div_eq_mul_inv
                    (Complex.logarithmicPhaseBProcessScale t) 6).symm
          calc
            ((‖t‖ / 6) * Complex.logarithmicPhaseBProcessScale t) / ‖t‖ =
                (Complex.logarithmicPhaseBProcessScale t / 6) * ‖t‖ / ‖t‖ := by
              exact congrArg (fun value : ℝ => value / ‖t‖) hreorder
            _ = Complex.logarithmicPhaseBProcessScale t / 6 :=
              mul_div_cancel_right₀ _ (ne_of_gt hnormPos)
        have htwoScaleDivSix :
            2 * (Complex.logarithmicPhaseBProcessScale t / 6) =
              (2 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
          calc
            (2 : ℝ) * (Complex.logarithmicPhaseBProcessScale t / 6) =
                2 * (Complex.logarithmicPhaseBProcessScale t * (6 : ℝ)⁻¹) :=
              congrArg (fun value : ℝ => 2 * value)
                (div_eq_mul_inv
                  (Complex.logarithmicPhaseBProcessScale t) 6)
            _ = 2 * ((6 : ℝ)⁻¹ *
                Complex.logarithmicPhaseBProcessScale t) := by
              exact congrArg (fun value : ℝ => 2 * value)
                (mul_comm
                  (Complex.logarithmicPhaseBProcessScale t) (6 : ℝ)⁻¹)
            _ = (2 * (6 : ℝ)⁻¹) *
                Complex.logarithmicPhaseBProcessScale t :=
              (mul_assoc 2 (6 : ℝ)⁻¹ _).symm
            _ = (2 / 6 : ℝ) *
                Complex.logarithmicPhaseBProcessScale t :=
              congrArg
                (fun coefficient : ℝ =>
                  coefficient * Complex.logarithmicPhaseBProcessScale t)
                (div_eq_mul_inv 2 6).symm
        exact Eq.trans (congrArg (fun value : ℝ => 2 * value) hcancel)
          (Eq.trans htwoScaleDivSix
            (congrArg
              (fun coefficient : ℝ => coefficient *
                Complex.logarithmicPhaseBProcessScale t)
              near_two_sixths_eq_one_third))
      have hmNeg :=
        (((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
          t (a : ℤ) (b : ℤ) m).mp
          ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
            t (a : ℤ) (b : ℤ) m).mp hm).1).2.1)
      have htailRaw :
          Complex.logarithmicPhaseBProcessLeftTailBudget t m ≤
            (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        Eq.subst
          (motive := fun value : ℝ => value ≤ _)
          (Complex.logarithmicPhaseBProcessLeftTailBudget_eq
            t ht hmNeg).symm
          (le_trans hscaled (le_of_eq hnormalize))
      exact Eq.subst
        (motive := fun value : ℝ => value ≤ _)
        (if_pos hraw).symm htailRaw
  | Or.inr hzero =>
      have hnonneg :
          0 ≤ (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
        mul_nonneg
          (div_nonneg zero_le_one (Nat.cast_nonneg 3))
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact Eq.subst
        (motive := fun value : ℝ => value ≤ _)
        (if_neg hzero).symm hnonneg

theorem Complex.logarithmicPhaseFiniteLeftNearPacketBudget_le_thirteen_sixths_scale
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m ≤
      (13 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hzero :=
    Complex.logarithmicPhaseFiniteLeftNear_clippedLeftTail_eq_zero ht hm
  have hcrossing := Complex.logarithmicPhaseFiniteNear_crossing_le_two_thirds_scale t
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp
      ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
        t (a : ℤ) (b : ℤ) m).mp hm).1).2.1
  have hradius :=
    Complex.logarithmicPhaseFiniteNear_two_radius_le_one_third_scale
      (t := t) hmNeg
  have htail :=
    Complex.logarithmicPhaseFiniteLeftNear_clippedRightTail_le_seven_sixths_scale
      ht ht_nonneg hgeometry hm
  unfold Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
  have hzeroBound :
      Complex.logarithmicPhaseBProcessClippedLeftTailBudget
          t (a : ℤ) m ≤
        0 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.subst (motive := fun value : ℝ => _ ≤ value)
      (zero_mul (Complex.logarithmicPhaseBProcessScale t)).symm
      (le_of_eq hzero)
  have hsum := add_le_add
    (add_le_add (add_le_add hcrossing hzeroBound) hradius) htail
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (Real.four_weighted_terms_eq_sum_coeff_mul
          (2 / 3) 0 (1 / 3) (7 / 6)
          (Complex.logarithmicPhaseBProcessScale t))
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          near_left_packet_coefficients_eq_thirteen_sixths)))

theorem Complex.logarithmicPhaseFiniteRightNearPacketBudget_le_four_thirds_scale
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m ≤
      (4 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hcrossing :=
    Complex.logarithmicPhaseFiniteNear_crossing_le_two_thirds_scale t
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp
      ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
        t (a : ℤ) (b : ℤ) m).mp hm).1).2.1
  have hleft :=
    Complex.logarithmicPhaseFiniteRightNear_clippedLeftTail_le_one_third_scale
      ht hgeometry hm
  have hradius :=
    Complex.logarithmicPhaseFiniteNear_two_radius_le_one_third_scale
      (t := t) hmNeg
  have hzero :=
    Complex.logarithmicPhaseFiniteRightNear_clippedRightTail_eq_zero ht hm
  have hzeroBound :
      Complex.logarithmicPhaseBProcessClippedRightTailBudget
          t (b : ℤ) m ≤
        0 * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.subst (motive := fun value : ℝ => _ ≤ value)
      (zero_mul (Complex.logarithmicPhaseBProcessScale t)).symm
      (le_of_eq hzero)
  unfold Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
  have hsum := add_le_add
    (add_le_add (add_le_add hcrossing hleft) hradius) hzeroBound
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (Real.four_weighted_terms_eq_sum_coeff_mul
          (2 / 3) (1 / 3) (1 / 3) 0
          (Complex.logarithmicPhaseBProcessScale t))
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          near_right_packet_coefficients_eq_four_thirds)))

theorem Finset.sum_le_one_mul_of_card_le_one
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) (C : ℝ)
    (hcard : s.card ≤ 1)
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, f x ≤ C) :
    ∑ x ∈ s, f x ≤ C := by
  have hsum := Finset.sum_le_card_mul_of_pointwise_le s f C hpoint
  have hcastRaw : (s.card : ℝ) ≤ ((1 : ℕ) : ℝ) := Nat.cast_le.mpr hcard
  have hcast : (s.card : ℝ) ≤ 1 :=
    Eq.subst (motive := fun value : ℝ => (s.card : ℝ) ≤ value)
      (Nat.cast_one (R := ℝ)) hcastRaw
  have hmul : (s.card : ℝ) * C ≤ 1 * C :=
    mul_le_mul_of_nonneg_right hcast hC
  exact le_trans hsum
    (le_trans hmul (le_of_eq (one_mul C)))

theorem Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_le_thirteen_sixths_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) ≤
      (13 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget
  have hcard :=
    Complex.logarithmicPhaseFiniteLeftNear_card_le_one ht hgeometry
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hmajorantNonneg :
      0 ≤ (13 / 6 : ℝ) *
        Complex.logarithmicPhaseBProcessScale t :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg 13) (Nat.cast_nonneg 6))
      hscaleNonneg
  exact Finset.sum_le_one_mul_of_card_le_one
    (Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ))
    (fun m =>
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m)
    ((13 / 6 : ℝ) * Complex.logarithmicPhaseBProcessScale t)
    hcard hmajorantNonneg
    (fun m hm =>
      Complex.logarithmicPhaseFiniteLeftNearPacketBudget_le_thirteen_sixths_scale
        ht ht_nonneg hgeometry hm)

theorem Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_le_four_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) ≤
      (4 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget
  have hcard :=
    Complex.logarithmicPhaseFiniteRightNear_card_le_one ht hgeometry
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hmajorantNonneg :
      0 ≤ (4 / 3 : ℝ) *
        Complex.logarithmicPhaseBProcessScale t :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3))
      hscaleNonneg
  exact Finset.sum_le_one_mul_of_card_le_one
    (Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ))
    (fun m =>
      Complex.logarithmicPhaseFiniteInactiveNearQuantitativePacketBudget
        t (a : ℤ) (b : ℤ) m)
    ((4 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t)
    hcard hmajorantNonneg
    (fun m hm =>
      Complex.logarithmicPhaseFiniteRightNearPacketBudget_le_four_thirds_scale
        ht hgeometry hm)

theorem Complex.logarithmicPhaseFiniteNearQuantitativeBudget_le_seven_halves_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteNearQuantitativeBudget
        t (a : ℤ) (b : ℤ) ≤
      (7 / 2 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftNearQuantitativeBudget_le_thirteen_sixths_scale
      ht ht_nonneg hgeometry
  have hright :=
    Complex.logarithmicPhaseFiniteRightNearQuantitativeBudget_le_four_thirds_scale
      ht hgeometry
  unfold Complex.logarithmicPhaseFiniteNearQuantitativeBudget
  have hsum := add_le_add hleft hright
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (add_mul (13 / 6 : ℝ) (4 / 3)
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          near_thirteen_sixths_add_four_thirds_eq_seven_halves)))

end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarLowFrequency

/-!
# Numerical closure of all finite inactive packets

This owner merges the low/high left regimes, adds the right reciprocal family,
controls the far crossing cardinality, and exports a single square-root-scale
majorant for the sharp finite inactive budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

theorem Real.div_eq_div_mul_div_of_pos
    (norm : ℝ) {middle endpoint : ℝ}
    (hmiddle : 0 < middle) :
    norm / endpoint =
      (middle / endpoint) * (norm / middle) := by
  have hcombine := div_mul_div_comm middle endpoint norm middle
  have hcommute : middle * norm = norm * middle := mul_comm middle norm
  have hcancel : (norm * middle) / (endpoint * middle) =
      norm / endpoint :=
    mul_div_mul_right norm endpoint (ne_of_gt hmiddle)
  exact (Eq.trans
      (Eq.trans hcombine
        (congrArg
          (fun numerator : ℝ => numerator / (endpoint * middle))
          hcommute))
      hcancel).symm

theorem Real.crossing_coefficient_normalization
    (scale : ℝ) :
    (2 / 3 : ℝ) * (2 * scale + 3 * (2 * scale)) =
      (16 / 3 : ℝ) * scale := by
  have hthreeMulTwo : (3 : ℝ) * 2 = 6 :=
    realOfNat_mul_eq_of_nat_eq 3 2 6 rfl
  have htwoAddSix : (2 : ℝ) + 6 = 8 :=
    realOfNat_add_eq_of_nat_eq 2 6 8 rfl
  have heightMulTwo : (8 : ℝ) * 2 = 16 :=
    realOfNat_mul_eq_of_nat_eq 8 2 16 rfl
  have hcoefficient : (2 / 3 : ℝ) * 8 = 16 / 3 :=
    Eq.trans (mul_comm (2 / 3 : ℝ) 8)
      (Eq.trans (mul_div_assoc' 8 2 3)
        (congrArg (fun numerator : ℝ => numerator / 3)
          heightMulTwo))
  have hinner : 2 * scale + 3 * (2 * scale) = 8 * scale := by
    have hsecond : 3 * (2 * scale) = 6 * scale := by
      exact Eq.trans (mul_assoc 3 2 scale).symm
        (congrArg (fun coefficient : ℝ => coefficient * scale)
          hthreeMulTwo)
    exact Eq.trans
      (congrArg (fun value : ℝ => 2 * scale + value) hsecond)
      (Eq.trans (add_mul 2 6 scale).symm
        (congrArg (fun coefficient : ℝ => coefficient * scale)
          htwoAddSix))
  exact Eq.trans (congrArg (fun value : ℝ => (2 / 3 : ℝ) * value) hinner)
    (Eq.trans (mul_assoc (2 / 3 : ℝ) 8 scale).symm
      (congrArg (fun coefficient : ℝ => coefficient * scale)
        hcoefficient))

theorem Complex.logarithmicPhaseFiniteLeftFarHighFrequency_budget_le_twenty_two_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hhigh : Complex.logarithmicPhaseFiniteLeftFarHighFrequency t a) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have ha : 1 ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hcard :=
    Complex.logarithmicPhaseFiniteLeftFar_card_real_le_modeRangeMajorant
      t (a : ℤ) (b : ℤ) ha
  have hperNonneg :=
    Complex.logarithmicPhaseFiniteLeftFarPerModeReciprocalMajorant_nonneg
      t (a : ℤ) ha
  have hscaled := mul_le_mul_of_nonneg_right hcard hperNonneg
  have hsum :=
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_card_mul
      t ht (a : ℤ) (b : ℤ) ha
  exact le_trans hsum
    (le_trans hscaled
      (Complex.logarithmicPhaseFiniteLeftFarHighFrequency_sideMajorant_le_twenty_two_thirds_scale
        ht hgeometry hhigh))

theorem Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_twenty_two_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (22 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have haTwo :=
    Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  match Complex.logarithmicPhaseFiniteLeftFar_frequency_regime t a with
  | Or.inl hlow =>
      have hsmall :=
        Complex.logarithmicPhaseFiniteLeftFarLowFrequency_budget_le_two_thirds_scale
          (b := b) haTwo hlow
      have hcoeff : (2 / 3 : ℝ) ≤ 22 / 3 := by
        have hnumeratorNat : (2 : ℕ) ≤ 22 :=
          Eq.subst (motive := fun value : ℕ => 2 ≤ value)
            (show 2 + 20 = 22 from rfl)
            (Nat.le_add_right 2 20)
        have hnumerator : (2 : ℝ) ≤ 22 := Nat.cast_le.mpr hnumeratorNat
        exact div_le_div_of_nonneg_right hnumerator
          (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3)
      have hscale := mul_le_mul_of_nonneg_right hcoeff
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      exact le_trans hsmall hscale
  | Or.inr hhigh =>
      exact
        Complex.logarithmicPhaseFiniteLeftFarHighFrequency_budget_le_twenty_two_thirds_scale
          ht hgeometry hhigh

theorem Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_twenty_nine_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (29 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_twenty_two_thirds_scale
      t ht a b hgeometry
  have hright :=
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale
      t ht a b hgeometry
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  have hsum := add_le_add hleft hright
  have hcoefficient : (22 / 3 : ℝ) + 7 / 3 = 29 / 3 :=
    Eq.trans (div_add_div_same 22 7 3)
      (congrArg (fun numerator : ℝ => numerator / 3)
        (realOfNat_add_eq_of_nat_eq 22 7 29 rfl))
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (add_mul (22 / 3 : ℝ) (7 / 3)
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          hcoefficient)))

theorem Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_twenty_nine_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (29 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
  exact
    Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_twenty_nine_thirds_scale
      t ht a b hgeometry

theorem Real.longGeometry_norm_div_a_le_two_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (a : ℝ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hab : (b : ℝ) ≤ 2 * (a : ℝ) := by
    have hcomparable :=
      Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry
    have hcast : ((b + 1 : ℕ) : ℝ) ≤ ((2 * a : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcomparable
    have hb : (b : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr (Nat.le_succ b)
    exact le_trans hb
      (Eq.subst (Nat.cast_mul 2 a) hcast)
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hbPos := Real.logarithmicPhaseLongBranchGeometry_b_pos_real hgeometry
  have hratio : (b : ℝ) / (a : ℝ) ≤ 2 :=
    (div_le_iff₀ haPos).mpr hab
  have hnormB :
      ‖t‖ / (b : ℝ) ≤
        Complex.logarithmicPhaseBProcessScale t := by
    unfold Complex.logarithmicPhaseBProcessScale
    exact
      Real.logarithmicPhaseLongBranchGeometry_norm_div_b_le_sqrt_one_add
        ht hgeometry
  have hfactor :
      ‖t‖ / (a : ℝ) =
        ((b : ℝ) / (a : ℝ)) * (‖t‖ / (b : ℝ)) := by
    exact Real.div_eq_div_mul_div_of_pos ‖t‖ hbPos
  have hnormDivBNonneg : 0 ≤ ‖t‖ / (b : ℝ) :=
    div_nonneg (norm_nonneg t) hbPos.le
  have hfirst := mul_le_mul hratio hnormB
    hnormDivBNonneg (show (0 : ℝ) ≤ 2 from Nat.cast_nonneg 2)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hfactor.symm hfirst

theorem Real.longGeometry_norm_div_b_le_two_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ / (b : ℝ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hbase :
      ‖t‖ / (b : ℝ) ≤
        Complex.logarithmicPhaseBProcessScale t := by
    unfold Complex.logarithmicPhaseBProcessScale
    exact
      Real.logarithmicPhaseLongBranchGeometry_norm_div_b_le_sqrt_one_add
        ht hgeometry
  have honeTwo : (1 : ℝ) ≤ 2 :=
    one_le_two
  have hscaled := mul_le_mul_of_nonneg_right honeTwo
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hscale :
      Complex.logarithmicPhaseBProcessScale t ≤
        2 * Complex.logarithmicPhaseBProcessScale t := by
    calc
      Complex.logarithmicPhaseBProcessScale t =
          1 * Complex.logarithmicPhaseBProcessScale t :=
        (one_mul _).symm
      _ ≤ 2 * Complex.logarithmicPhaseBProcessScale t := hscaled
  exact le_trans hbase hscale

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_sixteen_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (16 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have ha : 1 ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hcross :=
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_two_thirds_explicitFrequencyLength
      t (a : ℤ) (b : ℤ) ha hab
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_three_norm_div_a hgeometry
  have hnormA := Real.longGeometry_norm_div_a_le_two_scale ht hgeometry
  have hfrequencyScale := le_trans hfrequency
    (mul_le_mul_of_nonneg_left hnormA
      (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3))
  have honeScale := Complex.logarithmicPhaseBProcessScale_one_le t
  have htwoScale := mul_le_mul_of_nonneg_left honeScale
    (show (0 : ℝ) ≤ 2 from Nat.cast_nonneg 2)
  have hinside := add_le_add htwoScale hfrequencyScale
  have hscaled := mul_le_mul_of_nonneg_left hinside
    (div_nonneg (show (0 : ℝ) ≤ 2 from Nat.cast_nonneg 2)
      (show (0 : ℝ) ≤ 3 from Nat.cast_nonneg 3))
  have hnormalize :
      (2 / 3 : ℝ) *
          (2 * Complex.logarithmicPhaseBProcessScale t +
            3 * (2 * Complex.logarithmicPhaseBProcessScale t)) =
        (16 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Real.crossing_coefficient_normalization
      (Complex.logarithmicPhaseBProcessScale t)
  have hinner :
      2 * (1 : ℝ) + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) =
        2 + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) := by
    exact congrArg (fun value : ℝ => value + ‖t‖ /
      (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)))
      (mul_one 2)
  have hscaled' := Eq.subst
    (motive := fun value : ℝ => (2 / 3 : ℝ) * value ≤ _)
    hinner hscaled
  exact le_trans hcross
    (le_trans hscaled' (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget_le_sixteen_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (16 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
  exact
    Complex.logarithmicPhaseFiniteFarCrossingBudget_le_sixteen_thirds_scale
      t ht a b hgeometry

theorem Real.three_component_scale_coefficients_eq_thirty_seven_halves
    (scale : ℝ) :
    (7 / 2 : ℝ) * scale +
        (16 / 3 : ℝ) * scale +
          (29 / 3 : ℝ) * scale =
      (37 / 2 : ℝ) * scale := by
  have hthreeNonzero : (3 : ℝ) ≠ 0 := ne_of_gt zero_lt_three
  have htwoNonzero : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
  have hsixteenAddTwentyNine : (16 : ℝ) + 29 = 45 :=
    realOfNat_add_eq_of_nat_eq 16 29 45 rfl
  have hfortyFive : (45 / 3 : ℝ) = 15 :=
    (div_eq_iff hthreeNonzero).mpr
      (realOfNat_mul_eq_of_nat_eq 15 3 45 rfl).symm
  have hthirds : (16 / 3 : ℝ) + 29 / 3 = 15 :=
    Eq.trans (div_add_div_same 16 29 3)
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 3)
          hsixteenAddTwentyNine)
        hfortyFive)
  have hfifteenMulTwo : (15 : ℝ) * 2 = 30 :=
    realOfNat_mul_eq_of_nat_eq 15 2 30 rfl
  have hsevenAddThirty : (7 : ℝ) + 30 = 37 :=
    realOfNat_add_eq_of_nat_eq 7 30 37 rfl
  have hsevenHalvesAddFifteen : (7 / 2 : ℝ) + 15 = 37 / 2 :=
    Eq.trans (div_add' 7 15 2 htwoNonzero)
      (Eq.trans
        (congrArg (fun numerator : ℝ => (7 + numerator) / 2)
          hfifteenMulTwo)
        (congrArg (fun numerator : ℝ => numerator / 2)
          hsevenAddThirty))
  have hcoefficient :
      (7 / 2 : ℝ) + 16 / 3 + 29 / 3 = 37 / 2 :=
    Eq.trans (add_assoc (7 / 2 : ℝ) (16 / 3) (29 / 3))
      (Eq.trans
        (congrArg (fun value : ℝ => (7 / 2 : ℝ) + value) hthirds)
        hsevenHalvesAddFifteen)
  exact Eq.trans
    (Eq.trans
      (congrArg
        (fun value : ℝ => value + (29 / 3 : ℝ) * scale)
        (add_mul (7 / 2 : ℝ) (16 / 3) scale).symm)
      (add_mul ((7 / 2 : ℝ) + 16 / 3) (29 / 3) scale).symm)
    (congrArg (fun coefficient : ℝ => coefficient * scale)
      hcoefficient)

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_thirty_seven_halves_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      (37 / 2 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hstationary :=
    Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget_le_seven_halves_scale
      ht ht_nonneg hgeometry
  have hcrossing :=
    Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget_le_sixteen_thirds_scale
      t ht a b hgeometry
  have hreciprocal :=
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_twenty_nine_thirds_scale
      t ht a b hgeometry
  have hsum := add_le_add (add_le_add hstationary hcrossing) hreciprocal
  have hparts :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_eq_three_parts
      t (a : ℤ) (b : ℤ)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hparts.symm
    (le_trans hsum
      (le_of_eq
        (Real.three_component_scale_coefficients_eq_thirty_seven_halves
          (Complex.logarithmicPhaseBProcessScale t))))

end

end LFunctions
end Boundary

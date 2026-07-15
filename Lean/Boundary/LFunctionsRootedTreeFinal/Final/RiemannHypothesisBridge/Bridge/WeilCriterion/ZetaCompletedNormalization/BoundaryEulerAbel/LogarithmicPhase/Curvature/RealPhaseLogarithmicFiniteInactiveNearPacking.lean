import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveHybridBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointSidePacking

/-!
# Packing geometry for near finite inactive modes

Window intersection gives explicit center collars immediately outside the full
cutoff support.  These collars are transported to the positive frequency
coordinate `-m`, preparing cardinality-one estimates for each side.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseFiniteLeftNearCenterLower
    (t : ℝ) (a : ℤ) : ℝ :=
  (a : ℝ) * Complex.logarithmicPhaseBProcessScale t /
    (Complex.logarithmicPhaseBProcessScale t + 1)

def Complex.logarithmicPhaseFiniteRightNearCenterUpper
    (t : ℝ) (b : ℤ) : ℝ :=
  (b : ℝ) * Complex.logarithmicPhaseBProcessScale t /
    (Complex.logarithmicPhaseBProcessScale t - 1)

theorem Complex.logarithmicPhaseFiniteLeftNear_centerLower_le_center
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (ha : 1 ≤ a) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    Complex.logarithmicPhaseFiniteLeftNearCenterLower t a ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hdata :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      t a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hdata.1).2.1
  let S := Complex.logarithmicPhaseBProcessScale t
  let c := Complex.logarithmicPhaseFourierStationaryPoint t m
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have haddPos := add_pos hscalePos zero_lt_one
  have hcenterPos := Complex.logarithmicPhaseFourierStationaryPoint_pos
    t ht hmNeg
  have hwindow : (a : ℝ) ≤ c + c / S := by
    unfold Complex.logarithmicPhaseBProcessWindowRight at hdata
    unfold Complex.logarithmicPhaseBProcessRadius at hdata
    exact hdata.2
  have hscaled := mul_le_mul_of_nonneg_right hwindow hscalePos.le
  have hnormalizeLeft :
      (a : ℝ) * S ≤ c * (S + 1) := by
    have hright : (c + c / S) * S = c * (S + 1) := by
      have hcancel : (c / S) * S = c :=
        div_mul_cancel₀ c (ne_of_gt hscalePos)
      exact Eq.trans (add_mul c (c / S) S)
        (Eq.trans
          (congrArg (fun value : ℝ => c * S + value) hcancel)
          (Eq.trans
            (congrArg (fun value : ℝ => c * S + value)
              (mul_one c).symm)
            (mul_add c S 1).symm))
    exact Eq.subst (motive := fun value : ℝ => (a : ℝ) * S ≤ value)
      hright hscaled
  unfold Complex.logarithmicPhaseFiniteLeftNearCenterLower
  exact (div_le_iff₀ haddPos).mpr hnormalizeLeft

theorem Complex.logarithmicPhaseFiniteLeftNear_center_lt_fullLeft
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Real.integerBlockCutoffSupportLeftEndpoint a := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      t a b m).mp hm
  exact Complex.logarithmicPhasePoissonLeftInactive_center_lt_fullSupport
    t a b hab hbase.1

theorem Complex.logarithmicPhaseFiniteRightNear_fullRight_lt_center
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    (b : ℝ) + 2 / 3 <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      t a b m).mp hm
  exact Complex.logarithmicPhasePoissonRightInactive_fullSupport_lt_center
    t a b hab hbase.1

theorem Complex.logarithmicPhaseFiniteRightNear_center_le_centerUpper
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ) (hb : 1 ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      Complex.logarithmicPhaseFiniteRightNearCenterUpper t b := by
  have hdata :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      t a b m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hdata.1).2.1
  let S := Complex.logarithmicPhaseBProcessScale t
  let c := Complex.logarithmicPhaseFourierStationaryPoint t m
  have hsubPos := Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hcenterPos := Complex.logarithmicPhaseFourierStationaryPoint_pos
    t ht hmNeg
  have hwindow : c - c / S ≤ (b : ℝ) := by
    unfold Complex.logarithmicPhaseBProcessWindowLeft at hdata
    unfold Complex.logarithmicPhaseBProcessRadius at hdata
    exact hdata.2
  have hscaled := mul_le_mul_of_nonneg_right hwindow hscalePos.le
  have hnormalize : c * (S - 1) ≤ (b : ℝ) * S := by
    have hleft : (c - c / S) * S = c * (S - 1) := by
      have hcancel : (c / S) * S = c :=
        div_mul_cancel₀ c (ne_of_gt hscalePos)
      exact Eq.trans (sub_mul c (c / S) S)
        (Eq.trans
          (congrArg (fun value : ℝ => c * S - value) hcancel)
          (Eq.trans
            (congrArg (fun value : ℝ => c * S - value)
              (mul_one c).symm)
            (mul_sub c S 1).symm))
    exact Eq.subst (motive := fun value : ℝ => value ≤ (b : ℝ) * S)
      hleft hscaled
  unfold Complex.logarithmicPhaseFiniteRightNearCenterUpper
  exact (le_div_iff₀ hsubPos).mpr hnormalize

theorem Complex.logarithmicPhaseFiniteLeftNearCenterLower_pos
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    0 < Complex.logarithmicPhaseFiniteLeftNearCenterLower t a := by
  unfold Complex.logarithmicPhaseFiniteLeftNearCenterLower
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  exact div_pos (mul_pos haPos hscalePos) (add_pos hscalePos zero_lt_one)

theorem Complex.logarithmicPhaseFiniteRightNearCenterUpper_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) (b : ℤ) (hb : 1 ≤ b) :
    0 < Complex.logarithmicPhaseFiniteRightNearCenterUpper t b := by
  unfold Complex.logarithmicPhaseFiniteRightNearCenterUpper
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  exact div_pos (mul_pos hbPos hscalePos)
    (Complex.logarithmicPhaseBProcessScale_sub_one_pos t ht)

theorem Complex.logarithmicPhaseFiniteLeftNear_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes t a b) :
    ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) <
        -(m : ℝ) ∧
      -(m : ℝ) ≤
        ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseFiniteLeftNearCenterLower t a) := by
  have hcenterLower :=
    Complex.logarithmicPhaseFiniteLeftNear_centerLower_le_center
      t ht a b ha hm
  have hcenterFull :=
    Complex.logarithmicPhaseFiniteLeftNear_center_lt_fullLeft
      t a b hab hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff t a b m).mp
      ((Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
        t a b m).mp hm).1).2.1
  have hweak := Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
    t ht hmNeg
    (Complex.logarithmicPhaseFiniteLeftNearCenterLower_pos t a ha)
    hcenterLower hcenterFull.le
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hmNeg
  have hstrictCoordinate :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_strictAnti
      t ht hcenterPos hcenterFull
  have hmode :=
    Complex.logarithmicPhase_negativeModeCast_eq_centerFrequencyCoordinate
      t ht hmNeg
  have hstrictMode :
      Complex.logarithmicPhaseCenterFrequencyCoordinate t
          (Real.integerBlockCutoffSupportLeftEndpoint a) <
        -(m : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Complex.logarithmicPhaseCenterFrequencyCoordinate t
            (Real.integerBlockCutoffSupportLeftEndpoint a) < value)
      hmode.symm hstrictCoordinate
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate at hstrictMode hweak
  exact And.intro hstrictMode hweak.2

theorem Complex.logarithmicPhaseFiniteRightNear_negModeCast_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes t a b) :
    ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseFiniteRightNearCenterUpper t b) ≤
        -(m : ℝ) ∧
      -(m : ℝ) <
        ‖t‖ / (2 * Real.pi * ((b : ℝ) + 2 / 3)) := by
  have hb : 1 ≤ b := le_trans ha hab
  have hfullCenter :=
    Complex.logarithmicPhaseFiniteRightNear_fullRight_lt_center
      t a b hab hm
  have hcenterUpper :=
    Complex.logarithmicPhaseFiniteRightNear_center_le_centerUpper
      t ht a b hb hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff t a b m).mp
      ((Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
        t a b m).mp hm).1).2.1
  have hfullPos : 0 < (b : ℝ) + 2 / 3 :=
    add_pos
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb))
      (div_pos
        (Nat.cast_pos.mpr (Nat.succ_pos 1))
        (Nat.cast_pos.mpr (Nat.succ_pos 2)))
  have hfrequency := Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
    t ht hmNeg (add_pos
      (Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb))
      (div_pos
        (Nat.cast_pos.mpr (Nat.succ_pos 1))
        (Nat.cast_pos.mpr (Nat.succ_pos 2))))
    hfullCenter.le hcenterUpper
  have hstrictCoordinate :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_strictAnti
      t ht hfullPos hfullCenter
  have hmode :=
    Complex.logarithmicPhase_negativeModeCast_eq_centerFrequencyCoordinate
      t ht hmNeg
  have hstrictMode :
      -(m : ℝ) <
        Complex.logarithmicPhaseCenterFrequencyCoordinate t
          ((b : ℝ) + 2 / 3) :=
    Eq.subst
      (motive := fun value : ℝ =>
        value < Complex.logarithmicPhaseCenterFrequencyCoordinate t
          ((b : ℝ) + 2 / 3))
      hmode.symm hstrictCoordinate
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate at hfrequency hstrictMode
  exact And.intro hfrequency.1 hstrictMode

end

end LFunctions
end Boundary

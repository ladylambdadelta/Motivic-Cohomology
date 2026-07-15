import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointCardinalityAssembly

/-!
# Balanced-window geometry at the packet endpoints

Endpoint stationary centers lie in the fixed cutoff collars.  Long-branch
geometry makes the balanced radius strictly larger than the collar width
`2/3`.  Consequently even a stationary center outside the principal interval
has a balanced window which overlaps that interval.  This removes the false
singularity produced by estimating an almost-stationary outside packet as a
wholly nonstationary packet.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.two_thirds_pos :
    (0 : ℝ) < 2 / 3 := by
  exact div_pos
    (Nat.cast_pos.mpr (Nat.succ_pos 1))
    (Nat.cast_pos.mpr (Nat.succ_pos 2))

theorem Real.a_sub_two_thirds_add_two_thirds
    (a : ℝ) :
    a - 2 / 3 + 2 / 3 = a := by
  exact sub_add_cancel a (2 / 3)

theorem Real.b_add_two_thirds_sub_two_thirds
    (b : ℝ) :
    b + 2 / 3 - 2 / 3 = b := by
  exact add_sub_cancel_right b (2 / 3)

theorem Complex.logarithmicPhaseBProcessEndpointMode_center_lower
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (a : ℝ) - 2 / 3 ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t (a : ℤ) (b : ℤ) hm
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hactive
  exact hdata.2.2.1

theorem Complex.logarithmicPhaseBProcessEndpointMode_center_upper
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      (b : ℝ) + 2 / 3 := by
  have hactive :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_mem_active
      t (a : ℤ) (b : ℤ) hm
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hactive
  exact hdata.2.2.2

theorem Complex.logarithmicPhaseBProcessEndpointMode_negative_nat
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    m < 0 :=
  Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
    t (a : ℤ) (b : ℤ) hm

theorem Real.two_thirds_mul_scale_lt_two_thirds_mul_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t <
      (2 / 3 : ℝ) * (a : ℝ) := by
  exact mul_lt_mul_of_pos_left
    (Real.longGeometry_scale_lt_a hgeometry)
    Real.two_thirds_pos

theorem Complex.logarithmicPhaseBProcessEndpointMode_scaled_margin_lt_center
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hscaleA :=
    Real.two_thirds_mul_scale_lt_two_thirds_mul_a hgeometry
  have htwoA :
      (2 / 3 : ℝ) * (a : ℝ) ≤ (a : ℝ) - 2 / 3 :=
    Real.two_thirds_mul_a_le_a_sub_two_thirds
      (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hcenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_center_lower hm
  exact lt_of_lt_of_le hscaleA (le_trans htwoA hcenter)

theorem Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (2 / 3 : ℝ) < Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessRadius
  exact (lt_div_iff₀
    (Complex.logarithmicPhaseBProcessScale_pos t)).mpr
      (Complex.logarithmicPhaseBProcessEndpointMode_scaled_margin_lt_center
        hgeometry hm)

theorem Complex.logarithmicPhaseBProcessEndpointMode_radius_pos
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    0 < Complex.logarithmicPhaseBProcessRadius t m := by
  exact Complex.logarithmicPhaseBProcessRadius_pos t ht
    (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)

theorem Complex.logarithmicPhaseBProcessEndpointMode_leftSupport_lt_windowRight
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (a : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hcenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_center_lower hm
  have hradius :=
    Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
      hgeometry hm
  have hadd :
      (a : ℝ) - 2 / 3 + 2 / 3 <
        Complex.logarithmicPhaseFourierStationaryPoint t m +
          Complex.logarithmicPhaseBProcessRadius t m :=
    add_lt_add_of_le_of_lt hcenter hradius
  unfold Complex.logarithmicPhaseBProcessWindowRight
  exact Eq.subst
    (motive := fun value : ℝ =>
      value < Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhaseBProcessRadius t m)
    (Real.a_sub_two_thirds_add_two_thirds (a : ℝ))
    hadd

theorem Complex.logarithmicPhaseBProcessEndpointMode_windowLeft_lt_rightSupport
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m < (b : ℝ) := by
  have hcenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_center_upper hm
  have hradius :=
    Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
      hgeometry hm
  have hsub :
      Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhaseBProcessRadius t m <
        ((b : ℝ) + 2 / 3) - 2 / 3 := by
    have hnegativeRadius :
        -Complex.logarithmicPhaseBProcessRadius t m < -(2 / 3 : ℝ) :=
      neg_lt_neg hradius
    have hadd := add_lt_add_of_le_of_lt hcenter hnegativeRadius
    have hleft :
        Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhaseBProcessRadius t m =
          Complex.logarithmicPhaseFourierStationaryPoint t m +
            -Complex.logarithmicPhaseBProcessRadius t m :=
      sub_eq_add_neg _ _
    have hright :
        ((b : ℝ) + 2 / 3) - 2 / 3 =
          ((b : ℝ) + 2 / 3) + -(2 / 3 : ℝ) :=
      sub_eq_add_neg _ _
    exact (lt_of_eq_of_lt hleft hadd).trans_eq hright.symm
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  exact Eq.subst
    (motive := fun value : ℝ =>
      Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhaseBProcessRadius t m < value)
    (Real.b_add_two_thirds_sub_two_thirds (b : ℝ))
    hsub

theorem Complex.logarithmicPhaseBProcessEndpointMode_clippedWindow_order
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    max (a : ℝ) (Complex.logarithmicPhaseBProcessWindowLeft t m) ≤
      min (b : ℝ) (Complex.logarithmicPhaseBProcessWindowRight t m) := by
  have hab : (a : ℝ) ≤ (b : ℝ) :=
    Nat.cast_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have haRight :=
    (Complex.logarithmicPhaseBProcessEndpointMode_leftSupport_lt_windowRight
      hgeometry hm).le
  have hleftB :=
    (Complex.logarithmicPhaseBProcessEndpointMode_windowLeft_lt_rightSupport
      hgeometry hm).le
  have hmNeg :=
    Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm
  have hradiusPos := lt_trans Real.two_thirds_pos
    (Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
      hgeometry hm)
  have hleftCenter :
      Complex.logarithmicPhaseBProcessWindowLeft t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Complex.logarithmicPhaseBProcessWindowLeft
    exact sub_lt_self _ hradiusPos
  have hcenterRight :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhaseBProcessWindowRight t m := by
    unfold Complex.logarithmicPhaseBProcessWindowRight
    exact lt_add_of_pos_right _ hradiusPos
  have hwindow :
      Complex.logarithmicPhaseBProcessWindowLeft t m ≤
        Complex.logarithmicPhaseBProcessWindowRight t m :=
    le_trans hleftCenter.le hcenterRight.le
  exact max_le
    (le_min hab haRight)
    (le_min hleftB hwindow)

theorem Complex.logarithmicPhaseBProcessLeftOutside_window_overlaps
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) ∧
      (a : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hradiusPos := lt_trans Real.two_thirds_pos
    (Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
      hgeometry hclass.1)
  have hleftCenter :
      Complex.logarithmicPhaseBProcessWindowLeft t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Complex.logarithmicPhaseBProcessWindowLeft
    exact sub_lt_self _ hradiusPos
  have hleft := lt_trans hleftCenter hclass.2
  have hright :=
    Complex.logarithmicPhaseBProcessEndpointMode_leftSupport_lt_windowRight
      hgeometry hclass.1
  exact And.intro hleft hright

theorem Complex.logarithmicPhaseBProcessRightOutside_window_overlaps
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m < (b : ℝ) ∧
      (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hleft :=
    Complex.logarithmicPhaseBProcessEndpointMode_windowLeft_lt_rightSupport
      hgeometry hclass.1
  have hradiusPos := lt_trans Real.two_thirds_pos
    (Complex.logarithmicPhaseBProcessEndpointMode_two_thirds_lt_radius
      hgeometry hclass.1)
  have hcenterRight :
      Complex.logarithmicPhaseFourierStationaryPoint t m <
        Complex.logarithmicPhaseBProcessWindowRight t m := by
    unfold Complex.logarithmicPhaseBProcessWindowRight
    exact lt_add_of_pos_right _ hradiusPos
  have hright := lt_trans hclass.2 hcenterRight
  exact And.intro hleft hright

end

end LFunctions
end Boundary

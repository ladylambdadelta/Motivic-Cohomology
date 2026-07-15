import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicQuantitativeFiniteInactive

/-!
# Full-support separation of finite inactive modes

A negative mode in the canonical mode range is active whenever its stationary
center lies in the full cutoff support `[a-2/3,b+2/3]`.  Consequently the
finite inactive classes lie beyond those full-support endpoints, not merely
beyond the principal block.  Relative to the quantitative support
`[a-1/3,b+1/3]`, both classes have a deterministic one-third center gap.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhasePoissonLeftInactive_center_lt_fullSupport
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m <
      Real.integerBlockCutoffSupportLeftEndpoint a := by
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hm
  have hinactiveParts := Finset.mem_sdiff.mp hdata.1
  have hmRange := hinactiveParts.1
  have hnotActive := hinactiveParts.2
  by_contra hnot
  have hcenterLower :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    le_of_not_gt hnot
  have htwoThirdsNonneg : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have habCenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 := by
    have hcenterA := hdata.2.2.le
    have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
    exact le_trans hcenterA
      (le_trans habReal (le_add_of_nonneg_right htwoThirdsNonneg))
  have hactive :
      m ∈ Complex.logarithmicPhasePoissonActiveModes t a b :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
      (And.intro hmRange
        (And.intro hdata.2.1
          (And.intro hcenterLower habCenter)))
  exact hnotActive hactive

theorem Complex.logarithmicPhasePoissonRightInactive_fullSupport_lt_center
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    (b : ℝ) + 2 / 3 <
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hm
  have hinactiveParts := Finset.mem_sdiff.mp hdata.1
  have hmRange := hinactiveParts.1
  have hnotActive := hinactiveParts.2
  by_contra hnot
  have hcenterUpper :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) + 2 / 3 :=
    le_of_not_gt hnot
  have hcenterLower :
      Real.integerBlockCutoffSupportLeftEndpoint a ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
    unfold Real.integerBlockCutoffSupportLeftEndpoint
    have htwoThirdsNonneg : (0 : ℝ) ≤ 2 / 3 :=
      div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
    have hleftA : (a : ℝ) - 2 / 3 ≤ (a : ℝ) :=
      sub_le_self _ htwoThirdsNonneg
    have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
    exact le_trans hleftA (le_trans habReal hdata.2.2.le)
  have hactive :
      m ∈ Complex.logarithmicPhasePoissonActiveModes t a b :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
      (And.intro hmRange
        (And.intro hdata.2.1
          (And.intro hcenterLower hcenterUpper)))
  exact hnotActive hactive

theorem Real.quantitativeLeft_sub_fullLeft_eq_one_third
    (a : ℤ) :
    Complex.logarithmicPhaseQuantitativeSupportLeft a -
        Real.integerBlockCutoffSupportLeftEndpoint a =
      (1 : ℝ) / 3 := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  have hcancel :
      ((a : ℝ) - 1 / 3) - ((a : ℝ) - 2 / 3) =
        2 / 3 - 1 / 3 := by
    exact sub_sub_sub_cancel_left (1 / 3 : ℝ) (2 / 3) (a : ℝ)
  have honeAddOne : (1 : ℝ) + 1 = 2 :=
    one_add_one_eq_two
  have htwoSubOne : (2 : ℝ) - 1 = 1 :=
    Eq.trans
      (congrArg (fun value : ℝ => value - 1) honeAddOne).symm
      (add_sub_cancel_right 1 1)
  exact hcancel.trans
    ((sub_div 2 1 3).symm.trans
      (congrArg (fun value : ℝ => value / 3)
        htwoSubOne))

theorem Real.fullRight_sub_quantitativeRight_eq_one_third
    (b : ℤ) :
    ((b : ℝ) + 2 / 3) -
        Complex.logarithmicPhaseQuantitativeSupportRight b =
      (1 : ℝ) / 3 := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have hcancel :
      ((b : ℝ) + 2 / 3) - ((b : ℝ) + 1 / 3) =
        2 / 3 - 1 / 3 := by
    exact add_sub_add_left_eq_sub (2 / 3 : ℝ) (1 / 3) (b : ℝ)
  have honeAddOne : (1 : ℝ) + 1 = 2 :=
    one_add_one_eq_two
  have htwoSubOne : (2 : ℝ) - 1 = 1 :=
    Eq.trans
      (congrArg (fun value : ℝ => value - 1) honeAddOne).symm
      (add_sub_cancel_right 1 1)
  exact hcancel.trans
    ((sub_div 2 1 3).symm.trans
      (congrArg (fun value : ℝ => value / 3)
        htwoSubOne))

theorem Complex.logarithmicPhasePoissonLeftInactive_one_third_center_gap
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    (1 : ℝ) / 3 <
      Complex.logarithmicPhaseQuantitativeSupportLeft a -
        Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hcenter :=
    Complex.logarithmicPhasePoissonLeftInactive_center_lt_fullSupport
      t a b hab hm
  have hsubtract := sub_lt_sub_left hcenter
    (Complex.logarithmicPhaseQuantitativeSupportLeft a)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value < Complex.logarithmicPhaseQuantitativeSupportLeft a -
        Complex.logarithmicPhaseFourierStationaryPoint t m)
    (Real.quantitativeLeft_sub_fullLeft_eq_one_third a)
    hsubtract

theorem Complex.logarithmicPhasePoissonRightInactive_one_third_center_gap
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b) :
    (1 : ℝ) / 3 <
      Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhaseQuantitativeSupportRight b := by
  have hcenter :=
    Complex.logarithmicPhasePoissonRightInactive_fullSupport_lt_center
      t a b hab hm
  have hsubtract := sub_lt_sub_right hcenter
    (Complex.logarithmicPhaseQuantitativeSupportRight b)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value < Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhaseQuantitativeSupportRight b)
    (Real.fullRight_sub_quantitativeRight_eq_one_third b)
    hsubtract

end

end LFunctions
end Boundary

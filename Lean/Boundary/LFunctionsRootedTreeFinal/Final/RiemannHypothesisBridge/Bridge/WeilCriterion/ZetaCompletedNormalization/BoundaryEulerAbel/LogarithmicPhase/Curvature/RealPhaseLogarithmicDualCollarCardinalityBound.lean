import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualShiftCurvature

/-!
# Curvature insertion into dual collar cardinality

The explicit shifted curvature is inserted into the real mean-value theorem.
This gives the required growth inequality for the shifted derivative, hence a
uniform diameter bound for every derivative-value collar.  Passing to natural
integer points yields a levelwise cardinality bound and then a total bound over
the canonical represented-level range.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualShiftCurvatureLower
    (t h L U : ℝ) : ℝ :=
  ‖t‖ * h * (2 * L + h) /
    (U ^ 2 * (U + h) ^ 2)

theorem Complex.logarithmicPhaseDualShiftCurvatureLower_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h L U : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U) :
    0 < Complex.logarithmicPhaseDualShiftCurvatureLower t h L U := by
  unfold Complex.logarithmicPhaseDualShiftCurvatureLower
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hlinear : 0 < 2 * L + h :=
    add_pos (mul_pos zero_lt_two hL) hh
  have hnumerator : 0 < ‖t‖ * h * (2 * L + h) :=
    mul_pos (mul_pos hnorm hh) hlinear
  have hU : 0 < U := lt_of_lt_of_le hL hLU
  have hdenom : 0 < U ^ 2 * (U + h) ^ 2 :=
    mul_pos (sq_pos_of_pos hU) (sq_pos_of_pos (add_pos hU hh))
  exact div_pos hnumerator hdenom

theorem Complex.logarithmicPhaseDualShiftDerivative_continuousOn_Icc
    (t : ℝ) {h L U : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    ContinuousOn
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h)
      (Set.Icc L U) := by
  exact fun x hx =>
    (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceDerivative
      t (lt_of_lt_of_le hL hx.1) hh).continuousAt.continuousWithinAt

theorem Complex.logarithmicPhaseDualShiftDerivative_differentiableOn_interior_Icc
    (t : ℝ) {h L U : ℝ} (hh : 0 ≤ h) (hL : 0 < L) :
    DifferentiableOn ℝ
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h)
      (interior (Set.Icc L U)) := by
  intro x hx
  have hxIcc : x ∈ Set.Icc L U := interior_subset hx
  exact
    (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceDerivative
      t (lt_of_lt_of_le hL hxIcc.1) hh).differentiableAt.differentiableWithinAt

theorem Complex.deriv_logarithmicPhaseDualShiftDerivative_eq_curvature
    (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    deriv
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h) x =
      Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x := by
  exact
    (Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceDerivative
      t hx hh).deriv

theorem Complex.logarithmicPhaseDualShiftDerivative_growth_on_Icc
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h L U x y : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U)
    (hx : x ∈ Set.Icc L U) (hy : y ∈ Set.Icc L U)
    (hxy : x ≤ y) :
    Complex.logarithmicPhaseDualShiftCurvatureLower t h L U * (y - x) ≤
      Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y -
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x := by
  have hcontinuous :=
    Complex.logarithmicPhaseDualShiftDerivative_continuousOn_Icc
      t (le_of_lt hh) hL
  have hdifferentiable :=
    Complex.logarithmicPhaseDualShiftDerivative_differentiableOn_interior_Icc
      t (le_of_lt hh) hL
  have hlower :
      ∀ z ∈ interior (Set.Icc L U),
        Complex.logarithmicPhaseDualShiftCurvatureLower t h L U ≤
          deriv
            (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h) z := by
    intro z hz
    have hzIcc : z ∈ Set.Icc L U := interior_subset hz
    have hcurvature :=
      Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_lower_on_Icc
        t hh hL hLU hzIcc
    exact Eq.subst (motive := fun value : ℝ => _ ≤ value)
      (Complex.deriv_logarithmicPhaseDualShiftDerivative_eq_curvature
        t (le_of_lt hh) (lt_of_lt_of_le hL hzIcc.1)).symm
      hcurvature
  exact
    (convex_Icc L U).mul_sub_le_image_sub_of_le_deriv
      hcontinuous hdifferentiable hlower x hx y hy hxy

theorem Complex.logarithmicPhaseDualDiscreteLevelCollar_diameter_le
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M q : ℕ} (hh : 0 < h) (hK : 0 < K) (hKM : K ≤ M)
    {eta : ℝ}
    {x y : ℕ}
    (hx : x ∈
      Complex.logarithmicPhaseDualDiscreteLevelCollarModes
        t h eta K M q)
    (hy : y ∈
      Complex.logarithmicPhaseDualDiscreteLevelCollarModes
        t h eta K M q) :
    |(x : ℝ) - (y : ℝ)| ≤
      2 * eta /
        Complex.logarithmicPhaseDualShiftCurvatureLower
          t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 2 := by
  have hxMembership :=
    (Complex.mem_logarithmicPhaseDualDiscreteLevelCollarModes_iff
      t h eta K M q x).mp hx
  have hyMembership :=
    (Complex.mem_logarithmicPhaseDualDiscreteLevelCollarModes_iff
      t h eta K M q y).mp hy
  rcases hxMembership.2 with ⟨xw, hxCell, hxCollar⟩
  rcases hyMembership.2 with ⟨yw, hyCell, hyCollar⟩
  have hKMsucc : (K : ℝ) ≤ ((M + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (le_trans hKM (Nat.le_succ M))
  have hmu := Complex.logarithmicPhaseDualShiftCurvatureLower_pos
    t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) hKMsucc
  have hwitnessDistance : |xw - yw| ≤
      2 * eta /
        Complex.logarithmicPhaseDualShiftCurvatureLower
          t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) := by
    match le_total xw yw with
    | Or.inl hxy =>
        have hgrowth :=
          Complex.logarithmicPhaseDualShiftDerivative_growth_on_Icc
            t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) hKMsucc
            hxCollar.1 hyCollar.1 hxy
        have hdiam :=
          Complex.logarithmicPhaseDualCrossingCollar_diameter_le
            t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) hmu
            hxy hxCollar hyCollar hgrowth
        exact Eq.subst (motive := fun z : ℝ => z ≤ _)
          (abs_of_nonpos (sub_nonpos.mpr hxy)).symm
          (Eq.subst (motive := fun z : ℝ => z ≤ _)
            (neg_sub xw yw).symm hdiam)
    | Or.inr hyx =>
        have hgrowth :=
          Complex.logarithmicPhaseDualShiftDerivative_growth_on_Icc
            t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) hKMsucc
            hyCollar.1 hxCollar.1 hyx
        have hdiam :=
          Complex.logarithmicPhaseDualCrossingCollar_diameter_le
            t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) hmu
            hyx hyCollar hxCollar hgrowth
        exact Eq.subst (motive := fun z : ℝ => z ≤ _)
          (abs_of_nonneg (sub_nonneg.mpr hyx)).symm hdiam
  have hxError : |(x : ℝ) - xw| ≤ 1 := by
    exact abs_le.mpr (And.intro
      (neg_le.mpr (le_trans hxCell.1 (le_add_of_nonneg_right zero_le_one)))
      (sub_le_iff_le_add.mpr
        (le_trans hxCell.2
          (le_of_eq (Nat.cast_add x 1)))))
  have hyError : |yw - (y : ℝ)| ≤ 1 := by
    exact abs_le.mpr (And.intro
      (neg_le.mpr (le_trans hyCell.1 (le_add_of_nonneg_right zero_le_one)))
      (sub_le_iff_le_add.mpr
        (le_trans hyCell.2
          (le_of_eq (Nat.cast_add y 1)))))
  have htriangle : |(x : ℝ) - (y : ℝ)| ≤
      |(x : ℝ) - xw| + |xw - yw| + |yw - (y : ℝ)| := by
    have hsum : ((x : ℝ) - xw) + (xw - yw) + (yw - (y : ℝ)) =
        (x : ℝ) - (y : ℝ) := by
      exact Eq.trans (congrArg (fun z : ℝ => z + (yw - (y : ℝ)))
        (sub_add_sub_cancel (x : ℝ) xw yw))
        (sub_add_sub_cancel (x : ℝ) yw (y : ℝ))
    have hfirst := abs_add ((x : ℝ) - xw) (xw - yw)
    have hsecond := abs_add (((x : ℝ) - xw) + (xw - yw)) (yw - (y : ℝ))
    exact Eq.subst (motive := fun z : ℝ => |z| ≤ _)
      hsum.symm (le_trans hsecond (add_le_add_right hfirst _))
  exact le_trans htriangle
    (le_trans (add_le_add (add_le_add hxError hwitnessDistance) hyError)
      (le_of_eq (by
        exact Eq.trans
          (congrArg (fun z : ℝ => z + 1)
            (add_comm 1
              (2 * eta /
                Complex.logarithmicPhaseDualShiftCurvatureLower
                  t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ))))
          (add_assoc _ 1 1).symm)))

theorem Complex.logarithmicPhaseDualDiscreteLevelCollar_card_real_le
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M q : ℕ} (hh : 0 < h) (hK : 0 < K) (hKM : K ≤ M)
    {eta : ℝ} (heta : 0 ≤ eta) :
    ((Complex.logarithmicPhaseDualDiscreteLevelCollarModes
      t h eta K M q).card : ℝ) ≤
      2 * eta /
          Complex.logarithmicPhaseDualShiftCurvatureLower
          t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 3 := by
  have hmu := Complex.logarithmicPhaseDualShiftCurvatureLower_pos
    t ht (Nat.cast_pos.mpr hh) (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hKM)
  have hD :
      0 ≤ 2 * eta /
        Complex.logarithmicPhaseDualShiftCurvatureLower
          t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) :=
    div_nonneg (mul_nonneg (le_of_lt zero_lt_two) heta) (le_of_lt hmu)
  exact Finset.card_real_le_diameter_add_one
    (Complex.logarithmicPhaseDualDiscreteLevelCollarModes
      t h eta K M q)
    (2 * eta /
      Complex.logarithmicPhaseDualShiftCurvatureLower
        t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 2) (add_nonneg hD (OfNat.zero_le 2))
    (fun x hx y hy =>
      Complex.logarithmicPhaseDualDiscreteLevelCollar_diameter_le
        t ht hh hK hKM hx hy)

theorem Complex.logarithmicPhaseDualDiscreteCollarModes_card_real_le
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    {h K M : ℕ} (hh : 0 < h) (hK : 0 < K) (hKM : K ≤ M)
    {eta : ℝ} (heta : 0 ≤ eta) :
    ((Complex.logarithmicPhaseDualDiscreteCollarModes
      t h eta K M).card : ℝ) ≤
      ((Complex.logarithmicPhaseDualCrossingLevels
        t (h : ℝ) eta (K : ℝ)).card : ℝ) *
        (2 * eta /
          Complex.logarithmicPhaseDualShiftCurvatureLower
            t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 3) := by
  have hledger :=
    Complex.logarithmicPhaseDualDiscreteCollarModes_card_real_le_level_sum
      t h eta K M
  have hpoint :
      (∑ q ∈ Complex.logarithmicPhaseDualCrossingLevels
          t (h : ℝ) eta (K : ℝ),
        ((Complex.logarithmicPhaseDualDiscreteLevelCollarModes
          t h eta K M q).card : ℝ)) ≤
      ∑ q ∈ Complex.logarithmicPhaseDualCrossingLevels
          t (h : ℝ) eta (K : ℝ),
        (2 * eta /
          Complex.logarithmicPhaseDualShiftCurvatureLower
          t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 3) := by
    exact Finset.sum_le_sum (fun q hq =>
      Complex.logarithmicPhaseDualDiscreteLevelCollar_card_real_le
        t ht hh hK hKM heta)
  have hconstant := Finset.sum_const_zero
    (Complex.logarithmicPhaseDualCrossingLevels
      t (h : ℝ) eta (K : ℝ))
    (2 * eta /
      Complex.logarithmicPhaseDualShiftCurvatureLower
        t (h : ℝ) (K : ℝ) ((M + 1 : ℕ) : ℝ) + 3)
  exact le_trans hledger
    (le_trans hpoint (le_of_eq hconstant))

end

end LFunctions
end Boundary

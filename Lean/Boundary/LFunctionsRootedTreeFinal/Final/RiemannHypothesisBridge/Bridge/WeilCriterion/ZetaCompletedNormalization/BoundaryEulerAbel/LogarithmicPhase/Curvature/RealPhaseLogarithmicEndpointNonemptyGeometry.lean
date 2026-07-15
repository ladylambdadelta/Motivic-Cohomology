import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpCompleteActiveClosure

/-!
# Geometry supplied by a nonempty endpoint family

An endpoint packet has its clipped window intersecting the principal block.
Thus the block left endpoint is no larger than the raw window right endpoint.
The stationary center is at most `norm t`, and the balanced radius is at most
the center because the scale is at least one.  Consequently `a <= 2*norm t`
and dyadic comparability gives `b <= 4*norm t`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseBProcessEndpointMode_blockLeft_le_windowRight
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowRight t m := by
  have horder :=
    Complex.logarithmicPhaseBProcessEndpointMode_clippedWindow_order
      hgeometry hm
  have hleft :
      (a : ℝ) ≤
        max (a : ℝ) (Complex.logarithmicPhaseBProcessWindowLeft t m) :=
    le_max_left _ _
  have hright :
      min (b : ℝ) (Complex.logarithmicPhaseBProcessWindowRight t m) ≤
        Complex.logarithmicPhaseBProcessWindowRight t m :=
    min_le_right _ _
  exact le_trans hleft (le_trans horder hright)

theorem Complex.logarithmicPhaseBProcessEndpointMode_center_le_norm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤ ‖t‖ := by
  have hmNeg :=
    Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm
  exact Complex.logarithmicPhaseFourierStationaryPoint_le_norm t hmNeg

theorem Complex.logarithmicPhaseBProcessEndpointMode_radius_le_center
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessRadius t m ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhaseBProcessRadius
  have hcenterPos := Complex.logarithmicPhaseFourierStationaryPoint_pos
    t ht (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)
  have hscaleOne := Complex.logarithmicPhaseBProcessScale_one_le t
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hmul := mul_le_mul_of_nonneg_left hscaleOne hcenterPos.le
  have htarget :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m *
          Complex.logarithmicPhaseBProcessScale t :=
    Eq.subst
      (motive := fun value : ℝ => value ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m *
          Complex.logarithmicPhaseBProcessScale t)
      (mul_one (Complex.logarithmicPhaseFourierStationaryPoint t m))
      hmul
  exact (div_le_iff₀ hscalePos).mpr htarget

theorem Complex.logarithmicPhaseBProcessEndpointMode_windowRight_le_two_norm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowRight t m ≤ 2 * ‖t‖ := by
  unfold Complex.logarithmicPhaseBProcessWindowRight
  have hcenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_center_le_norm hm
  have hradiusCenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_radius_le_center ht hm
  have hradius := le_trans hradiusCenter hcenter
  have hadd := add_le_add hcenter hradius
  exact le_trans hadd (le_of_eq (two_mul ‖t‖).symm)

theorem Complex.logarithmicPhaseBProcess_natBlockLeft_le_two_norm_of_endpoint_mem
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (a : ℝ) ≤ 2 * ‖t‖ := by
  exact le_trans
    (Complex.logarithmicPhaseBProcessEndpointMode_blockLeft_le_windowRight
      hgeometry hm)
    (Complex.logarithmicPhaseBProcessEndpointMode_windowRight_le_two_norm
      ht hm)

theorem Complex.logarithmicPhaseBProcess_natBlockRight_le_four_norm_of_endpoint_mem
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (b : ℝ) ≤ 4 * ‖t‖ := by
  have hba := Real.natCast_blockRight_le_two_mul_blockLeft
    (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
  have hat :=
    Complex.logarithmicPhaseBProcess_natBlockLeft_le_two_norm_of_endpoint_mem
      ht hgeometry hm
  have hscaled := mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg 2)
  have hnormalize : 2 * (2 * ‖t‖) = 4 * ‖t‖ := by
    have htwoTwo : (2 : ℝ) * 2 = 4 := by
      have hnat : (2 * 2 : ℕ) = 4 := rfl
      exact Eq.trans (Nat.cast_mul 2 2).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact Eq.trans (mul_assoc 2 2 ‖t‖).symm
      (congrArg (fun value : ℝ => value * ‖t‖) htwoTwo)
  exact le_trans hba (le_trans hscaled (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseBProcess_natBlockRight_le_four_norm_of_endpoint_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) ≤ 4 * ‖t‖ := by
  exact
    Complex.logarithmicPhaseBProcess_natBlockRight_le_four_norm_of_endpoint_mem
      ht hgeometry hnonempty.choose_spec

theorem Real.endpointNonempty_blockRight_mul_scale_div_norm_le_four_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessEndpointModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ ≤
      4 * Complex.logarithmicPhaseBProcessScale t := by
  have hbNorm :=
    Complex.logarithmicPhaseBProcess_natBlockRight_le_four_norm_of_endpoint_nonempty
      ht hgeometry hnonempty
  have hmul := mul_le_mul_of_nonneg_right hbNorm
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hnormPos := Complex.logarithmicPhaseBProcess_norm_pos t ht
  have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
  have hcancel :
      (4 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
        4 * Complex.logarithmicPhaseBProcessScale t := by
    calc
      (4 * ‖t‖) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
          (4 * Complex.logarithmicPhaseBProcessScale t) * ‖t‖ / ‖t‖ := by
        exact congrArg (fun value : ℝ => value / ‖t‖)
          (Eq.trans (mul_assoc 4 ‖t‖ _)
            (Eq.trans
              (congrArg (fun value : ℝ => 4 * value)
                (mul_comm ‖t‖ _))
              (mul_assoc 4 _ ‖t‖).symm))
      _ = 4 * Complex.logarithmicPhaseBProcessScale t :=
        mul_div_cancel_right₀ _ (ne_of_gt hnormPos)
  exact le_trans hdiv (le_of_eq hcancel)

theorem Complex.logarithmicPhaseBProcessEndpointBudget_eq_zero_of_empty
    (t : ℝ) (a b : ℤ)
    (hempty :
      Complex.logarithmicPhasePoissonBProcessEndpointModes t a b = ∅) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget t a b = 0 := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Eq.subst
    (motive := fun modes : Finset ℤ =>
      (∑ m ∈ modes,
        Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
          t a b m) = 0)
    hempty.symm Finset.sum_empty

end

end LFunctions
end Boundary

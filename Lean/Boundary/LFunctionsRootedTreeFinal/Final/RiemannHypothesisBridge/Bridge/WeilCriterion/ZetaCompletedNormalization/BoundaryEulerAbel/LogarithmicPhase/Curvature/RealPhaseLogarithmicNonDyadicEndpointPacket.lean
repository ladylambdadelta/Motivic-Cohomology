import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicNonDyadicGeometry
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicEndpointNonemptyGeometry

/-!
# Intrinsic non-dyadic endpoint packet geometry

Endpoint packet windows are controlled by frequency, not by the ambient block
right endpoint.  Their centers are at most `‖t‖`; division by the balanced
scale turns this into a radius bounded by the same scale.  Thus every raw
endpoint window is contained below `‖t‖ + sqrt (1 + ‖t‖)` independently of
block width.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseIntrinsicEndpointRight
    (t : ℝ) : ℝ :=
  ‖t‖ + Complex.logarithmicPhaseBProcessScale t

theorem Real.norm_div_rootScale_le_rootScale
    (t : ℝ) :
    ‖t‖ / Complex.logarithmicPhaseBProcessScale t ≤
      Complex.logarithmicPhaseBProcessScale t := by
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hnormLeSquare :
      ‖t‖ ≤ Complex.logarithmicPhaseBProcessScale t ^ 2 := by
    unfold Complex.logarithmicPhaseBProcessScale
    have hsquare := Real.sq_sqrt
      (add_nonneg zero_le_one (norm_nonneg t))
    exact Eq.subst (motive := fun value : ℝ => ‖t‖ ≤ value)
      hsquare.symm (le_add_of_nonneg_left zero_le_one)
  have hmulForm :
      Complex.logarithmicPhaseBProcessScale t ^ 2 =
        Complex.logarithmicPhaseBProcessScale t *
          Complex.logarithmicPhaseBProcessScale t :=
    pow_two _
  exact (div_le_iff₀ hscalePos).mpr
    (Eq.subst (motive := fun value : ℝ => ‖t‖ ≤ value)
      hmulForm.symm hnormLeSquare)

theorem Complex.logarithmicPhaseBProcessEndpointMode_radius_le_scale_general
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessRadius t m ≤
      Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessRadius
  have hcenter :=
    Complex.logarithmicPhaseBProcessEndpointMode_center_le_norm hm
  have hdivide := div_le_div_of_nonneg_right hcenter
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hdivide (Real.norm_div_rootScale_le_rootScale t)

theorem Complex.logarithmicPhaseBProcessEndpointMode_windowLeft_le_norm_general
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m ≤ ‖t‖ := by
  unfold Complex.logarithmicPhaseBProcessWindowLeft
  have hsub := sub_le_self
    (Complex.logarithmicPhaseFourierStationaryPoint t m)
    (Complex.logarithmicPhaseBProcessRadius_nonneg t m)
  exact le_trans hsub
    (Complex.logarithmicPhaseBProcessEndpointMode_center_le_norm hm)

theorem Complex.logarithmicPhaseBProcessEndpointMode_windowRight_le_intrinsic
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowRight t m ≤
      Complex.logarithmicPhaseIntrinsicEndpointRight t := by
  unfold Complex.logarithmicPhaseBProcessWindowRight
  unfold Complex.logarithmicPhaseIntrinsicEndpointRight
  exact add_le_add
    (Complex.logarithmicPhaseBProcessEndpointMode_center_le_norm hm)
    (Complex.logarithmicPhaseBProcessEndpointMode_radius_le_scale_general hm)

theorem Real.norm_mul_scale_div_norm_eq_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    ‖t‖ * Complex.logarithmicPhaseBProcessScale t / ‖t‖ =
      Complex.logarithmicPhaseBProcessScale t := by
  have hnormNe : ‖t‖ ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  exact Eq.trans
    (mul_div_assoc ‖t‖ (Complex.logarithmicPhaseBProcessScale t) ‖t‖)
    (Eq.trans
      (congrArg (fun value : ℝ => value / ‖t‖)
        (mul_comm ‖t‖ (Complex.logarithmicPhaseBProcessScale t)))
      (Eq.trans
        (div_mul_eq_mul_div
          (Complex.logarithmicPhaseBProcessScale t) ‖t‖ ‖t‖)
        (Eq.trans
          (congrArg
            (fun value : ℝ =>
              Complex.logarithmicPhaseBProcessScale t * value)
            (div_self hnormNe))
          (mul_one _))))

theorem Real.scale_sq_div_norm_le_two
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseBProcessScale t ^ 2 / ‖t‖ ≤ 2 := by
  have hnormPos := lt_of_lt_of_le zero_lt_one ht
  have hscaleSquare :
      Complex.logarithmicPhaseBProcessScale t ^ 2 = 1 + ‖t‖ := by
    unfold Complex.logarithmicPhaseBProcessScale
    exact Real.sq_sqrt (add_nonneg zero_le_one (norm_nonneg t))
  have honeLeNorm : (1 : ℝ) ≤ ‖t‖ := ht
  have hsumLe : (1 : ℝ) + ‖t‖ ≤ 2 * ‖t‖ := by
    have hadd := add_le_add_right honeLeNorm ‖t‖
    exact le_trans hadd (le_of_eq (two_mul ‖t‖).symm)
  have hdivide := div_le_div_of_nonneg_right hsumLe hnormPos.le
  have hnormalize : (2 * ‖t‖) / ‖t‖ = 2 := by
    exact Eq.trans (mul_div_assoc 2 ‖t‖ ‖t‖)
      (Eq.trans (congrArg (fun value : ℝ => 2 * value)
        (div_self (ne_of_gt hnormPos))) (mul_one 2))
  exact Eq.subst (motive := fun value : ℝ => value / ‖t‖ ≤ 2)
    hscaleSquare.symm (le_trans hdivide (le_of_eq hnormalize))

theorem Real.intrinsicEndpointRight_mul_scale_div_norm_le_three_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) :
    Complex.logarithmicPhaseIntrinsicEndpointRight t *
          Complex.logarithmicPhaseBProcessScale t / ‖t‖ ≤
      3 * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  have hnormPart := Real.norm_mul_scale_div_norm_eq_scale t ht
  have hscaleSquare := Real.scale_sq_div_norm_le_two t ht
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hscalePart := mul_le_mul_of_nonneg_right hscaleSquare hscaleNonneg
  unfold Complex.logarithmicPhaseIntrinsicEndpointRight
  have hexpand :
      (‖t‖ + S) * S / ‖t‖ =
        ‖t‖ * S / ‖t‖ + S ^ 2 / ‖t‖ := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value / ‖t‖)
        (add_mul ‖t‖ S S))
      (add_div (‖t‖ * S) (S * S) ‖t‖).trans
        (congrArg (fun value : ℝ => ‖t‖ * S / ‖t‖ + value)
          (congrArg (fun value : ℝ => value / ‖t‖) (pow_two S).symm))
  have hsum := add_le_add (le_of_eq hnormPart) hscaleSquare
  have htwoLeTwoScale : (2 : ℝ) ≤ 2 * S := by
    have hone := Complex.logarithmicPhaseBProcessScale_one_le t
    have hmul := mul_le_mul_of_nonneg_left hone (OfNat.zero_le 2)
    exact Eq.subst (motive := fun value : ℝ => value ≤ 2 * S)
      (mul_one (2 : ℝ)).symm hmul
  have hsumScale := add_le_add_left htwoLeTwoScale S
  have hcollect : S + 2 * S = 3 * S := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 2 * S) (one_mul S).symm)
      (Eq.trans (add_mul 1 2 S).symm
        (congrArg (fun value : ℝ => value * S)
          (show (1 : ℝ) + 2 = 3 from rfl)))
  exact Eq.subst (motive := fun value : ℝ => value ≤ 3 * S)
    hexpand.symm
    (le_trans hsum (le_trans hsumScale (le_of_eq hcollect)))

theorem Complex.logarithmicPhaseIntrinsicEndpointRight_nonneg
    (t : ℝ) :
    0 ≤ Complex.logarithmicPhaseIntrinsicEndpointRight t := by
  unfold Complex.logarithmicPhaseIntrinsicEndpointRight
  exact add_nonneg (norm_nonneg t)
    (Complex.logarithmicPhaseBProcessScale_nonneg t)

theorem Complex.logarithmicPhaseBProcessClippedLeftTailBudget_le_two_scale_intrinsic
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget
        t (a : ℤ) m ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hraw =>
      have hwindow :=
        Complex.logarithmicPhaseBProcessEndpointMode_windowLeft_le_norm_general hm
      have hmul := mul_le_mul_of_nonneg_right hwindow
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      have hdiv := div_le_div_of_nonneg_right hmul (norm_nonneg t)
      have hscaled := mul_le_mul_of_nonneg_left hdiv (OfNat.zero_le 2)
      have hidentity :=
        Complex.logarithmicPhaseBProcessLeftTailBudget_eq
          t ht (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)
      have hnormalize := Real.norm_mul_scale_div_norm_eq_scale t ht
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * Complex.logarithmicPhaseBProcessScale t)
        hidentity.symm
        (le_trans hscaled
          (le_of_eq
            (congrArg (fun value : ℝ => 2 * value) hnormalize)))
  | Or.inr hraw =>
      exact mul_nonneg (OfNat.zero_le 2)
        (Complex.logarithmicPhaseBProcessScale_nonneg t)

theorem Complex.logarithmicPhaseBProcessClippedRightTailBudget_le_six_scale_intrinsic
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedRightTailBudget
        t (b : ℤ) m ≤
      6 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hwindow :=
        Complex.logarithmicPhaseBProcessEndpointMode_windowRight_le_intrinsic hm
      have hmul := mul_le_mul_of_nonneg_right hwindow
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      have hdiv := div_le_div_of_nonneg_right hmul (norm_nonneg t)
      have hbase :=
        Real.intrinsicEndpointRight_mul_scale_div_norm_le_three_scale t ht
      have hwindowBudget := le_trans hdiv hbase
      have hscaled := mul_le_mul_of_nonneg_left hwindowBudget
        (OfNat.zero_le 2)
      have hnormalize :
          2 * (3 * Complex.logarithmicPhaseBProcessScale t) =
            6 * Complex.logarithmicPhaseBProcessScale t := by
        exact Eq.trans (mul_assoc 2 3 _).symm
          (congrArg
            (fun value : ℝ => value *
              Complex.logarithmicPhaseBProcessScale t)
            (show (2 : ℝ) * 3 = 6 from rfl))
      have hidentity :=
        Complex.logarithmicPhaseBProcessRightTailBudget_eq
          t ht (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 6 * Complex.logarithmicPhaseBProcessScale t)
        hidentity.symm
        (le_trans hscaled (le_of_eq hnormalize))
  | Or.inr hraw =>
      exact mul_nonneg (OfNat.zero_le 6)
        (Complex.logarithmicPhaseBProcessScale_nonneg t)

theorem Complex.two_mul_endpointMode_radius_le_two_scale_intrinsic
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    2 * Complex.logarithmicPhaseBProcessRadius t m ≤
      2 * Complex.logarithmicPhaseBProcessScale t :=
  mul_le_mul_of_nonneg_left
    (Complex.logarithmicPhaseBProcessEndpointMode_radius_le_scale_general hm)
    (OfNat.zero_le 2)

def Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant
    (t : ℝ) : ℝ :=
  4 / 3 + 10 * Complex.logarithmicPhaseBProcessScale t

theorem Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant_nonneg
    (t : ℝ) :
    0 ≤ Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant t := by
  unfold Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant
  exact add_nonneg
    (div_nonneg (OfNat.zero_le 4) (OfNat.zero_le 3))
    (mul_nonneg (OfNat.zero_le 10)
      (Complex.logarithmicPhaseBProcessScale_nonneg t))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_intrinsicMajorant
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
        t (a : ℤ) (b : ℤ) m ≤
      Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant t := by
  have hleft :=
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget_le_two_scale_intrinsic
      ht hm
  have hcentral :=
    Complex.two_mul_endpointMode_radius_le_two_scale_intrinsic hm
  have hright :=
    Complex.logarithmicPhaseBProcessClippedRightTailBudget_le_six_scale_intrinsic
      ht hm
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  unfold Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant
  have hsum := add_le_add (add_le_add (add_le_add le_rfl hleft) hcentral) hright
  have hcollect :
      (4 / 3 : ℝ) + 2 * Complex.logarithmicPhaseBProcessScale t +
          2 * Complex.logarithmicPhaseBProcessScale t +
          6 * Complex.logarithmicPhaseBProcessScale t =
        4 / 3 + 10 * Complex.logarithmicPhaseBProcessScale t := by
    have hweighted := Real.three_weighted_terms_eq_sum_coeff_mul
      2 2 6 (Complex.logarithmicPhaseBProcessScale t)
    exact Eq.trans
      (add_assoc (4 / 3 : ℝ)
        (2 * Complex.logarithmicPhaseBProcessScale t)
        (2 * Complex.logarithmicPhaseBProcessScale t)).symm
      (Eq.trans
        (congrArg
          (fun value : ℝ => value +
            6 * Complex.logarithmicPhaseBProcessScale t)
          (add_assoc (4 / 3 : ℝ)
            (2 * Complex.logarithmicPhaseBProcessScale t)
            (2 * Complex.logarithmicPhaseBProcessScale t)))
        (Eq.trans
          (add_assoc (4 / 3 : ℝ)
            (2 * Complex.logarithmicPhaseBProcessScale t +
              2 * Complex.logarithmicPhaseBProcessScale t)
            (6 * Complex.logarithmicPhaseBProcessScale t))
          (congrArg (fun value : ℝ => (4 / 3 : ℝ) + value)
            (Eq.trans hweighted
              (congrArg
                (fun value : ℝ => value *
                  Complex.logarithmicPhaseBProcessScale t)
                (show (2 : ℝ) + 2 + 6 = 10 from rfl))))))
  exact le_trans hsum (le_of_eq hcollect)

theorem Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant_le_thirty_four_thirds_scale
    (t : ℝ) :
    Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant t ≤
      (34 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hone := Complex.logarithmicPhaseBProcessScale_one_le t
  have hcross := mul_le_mul_of_nonneg_left hone
    (div_nonneg (OfNat.zero_le 4) (OfNat.zero_le 3))
  have hcrossForm :
      (4 / 3 : ℝ) ≤ (4 / 3) *
        Complex.logarithmicPhaseBProcessScale t :=
    Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (4 / 3 : ℝ)).symm hcross
  unfold Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant
  have hsum := add_le_add_right hcrossForm
    (10 * Complex.logarithmicPhaseBProcessScale t)
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (add_mul (4 / 3 : ℝ) 10
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun value : ℝ => value *
            Complex.logarithmicPhaseBProcessScale t)
          (show (4 / 3 : ℝ) + 10 = 34 / 3 from rfl))))

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_intrinsicFamilyMajorant
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      2 * Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant t := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Finset.sum_le_two_mul_of_card_le_two
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant t)
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two
      ht hgeometry)
    (Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant_nonneg t)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_intrinsicMajorant
        ht hm)

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_sixty_eight_thirds_scale_intrinsic
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      (68 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hfamily :=
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_intrinsicFamilyMajorant
      ht hgeometry
  have hper :=
    Complex.logarithmicPhaseIntrinsicEndpointPacketMajorant_le_thirty_four_thirds_scale
      t
  have htwice := mul_le_mul_of_nonneg_left hper (OfNat.zero_le 2)
  have hnormalize :
      2 * ((34 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t) =
        (68 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Eq.trans (mul_assoc 2 (34 / 3 : ℝ) _).symm
      (congrArg
        (fun value : ℝ => value *
          Complex.logarithmicPhaseBProcessScale t)
        (show (2 : ℝ) * (34 / 3) = 68 / 3 from by rfl))
  exact le_trans hfamily (le_trans htwice (le_of_eq hnormalize))

end

end LFunctions
end Boundary

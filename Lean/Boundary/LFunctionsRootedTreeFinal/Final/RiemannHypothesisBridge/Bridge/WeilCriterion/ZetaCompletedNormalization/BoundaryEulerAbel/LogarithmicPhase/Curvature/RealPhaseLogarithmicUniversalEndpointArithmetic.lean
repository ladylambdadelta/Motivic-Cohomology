import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicUniversalEndpointPacket

/-!
# Arithmetic majorant for universal endpoint packets

Every nonzero clipped tail has its raw window endpoint inside the principal
block and is therefore bounded by the block-right tail scalar.  The balanced
central radius is bounded using the cutoff-support endpoint `b + 2/3`.
Together these give one explicit pointwise majorant, and endpoint cardinality
turns it into a finite-family bound without double counting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessEndpointSupportRight
    (b : ℤ) : ℝ :=
  (b : ℝ) + 2 / 3

def Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
    (t : ℝ) (b : ℤ) : ℝ :=
  4 / 3 +
    2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
      2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight b /
        Complex.logarithmicPhaseBProcessScale t) +
        2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

theorem Complex.logarithmicPhaseBProcessEndpointSupportRight_nonneg
    {b : ℕ} :
    0 ≤ Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessEndpointSupportRight
  exact add_nonneg (Nat.cast_nonneg b)
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))

theorem Complex.logarithmicPhaseBProcessEndpointMode_center_le_supportRight
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤
      Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessEndpointSupportRight
  exact Complex.logarithmicPhaseBProcessEndpointMode_center_upper hm

theorem Complex.logarithmicPhaseBProcessEndpointMode_radius_le_supportRight_div_scale
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessRadius t m ≤
      Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseBProcessRadius
  exact div_le_div_of_nonneg_right
    (Complex.logarithmicPhaseBProcessEndpointMode_center_le_supportRight hm)
    (Complex.logarithmicPhaseBProcessScale_pos t).le

theorem Complex.two_mul_endpointMode_radius_le_supportRightTerm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    2 * Complex.logarithmicPhaseBProcessRadius t m ≤
      2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t) := by
  exact mul_le_mul_of_nonneg_left
    (Complex.logarithmicPhaseBProcessEndpointMode_radius_le_supportRight_div_scale hm)
    (Nat.cast_nonneg 2)

theorem Complex.logarithmicPhaseBProcessClippedLeftTailBudget_le_blockRightTerm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t (a : ℤ) m ≤
      2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hraw =>
      have horder :=
        Complex.logarithmicPhaseBProcessEndpointMode_clippedWindow_order
          hgeometry hm
      have hleftEq :
          max (a : ℝ) (Complex.logarithmicPhaseBProcessWindowLeft t m) =
            Complex.logarithmicPhaseBProcessWindowLeft t m :=
        max_eq_right hraw
      have hrightLe :
          min (b : ℝ) (Complex.logarithmicPhaseBProcessWindowRight t m) ≤
            (b : ℝ) :=
        min_le_left _ _
      have hwindowLeftLe :
          Complex.logarithmicPhaseBProcessWindowLeft t m ≤ (b : ℝ) := by
        have htransport :
            Complex.logarithmicPhaseBProcessWindowLeft t m ≤
              min (b : ℝ) (Complex.logarithmicPhaseBProcessWindowRight t m) :=
          Eq.subst
            (motive := fun value : ℝ =>
              value ≤ min (b : ℝ)
                (Complex.logarithmicPhaseBProcessWindowRight t m))
            hleftEq horder
        exact le_trans htransport hrightLe
      have hmul := mul_le_mul_of_nonneg_right hwindowLeftLe
        (Complex.logarithmicPhaseBProcessScale_pos t).le
      have hnormPos :=
        Complex.logarithmicPhaseBProcess_norm_pos t ht
      have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
      have hscaled := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg 2)
      have htailBound := Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        (Complex.logarithmicPhaseBProcessLeftTailBudget_eq
          t ht
          (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)).symm
        hscaled
      have hbudget :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m else 0) =
            Complex.logarithmicPhaseBProcessLeftTailBudget t m :=
        if_pos hraw
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        hbudget.symm htailBound
  | Or.inr hraw =>
      have hrightNonneg :
          0 ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
        have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
        have hproduct := mul_nonneg hbNonneg
          (Complex.logarithmicPhaseBProcessScale_nonneg t)
        have hquotient := div_nonneg hproduct (norm_nonneg t)
        exact mul_nonneg (Nat.cast_nonneg 2) hquotient
      have hbudget :
          (if (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m then
              Complex.logarithmicPhaseBProcessLeftTailBudget t m else 0) = 0 :=
        if_neg hraw
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        hbudget.symm hrightNonneg

theorem Complex.logarithmicPhaseBProcessClippedRightTailBudget_le_blockRightTerm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedRightTailBudget t (b : ℤ) m ≤
      2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hraw =>
      have hmul := mul_le_mul_of_nonneg_right hraw
        (Complex.logarithmicPhaseBProcessScale_pos t).le
      have hnormPos :=
        Complex.logarithmicPhaseBProcess_norm_pos t ht
      have hdiv := div_le_div_of_nonneg_right hmul hnormPos.le
      have hscaled := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg 2)
      have htailBound := Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        (Complex.logarithmicPhaseBProcessRightTailBudget_eq
          t ht
          (Complex.logarithmicPhaseBProcessEndpointMode_negative_nat hm)).symm
        hscaled
      have hbudget :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m else 0) =
            Complex.logarithmicPhaseBProcessRightTailBudget t m :=
        if_pos hraw
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        hbudget.symm htailBound
  | Or.inr hraw =>
      have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
      have hproduct := mul_nonneg hbNonneg
        (Complex.logarithmicPhaseBProcessScale_nonneg t)
      have hquotient := div_nonneg hproduct (norm_nonneg t)
      have hrightNonneg := mul_nonneg (Nat.cast_nonneg 2) hquotient
      have hbudget :
          (if Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) then
              Complex.logarithmicPhaseBProcessRightTailBudget t m else 0) = 0 :=
        if_neg hraw
      exact Eq.subst
        (motive := fun value : ℝ =>
          value ≤ 2 * ((b : ℝ) *
            Complex.logarithmicPhaseBProcessScale t / ‖t‖))
        hbudget.symm hrightNonneg

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_perModeMajorant
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
        t (a : ℤ) (b : ℤ) m ≤
      Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
        t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
  exact add_le_add
    (add_le_add
      (add_le_add le_rfl
        (Complex.logarithmicPhaseBProcessClippedLeftTailBudget_le_blockRightTerm
          ht hgeometry hm))
      (Complex.two_mul_endpointMode_radius_le_supportRightTerm hm))
    (Complex.logarithmicPhaseBProcessClippedRightTailBudget_le_blockRightTerm
      ht hm)

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_nonneg
    {t : ℝ} {b : ℕ} (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
      t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
  have hcrossing : 0 ≤ (4 / 3 : ℝ) :=
    div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3)
  have hbNonneg : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  have htailBase :
      0 ≤ (b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖ :=
    div_nonneg
      (mul_nonneg hbNonneg
        (Complex.logarithmicPhaseBProcessScale_nonneg t))
      (norm_nonneg t)
  have htail :
      0 ≤ 2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
    mul_nonneg (Nat.cast_nonneg 2) htailBase
  have hcentralBase :
      0 ≤ Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t :=
    div_nonneg
      Complex.logarithmicPhaseBProcessEndpointSupportRight_nonneg
      (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hcentral :
      0 ≤ 2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
        Complex.logarithmicPhaseBProcessScale t) :=
    mul_nonneg (Nat.cast_nonneg 2) hcentralBase
  exact add_nonneg (add_nonneg (add_nonneg hcrossing htail) hcentral) htail

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_four_perModeMajorant
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      4 * Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
        t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Finset.sum_le_four_mul_of_card_le_four
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant
      t (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_four
      ht hgeometry)
    (Complex.logarithmicPhaseBProcessUniversalEndpointPerModeMajorant_nonneg ht)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_perModeMajorant
        ht hgeometry hm)

end

end LFunctions
end Boundary

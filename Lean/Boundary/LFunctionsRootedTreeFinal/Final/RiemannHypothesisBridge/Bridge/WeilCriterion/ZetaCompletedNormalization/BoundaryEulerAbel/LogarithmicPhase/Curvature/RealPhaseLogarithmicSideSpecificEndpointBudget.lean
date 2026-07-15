import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCompleteActiveDichotomy

/-!
# Side-specific endpoint packet budget

Every endpoint mode belongs to a left or right endpoint family.  On the left
family the clipped left tail is zero; on the right family the clipped right
tail is zero.  Therefore an endpoint packet is charged only one tail term.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
    (t : ℝ) (b : ℤ) : ℝ :=
  4 / 3 +
    2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight b /
      Complex.logarithmicPhaseBProcessScale t) +
    2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)

theorem Complex.logarithmicPhaseBProcessLeftEndpoint_windowLeft_lt_blockLeft
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessWindowLeft t m < (a : ℝ) := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  match hclass with
  | Or.inl houtside =>
      exact
        (Complex.logarithmicPhaseBProcessLeftOutside_window_overlaps
          hgeometry houtside).1
  | Or.inr hclipped =>
      exact
        ((Complex.mem_logarithmicPhasePoissonBProcessLeftClippedModes_iff
          t (a : ℤ) (b : ℤ) m).mp hclipped).2.2.2

theorem Complex.logarithmicPhaseBProcessRightEndpoint_blockRight_lt_windowRight
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (b : ℝ) < Complex.logarithmicPhaseBProcessWindowRight t m := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  match hclass with
  | Or.inl houtside =>
      exact
        (Complex.logarithmicPhaseBProcessRightOutside_window_overlaps
          hgeometry houtside).2
  | Or.inr hclipped =>
      exact
        ((Complex.mem_logarithmicPhasePoissonBProcessRightClippedModes_iff
          t (a : ℤ) (b : ℤ) m).mp hclipped).2.2.2

theorem Complex.logarithmicPhaseBProcessClippedLeftTailBudget_eq_zero_of_leftEndpoint
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedLeftTailBudget t (a : ℤ) m = 0 := by
  unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
  have hwindow :=
    Complex.logarithmicPhaseBProcessLeftEndpoint_windowLeft_lt_blockLeft
      hgeometry hm
  match Classical.em
      ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
  | Or.inl hcontradiction =>
      exact False.elim ((not_le_of_gt hwindow) hcontradiction)
  | Or.inr hnot => exact if_neg hnot

theorem Complex.logarithmicPhaseBProcessClippedRightTailBudget_eq_zero_of_rightEndpoint
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessClippedRightTailBudget t (b : ℤ) m = 0 := by
  unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
  have hwindow :=
    Complex.logarithmicPhaseBProcessRightEndpoint_blockRight_lt_windowRight
      hgeometry hm
  match Classical.em
      (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
  | Or.inl hcontradiction =>
      exact False.elim ((not_le_of_gt hwindow) hcontradiction)
  | Or.inr hnot => exact if_neg hnot

theorem Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_sideMajorant
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
        t (a : ℤ) (b : ℤ) m ≤
      Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) := by
  have hside :=
    Complex.logarithmicPhasePoissonBProcessEndpointModes_subset_sideUnion
      t (a : ℤ) (b : ℤ) hm
  have hsideCases := Finset.mem_union.mp hside
  have hcentral :=
    Complex.two_mul_endpointMode_radius_le_supportRightTerm hm
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  match hsideCases with
  | Or.inl hleft =>
      have hzero :=
        Complex.logarithmicPhaseBProcessClippedLeftTailBudget_eq_zero_of_leftEndpoint
          hgeometry hleft
      have htail :=
        Complex.logarithmicPhaseBProcessClippedRightTailBudget_le_blockRightTerm
          ht hm
      have hzeroLe :
          Complex.logarithmicPhaseBProcessClippedLeftTailBudget
              t (a : ℤ) m ≤ 0 :=
        le_of_eq hzero
      have hraw :
          ((4 / 3 : ℝ) +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                t (a : ℤ) m +
              2 * Complex.logarithmicPhaseBProcessRadius t m) +
              Complex.logarithmicPhaseBProcessClippedRightTailBudget
                t (b : ℤ) m ≤
            ((4 / 3 : ℝ) + 0 +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
        add_le_add
          (add_le_add
            (add_le_add (le_refl (4 / 3 : ℝ)) hzeroLe)
            hcentral)
          htail
      have htarget :
          ((4 / 3 : ℝ) + 0 +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) =
            ((4 / 3 : ℝ) +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
        have hzeroAdd : (4 / 3 : ℝ) + 0 = 4 / 3 := add_zero _
        exact congrArg
          (fun value : ℝ =>
            (value +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖))
          hzeroAdd
      exact hraw.trans_eq htarget
  | Or.inr hright =>
      have hzero :=
        Complex.logarithmicPhaseBProcessClippedRightTailBudget_eq_zero_of_rightEndpoint
          hgeometry hright
      have htail :=
        Complex.logarithmicPhaseBProcessClippedLeftTailBudget_le_blockRightTerm
          ht hgeometry hm
      have hzeroLe :
          Complex.logarithmicPhaseBProcessClippedRightTailBudget
              t (b : ℤ) m ≤ 0 :=
        le_of_eq hzero
      have hraw :
          ((4 / 3 : ℝ) +
              Complex.logarithmicPhaseBProcessClippedLeftTailBudget
                t (a : ℤ) m +
              2 * Complex.logarithmicPhaseBProcessRadius t m) +
              Complex.logarithmicPhaseBProcessClippedRightTailBudget
                t (b : ℤ) m ≤
            ((4 / 3 : ℝ) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) + 0 :=
        add_le_add
          (add_le_add
            (add_le_add (le_refl (4 / 3 : ℝ)) htail)
            hcentral)
          hzeroLe
      have hcommute :
          ((4 / 3 : ℝ) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) + 0 =
            ((4 / 3 : ℝ) +
              2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                Complex.logarithmicPhaseBProcessScale t)) +
              2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
        have hdropZero :
            ((4 / 3 : ℝ) +
                2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
                2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                  Complex.logarithmicPhaseBProcessScale t)) + 0 =
              (4 / 3 : ℝ) +
                2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
                2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                  Complex.logarithmicPhaseBProcessScale t) :=
          add_zero _
        have hswap :
            (4 / 3 : ℝ) +
                2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
                2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                  Complex.logarithmicPhaseBProcessScale t) =
              ((4 / 3 : ℝ) +
                2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                  Complex.logarithmicPhaseBProcessScale t)) +
                2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) := by
          calc
            _ = (4 / 3 : ℝ) +
                (2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) +
                  2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                    Complex.logarithmicPhaseBProcessScale t)) := add_assoc _ _ _
            _ = (4 / 3 : ℝ) +
                (2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                    Complex.logarithmicPhaseBProcessScale t) +
                  2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)) :=
              congrArg (fun value : ℝ => (4 / 3 : ℝ) + value) (add_comm _ _)
            _ = ((4 / 3 : ℝ) +
                2 * (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
                  Complex.logarithmicPhaseBProcessScale t)) +
                2 * ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
              (add_assoc _ _ _).symm
        exact Eq.trans hdropZero hswap
      exact hraw.trans_eq hcommute

theorem Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_nonneg
    {t : ℝ} {b : ℕ} (ht : 1 ≤ ‖t‖) :
    0 ≤ Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
      t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
  have hcrossing : (0 : ℝ) ≤ 4 / 3 :=
    div_nonneg (Nat.cast_nonneg 4) (Nat.cast_nonneg 3)
  have hcentral :
      (0 : ℝ) ≤ 2 *
        (Complex.logarithmicPhaseBProcessEndpointSupportRight (b : ℤ) /
          Complex.logarithmicPhaseBProcessScale t) :=
    mul_nonneg (Nat.cast_nonneg 2)
    (div_nonneg
      Complex.logarithmicPhaseBProcessEndpointSupportRight_nonneg
      (Complex.logarithmicPhaseBProcessScale_nonneg t))
  have htail :
      (0 : ℝ) ≤ 2 *
        ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖) :=
    mul_nonneg (Nat.cast_nonneg 2)
    (div_nonneg
      (mul_nonneg (Nat.cast_nonneg b)
        (Complex.logarithmicPhaseBProcessScale_nonneg t))
      (norm_nonneg t))
  exact add_nonneg (add_nonneg hcrossing hcentral) htail

theorem Complex.logarithmicPhaseBProcessUniversalEndpointBudget_le_two_sideMajorant
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessUniversalEndpointBudget
        t (a : ℤ) (b : ℤ) ≤
      2 * Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant
        t (b : ℤ) := by
  unfold Complex.logarithmicPhaseBProcessUniversalEndpointBudget
  exact Finset.sum_le_two_mul_of_card_le_two
    (Complex.logarithmicPhasePoissonBProcessEndpointModes
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget
      t (a : ℤ) (b : ℤ))
    (Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant t (b : ℤ))
    (Complex.logarithmicPhasePoissonBProcessEndpointModes_card_le_two
      ht hgeometry)
    (Complex.logarithmicPhaseBProcessSideEndpointPerModeMajorant_nonneg ht)
    (fun m hm =>
      Complex.logarithmicPhaseBProcessUniversalEndpointPacketBudget_le_sideMajorant
        ht hgeometry hm)

end

end LFunctions
end Boundary

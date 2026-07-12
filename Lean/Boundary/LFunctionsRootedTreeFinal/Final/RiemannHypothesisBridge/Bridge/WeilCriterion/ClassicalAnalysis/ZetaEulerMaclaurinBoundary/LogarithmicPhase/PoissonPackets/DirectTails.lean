import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectBudget

/-!
# Direct logarithmic Poisson tail classification

The non-active family is not treated as one undifferentiated object.  Its
finite part is the complement of the active modes inside the canonical mode
range; its infinite part lies outside that range and is the only portion to
which an inverse-square frequency majorant may be applied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonInRangeInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

def Complex.logarithmicPhasePoissonOutsideRangeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

theorem Complex.logarithmicPhasePoissonInRangeInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonInRangeInactiveBudget t a b := by
  unfold Complex.logarithmicPhasePoissonInRangeInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonOutsideRangeBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonOutsideRangeBudget t a b := by
  unfold Complex.logarithmicPhasePoissonOutsideRangeBudget
  exact tsum_nonneg (fun m => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonActive_subset_modeRange
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonActiveModes t a b : Set ℤ) ⊆
      (Complex.logarithmicPhasePoissonModeRange t a : Set ℤ) := by
  intro m hm
  exact Finset.filter_subset _ _ hm

theorem Complex.logarithmicPhasePoisson_nonactive_eq_inRangeInactive_union_outsideRange
    (t : ℝ) (a b : ℤ) :
    ((Complex.logarithmicPhasePoissonActiveModes t a b : Set ℤ)ᶜ) =
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b : Set ℤ) ∪
        ((Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ) := by
  ext m
  constructor
  · intro hm
    match Classical.em (m ∈ Complex.logarithmicPhasePoissonModeRange t a) with
    | Or.inl hmrange =>
        have hminactive :
            m ∉ Complex.logarithmicPhasePoissonActiveModes t a b := hm
        have hminrange :
            m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b :=
          Finset.mem_sdiff.mpr ⟨hmrange, hminactive⟩
        exact Or.inl hminrange
    | Or.inr hmoutside =>
        exact Or.inr hmoutside
  · intro hm
    match hm with
    | Or.inl hminrange =>
        have hsplit :=
          Finset.mem_sdiff.mp hminrange
        exact hsplit.2
    | Or.inr hmoutside =>
        intro hmactive
        have hmrange :=
          Complex.logarithmicPhasePoissonActive_subset_modeRange
            t a b hmactive
        exact hmoutside hmrange

theorem Complex.logarithmicPhasePoissonInRangeInactiveBudget_le_modeRange_card_mul_max
    (t : ℝ) (a b : ℤ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b →
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤ C) :
    Complex.logarithmicPhasePoissonInRangeInactiveBudget t a b ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) * C := by
  have hpacket_card :
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card ≤
        (Complex.logarithmicPhasePoissonModeRange t a).card :=
    Complex.logarithmicPhasePoissonInRangeInactive_card_le_modeRange_card t a b
  have hsum :
      Complex.logarithmicPhasePoissonInRangeInactiveBudget t a b ≤
        ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) * C :=
    by
      unfold Complex.logarithmicPhasePoissonInRangeInactiveBudget
      have hpointwise :=
        Finset.sum_le_sum
          (fun m hm => hbound m hm)
      have hconstant :
          (∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
            C) =
            ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) * C := by
        exact
          Finset.sum_const_real_eq_card_mul
            (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b) C
      exact hpointwise.trans_eq hconstant
  have hcard_real :
      ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr hpacket_card
  exact le_trans hsum (mul_le_mul_of_nonneg_right hcard_real hC)

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeSecondDerivativeClosedBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.ModeRangeArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.InactiveGeometry

/-!
# Quantitative inactive packets and genuinely far frequency tails

This owner refines the complement of the stationary packet family into the
finite inactive modes inside the canonical frequency interval and the infinite
tail outside that interval.  The distinction is quantitative: finite inactive
modes are estimated by their actual packet norms, while inverse-square decay is
reserved for the genuinely far family.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
    (t : ℝ) (a b : ℤ) (m : ℤ) : ℝ :=
  (Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound t a b /
      (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ)

def Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a},
    Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant t a b m

def Complex.logarithmicPhaseQuantitativeRefinedComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b +
    Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget
  exact tsum_nonneg (fun m => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
      t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
  have hmass :=
    Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound_nonneg
      t a b ha hab
  have hdenominator : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hcoefficient :
      0 ≤ Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
        t a b / (2 * Real.pi) ^ 2 :=
    div_nonneg hmass hdenominator
  have habsolute : (0 : ℝ) ≤ |(m : ℝ)| :=
    abs_nonneg (m : ℝ)
  have hfrequency : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg habsolute (-2 : ℝ)
  exact mul_nonneg hcoefficient hfrequency

theorem Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant_nonneg
      t a b m ha hab)

theorem Complex.logarithmicPhaseQuantitativeRefinedComplementBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRefinedComplementBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedComplementBudget
  exact add_nonneg
    (Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_nonneg t a b)
    (Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget_nonneg
      t a b ha hab)

theorem Complex.summable_logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a} =>
        Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
          t a b m) := by
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
  exact
    (Complex.summable_scaled_integer_frequency_inverse_square
      (Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
        t a b / (2 * Real.pi) ^ 2)).subtype
      {m : ℤ | m ∉ Complex.logarithmicPhasePoissonModeRange t a}

theorem Complex.logarithmicPhasePoissonModeRange_complement_zero_not_mem
    (t : ℝ) (a : ℤ)
    (ha : 1 ≤ a)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    (m : ℤ) ≠ 0 := by
  intro hmzero
  have hlower :=
    Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha
  have hzero :=
    Complex.zero_mem_logarithmicPhasePoissonModeRange_of_lower_le_zero
      t a hlower
  have hmMembership :
      (m : ℤ) ∈ Complex.logarithmicPhasePoissonModeRange t a :=
    Eq.subst
      (motive := fun value : ℤ =>
        value ∈ Complex.logarithmicPhasePoissonModeRange t a)
      hmzero.symm
      hzero
  exact m.property hmMembership

theorem Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (m : {m : ℤ // m ∉ Complex.logarithmicPhasePoissonModeRange t a}) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
        t a b m := by
  have hmNonzero :=
    Complex.logarithmicPhasePoissonModeRange_complement_zero_not_mem
      t a ha m
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
  exact
    Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_closed
      t a b m ha hab hmNonzero

theorem Complex.summable_norm_logarithmicPhaseQuantitativeOutsideRangePacket
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Summable
      (fun m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a} =>
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖) := by
  have hmajorant :=
    Complex.summable_logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
      t a b
  exact Summable.of_nonneg_of_le
    (fun m => norm_nonneg _)
    (fun m =>
      Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_le_closed
        t a b ha hab m)
    hmajorant

theorem Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget t a b ≤
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangePacketBudget
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget
  have hpacketSummable :=
    Complex.summable_norm_logarithmicPhaseQuantitativeOutsideRangePacket
      t a b ha hab
  have hmajorantSummable :=
    Complex.summable_logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
      t a b
  have hpointwise :
      ∀ m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
            t a b m :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_le_closed
        t a b ha hab m
  exact tsum_le_tsum
    hpointwise
    hpacketSummable
    hmajorantSummable

theorem Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_le_card_mul
    (t : ℝ) (a b : ℤ) (C : ℝ)
    (hC : 0 ≤ C)
    (hpacket :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b →
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤ C) :
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) * C := by
  have hcard :
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card ≤
        (Complex.logarithmicPhasePoissonModeRange t a).card :=
    Complex.logarithmicPhasePoissonInRangeInactive_card_le_modeRange_card t a b
  have hfinite :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
        ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) * C := by
    unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
    have hsum := Finset.sum_le_sum (fun m hm => hpacket m hm)
    have hconstant :
        (∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b, C) =
          ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) * C :=
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b) C
    exact le_trans hsum (le_of_eq hconstant)
  have hcardReal :
      ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr hcard
  have hproduct := mul_le_mul_of_nonneg_right hcardReal hC
  exact le_trans hfinite hproduct

theorem Complex.logarithmicPhaseQuantitative_nonactive_eq_inRange_union_outside
    (t : ℝ) (a b : ℤ) :
    ((Complex.logarithmicPhasePoissonActiveModes t a b : Set ℤ)ᶜ) =
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b : Set ℤ) ∪
        ((Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ) := by
  exact
    Complex.logarithmicPhasePoisson_nonactive_eq_inRangeInactive_union_outsideRange
      t a b

theorem Complex.logarithmicPhaseQuantitative_inRange_disjoint_outside
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b : Set ℤ)
      ((Complex.logarithmicPhasePoissonModeRange t a : Set ℤ)ᶜ) := by
  refine Set.disjoint_left.mpr ?_
  intro m hminactive hmoutside
  have hmrange := (Finset.mem_sdiff.mp hminactive).1
  exact hmoutside hmrange

theorem Complex.logarithmicPhaseQuantitativePacket_tsum_eq_modeRange_add_outside
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) :
    (∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  have hsummable :=
    Complex.summable_logarithmicPhaseQuantitativeBlockFourierPacket t a b ha
  let modeSet : Set ℤ :=
    {m : ℤ | m ∈ Complex.logarithmicPhasePoissonModeRange t a}
  have hsplit := tsum_subtype_add_tsum_subtype_compl hsummable modeSet
  have hcomplement :
      modeSetᶜ = {m : ℤ | m ∉ Complex.logarithmicPhasePoissonModeRange t a} := by
    ext m
    rfl
  exact hsplit.symm.trans
    (congrArg₂ (fun first second : ℂ => first + second)
      rfl
      (Eq.subst
        (motive := fun modes : Set ℤ =>
          (∑' m : modes,
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
          (∑' m : {m : ℤ //
              m ∉ Complex.logarithmicPhasePoissonModeRange t a},
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
        hcomplement
        rfl))

theorem Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_tsum_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b := by
  have hmajorantSummable :=
    Complex.summable_logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
      t a b
  have hpointwise :
      ∀ m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeOutsideRangeClosedMajorant
            t a b m :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_le_closed
        t a b ha hab m
  unfold Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget
  exact tsum_of_norm_bounded hmajorantSummable.hasSum hpointwise

end
end LFunctions
end Boundary

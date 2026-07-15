import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepLinearFourierDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeDerivatives
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCrossings

/-!
# Deterministic far-frequency majorants

The Fourier variable in Poisson summation is angular frequency `-2 * π * m`.
This file records its exact norm, names the second-derivative mass of the
quantitative logarithmic amplitude, and constructs deterministic positive and
negative inverse-square tails.  No finite exceptional set is chosen.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhasePoissonAngularFrequency (m : ℤ) : ℝ :=
  -(2 * Real.pi * (m : ℝ))

def Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) : ℝ :=
  (a : ℝ) - 1 / 3

def Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) : ℝ :=
  (b : ℝ) + 1 / 3

def Complex.logarithmicPhaseQuantitativeSecondDerivativeMass
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
      Complex.logarithmicPhaseQuantitativeSupportRight b,
    ‖Complex.logarithmicPhaseQuantitativeAmplitudeSecondDerivative t a b x‖

def Complex.logarithmicPhaseQuantitativeInverseSquareMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b *
    ‖Complex.logarithmicPhasePoissonAngularFrequency m‖⁻¹ ^ 2

def Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
      (2 * Real.pi) ^ 2) *
    |(m : ℝ)| ^ (-2 : ℝ)

def Complex.logarithmicPhasePoissonNegativeTailModes : Set ℤ :=
  {m : ℤ | m < 0}

def Complex.logarithmicPhasePoissonPositiveTailModes : Set ℤ :=
  {m : ℤ | 0 < m}

def Complex.logarithmicPhasePoissonNonzeroModes : Set ℤ :=
  {m : ℤ | m ≠ 0}

def Complex.logarithmicPhaseQuantitativeNegativeTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m

def Complex.logarithmicPhaseQuantitativePositiveTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m

def Complex.logarithmicPhaseQuantitativeNegativeTailPacket
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonNegativeTailModes) : ℂ :=
  Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m.1

def Complex.logarithmicPhaseQuantitativePositiveTailPacket
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) : ℂ :=
  Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m.1

def Complex.logarithmicPhaseQuantitativeNegativeTailMajorant
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonNegativeTailModes) : ℝ :=
  Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m.1

def Complex.logarithmicPhaseQuantitativePositiveTailMajorant
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) : ℝ :=
  Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m.1

theorem Complex.logarithmicPhasePoissonAngularFrequency_zero :
    Complex.logarithmicPhasePoissonAngularFrequency 0 = 0 := by
  unfold Complex.logarithmicPhasePoissonAngularFrequency
  have hcast : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
  calc
    -(2 * Real.pi * ((0 : ℤ) : ℝ)) = -(2 * Real.pi * 0) :=
      congrArg (fun value : ℝ => -(2 * Real.pi * value)) hcast
    _ = -0 := congrArg Neg.neg (mul_zero (2 * Real.pi))
    _ = 0 := neg_zero

theorem Complex.logarithmicPhasePoissonAngularFrequency_ne_zero
    (m : ℤ)
    (hm : m ≠ 0) :
    Complex.logarithmicPhasePoissonAngularFrequency m ≠ 0 := by
  intro hzero
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have htwo : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have htwoPi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero htwo hpi
  have hproduct : (2 * Real.pi) * (m : ℝ) = 0 :=
    neg_eq_zero.mp hzero
  have hmReal : (m : ℝ) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left htwoPi
  have hmZero : m = 0 := Int.cast_eq_zero.mp hmReal
  exact hm hmZero

theorem Complex.norm_logarithmicPhasePoissonAngularFrequency
    (m : ℤ) :
    ‖Complex.logarithmicPhasePoissonAngularFrequency m‖ =
      (2 * Real.pi) * |(m : ℝ)| := by
  unfold Complex.logarithmicPhasePoissonAngularFrequency
  have hnegative : ‖-(2 * Real.pi * (m : ℝ))‖ =
      ‖2 * Real.pi * (m : ℝ)‖ := norm_neg _
  have hproduct : ‖2 * Real.pi * (m : ℝ)‖ =
      ‖2 * Real.pi‖ * ‖(m : ℝ)‖ := norm_mul _ _
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hpiNonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  have htwoPiNonneg : (0 : ℝ) ≤ 2 * Real.pi :=
    mul_nonneg htwoNonneg hpiNonneg
  have htwoPiNorm : ‖(2 * Real.pi : ℝ)‖ = 2 * Real.pi :=
    Real.norm_of_nonneg htwoPiNonneg
  have hmNorm : ‖(m : ℝ)‖ = |(m : ℝ)| := Real.norm_eq_abs (m : ℝ)
  exact
    hnegative.trans
      (hproduct.trans
        (congrArg₂ (fun first second : ℝ => first * second)
          htwoPiNorm hmNorm))

theorem Complex.logarithmicPhaseQuantitativeSupportLeft_le_right
    (a b : ℤ)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSupportLeft a ≤
      Complex.logarithmicPhaseQuantitativeSupportRight b := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 :=
    div_nonneg zero_le_one (Nat.cast_nonneg 3)
  exact le_trans
    (sub_le_self (a : ℝ) hthirdNonneg)
    (le_trans habReal (le_add_of_nonneg_right hthirdNonneg))

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMass
  exact intervalIntegral.integral_nonneg
    (Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab)
    (fun x hx => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeInverseSquareMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeInverseSquareMajorant t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeInverseSquareMajorant
  exact mul_nonneg
    (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_nonneg t a b hab)
    (sq_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  have hmass :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_nonneg t a b hab
  have hdenominator : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hcoefficient :
      0 ≤ Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
        (2 * Real.pi) ^ 2 := div_nonneg hmass hdenominator
  have hpower : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg (abs_nonneg _) _
  exact mul_nonneg hcoefficient hpower

theorem Complex.logarithmicPhasePoissonNegativeTailModes_subset_nonzero :
    Complex.logarithmicPhasePoissonNegativeTailModes ⊆
      Complex.logarithmicPhasePoissonNonzeroModes := by
  intro m hm
  unfold Complex.logarithmicPhasePoissonNegativeTailModes at hm
  unfold Complex.logarithmicPhasePoissonNonzeroModes
  intro hmzero
  have htransport : (0 : ℤ) < 0 :=
    Eq.subst (motive := fun value : ℤ => value < 0) hmzero hm
  exact lt_irrefl 0 htransport

theorem Complex.logarithmicPhasePoissonPositiveTailModes_subset_nonzero :
    Complex.logarithmicPhasePoissonPositiveTailModes ⊆
      Complex.logarithmicPhasePoissonNonzeroModes := by
  intro m hm
  unfold Complex.logarithmicPhasePoissonPositiveTailModes at hm
  unfold Complex.logarithmicPhasePoissonNonzeroModes
  intro hmzero
  have htransport : (0 : ℤ) < 0 :=
    Eq.subst (motive := fun value : ℤ => 0 < value) hmzero hm
  exact lt_irrefl 0 htransport

theorem Complex.logarithmicPhasePoissonNegativePositiveTail_disjoint :
    Disjoint
      Complex.logarithmicPhasePoissonNegativeTailModes
      Complex.logarithmicPhasePoissonPositiveTailModes := by
  exact Set.disjoint_left.mpr
    (fun m hmNegative hmPositive =>
      have hcycle : m < m := lt_trans hmNegative hmPositive
      lt_irrefl m hcycle)

theorem Complex.logarithmicPhasePoissonNegativePositiveTail_union_eq_nonzero :
    Complex.logarithmicPhasePoissonNegativeTailModes ∪
        Complex.logarithmicPhasePoissonPositiveTailModes =
      Complex.logarithmicPhasePoissonNonzeroModes := by
  ext m
  constructor
  · intro hm
    match hm with
    | Or.inl hmNegative =>
        exact Complex.logarithmicPhasePoissonNegativeTailModes_subset_nonzero hmNegative
    | Or.inr hmPositive =>
        exact Complex.logarithmicPhasePoissonPositiveTailModes_subset_nonzero hmPositive
  · intro hm
    unfold Complex.logarithmicPhasePoissonNonzeroModes at hm
    match lt_trichotomy m 0 with
    | Or.inl hmNegative => exact Or.inl hmNegative
    | Or.inr hremaining =>
        match hremaining with
        | Or.inl hmZero => exact False.elim (hm hmZero)
        | Or.inr hmPositive => exact Or.inr hmPositive

theorem Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_on_set
    (t : ℝ) (a b : ℤ) (modes : Set ℤ) :
    Summable
      (fun m : modes =>
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m) := by
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  exact
    Complex.summable_scaled_integer_frequency_inverse_square_on_set
      (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
        (2 * Real.pi) ^ 2)
      modes

theorem Complex.summable_logarithmicPhaseQuantitativeNegativeTailMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : Complex.logarithmicPhasePoissonNegativeTailModes =>
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m) := by
  exact
    Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_on_set
      t a b Complex.logarithmicPhasePoissonNegativeTailModes

theorem Complex.summable_logarithmicPhaseQuantitativePositiveTailMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m) := by
  exact
    Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_on_set
      t a b Complex.logarithmicPhasePoissonPositiveTailModes

theorem Complex.summable_logarithmicPhaseQuantitativeNegativeTailMajorantFunction
    (t : ℝ) (a b : ℤ) :
    Summable
      (Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b) := by
  exact
    Complex.summable_logarithmicPhaseQuantitativeNegativeTailMajorant t a b

theorem Complex.summable_logarithmicPhaseQuantitativePositiveTailMajorantFunction
    (t : ℝ) (a b : ℤ) :
    Summable
      (Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b) := by
  exact
    Complex.summable_logarithmicPhaseQuantitativePositiveTailMajorant t a b

theorem Complex.logarithmicPhaseQuantitativeNegativeTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeNegativeTailBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeNegativeTailBudget
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_nonneg
      t a b m hab)

theorem Complex.logarithmicPhaseQuantitativePositiveTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativePositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativePositiveTailBudget
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_nonneg
      t a b m hab)

theorem Complex.logarithmicPhaseQuantitativeNegativeTailPacket_apply
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonNegativeTailModes) :
    Complex.logarithmicPhaseQuantitativeNegativeTailPacket t a b m =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m.1 := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativePositiveTailPacket_apply
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseQuantitativePositiveTailPacket t a b m =
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m.1 := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativeNegativeTailMajorant_apply
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonNegativeTailModes) :
    Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m =
      Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
        t a b m.1 := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativePositiveTailMajorant_apply
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m =
      Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
        t a b m.1 := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativeNegativeTailPacket_norm_le_majorant
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonNegativeTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m)
    (m : Complex.logarithmicPhasePoissonNegativeTailModes) :
    ‖Complex.logarithmicPhaseQuantitativeNegativeTailPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m := by
  exact hpacket m

theorem Complex.logarithmicPhaseQuantitativePositiveTailPacket_norm_le_majorant
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m)
    (m : Complex.logarithmicPhasePoissonPositiveTailModes) :
    ‖Complex.logarithmicPhaseQuantitativePositiveTailPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m := by
  exact hpacket m

theorem Complex.logarithmicPhaseQuantitativeNegativeTailMajorant_hasSum
    (t : ℝ) (a b : ℤ) :
    HasSum
      (Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b)
      (∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m) := by
  exact
    (Complex.summable_logarithmicPhaseQuantitativeNegativeTailMajorantFunction
      t a b).hasSum

theorem Complex.logarithmicPhaseQuantitativePositiveTailMajorant_hasSum
    (t : ℝ) (a b : ℤ) :
    HasSum
      (Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b)
      (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m) := by
  exact
    (Complex.summable_logarithmicPhaseQuantitativePositiveTailMajorantFunction
      t a b).hasSum

theorem Complex.logarithmicPhaseQuantitativeNegativeTailPacket_tsum_norm_le_majorant_tsum
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonNegativeTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m) :
    ‖∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailPacket t a b m‖ ≤
      ∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m := by
  exact
    tsum_of_norm_bounded
      (Complex.logarithmicPhaseQuantitativeNegativeTailMajorant_hasSum t a b)
      (fun m : Complex.logarithmicPhasePoissonNegativeTailModes =>
        Complex.logarithmicPhaseQuantitativeNegativeTailPacket_norm_le_majorant
          t a b hpacket m)

theorem Complex.logarithmicPhaseQuantitativePositiveTailPacket_tsum_norm_le_majorant_tsum
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailPacket t a b m‖ ≤
      ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m := by
  exact
    tsum_of_norm_bounded
      (Complex.logarithmicPhaseQuantitativePositiveTailMajorant_hasSum t a b)
      (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
        Complex.logarithmicPhaseQuantitativePositiveTailPacket_norm_le_majorant
          t a b hpacket m)

theorem Complex.logarithmicPhaseQuantitativeNegativeTailPacket_tsum_eq
    (t : ℝ) (a b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      ∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailPacket t a b m := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativePositiveTailPacket_tsum_eq
    (t : ℝ) (a b : ℤ) :
    (∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailPacket t a b m := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativeNegativeTailBudget_eq_majorant_tsum
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativeNegativeTailBudget t a b =
      ∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativePositiveTailBudget_eq_majorant_tsum
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativePositiveTailBudget t a b =
      ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m := by
  exact Eq.refl _

theorem Complex.logarithmicPhaseQuantitativeNegativeTail_tsum_norm_le
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonNegativeTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m) :
    ‖∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeNegativeTailBudget t a b := by
  calc
    ‖∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ =
        ‖∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
          Complex.logarithmicPhaseQuantitativeNegativeTailPacket t a b m‖ :=
      congrArg norm
        (Complex.logarithmicPhaseQuantitativeNegativeTailPacket_tsum_eq t a b)
    _ ≤ ∑' m : Complex.logarithmicPhasePoissonNegativeTailModes,
        Complex.logarithmicPhaseQuantitativeNegativeTailMajorant t a b m :=
      Complex.logarithmicPhaseQuantitativeNegativeTailPacket_tsum_norm_le_majorant_tsum
        t a b hpacket
    _ = Complex.logarithmicPhaseQuantitativeNegativeTailBudget t a b :=
      (Complex.logarithmicPhaseQuantitativeNegativeTailBudget_eq_majorant_tsum
        t a b).symm

theorem Complex.logarithmicPhaseQuantitativePositiveTail_tsum_norm_le
    (t : ℝ) (a b : ℤ)
    (hpacket :
      ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
            t a b m) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativePositiveTailBudget t a b := by
  calc
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ =
        ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
          Complex.logarithmicPhaseQuantitativePositiveTailPacket t a b m‖ :=
      congrArg norm
        (Complex.logarithmicPhaseQuantitativePositiveTailPacket_tsum_eq t a b)
    _ ≤ ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativePositiveTailMajorant t a b m :=
      Complex.logarithmicPhaseQuantitativePositiveTailPacket_tsum_norm_le_majorant_tsum
        t a b hpacket
    _ = Complex.logarithmicPhaseQuantitativePositiveTailBudget t a b :=
      (Complex.logarithmicPhaseQuantitativePositiveTailBudget_eq_majorant_tsum
        t a b).symm

end
end LFunctions
end Boundary

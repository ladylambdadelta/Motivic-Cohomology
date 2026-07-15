import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePacketDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeZeroMode

/-!
# Unconditional quantitative Poisson budget

The zero mode is controlled by the direct logarithmic nonstationary estimate.
Every nonzero mode is controlled by the deterministic two-step Fourier-decay
estimate.  Their sum is an unconditional majorant for the exact quantitative
Poisson reconstruction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseQuantitativeZeroModeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  2 / 3 + 2 * ((b : ℝ) / ‖t‖) +
    ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹

def Complex.logarithmicPhaseQuantitativeModeMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  (if m = 0
    then Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b
    else 0) +
  Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m

def Complex.logarithmicPhaseQuantitativeNonzeroTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : ℤ,
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m

def Complex.logarithmicPhaseQuantitativeGlobalBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b +
    Complex.logarithmicPhaseQuantitativeNonzeroTailBudget t a b

theorem Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeZeroModeBudget
  have htwoThirds : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hbNorm : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t
  have hquotient : (0 : ℝ) ≤ (b : ℝ) / ‖t‖ := by
    have hbNonneg : (0 : ℝ) ≤ (b : ℝ) := by
      have hzeroOne : (0 : ℤ) ≤ 1 := zero_le_one
      have haNonneg : (0 : ℤ) ≤ a := le_trans hzeroOne ha
      exact Int.cast_nonneg.mpr (le_trans haNonneg hab)
    exact div_nonneg hbNonneg hbNorm
  have htwice : (0 : ℝ) ≤ 2 * ((b : ℝ) / ‖t‖) :=
    mul_nonneg (Nat.cast_nonneg 2) hquotient
  have hdifference : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) :=
    sub_nonneg.mpr (Int.cast_le.mpr hab)
  have hinverse : (0 : ℝ) ≤ ‖t‖⁻¹ := inv_nonneg.mpr hbNorm
  have hlength : (0 : ℝ) ≤ ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ :=
    mul_nonneg hdifference hinverse
  exact add_nonneg (add_nonneg htwoThirds htwice) hlength

theorem Complex.logarithmicPhaseQuantitativeZeroModeBudget_eq_packet_bound
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b =
      2 / 3 + 2 * ((b : ℝ) / ‖t‖) +
        ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ := by
  rfl

theorem Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b 0‖ ≤
      Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b := by
  exact
    Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le
      t ht htNonneg a b ha hab

theorem Complex.summable_logarithmicPhaseQuantitativeZeroModeDelta
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : ℤ =>
        if m = 0
        then Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b
        else 0) := by
  exact
    (hasSum_ite_eq 0
      (Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b)).summable

theorem Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m) := by
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  exact
    Complex.summable_scaled_integer_frequency_inverse_square
      (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
        (2 * Real.pi) ^ 2)

theorem Complex.summable_logarithmicPhaseQuantitativeModeMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (Complex.logarithmicPhaseQuantitativeModeMajorant t a b) := by
  unfold Complex.logarithmicPhaseQuantitativeModeMajorant
  exact
    (Complex.summable_logarithmicPhaseQuantitativeZeroModeDelta t a b).add
      (Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
        t a b)

theorem Complex.logarithmicPhaseQuantitativeModeMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeModeMajorant t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeModeMajorant
  have hdelta :
      0 ≤ (if m = 0
        then Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b
        else 0) := by
    match Classical.em (m = 0) with
    | Or.inl hm =>
        exact Eq.subst
          (motive := fun value : ℤ =>
            0 ≤ (if value = 0
              then Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b
              else 0))
          hm.symm
          (Complex.logarithmicPhaseQuantitativeZeroModeBudget_nonneg t a b ha hab)
    | Or.inr hm =>
        exact Eq.subst
          (motive := fun value : ℝ => 0 ≤ value)
          (if_neg hm).symm (le_refl (0 : ℝ))
  have hinverse :=
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_nonneg
      t a b m hab
  exact add_nonneg hdelta hinverse

theorem Complex.norm_logarithmicPhaseQuantitativePacket_le_modeMajorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeModeMajorant t a b m := by
  match Classical.em (m = 0) with
  | Or.inl hm =>
      have hzero :=
        Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le_budget
          t ht htNonneg a b ha hab
      have hinverseNonneg :=
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_nonneg
          t a b 0 hab
      have hmajorant :
          Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b ≤
            Complex.logarithmicPhaseQuantitativeModeMajorant t a b 0 := by
        unfold Complex.logarithmicPhaseQuantitativeModeMajorant
        exact le_add_of_nonneg_right hinverseNonneg
      exact Eq.subst
        (motive := fun value : ℤ =>
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b value‖ ≤
            Complex.logarithmicPhaseQuantitativeModeMajorant t a b value)
        hm.symm
        (le_trans hzero hmajorant)
  | Or.inr hm =>
      have hinverse :=
        Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
          t a b m ha hab hm
      have hmajorant :
          Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m =
            Complex.logarithmicPhaseQuantitativeModeMajorant t a b m := by
        unfold Complex.logarithmicPhaseQuantitativeModeMajorant
        exact
          ((congrArg
              (fun value : ℝ => value +
                Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
                  t a b m)
              (if_neg hm)).trans
              (zero_add _)).symm
      exact le_trans hinverse (le_of_eq hmajorant)

theorem Complex.logarithmicPhaseQuantitativeModeMajorant_tsum_eq_globalBudget
    (t : ℝ) (a b : ℤ) :
    (∑' m : ℤ,
      Complex.logarithmicPhaseQuantitativeModeMajorant t a b m) =
      Complex.logarithmicPhaseQuantitativeGlobalBudget t a b := by
  have hdelta :=
    Complex.summable_logarithmicPhaseQuantitativeZeroModeDelta t a b
  have hinverse :=
    Complex.summable_logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
      t a b
  have hadd := tsum_add hdelta hinverse
  have hdeltaTsum :
      (∑' m : ℤ,
        if m = 0
        then Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b
        else 0) =
        Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b :=
    tsum_ite_eq 0 (Complex.logarithmicPhaseQuantitativeZeroModeBudget t a b)
  unfold Complex.logarithmicPhaseQuantitativeGlobalBudget
  unfold Complex.logarithmicPhaseQuantitativeNonzeroTailBudget
  unfold Complex.logarithmicPhaseQuantitativeModeMajorant
  exact hadd.trans
    (congrArg₂ (fun first second : ℝ => first + second)
      hdeltaTsum rfl)

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_globalBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeGlobalBudget t a b := by
  have hmajorant :=
    Complex.summable_logarithmicPhaseQuantitativeModeMajorant t a b
  have hpointwise :
      ∀ m : ℤ,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
          Complex.logarithmicPhaseQuantitativeModeMajorant t a b m :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativePacket_le_modeMajorant
        t ht htNonneg a b m ha hab
  have hnorm :
      ‖∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        ∑' m : ℤ,
          Complex.logarithmicPhaseQuantitativeModeMajorant t a b m :=
    tsum_of_norm_bounded hmajorant.hasSum hpointwise
  exact le_trans hnorm
    (le_of_eq
      (Complex.logarithmicPhaseQuantitativeModeMajorant_tsum_eq_globalBudget
        t a b))

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_globalBudget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhaseQuantitativeGlobalBudget t a b := by
  have hreconstruction :=
    Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_globalBudget
      t ht htNonneg a b ha hab
  exact le_trans
    (le_of_eq (congrArg norm hreconstruction))
    hpacket

end
end LFunctions
end Boundary

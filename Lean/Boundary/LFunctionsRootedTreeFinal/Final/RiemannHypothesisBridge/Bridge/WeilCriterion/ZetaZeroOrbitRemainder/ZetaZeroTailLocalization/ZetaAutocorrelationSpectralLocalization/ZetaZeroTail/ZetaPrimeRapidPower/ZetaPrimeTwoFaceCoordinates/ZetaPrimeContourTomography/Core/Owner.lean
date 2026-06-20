import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Prime contour tomography

This owner layer is split from the public tomography owner.  It preserves the
public theorem names while keeping the proof graph in smaller linear layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Prime contour tomography

This file owns the sampled horizontal contour reconstruction used by completed
boundary descent.  It sits below the prime distribution layer and above descent,
so the remaining contour-tomography proof burden is no longer embedded in the
large descent file.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real part of a complex number plus an embedded real scalar. -/
theorem complex_re_add_ofReal
    (z : ℂ) (r : ℝ) :
    Complex.re (z + (r : ℂ)) = Complex.re z + r := by
  calc
    Complex.re (z + (r : ℂ)) = Complex.re z + Complex.re (r : ℂ) := by
      exact Complex.add_re z (r : ℂ)
    _ = Complex.re z + r := by
      exact congrArg (fun x : ℝ => Complex.re z + x) (Complex.ofReal_re r)

/-- Real part of a negated product by an embedded real scalar. -/
theorem complex_re_ofReal_mul
    (r : ℝ) (z : ℂ) :
    Complex.re ((r : ℂ) * z) = r * Complex.re z := by
  calc
    Complex.re ((r : ℂ) * z) =
        Complex.re (r : ℂ) * Complex.re z - Complex.im (r : ℂ) * Complex.im z := by
      exact Complex.mul_re (r : ℂ) z
    _ = r * Complex.re z - Complex.im (r : ℂ) * Complex.im z := by
      exact congrArg
        (fun x : ℝ => x * Complex.re z - Complex.im (r : ℂ) * Complex.im z)
        (Complex.ofReal_re r)
    _ = r * Complex.re z - 0 * Complex.im z := by
      exact congrArg
        (fun x : ℝ => r * Complex.re z - x * Complex.im z)
        (Complex.ofReal_im r)
    _ = r * Complex.re z - 0 := by
      exact congrArg
        (fun x : ℝ => r * Complex.re z - x)
        (zero_mul (Complex.im z))
    _ = r * Complex.re z := by
      exact sub_zero (r * Complex.re z)

/-- The real part of a negated complex number. -/
theorem complex_re_neg
    (z : ℂ) :
    Complex.re (-z) = -Complex.re z := by
  exact Complex.neg_re z

/-- Real part of a negated product by an embedded real scalar. -/
theorem complex_re_neg_ofReal_mul
    (r : ℝ) (z : ℂ) :
    Complex.re (-((r : ℂ) * z)) = -(r * Complex.re z) := by
  exact
    (complex_re_neg ((r : ℂ) * z)).trans
      (congrArg Neg.neg (complex_re_ofReal_mul r z))

/-- Real subtraction transport: an additive balance is equivalently a subtraction formula
for the left summand. -/
theorem real_left_eq_sub_of_add_eq
    {H T W : ℝ} (h : H + T = W) :
    H = W - T := by
  calc
    H = H + T - T := by
      exact (add_sub_cancel_right H T).symm
    _ = W - T := by
      exact congrArg (fun x : ℝ => x - T) h

/-- Real subtraction transport: a subtraction formula for the left summand gives the
corresponding additive balance. -/
theorem real_add_eq_of_left_eq_sub
    {H T W : ℝ} (h : H = W - T) :
    H + T = W := by
  calc
    H + T = (W - T) + T := by
      exact congrArg (fun x : ℝ => x + T) h
    _ = W := by
      exact sub_add_cancel W T

/-- Transport an additive balance across an equality on its left summand. -/
theorem real_add_eq_of_left_eq_of_add_eq
    {H H' T W : ℝ} (hleft : H = H') (hbalance : H' + T = W) :
    H + T = W := by
  calc
    H + T = H' + T := by
      exact congrArg (fun x : ℝ => x + T) hleft
    _ = W := by
      exact hbalance

/-- Transport a finite-window identity and an additive balance into the residual-tail
subtraction identity. -/
theorem real_residual_eq_tail_of_window_eq_of_add_eq
    {R H T W : ℝ} (hR : R = W) (hbalance : H + T = W) :
    R - H = T := by
  calc
    R - H = W - H := by
      exact congrArg (fun x : ℝ => x - H) hR
    _ = (H + T) - H := by
      exact congrArg (fun x : ℝ => x - H) hbalance.symm
    _ = (H + T) + -H := by
      exact sub_eq_add_neg (H + T) H
    _ = H + (T + -H) := by
      exact add_assoc H T (-H)
    _ = H + (-H + T) := by
      exact congrArg (fun x : ℝ => H + x) (add_comm T (-H))
    _ = (H + -H) + T := by
      exact (add_assoc H (-H) T).symm
    _ = 0 + T := by
      exact congrArg (fun x : ℝ => x + T) (add_right_neg H)
    _ = T := by
      exact zero_add T

/-- A real number splits as a chosen reference plus the corresponding residual. -/
theorem real_eq_reference_add_residual
    (R H : ℝ) :
    R = H + (R - H) := by
  calc
    R = R + 0 := by
      exact (add_zero R).symm
    _ = R + (H + -H) := by
      exact congrArg (fun x : ℝ => R + x) (add_right_neg H).symm
    _ = (R + H) + -H := by
      exact (add_assoc R H (-H)).symm
    _ = (H + R) + -H := by
      exact congrArg (fun x : ℝ => x + -H) (add_comm R H)
    _ = H + (R + -H) := by
      exact add_assoc H R (-H)
    _ = H + (R - H) := by
      exact congrArg (fun x : ℝ => H + x) (sub_eq_add_neg R H).symm

/-- Adding a reference value to the complementary residual recovers the target value. -/
theorem real_reference_add_complementary_residual
    (T C : ℝ) :
    T + (C - T) = C := by
  calc
    T + (C - T) = T + (C + -T) := by
      exact congrArg (fun x : ℝ => T + x) (sub_eq_add_neg C T)
    _ = (T + C) + -T := by
      exact (add_assoc T C (-T)).symm
    _ = (C + T) + -T := by
      exact congrArg (fun x : ℝ => x + -T) (add_comm T C)
    _ = C + (T + -T) := by
      exact add_assoc C T (-T)
    _ = C + 0 := by
      exact congrArg (fun x : ℝ => C + x) (add_right_neg T)
    _ = C := by
      exact add_zero C

/-- Subtracting `T + τ` and then restoring `τ` is the same as subtracting `T`. -/
theorem real_sub_add_tail_cancel
    (C T τ : ℝ) :
    C - (T + τ) + τ = C - T := by
  calc
    C - (T + τ) + τ = C + (-(T + τ) + τ) := by
      exact add_assoc C (-(T + τ)) τ
    _ = C + (-T + (-τ + τ)) := by
      exact congrArg (fun x : ℝ => C + x) (neg_add T τ)
    _ = C + (-T + 0) := by
      exact congrArg (fun x : ℝ => C + (-T + x)) (neg_add_cancel τ)
    _ = C + -T := by
      exact congrArg (fun x : ℝ => C + x) (add_zero (-T))
    _ = C - T := by
      exact (sub_eq_add_neg C T).symm

/-- The finite time-side prime windows converge to the completed time-side prime
distribution. -/
theorem finitePrimeTimeDistributionWindow_tendsto_completed
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) := by
  have hcoordinate :
      ∀ ι : ZetaPrimePowerIndex,
        zetaPrimeOffDiagonalCoordinate ι f =
          completedPrimeTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) := by
    intro ι
    exact
      (completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical
        ι f).symm
  have htime :
      Summable (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTimeDistributionCoordinate ι
          (convolutionAutocorrelation f)) :=
    (summable_zetaPrimeOffDiagonalCoordinate f).congr hcoordinate
  exact ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
    (fun ι : ZetaPrimePowerIndex =>
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))
    htime
    (fun ι hι => by
      have hphysical :
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
            zetaPrimeOffDiagonalCoordinate ι f :=
        completedPrimeTimeDistributionCoordinate_convolutionAutocorrelation_eq_physical ι f
      exact hphysical.trans
        (zetaPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine ι f hι))


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

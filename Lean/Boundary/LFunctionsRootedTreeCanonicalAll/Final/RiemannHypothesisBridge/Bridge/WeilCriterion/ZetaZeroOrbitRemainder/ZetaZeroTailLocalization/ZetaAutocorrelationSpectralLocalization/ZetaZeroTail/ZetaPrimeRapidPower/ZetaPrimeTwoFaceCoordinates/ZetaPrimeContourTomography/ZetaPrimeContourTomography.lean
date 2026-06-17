import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.ZetaPrimeDistributionTransport

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
    C - (T + τ) + τ = C - ((T + τ) - τ) := by
      exact sub_add_eq_sub_sub C (T + τ) τ
    _ = C - T := by
      exact congrArg (fun x : ℝ => C - x) (add_sub_cancel_right T τ)

/-- The coordinatewise contour-transport remainder between the contour-realized and
time-side prime distributions. -/
noncomputable def completedPrimeContourTransportCoordinateRemainder
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f) -
    completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)

/-- The completed contour-transport coordinate-remainder family. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderFamily
    (f : ZetaAdmissibleFunction) : ZetaPrimePowerIndex → ℝ :=
  fun ι => completedPrimeContourTransportCoordinateRemainder ι f

/-- The coordinate-remainder family evaluates to the coordinate remainder. -/
theorem completedPrimeContourTransportCoordinateRemainderFamily_apply
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderFamily f ι =
      completedPrimeContourTransportCoordinateRemainder ι f := by
  rfl

/-- The contour-transport coordinate remainder unfolds to the contour-realized coordinate
minus the time-side coordinate. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainder ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  rfl

/-- The coordinate ledger of the finite prime transport packet.

This is the coordinate-level algebraic presentation of the finite prime residue-defect
packet before the outside-window tail is subtracted. -/
noncomputable def finitePrimeTransportPacketCoordinateLedger
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeContourTransportCoordinateRemainderFamily f ι

/-- The finite prime transport packet coordinate ledger is the coordinate-remainder family. -/
theorem finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeTransportPacketCoordinateLedger ι f =
      completedPrimeContourTransportCoordinateRemainderFamily f ι := by
  rfl

/-- The finite prime transport packet coordinate ledger is the contour-realized coordinate
minus the time-side coordinate. -/
theorem finitePrimeTransportPacketCoordinateLedger_eq_contour_sub_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeTransportPacketCoordinateLedger ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  exact
    (finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
      ι f).trans
      ((completedPrimeContourTransportCoordinateRemainderFamily_apply ι f).trans
        (completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f))

/-- The coordinate shadow of the finite prime horizontal residue packet.

This is the coordinate presentation used by the horizontal residue-shadow window.  Its
coordinate ledger value is the finite prime transport packet coordinate ledger; the
remaining analytic content is the window presentation of the global horizontal residue
shadow, not a top/bottom edge reconstruction. -/
noncomputable def finitePrimeHorizontalResidueCoordinateShadow
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeTransportPacketCoordinateLedger ι f

/-- The finite prime horizontal residue coordinate shadow is the packet coordinate ledger. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadow ι f =
      finitePrimeTransportPacketCoordinateLedger ι f := by
  rfl

/-- The finite prime horizontal residue shadow.

This is the combined top-minus-bottom horizontal prime transport contribution after taking
the real shadow. -/
noncomputable def finitePrimeHorizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (explicitFormulaFamilyHorizontalResidueWindowError
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      (N : ℝ))

/-- The finite prime horizontal residue shadow unfolds to the real part of the combined
horizontal residue-window error. -/
theorem finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) := by
  rfl

/-- The norm of a contour-transport coordinate remainder is bounded by the two coordinate
norms before any height localization estimate is applied. -/
theorem norm_completedPrimeContourTransportCoordinateRemainder_le_contour_add_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ ≤
      ‖completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)‖ +
        ‖completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)‖ := by
  calc
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ =
        ‖completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)‖ := by
      exact congrArg norm
        (completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f)
    _ ≤
        ‖completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ +
          ‖completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ := by
      exact norm_sub_le
        (completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f))
        (completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))

/-- Nongenuine prime-power coordinates carry no contour-transport remainder. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine_ownerTomography
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourTransportCoordinateRemainder ι f = 0 := by
  have hcontour :
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) =
        0 :=
    completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
      ι (convolutionAutocorrelation f) hι
  have htime :
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
        0 :=
    completedPrimeTimeDistributionCoordinate_eq_zero_of_not_isGenuine
      ι (convolutionAutocorrelation f) hι
  calc
    completedPrimeContourTransportCoordinateRemainder ι f =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f
    _ = 0 - completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))
        hcontour
    _ = 0 - 0 := by
      exact congrArg (fun x : ℝ => 0 - x) htime
    _ = 0 := by
      exact sub_self 0

/-- Nongenuine prime-power coordinates carry no finite horizontal residue coordinate shadow.

This is the support statement for the coordinate-shadow family used by the finite-window
tail: only genuine prime-power indices contribute to the window ledger. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    finitePrimeHorizontalResidueCoordinateShadow ι f = 0 := by
  calc
    finitePrimeHorizontalResidueCoordinateShadow ι f =
        finitePrimeTransportPacketCoordinateLedger ι f := by
      exact finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger ι f
    _ = completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily ι f
    _ = completedPrimeContourTransportCoordinateRemainder ι f := by
      exact completedPrimeContourTransportCoordinateRemainderFamily_apply ι f
    _ = 0 := by
      exact
        completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine_ownerTomography
          ι f hι

/-- The finite horizontal residue coordinate-shadow family is supported on genuine
prime-power indices. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_supportedOn_genuine
    (f : ZetaAdmissibleFunction) :
    ∀ ι : ZetaPrimePowerIndex,
      ¬ ZetaPrimePowerIndex.IsGenuine ι →
        finitePrimeHorizontalResidueCoordinateShadow ι f = 0 := by
  intro ι hι
  exact finitePrimeHorizontalResidueCoordinateShadow_eq_zero_of_not_isGenuine
    ι f hι

/-- The finite-window coordinate remainder presentation of contour transport. -/
noncomputable def finitePrimeContourTransportCoordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedPrimeContourTransportCoordinateRemainderFamily f ι

/-- The finite coordinate-remainder window is the finite window sum of the coordinate
remainder family. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_windowSum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourTransportCoordinateRemainderFamily f ι := by
  rfl

/-- The finite coordinate-remainder window is the finite sum of the packet coordinate
ledger. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_windowSum N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f := by
      exact Finset.sum_congr
        rfl
        (fun ι _ =>
          (finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
            ι f).symm)

/-- The finite coordinate-remainder window is the finite window sum of horizontal residue
coordinate shadows. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
        N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f := by
      exact Finset.sum_congr
        rfl
        (fun ι _ =>
          (finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
            ι f).symm)

/-- The finite coordinate-remainder window is the sum of contour-realized coordinates minus
time-side coordinates. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_sum_coordinate_sub
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        (completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)) := by
  rfl

/-- The finite contour-transport remainder between the time-side and contour-realized prime
windows.  This is the honest finite-level difference; it is not asserted to vanish before
passing to the completed contour realization. -/
def finitePrimeContourTransportRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) -
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)

/-- The finite contour-transport remainder is the contour-realized finite window minus the
time-side finite window. -/
theorem finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
  rfl

/-- The finite time-side prime window is the finite sum of its time-side coordinates. -/
theorem finitePrimeTimeDistributionWindow_eq_sum_coordinate
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  rfl

/-- Subtracting two finite coordinate windows is the finite sum of the coordinatewise
differences. -/
theorem real_finset_sum_sub_distrib
    (s : Finset ZetaPrimePowerIndex)
    (u v : ZetaPrimePowerIndex → ℝ) :
    (∑ ι in s, u ι) - (∑ ι in s, v ι) =
      ∑ ι in s, (u ι - v ι) := by
  exact Finset.sum_sub_distrib

/-- Transport finite coordinate-window descriptions into a coordinatewise subtraction
description. -/
theorem real_window_sub_eq_sum_coordinate_sub_of_window_eq
    {A B : ℝ} {s : Finset ZetaPrimePowerIndex}
    {u v : ZetaPrimePowerIndex → ℝ}
    (hA : A = ∑ ι in s, u ι)
    (hB : B = ∑ ι in s, v ι) :
    A - B = ∑ ι in s, (u ι - v ι) := by
  calc
    A - B = (∑ ι in s, u ι) - B := by
      exact congrArg (fun x : ℝ => x - B) hA
    _ = (∑ ι in s, u ι) - (∑ ι in s, v ι) := by
      exact congrArg (fun x : ℝ => (∑ ι in s, u ι) - x) hB
    _ = ∑ ι in s, (u ι - v ι) := by
      exact real_finset_sum_sub_distrib s u v

/-- The difference between the finite contour-realized and time-side prime windows is the
sum of the coordinatewise differences. -/
theorem finitePrimeContourRealized_sub_time_window_eq_sum_coordinate_sub
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N g -
        finitePrimeTimeDistributionWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        (completedPrimeContourRealizedTimeDistributionCoordinate ι g -
          completedPrimeTimeDistributionCoordinate ι g) := by
  exact
    real_window_sub_eq_sum_coordinate_sub_of_window_eq
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate N g)
      (finitePrimeTimeDistributionWindow_eq_sum_coordinate N g)

/-- The finite contour-transport remainder is the finite window sum of the coordinatewise
contour-transport remainders. -/
theorem finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    finitePrimeContourTransportRemainder N f =
        finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) -
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
      exact finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          (completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f) -
            completedPrimeTimeDistributionCoordinate
              ι (convolutionAutocorrelation f)) := by
      exact
        finitePrimeContourRealized_sub_time_window_eq_sum_coordinate_sub
          N (convolutionAutocorrelation f)
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact
        (finitePrimeContourTransportCoordinateRemainderWindow_eq_sum_coordinate_sub
          N f).symm

/-- The finite coordinate-remainder window is the contour-realized window minus the
time-side window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
  exact
    (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm.trans
      (finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f)

/-- The completed boundary difference measured by the finite contour-transport remainder. -/
noncomputable def completedPrimeContourTransportBoundaryDifference
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f) -
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)

/-- Finite contour realization is time-side window plus the named contour-transport
remainder. -/
theorem finitePrimeTimeDistributionWindow_add_contourTransportRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportRemainder N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  let T : ℝ := finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  have hrem : finitePrimeContourTransportRemainder N f = C - T :=
    finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f
  calc
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportRemainder N f =
        T + (C - T) := by
      exact congrArg
        (fun x : ℝ => T + x)
        hrem
    _ = C := by
      exact real_reference_add_complementary_residual T C

/-- Finite contour realization is the time-side window plus the coordinate-remainder
window. -/
theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  calc
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          finitePrimeContourTransportRemainder N f := by
      exact congrArg
        (fun x : ℝ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) + x)
        (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm
    _ =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) := by
      exact finitePrimeTimeDistributionWindow_add_contourTransportRemainder N f

/-- The finite contour-realized window is the time-side window plus the
coordinate-remainder window. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_eq_timeWindow_add_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    (finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f).symm

/-- A real subtraction identity can be transported into a top-minus-bottom real-part
identity. -/
theorem complex_re_sub_eq_real_difference_of_re_eq
    {top bottom : ℂ} {a b : ℝ}
    (htop : Complex.re top = a)
    (hbottom : Complex.re bottom = b) :
    Complex.re (top - bottom) = a - b := by
  calc
    Complex.re (top - bottom) = Complex.re top - Complex.re bottom := by
      exact Complex.sub_re top bottom
    _ = a - Complex.re bottom := by
      exact congrArg (fun x : ℝ => x - Complex.re bottom) htop
    _ = a - b := by
      exact congrArg (fun x : ℝ => a - x) hbottom

/-- The canonical contour family used to compare the finite prime transport remainder with
the horizontal top-minus-bottom contour remainder. -/
def completedPrimeContourTransportFamily : ExplicitFormulaContourFamily where
  c := (1 / 2 : ℝ) + 1
  c_gt_half := by
    exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one

/-- The sampled top horizontal contour integral along the prime transport family. -/
noncomputable def sampledHorizontalTopIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ))

/-- The sampled bottom horizontal contour integral along the prime transport family. -/
noncomputable def sampledHorizontalBottomIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ))

/-- The sampled horizontal top-minus-bottom contour remainder along the prime transport
family. -/
noncomputable def sampledHorizontalDifferenceComplex
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  sampledHorizontalTopIntegral N f -
    sampledHorizontalBottomIntegral N f

/-- The sampled top horizontal integral is the top edge integral of the prime transport
rectangle. -/
theorem sampledHorizontalTopIntegral_eq_topLineIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalTopIntegral N f =
      zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) := by
  rfl

/-- The sampled bottom horizontal integral is the bottom edge integral of the prime
transport rectangle. -/
theorem sampledHorizontalBottomIntegral_eq_bottomLineIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalBottomIntegral N f =
      zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) := by
  rfl

/-- The sampled horizontal difference is the sampled top edge minus the sampled bottom
edge. -/
theorem sampledHorizontalDifferenceComplex_eq_top_sub_bottom
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplex N f =
      sampledHorizontalTopIntegral N f -
        sampledHorizontalBottomIntegral N f := by
  rfl

/-- The top horizontal contour integrand along the prime transport rectangle. -/
noncomputable def primeTransportTopContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) (x : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
    zetaCompletedExplicitFormulaPhi
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormulaTopPath
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2)

/-- The bottom horizontal contour integrand along the prime transport rectangle. -/
noncomputable def primeTransportBottomContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) (x : ℝ) : ℂ :=
  completedZetaNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x) *
    zetaCompletedExplicitFormulaPhi
      (convolutionAutocorrelation f)
      (zetaCompletedExplicitFormulaBottomPath
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) x - 1 / 2)

/-- The top line integral is the interval integral of the named top contour integrand. -/
theorem primeTransportTopLineIntegral_eq_integral_topContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportTopContourIntegrand N f x := by
  rfl

/-- The bottom line integral is the interval integral of the named bottom contour
integrand. -/
theorem primeTransportBottomLineIntegral_eq_integral_bottomContourIntegrand
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportBottomContourIntegrand N f x := by
  rfl

/-- The named top contour-integrand integral along the prime transport rectangle. -/
noncomputable def primeTransportTopContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c),
    primeTransportTopContourIntegrand N f x

/-- The named bottom contour-integrand integral along the prime transport rectangle. -/
noncomputable def primeTransportBottomContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
      (1 - completedPrimeContourTransportFamily.c),
    primeTransportBottomContourIntegrand N f x

/-- The top contour integral unfolds to the interval integral of its named integrand. -/
theorem primeTransportTopContourIntegral_eq_integral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopContourIntegral N f =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportTopContourIntegrand N f x := by
  rfl

/-- The bottom contour integral unfolds to the interval integral of its named integrand. -/
theorem primeTransportBottomContourIntegral_eq_integral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomContourIntegral N f =
      ∫ x in Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c),
        primeTransportBottomContourIntegrand N f x := by
  rfl

/-- The top line integral is the named top contour integral. -/
theorem primeTransportTopLineIntegral_eq_topContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      primeTransportTopContourIntegral N f := by
  exact
    (primeTransportTopLineIntegral_eq_integral_topContourIntegrand N f).trans
      (primeTransportTopContourIntegral_eq_integral N f).symm

/-- The bottom line integral is the named bottom contour integral. -/
theorem primeTransportBottomLineIntegral_eq_bottomContourIntegral
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      primeTransportBottomContourIntegral N f := by
  exact
    (primeTransportBottomLineIntegral_eq_integral_bottomContourIntegrand N f).trans
      (primeTransportBottomContourIntegral_eq_integral N f).symm

/-- One symmetrized complex prime coordinate sampled from a boundary channel. -/
noncomputable def finitePrimeSymmetrizedComplexCoordinate
    (A : ℝ → ℂ) (ι : ZetaPrimePowerIndex) : ℂ :=
  -((ι.weight : ℂ) * (A ι.center + star (A ι.center)))

/-- A finite symmetrized complex prime window sampled from a boundary channel. -/
noncomputable def finitePrimeSymmetrizedComplexWindow
    (N : ℕ) (A : ℝ → ℂ) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    finitePrimeSymmetrizedComplexCoordinate A ι

/-- The symmetrized complex coordinate unfolds to its sampled boundary expression. -/
theorem finitePrimeSymmetrizedComplexCoordinate_eq
    (A : ℝ → ℂ) (ι : ZetaPrimePowerIndex) :
    finitePrimeSymmetrizedComplexCoordinate A ι =
      -((ι.weight : ℂ) * (A ι.center + star (A ι.center))) := by
  rfl

/-- The symmetrized complex window unfolds to the finite sum of its coordinates. -/
theorem finitePrimeSymmetrizedComplexWindow_eq_sum
    (N : ℕ) (A : ℝ → ℂ) :
    finitePrimeSymmetrizedComplexWindow N A =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeSymmetrizedComplexCoordinate A ι := by
  rfl

/-- The finite complex contour-realized prime coordinate is the symmetrized spectral
boundary coordinate. -/
noncomputable def finitePrimeContourRealizedComplexCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexCoordinate
    (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) ι

/-- The finite complex contour-realized prime window before taking its real shadow. -/
noncomputable def finitePrimeContourRealizedComplexWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexWindow N
    (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a)

/-- The contour-realized complex coordinate is the symmetrized spectral coordinate. -/
theorem finitePrimeContourRealizedComplexCoordinate_eq_symmetrizedSpectral
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexCoordinate ι g =
      finitePrimeSymmetrizedComplexCoordinate
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) ι := by
  rfl

/-- The contour-realized complex window is the symmetrized spectral window. -/
theorem finitePrimeContourRealizedComplexWindow_eq_symmetrizedSpectral
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexWindow N g =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) := by
  rfl

/-- The contour-realized complex window is the finite sum of contour-realized complex
coordinates. -/
theorem finitePrimeContourRealizedComplexWindow_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate ι g := by
  rfl

/-- The symmetrized spectral window is the finite sum of contour-realized complex
coordinates. -/
theorem finitePrimeSymmetrizedSpectralWindow_eq_contourRealizedComplexCoordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedSpectralLaplaceTransform g a) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate ι g := by
  exact
    (finitePrimeContourRealizedComplexWindow_eq_symmetrizedSpectral N g).symm.trans
      (finitePrimeContourRealizedComplexWindow_eq_coordinateSum N g)

/-- The finite contour-realized complex coordinate unfolds to the spectral Laplace
coordinate expression. -/
theorem finitePrimeContourRealizedComplexCoordinate_eq
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedComplexCoordinate ι g =
      -((ι.weight : ℂ) *
        (zetaCompletedSpectralLaplaceTransform g ι.center +
          star (zetaCompletedSpectralLaplaceTransform g ι.center))) := by
  rfl

/-- The real part of one finite contour-realized complex coordinate is the corresponding
contour-realized real coordinate. -/
theorem finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexCoordinate ι g) =
      completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  rfl

/-- The real part of the finite complex contour-realized prime window is the finite sum of
contour-realized coordinates. -/
theorem finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexWindow N g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  exact
    (Complex.sum_re
      (fun ι : ZetaPrimePowerIndex =>
        finitePrimeContourRealizedComplexCoordinate ι g)
      (ZetaPrimePowerIndex.window N)).trans
      (Finset.sum_congr
        rfl
        (fun ι _ =>
          finitePrimeContourRealizedComplexCoordinate_re_eq_contourRealizedCoordinate
            ι g))

/-- The real part of the displayed finite contour-realized complex coordinate sum is the
finite sum of contour-realized real coordinates. -/
theorem finitePrimeContourRealizedComplexCoordinateSum_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeContourRealizedComplexCoordinate ι g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate ι g := by
  exact finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum N g

/-- The real part of the finite complex contour-realized prime window is the finite
contour-realized prime window. -/
theorem finitePrimeContourRealizedComplexWindow_re_eq_window
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourRealizedComplexWindow N g) =
      finitePrimeContourRealizedTimeDistributionWindow N g := by
  exact
    (finitePrimeContourRealizedComplexWindow_re_eq_coordinateSum N g).trans
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate N g).symm

/-- The finite complex time-side prime window before taking its real shadow. -/
noncomputable def finitePrimeTimeDistributionComplexCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexCoordinate
    (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) ι

/-- The finite complex time-side prime window before taking its real shadow. -/
noncomputable def finitePrimeTimeDistributionComplexWindow
    (N : ℕ) (g : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeSymmetrizedComplexWindow N
    (fun a : ℝ => zetaCompletedTimeBoundaryValue g a)

/-- The time-side complex coordinate is the symmetrized time-boundary coordinate. -/
theorem finitePrimeTimeDistributionComplexCoordinate_eq_symmetrizedTime
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexCoordinate ι g =
      finitePrimeSymmetrizedComplexCoordinate
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) ι := by
  rfl

/-- The time-side complex window is the symmetrized time-boundary window. -/
theorem finitePrimeTimeDistributionComplexWindow_eq_symmetrizedTime
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexWindow N g =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) := by
  rfl

/-- The time-side complex window is the finite sum of time-side complex coordinates. -/
theorem finitePrimeTimeDistributionComplexWindow_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate ι g := by
  rfl

/-- The symmetrized time-boundary window is the finite sum of time-side complex
coordinates. -/
theorem finitePrimeSymmetrizedTimeWindow_eq_timeComplexCoordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ => zetaCompletedTimeBoundaryValue g a) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate ι g := by
  exact
    (finitePrimeTimeDistributionComplexWindow_eq_symmetrizedTime N g).symm.trans
      (finitePrimeTimeDistributionComplexWindow_eq_coordinateSum N g)

/-- The finite time-side complex coordinate unfolds to the raw time-boundary expression. -/
theorem finitePrimeTimeDistributionComplexCoordinate_eq
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexCoordinate ι g =
      -((ι.weight : ℂ) *
        (zetaCompletedTimeBoundaryValue g ι.center +
          star (zetaCompletedTimeBoundaryValue g ι.center))) := by
  rfl

/-- The real part of one finite time-side complex coordinate is the corresponding
time-side distribution coordinate. -/
theorem finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
    (ι : ZetaPrimePowerIndex) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexCoordinate ι g) =
      completedPrimeTimeDistributionCoordinate ι g := by
  exact complex_re_neg_ofReal_mul
    ι.weight
    (zetaCompletedTimeBoundaryValue g ι.center +
      star (zetaCompletedTimeBoundaryValue g ι.center))

/-- The real part of the finite complex time-side prime window is the finite time-side
coordinate sum. -/
theorem finitePrimeTimeDistributionComplexWindow_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexWindow N g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  exact
    (Complex.sum_re
      (fun ι : ZetaPrimePowerIndex =>
        finitePrimeTimeDistributionComplexCoordinate ι g)
      (ZetaPrimePowerIndex.window N)).trans
      (Finset.sum_congr
        rfl
        (fun ι _ =>
          finitePrimeTimeDistributionComplexCoordinate_re_eq_timeCoordinate
            ι g))

/-- The real part of the displayed finite time-side complex coordinate sum is the finite
sum of time-side real coordinates. -/
theorem finitePrimeTimeDistributionComplexCoordinateSum_re_eq_coordinateSum
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTimeDistributionComplexCoordinate ι g) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  exact finitePrimeTimeDistributionComplexWindow_re_eq_coordinateSum N g

/-- The real part of the sampled horizontal difference is the difference of the real parts
of the sampled top and bottom edges. -/
theorem sampledHorizontalDifferenceComplex_re_eq_top_re_sub_bottom_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      Complex.re (sampledHorizontalTopIntegral N f) -
        Complex.re (sampledHorizontalBottomIntegral N f) := by
  exact
    Eq.trans
      (congrArg Complex.re (sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f))
      (Complex.sub_re (sampledHorizontalTopIntegral N f)
        (sampledHorizontalBottomIntegral N f))

/-- The real shadow of the sampled horizontal top-minus-bottom contour remainder along the
prime transport family. -/
noncomputable def sampledHorizontalDifference
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f)

/-- The sampled horizontal difference is the real part of the complex top-minus-bottom
horizontal contour difference. -/
theorem sampledHorizontalDifference_eq_complex_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      Complex.re (sampledHorizontalDifferenceComplex N f) := by
  rfl

/-- The sampled horizontal difference is the finite horizontal residue shadow. -/
theorem sampledHorizontalDifference_eq_finitePrimeHorizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeHorizontalResidueShadow N f := by
  calc
    sampledHorizontalDifference N f =
        Complex.re (sampledHorizontalDifferenceComplex N f) := by
      exact sampledHorizontalDifference_eq_complex_re N f
    _ =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) := by
      rfl
    _ = finitePrimeHorizontalResidueShadow N f := by
      exact (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
        N f).symm

/-- The residual finite prime tomography error after subtracting the sampled horizontal
contour term from the finite contour-transport remainder. -/
noncomputable def finitePrimeContourTransportTomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportRemainder N f -
    sampledHorizontalDifference N f

/-- The outside-window coordinate-remainder tail. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (∑ ι in ZetaPrimePowerIndex.window N,
    finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadow N f

/-- The norm of the omitted coordinate-remainder tail is the norm of the finite
coordinate-shadow window minus the horizontal residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_norm_eq_window_sub_shadow_norm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ =
      ‖(∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  rfl

/-- Remainder-bound presentation for the omitted coordinate tail.

This is the explicit finite-window bound shape used by the tail estimate: the omitted tail is
controlled by the norm of the window coordinate-shadow remainder against the horizontal
residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_remainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  exact
    le_of_eq
      (completedPrimeContourTransportCoordinateRemainderTail_norm_eq_window_sub_shadow_norm
        N f)

/-- The coordinate-shadow family is supported on genuine prime-power indices, so summing it
over the raw rectangular box is the same as summing it over the genuine prime-power
window. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  exact
    ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
      (fun ι : ZetaPrimePowerIndex =>
        finitePrimeHorizontalResidueCoordinateShadow ι f)
      (finitePrimeHorizontalResidueCoordinateShadow_supportedOn_genuine f)
      N

/-- The omitted coordinate-remainder tail is the supported box remainder: the raw
rectangular coordinate-shadow sum, with nongenuine entries already zero, minus the finite
horizontal residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_eq_coordinateShadow_box_sum_sub_shadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f := by
  have hbox :
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum N f
  calc
    completedPrimeContourTransportCoordinateRemainderTail N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      rfl
    _ =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      exact congrArg
        (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
        hbox.symm

/-- Support reduction for the omitted coordinate-remainder tail.

This theorem contains only the support bookkeeping: nongenuine coordinates vanish, so the
tail can be presented using the raw rectangular box.  The analytic convergence of that
boxed remainder is kept separate below. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_supportReduction
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_eq_coordinateShadow_box_sum_sub_shadow
      N f

/-- Box-remainder-bound presentation for the omitted coordinate tail.

This is the finite-support support reduction plus the explicit remainder bound: the tail
is controlled by the raw rectangular coordinate-shadow remainder after nongenuine
coordinates have been killed. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_boxRemainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  exact
    le_of_eq
      (congrArg norm
        (completedPrimeContourTransportCoordinateRemainderTail_supportReduction
          N f))

/-- The boxed finite-window remainder between the supported coordinate-shadow ledger and
the finite horizontal residue shadow. -/
noncomputable def finitePrimeHorizontalResidueCoordinateShadowBoxRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  (∑ ι in ZetaPrimePowerIndex.box N,
    finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadow N f

/-- The boxed coordinate-shadow remainder unfolds to the raw rectangular coordinate-shadow
sum minus the finite horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f := by
  rfl

/-- The omitted coordinate tail is the boxed finite-window remainder after support
reduction. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_eq_boxRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f := by
  calc
    completedPrimeContourTransportCoordinateRemainderTail N f =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      exact completedPrimeContourTransportCoordinateRemainderTail_supportReduction
        N f
    _ = finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f := by
      exact (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f).symm

/-- Norm-bound form of the boxed finite-window remainder. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_bound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  exact
    le_of_eq
      (congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f))

/-- The boxed coordinate-shadow remainder is the finite tomographic residual. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
      finitePrimeContourTransportTomographicError N f := by
  have hbox :
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum N f
  have hwindow :
      finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
      N f
  have hshadow :
      sampledHorizontalDifference N f =
        finitePrimeHorizontalResidueShadow N f :=
    sampledHorizontalDifference_eq_finitePrimeHorizontalResidueShadow N f
  have hrem :
      finitePrimeContourTransportRemainder N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f :=
    finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f
  calc
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      exact finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      exact congrArg
        (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
        hbox
    _ =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f := by
      exact congrArg
        (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
        hwindow.symm
    _ =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          sampledHorizontalDifference N f := by
      exact congrArg
        (fun x : ℝ => finitePrimeContourTransportCoordinateRemainderWindow N f - x)
        hshadow.symm
    _ =
        finitePrimeContourTransportRemainder N f -
          sampledHorizontalDifference N f := by
      exact congrArg
        (fun x : ℝ => x - sampledHorizontalDifference N f)
        hrem.symm
    _ = finitePrimeContourTransportTomographicError N f := by
      rfl

/-- The finite tomographic residual is bounded by the supported boxed remainder.

This is the pointwise remainder-bound layer after support reduction: the residual error is
identified with the boxed coordinate-shadow remainder, then bounded by its unfolded norm. -/
theorem finitePrimeContourTransportTomographicError_remainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ := by
  calc
    ‖finitePrimeContourTransportTomographicError N f‖ =
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
          N f).symm
    _ ≤
        ‖(∑ ι in ZetaPrimePowerIndex.box N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f‖ := by
      exact finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_bound
        N f

/-- The explicit finite-window tail majorant for the tomographic residual.

This is the norm of the supported boxed coordinate-shadow remainder against the horizontal
residue shadow. -/
noncomputable def finitePrimeContourTransportTomographicErrorRemainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖(∑ ι in ZetaPrimePowerIndex.box N,
      finitePrimeHorizontalResidueCoordinateShadow ι f) -
    finitePrimeHorizontalResidueShadow N f‖

/-- The finite tomographic residual norm is the explicit boxed-remainder majorant. -/
theorem finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ =
      finitePrimeContourTransportTomographicErrorRemainderMajorant N f := by
  calc
    ‖finitePrimeContourTransportTomographicError N f‖ =
        ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
          N f).symm
    _ =
        ‖(∑ ι in ZetaPrimePowerIndex.box N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f‖ := by
      exact congrArg norm
        (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f)
    _ = finitePrimeContourTransportTomographicErrorRemainderMajorant N f := by
      rfl

/-- The completed finite-window contour scalar for the autocorrelation prime channel.

The scalar is owned as the limit of finite contour windows through the completed
finite-window/GNS realization.  It is separated from the raw spectral scalar
`completedPrimeContourRealizedTimeDistributionPairing`; the comparison between the two is
part of the completed finite-window/GNS contour realization theorem below. -/
noncomputable def completedPrimeContourRealizedFiniteWindowPairing
    (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)

/-- The ordered-heart scalar reconstructed by the completed prime two-face/GNS channel.

This is the scalar target of prime contour tomography.  The raw contour presentation is
compared to this scalar only after finite-window/GNS reconstruction. -/
noncomputable def completedPrimeContourGNSHeartScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)

/-- Finite completed prime defect-square expansion in the contour-realization vocabulary.

This is the finite GNS/defect-kernel identity: the positive defect square plus the
two-face cross term is the finite diagonal debt. -/
theorem finitePrimeContourGNS_defectSquareExpansion
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  exact zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    N f

/-- Completed diagonal-debt absorption for the prime two-face/GNS boundary coefficient.

The positive defect kernel absorbs the diagonal debt and leaves the signed two-face boundary
coefficient.  This is the completed form of the finite defect-square expansion. -/
theorem completedPrimeContourGNS_diagonalDebtAbsorption
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f +
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  exact zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
    f

/-- The raw spectral contour scalar is the real part of the completed two-face/GNS boundary
coefficient.

This is the raw spectral/two-face identification in the contour-realization owner file. -/
theorem completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) =
      completedPrimeContourGNSHeartScalar f := by
  have hspectral :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedPrimeContourRealizedTimeDistribution_eq_spectralPrimePowerContribution
      (convolutionAutocorrelation f)
  have hchannel :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeSpectralDistributionPairing
          (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) :=
    completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing f
  have htwoFace :
      completedSpectralPrimeOffDiagonalChannel f =
        completedPrimeContourGNSHeartScalar f := by
    unfold completedPrimeContourGNSHeartScalar
    exact
      completedSpectralPrimeOffDiagonalChannel_eq_completedTwoFaceBoundaryCoefficient_re
        f
  exact hspectral.trans (hchannel.symm.trans htwoFace)

/-- Finite-window expansion and diagonal-debt absorption reach the GNS heart scalar.

This is the finite-window defect-square expansion and diagonal-debt absorption bridge:
it identifies the completed finite-window contour measurement with the two-face/GNS
ordered-heart scalar before the separate raw spectral/two-face comparison is applied. -/
theorem completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  have htime :
      completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) := by
    rfl
  have hphysical :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeOffDiagonalChannel f :=
    completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel f
  have hgns :
      completedPrimeOffDiagonalChannel f =
        completedPrimeContourGNSHeartScalar f := by
    unfold completedPrimeContourGNSHeartScalar
    exact
      completedPrimeOffDiagonalChannel_eq_completedTwoFaceGNSBoundaryCoefficient_re_ownerDistributionTransport
        f
  exact htime.trans (hphysical.trans hgns)

/-- Finite-window contour normalization lands in the GNS/ordered-heart scalar. -/
theorem completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact
    completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar
      f

/-- Finite-window contour normalization agrees with the raw spectral contour scalar. -/
theorem completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralPairing
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact
    (completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar f).trans
      (completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re f).symm

/-- Finite-window expansion and diagonal-debt absorption identify the completed
finite-window contour scalar with the raw spectral contour scalar.

This is the local contour theorem requested by the finite-window/GNS bridge: first the
finite-window scalar is reconstructed as the GNS heart scalar, then the raw spectral
two-face comparison identifies that heart scalar with the raw contour presentation. -/
theorem completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_rawSpectralPairing
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeContourRealizedFiniteWindowPairing_eq_rawSpectralPairing f

/-- The explicit finite-window tail majorant tends to zero.

This is the remaining analytic tail-remainder estimate after support reduction and
finite-window remainder naming. -/
theorem finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
      atTop
      (𝓝 0) := by
  sorry

/-- Norm convergence of the finite tomographic residual remainder.

This is the remaining analytic tail estimate after support reduction and the pointwise
remainder bound: the finite tomographic residual has norm tending to zero. -/
theorem finitePrimeContourTransportTomographicError_norm_tendsto_zero_ownerContourTailEstimate
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖)
      atTop
      (𝓝 0) := by
  have hmajorant :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicErrorRemainderMajorant_tendsto_zero f
  have hfun :
      (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖) =
        (fun N : ℕ =>
          finitePrimeContourTransportTomographicErrorRemainderMajorant N f) := by
    funext N
    exact finitePrimeContourTransportTomographicError_norm_eq_remainderMajorant
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hmajorant

/-- The finite tomographic residual tends to zero.

This is a wrapper over the norm-remainder tail estimate. -/
theorem finitePrimeContourTransportTomographicError_tendsto_zero_ownerContourTailEstimate
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
      atTop
      (𝓝 0) := by
  have hnorm :
      Tendsto
        (fun N : ℕ => ‖finitePrimeContourTransportTomographicError N f‖)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicError_norm_tendsto_zero_ownerContourTailEstimate
      f
  have hbound :
      ∀ᶠ N in atTop,
        ‖finitePrimeContourTransportTomographicError N f‖ ≤
          ‖finitePrimeContourTransportTomographicError N f‖ :=
    Eventually.of_forall (fun _N : ℕ => le_rfl)
  exact squeeze_zero_norm' hbound hnorm

/-- The boxed finite-window coordinate-shadow remainder tends to zero.

This is the boxed-remainder wrapper over the finite tomographic residual estimate. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
      atTop
      (𝓝 0) := by
  have herror :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportTomographicError N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportTomographicError_tendsto_zero_ownerContourTailEstimate
      f
  have hfun :
      (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) =
        (fun N : ℕ => finitePrimeContourTransportTomographicError N f) := by
    funext N
    exact finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    herror

/-- Finite-window box-remainder estimate for the omitted prime coordinate tail.

This is only the unfolded expression form of
`finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero`. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_boxRemainder_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hbox :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero f
  have hfun :
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) := by
    funext N
    exact (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- Finite-window remainder estimate for the omitted prime coordinate tail.

This is the genuine tail estimate: after finite-window contour transport, the omitted
coordinate-remainder tail is a residual finite-window error tending to zero.  The visible
tail-localization theorem below is only a named wrapper over this estimate. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_remainderEstimate_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  have hbox :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_tendsto_zero f
  have hfun :
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) =
        (fun N : ℕ => finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f) := by
    funext N
    exact
      completedPrimeContourTransportCoordinateRemainderTail_eq_boxRemainder
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hbox

/-- The omitted prime coordinate-remainder tail vanishes after finite-window transport.

This is the tail-localization input in invariant tail-object form.  The coordinate
window-minus-shadow statement below is only this theorem transported through the definition
of `completedPrimeContourTransportCoordinateRemainderTail`. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_remainderEstimate_tendsto_zero
      f

/-- The prime coordinate-remainder tail vanishes after finite-window renormalization.

This is the exact window-tail localization input:
`finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`
shows that the finite coordinate-shadow window and the horizontal residue shadow differ by
a term tending to zero. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
      f
  have hfun :
      (fun N : ℕ =>
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) := by
    funext N
    rfl
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htail

/-- The prime coordinate-remainder tail vanishes after finite-window renormalization. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact
    completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero_ownerContourTailLocalization
      f

/-- Completed prime contour normalization-to-heart transport.

The scheduled finite-window contour normalization lands in the two-face/GNS ordered-heart
scalar, and the omitted prime tail vanishes in the same reconstructed channel. -/
theorem completedPrimeContourNormalizationToHeart_transport
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar f,
      completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero f⟩

/-- Prime tail convergence after finite-window contour normalization.

This is the renormalization/tail link in the normalization-to-heart chain. -/
theorem completedPrimeContourPrimeTailRenormalization_tendsto_zero
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero f

/-- Completed finite-window contour normalization lands in the GNS/ordered-heart scalar.

This is the scalar comparison link in the normalization-to-heart chain: after the finite
defect-square expansion, lower-weight diagonal-debt absorption, and prime tail
renormalization, the completed contour measurement is the two-face/GNS heart scalar. -/
theorem completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact completedPrimeContourRealizedFiniteWindowPairing_eq_GNSHeartScalar f

/-- Completed finite-window/GNS contour reconstruction at the ordered-heart scalar.

This is the remaining construction theorem after the finite defect-square expansion,
raw spectral/two-face extraction, and diagonal-debt absorption have been exposed as named
constituents.  It says that the completed finite-window contour measurement reconstructs
the GNS/ordered-heart scalar, and that the omitted prime tail vanishes after the
finite-window transport. -/
theorem completedPrimeFiniteWindowGNSContourReconstruction_twoFaceComparison_and_tailConvergence
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    ⟨completedPrimeFiniteWindowContourNormalization_eq_GNSHeartScalar f,
      completedPrimeContourPrimeTailRenormalization_tendsto_zero f⟩

/-- Completed prime finite-window/GNS contour realization at the two-face coefficient.

This is the construction-level GNS comparison: the completed finite-window contour scalar
is the real two-face/GNS coefficient, and the omitted prime tail vanishes after
finite-window transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison_and_primeTail
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    completedPrimeFiniteWindowGNSContourReconstruction_twoFaceComparison_and_tailConvergence
      f

/-- Completed prime finite-window/GNS coordinate comparison with the two-face coefficient. -/
theorem completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
      completedPrimeContourGNSHeartScalar f := by
  exact
    (completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison_and_primeTail
      f).left

/-- The omitted prime tail vanishes after finite-window/GNS contour transport. -/
theorem completedPrimeFiniteWindowGNSContourRealization_primeTail_tendsto_after_finiteWindowTransport
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
      atTop
      (𝓝 0) := by
  exact completedPrimeContourTransportCoordinateRemainderTail_tendsto_zero f

/-- Completed prime finite-window/GNS contour realization, in construction form.

The completed finite-window/GNS contour scalar realizes the raw spectral contour scalar,
and the omitted coordinate-remainder tails vanish in the same completed realization.  This
is the single construction theorem for the prime finite-window/GNS-to-raw-contour bridge. -/
theorem completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  have hgns :
      completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeFiniteWindowGNSContourRealization_gnsCoordinateComparison f
  have hraw :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        completedPrimeContourGNSHeartScalar f :=
    completedPrimeContourRawSpectralPairing_eq_twoFaceGNSBoundaryCoefficient_re f
  have htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) :=
    completedPrimeFiniteWindowGNSContourRealization_primeTail_tendsto_after_finiteWindowTransport
      f
  exact ⟨hgns.trans hraw.symm, htail⟩

/-- Completed prime finite-window/GNS contour realization.

This compatibility wrapper packages the two split prime owner facts:
`completedPrimeContourFiniteWindowExpansion_diagonalDebtAbsorption_eq_GNSHeartScalar`
and `finitePrimeHorizontalResidueCoordinateShadow_window_sub_residueShadow_tendsto_zero`,
under the historical horizontal-decay owner name consumed by the finite-window transport
layer. -/
theorem completedPrimeContourFiniteWindowGNSRealization_ownerHorizontalDecay
    (f : ZetaAdmissibleFunction) :
    completedPrimeContourRealizedFiniteWindowPairing f =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) ∧
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0) := by
  exact
    completedPrimeFiniteWindowGNSContourRealization_identifies_rawSpectral_and_tail_tendsto
      f

/-- The outside-window coordinate-remainder tail is the part needed to restore the
finite coordinate-shadow window from the horizontal residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_eq_coordinateShadow_sum_sub_shadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f := by
  rfl

/-- The finite complex time-side prime window together with the omitted contour-transport
tail embedded as a complex scalar. -/
noncomputable def finitePrimeTimeDistributionComplexWindowWithTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeTimeDistributionComplexWindow N (convolutionAutocorrelation f) +
    (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)

/-- The finite complex time-side window with tail unfolds to the complex window plus the
embedded real tail. -/
theorem finitePrimeTimeDistributionComplexWindowWithTail_eq_complexWindow_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionComplexWindowWithTail N f =
      finitePrimeTimeDistributionComplexWindow N (convolutionAutocorrelation f) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  rfl

/-- The real part of the finite time-side complex window with tail is the finite time-side
coordinate sum plus the omitted contour-transport tail. -/
theorem finitePrimeTimeDistributionComplexWindowWithTail_re_eq_coordinateSum_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexWindowWithTail N f) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    Eq.trans
      (congrArg Complex.re
        (finitePrimeTimeDistributionComplexWindowWithTail_eq_complexWindow_add_tail
          N f))
      ((complex_re_add_ofReal
        (finitePrimeTimeDistributionComplexWindow N (convolutionAutocorrelation f))
        (completedPrimeContourTransportCoordinateRemainderTail N f)).trans
        (congrArg
          (fun x : ℝ => x + completedPrimeContourTransportCoordinateRemainderTail N f)
          (finitePrimeTimeDistributionComplexWindow_re_eq_coordinateSum
            N (convolutionAutocorrelation f))))

/-- The real part of the finite time-side complex window with tail is the finite
time-side window plus the omitted contour-transport tail. -/
theorem finitePrimeTimeDistributionComplexWindowWithTail_re_eq_window_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeTimeDistributionComplexWindowWithTail N f) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (finitePrimeTimeDistributionComplexWindowWithTail_re_eq_coordinateSum_add_tail
      N f).trans
      (congrArg
        (fun x : ℝ => x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeTimeDistributionWindow_eq_sum_coordinate
          N (convolutionAutocorrelation f)).symm)

/-- The finite residue defect reconstructed by the sampled horizontal contour.

This is the sign-sensitive finite object: the horizontal top-minus-bottom sample
reconstructs the finite coordinate-remainder window after subtracting the omitted
outside-window coordinate tail. -/
noncomputable def finitePrimeContourTransportResidueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportCoordinateRemainderWindow N f -
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The finite residue defect is the coordinate window minus the outside-window tail. -/
theorem finitePrimeContourTransportResidueDefect_eq_window_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportResidueDefect N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The complex representative of the finite residue defect reconstructed by the sampled
horizontal contour. -/
noncomputable def finitePrimeContourTransportComplexResidueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  finitePrimeContourTransportResidueDefect N f

/-- The real part of the complex finite residue defect is the real residue defect. -/
theorem finitePrimeContourTransportComplexResidueDefect_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (finitePrimeContourTransportComplexResidueDefect N f) =
      finitePrimeContourTransportResidueDefect N f := by
  exact Complex.ofReal_re (finitePrimeContourTransportResidueDefect N f)

/-- The imaginary part of the complex finite residue defect vanishes because the defect is
the real residue defect embedded in `ℂ`. -/
theorem finitePrimeContourTransportComplexResidueDefect_im
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (finitePrimeContourTransportComplexResidueDefect N f) = 0 := by
  exact Complex.ofReal_im (finitePrimeContourTransportResidueDefect N f)

/-- The real shadow of the combined horizontal contour sample after restoring the
outside-window coordinate-remainder tail.

This is the analytic side of finite prime contour tomography: a single real-valued
top-minus-bottom horizontal shadow, not a pair of separately reconstructed edge shadows. -/
noncomputable def sampledHorizontalContourTransportShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f) +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The finite contour-transport projection targeted by the sampled-horizontal shadow.

This projection is the finite coordinate-remainder window.  Its identification with the
window-level contour transport remainder is algebraic and is proved separately below. -/
noncomputable def finitePrimeContourTransportProjection
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportCoordinateRemainderWindow N f

/-- The contour-visible finite prime ledger reconstructed by sampled-horizontal tomography.

The ledger is the finite coordinate-remainder projection seen by the combined horizontal
sample.  It is intentionally a single finite object, not a pair of top and bottom edge
objects. -/
noncomputable def finitePrimeContourVisibleLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportProjection N f

/-- The combined contour-ledger evaluator for finite prime tomography.

This evaluator is the owner-level target of the sampled-horizontal reconstruction.  The
horizontal shadow and the finite visible ledger are both compared to this single object,
rather than to separately reconstructed edge contributions. -/
noncomputable def finitePrimeCombinedContourLedgerEvaluator
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourVisibleLedger N f

/-- The sampled-horizontal shadow unfolds to the real part of the combined contour sample
with the omitted coordinate-remainder tail restored. -/
theorem sampledHorizontalContourTransportShadow_eq_complex_re_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The finite contour-transport projection is the finite coordinate-remainder window. -/
theorem finitePrimeContourTransportProjection_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportProjection N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  rfl

/-- The finite coordinate-remainder window is the contour-visible prime ledger. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_visibleLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourVisibleLedger N f := by
  rfl

/-- The finite contour-transport projection is the contour-visible prime ledger. -/
theorem finitePrimeContourTransportProjection_eq_visibleLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportProjection N f =
      finitePrimeContourVisibleLedger N f := by
  rfl

/-- The contour-visible prime ledger is the finite contour-transport projection. -/
theorem finitePrimeContourVisibleLedger_eq_projection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourVisibleLedger N f =
      finitePrimeContourTransportProjection N f := by
  rfl

/-- The contour-visible finite prime ledger is the combined contour-ledger evaluator. -/
theorem finitePrimeContourVisibleLedger_eq_combinedLedgerEvaluator
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourVisibleLedger N f =
      finitePrimeCombinedContourLedgerEvaluator N f := by
  rfl

/-- The combined contour-ledger evaluator is the contour-visible finite prime ledger. -/
theorem finitePrimeCombinedContourLedgerEvaluator_eq_visibleLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeCombinedContourLedgerEvaluator N f =
      finitePrimeContourVisibleLedger N f := by
  rfl

/-- The combined contour-ledger evaluator is the finite contour-transport projection. -/
theorem finitePrimeCombinedContourLedgerEvaluator_eq_projection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeCombinedContourLedgerEvaluator N f =
      finitePrimeContourTransportProjection N f := by
  exact
    (finitePrimeCombinedContourLedgerEvaluator_eq_visibleLedger N f).trans
      (finitePrimeContourVisibleLedger_eq_projection N f)

/-- The finite contour-transport projection is the window-level contour-transport
remainder. -/
theorem finitePrimeContourTransportProjection_eq_contourTransportRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportProjection N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    (finitePrimeContourTransportProjection_eq_coordinateRemainderWindow N f).trans
      (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm

/-- In a complex additive decomposition `E = V + H`, the horizontal summand is the
full residue-window error with the vertical summand subtracted. -/
theorem complex_right_eq_sub_left_of_eq_left_add_right
    {E V H : ℂ} (h : E = V + H) :
    H = E - V := by
  calc
    H = 0 + H := by
      exact (zero_add H).symm
    _ = (-V + V) + H := by
      exact congrArg (fun x : ℂ => x + H) (neg_add_cancel V).symm
    _ = -V + (V + H) := by
      exact add_assoc (-V) V H
    _ = -V + E := by
      exact congrArg (fun x : ℂ => -V + x) h.symm
    _ = E + -V := by
      exact add_comm (-V) E
    _ = E - V := by
      exact (sub_eq_add_neg E V).symm

/-- The horizontal residue-window error is the full finite rectangle residue-window error
after subtracting the vertical residue-window error. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
    (g : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyHorizontalResidueWindowError g F T =
      explicitFormulaFamilyResidueWindowError g F T -
        explicitFormulaFamilyVerticalResidueWindowError g F T := by
  exact
    complex_right_eq_sub_left_of_eq_left_add_right
      (explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal g F T)

/-- The sampled horizontal difference is the horizontal residue-window error for the
prime transport rectangle. -/
theorem sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplex N f =
      explicitFormulaFamilyHorizontalResidueWindowError
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        (N : ℝ) := by
  rfl

/-- The prime transport combined residue-window shadow: the real part of the full
finite rectangle residue-window error after removing the vertical residue-window error,
with the coordinate-remainder tail restored. -/
noncomputable def primeTransportCombinedResidueWindowShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
      (explicitFormulaFamilyResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ) -
        explicitFormulaFamilyVerticalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The explicit horizontal sample with restored tail is the prime transport combined
residue-window shadow. -/
theorem combinedHorizontalSampleWithTail_eq_residueWindowShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      primeTransportCombinedResidueWindowShadow N f := by
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError N f)
    _ =
        Complex.re
          (explicitFormulaFamilyResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ) -
            explicitFormulaFamilyVerticalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ))
    _ = primeTransportCombinedResidueWindowShadow N f := by
      rfl

/-- The combined residue-window shadow is the real horizontal residue-window error with
the coordinate-remainder tail restored. -/
theorem primeTransportCombinedResidueWindowShadow_eq_horizontalResidueWindowError_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportCombinedResidueWindowShadow N f =
      Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    primeTransportCombinedResidueWindowShadow N f =
        Complex.re
            (explicitFormulaFamilyResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ) -
              explicitFormulaFamilyVerticalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      rfl
    _ =
        Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)).symm

/-- The horizontal residue-window error is the sampled horizontal difference for the prime
transport family, after taking real parts. -/
theorem finitePrimeHorizontalResidueWindowError_re_eq_sampledHorizontalDifferenceComplex_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      Complex.re (sampledHorizontalDifferenceComplex N f) := by
  exact congrArg Complex.re
    (sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError N f).symm

/-- The finite prime transport packet, with its analytic horizontal residue-shadow
presentation and its algebraic residue-defect and visible-ledger presentations.

This is a concrete packet of values, not an assumption interface: each field is populated
from the finite prime transport definitions below. -/
structure FinitePrimeTransportPacket where
  horizontalResidueShadow : ℝ
  residueDefectLedger : ℝ
  visiblePrimeLedger : ℝ
  coordinateRemainderTail : ℝ

/-- The finite prime residue-defect ledger.

This is the owner ledger for the finite prime residue defect: the finite
coordinate-remainder window with the outside-window coordinate-remainder tail subtracted. -/
noncomputable def finitePrimeResidueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportResidueDefect N f

/-- The finite prime transport packet attached to the prime transport family and cutoff. -/
noncomputable def finitePrimeTransportPacket
    (N : ℕ) (f : ZetaAdmissibleFunction) : FinitePrimeTransportPacket where
  horizontalResidueShadow := finitePrimeHorizontalResidueShadow N f
  residueDefectLedger := finitePrimeResidueDefectLedger N f
  visiblePrimeLedger := finitePrimeContourVisibleLedger N f
  coordinateRemainderTail := completedPrimeContourTransportCoordinateRemainderTail N f

/-- The finite prime transport packet's analytic presentation is the horizontal residue
shadow. -/
theorem finitePrimeTransportPacket_horizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).horizontalResidueShadow =
      finitePrimeHorizontalResidueShadow N f := by
  rfl

/-- The finite prime transport packet's algebraic presentation is the residue-defect
ledger. -/
theorem finitePrimeTransportPacket_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).residueDefectLedger =
      finitePrimeResidueDefectLedger N f := by
  rfl

/-- The finite prime transport packet's visible presentation is the visible prime ledger. -/
theorem finitePrimeTransportPacket_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).visiblePrimeLedger =
      finitePrimeContourVisibleLedger N f := by
  rfl

/-- The finite prime transport packet's tail field is the outside-window coordinate-remainder
tail. -/
theorem finitePrimeTransportPacket_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).coordinateRemainderTail =
      completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The finite prime residue-defect ledger is the named finite contour-transport residue
defect. -/
theorem finitePrimeResidueDefectLedger_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      finitePrimeContourTransportResidueDefect N f := by
  rfl

/-- The finite prime residue-defect ledger is the coordinate-remainder window with the
outside-window coordinate-remainder tail subtracted. -/
theorem finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (finitePrimeResidueDefectLedger_eq_residueDefect N f).trans
      (finitePrimeContourTransportResidueDefect_eq_window_sub_tail N f)

/-- The finite prime residue-defect ledger is the packet coordinate-ledger window with the
outside-window tail subtracted. -/
theorem finitePrimeResidueDefectLedger_eq_packetCoordinateLedger_sum_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeResidueDefectLedger N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
          N f)

/-- Restoring the outside-window tail to the finite prime residue-defect ledger recovers the
finite coordinate-remainder ledger. -/
theorem finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        (finitePrimeContourTransportCoordinateRemainderWindow N f -
            completedPrimeContourTransportCoordinateRemainderTail N f) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f)
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact sub_add_cancel
        (finitePrimeContourTransportCoordinateRemainderWindow N f)
        (completedPrimeContourTransportCoordinateRemainderTail N f)

/-- Restoring the outside-window tail to the finite prime residue-defect ledger recovers the
visible finite prime ledger. -/
theorem finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow
      N f).trans
      (finitePrimeContourTransportCoordinateRemainderWindow_eq_visibleLedger N f)

/-- In the finite prime transport packet, the algebraic residue-defect ledger with the tail
restored is the visible prime ledger. -/
theorem finitePrimeTransportPacket_residueDefectLedger_add_tail_eq_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).residueDefectLedger +
        (finitePrimeTransportPacket N f).coordinateRemainderTail =
      (finitePrimeTransportPacket N f).visiblePrimeLedger := by
  calc
    (finitePrimeTransportPacket N f).residueDefectLedger +
        (finitePrimeTransportPacket N f).coordinateRemainderTail =
        finitePrimeResidueDefectLedger N f +
          (finitePrimeTransportPacket N f).coordinateRemainderTail := by
      exact congrArg
        (fun x : ℝ =>
          x + (finitePrimeTransportPacket N f).coordinateRemainderTail)
        (finitePrimeTransportPacket_residueDefectLedger N f)
    _ =
        finitePrimeResidueDefectLedger N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ => finitePrimeResidueDefectLedger N f + x)
        (finitePrimeTransportPacket_coordinateRemainderTail N f)
    _ = finitePrimeContourVisibleLedger N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger N f
    _ = (finitePrimeTransportPacket N f).visiblePrimeLedger := by
      exact (finitePrimeTransportPacket_visiblePrimeLedger N f).symm

/-- The full finite horizontal coordinate-shadow ledger visible at cutoff `N`.

This is the full horizontal residue shadow with the omitted outside-window tail restored.
The partition theorem below identifies this full ledger with the finite window of
coordinate shadows. -/
noncomputable def finitePrimeHorizontalFullCoordinateShadowLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeHorizontalResidueShadow N f +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The full finite horizontal coordinate-shadow ledger is the window sum of coordinate
shadows. -/
theorem finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalFullCoordinateShadowLedger N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  calc
    finitePrimeHorizontalFullCoordinateShadowLedger N f =
        finitePrimeHorizontalResidueShadow N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      rfl
    _ =
        finitePrimeHorizontalResidueShadow N f +
          ((∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
            finitePrimeHorizontalResidueShadow N f) := by
      exact congrArg
        (fun x : ℝ => finitePrimeHorizontalResidueShadow N f + x)
        (completedPrimeContourTransportCoordinateRemainderTail_eq_coordinateShadow_sum_sub_shadow
          N f)
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f := by
      exact
        real_reference_add_complementary_residual
          (finitePrimeHorizontalResidueShadow N f)
          (∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeHorizontalResidueCoordinateShadow ι f)

/-- The finite horizontal residue shadow plus the omitted outside-window tail is the full
coordinate-shadow ledger. -/
theorem finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeHorizontalFullCoordinateShadowLedger N f := by
  rfl

/-- The finite horizontal residue shadow is the full coordinate-shadow ledger after
subtracting the omitted outside-window tail. -/
theorem finitePrimeHorizontalResidueShadow_eq_fullCoordinateShadowLedger_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeHorizontalFullCoordinateShadowLedger N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    real_left_eq_sub_of_add_eq
      (finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
        N f)

/-- The finite horizontal residue shadow plus the omitted outside-window tail is the window
sum of coordinate shadows. -/
theorem finitePrimeHorizontalResidueShadow_add_tail_eq_sum_coordinateShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  exact
    (finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
      N f).trans
      (finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow N f)

/-- Finite prime horizontal residue shadow in coordinate-shadow window presentation.

The combined horizontal residue shadow for the prime transport family is the finite
coordinate-shadow window with the outside-window tail subtracted.  This is the single
analytic finite-prime packet-normalization root in this lane. -/
theorem finitePrimeHorizontalResidueShadow_eq_sum_coordinateShadow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeHorizontalResidueShadow N f =
        finitePrimeHorizontalFullCoordinateShadowLedger N f -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeHorizontalResidueShadow_eq_fullCoordinateShadowLedger_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow N f)

/-- Prime transport horizontal residue shadow in packet coordinate-ledger presentation.

The coordinate-shadow presentation of the horizontal residue shadow is the packet
coordinate-ledger presentation. -/
theorem primeTransportHorizontalResidueShadow_eq_packetCoordinateLedger_sum_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeHorizontalResidueShadow_eq_sum_coordinateShadow_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (Finset.sum_congr
          rfl
          (fun ι _ =>
            finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
              ι f))

/-- Prime transport horizontal residue normalization.

The combined horizontal residue shadow for the prime transport family realizes the finite
prime residue-defect ledger. -/
theorem primeTransportHorizontalResidueShadow_realizes_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeResidueDefectLedger N f := by
  exact
    (primeTransportHorizontalResidueShadow_eq_packetCoordinateLedger_sum_sub_tail
      N f).trans
      (finitePrimeResidueDefectLedger_eq_packetCoordinateLedger_sum_sub_tail N f).symm

/-- Combined finite-prime horizontal residue normalization.

The finite prime horizontal residue shadow realizes the finite prime residue-defect
ledger. -/
theorem finitePrimeHorizontalResidueShadow_eq_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeResidueDefectLedger N f := by
  exact primeTransportHorizontalResidueShadow_realizes_residueDefectLedger N f

/-- Restoring the outside-window tail to the realized horizontal residue shadow gives the
visible finite prime ledger. -/
theorem primeTransportHorizontalResidueShadow_add_tail_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  calc
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeResidueDefectLedger N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalResidueShadow_eq_residueDefectLedger N f)
    _ = finitePrimeContourVisibleLedger N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger N f

/-- Prime residue-defect normalization.

The real shadow of the combined horizontal prime residue-window contribution is the finite
prime residue-defect ledger. -/
theorem finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeResidueDefectLedger N f := by
  exact
    (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
      N f).symm.trans
      (finitePrimeHorizontalResidueShadow_eq_residueDefectLedger N f)

/-- Prime residue-defect normalization in exposed finite-window form.

The real shadow of the combined horizontal prime residue-window contribution is the
finite coordinate-remainder window after subtracting the outside-window tail. -/
theorem finitePrimeHorizontalResidueWindow_realShadow_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
      N f).trans
      (finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f)

/-- Prime sampled-horizontal real-shadow normalization.

The real shadow of the combined sampled horizontal prime transport contribution is the
finite residue defect ledger, transported to the historical residue-defect name. -/
theorem finitePrimeSampledHorizontalRealShadow_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportResidueDefect N f := by
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) := by
      exact
        (finitePrimeHorizontalResidueWindowError_re_eq_sampledHorizontalDifferenceComplex_re
          N f).symm
    _ = finitePrimeResidueDefectLedger N f := by
      exact finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger N f
    _ = finitePrimeContourTransportResidueDefect N f := by
      exact finitePrimeResidueDefectLedger_eq_residueDefect N f

/-- Prime residue-defect normalization in horizontal residue-window form.

The real shadow of the combined horizontal residue-window contribution is the finite
residue defect. -/
theorem finitePrimeHorizontalResidueWindowError_re_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeContourTransportResidueDefect N f := by
  exact
    (finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
      N f).trans
      (finitePrimeResidueDefectLedger_eq_residueDefect N f)

/-- Restoring the coordinate-remainder tail to the horizontal residue-window real shadow
recovers the finite coordinate-remainder window. -/
theorem finitePrimeHorizontalResidueWindowError_re_add_tail_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeContourTransportResidueDefect N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalResidueWindowError_re_eq_residueDefect N f)
    _ = finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeResidueDefectLedger_eq_residueDefect N f).symm
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow N f

/-- Combined finite rectangle residue-window tomography for the prime transport family,
after consuming the scheduled finite rectangle residue equality.

The residue-window shadow produced by the scheduled finite rectangle residue layer is the
finite coordinate-remainder window.  This is prime-window accounting: it matches the
residue-window presentation to the coordinate remainder ledger, with the tail kept
visible. -/
theorem finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow_of_scheduledRectangleResidueEquality
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (_hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    (primeTransportCombinedResidueWindowShadow_eq_horizontalResidueWindowError_add_tail
      N f).trans
      (finitePrimeHorizontalResidueWindowError_re_add_tail_eq_coordinateRemainderWindow
        N f)

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

The scheduled package and its finite-rectangle residue convergence are explicit inputs;
this theorem does not choose a contour schedule. -/
theorem finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow_of_scheduledRectangleResidueEquality
      N f h hfinite

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

This is the prime-window accounting bridge after the scheduled finite rectangle residue
equality has supplied the residue-window objects: it identifies the combined
residue-window shadow with the finite contour-visible prime ledger. -/
theorem finitePrimeTransportWindowAccounting_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow
      N f h hfinite).trans
      (finitePrimeContourTransportCoordinateRemainderWindow_eq_visibleLedger N f)

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

After the finite Cauchy/residue decomposition has isolated the full residue-window error
and the vertical residue-window error, their combined horizontal real shadow with the
coordinate-remainder tail restored is the contour-visible finite prime ledger. -/
theorem primeTransportCombinedResidueWindowShadow_eq_visiblePrimeLedger_ownerContourResidue_root
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact finitePrimeTransportWindowAccounting_realizes_visiblePrimeLedger
    N f h hfinite

/-- Explicit scheduled contour measurement reconstructs the finite visible prime ledger.

The scheduled contour package is the finite-window measurement channel.  The theorem
identifies the reconstructed finite GNS/contour ledger, not coordinatewise data attached to
a particular schedule. -/
theorem explicitScheduledPrimeContourMeasurement_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    primeTransportCombinedResidueWindowShadow_eq_visiblePrimeLedger_ownerContourResidue_root
      N f h hfinite

/-- Combined finite-prime packet comparison for the prime transport rectangle.

The top-minus-bottom horizontal contour sample, after taking its real shadow and restoring
the outside-window coordinate-remainder tail, is the contour-visible finite prime ledger.
This is routed through the finite prime horizontal residue-shadow realization; no
individual horizontal edge is reconstructed here. -/
theorem combinedHorizontalSampleWithTail_eq_visiblePrimeLedger_ownerContourResidue_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeHorizontalResidueShadow N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      have hshadow :
          Complex.re (sampledHorizontalDifferenceComplex N f) =
            finitePrimeHorizontalResidueShadow N f := by
        calc
          Complex.re (sampledHorizontalDifferenceComplex N f) =
              Complex.re
                (explicitFormulaFamilyHorizontalResidueWindowError
                  (convolutionAutocorrelation f)
                  completedPrimeContourTransportFamily
                  (N : ℝ)) := by
            exact
              (finitePrimeHorizontalResidueWindowError_re_eq_sampledHorizontalDifferenceComplex_re
                N f).symm
          _ = finitePrimeHorizontalResidueShadow N f := by
            exact
              (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
                N f).symm
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        hshadow
    _ = finitePrimeContourVisibleLedger N f := by
      exact
        primeTransportHorizontalResidueShadow_add_tail_realizes_visiblePrimeLedger
          N f

/-- The combined horizontal contour shadow realizes the contour-visible finite prime ledger.

This is the owner analytic input for finite prime contour tomography: the top-minus-bottom
horizontal sample, after restoring the outside-window coordinate-remainder tail, is the
single contour-visible ledger.  It does not assert reconstruction of either horizontal
edge separately. -/
theorem combinedHorizontalContourShadow_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_complex_re_add_tail N f).trans
      (combinedHorizontalSampleWithTail_eq_visiblePrimeLedger_ownerContourResidue_root
        N f)

/-- Analytic sampled-horizontal ledger reconstruction root.

The combined horizontal contour shadow reconstructs the contour-visible finite prime
ledger.  This is the single contour-visible tomography input; it does not split into
individual edge reconstructions. -/
theorem sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact combinedHorizontalContourShadow_realizes_visiblePrimeLedger N f

/-- The sampled-horizontal shadow evaluates to the combined contour-ledger evaluator. -/
theorem sampledHorizontalContourTransportShadow_eq_combinedLedgerEvaluator_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeCombinedContourLedgerEvaluator N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
      N f).trans
      (finitePrimeContourVisibleLedger_eq_combinedLedgerEvaluator N f)

/-- Analytic sampled-horizontal tomography root in shadow/projection form.

The combined horizontal contour shadow reconstructs the finite contour-transport
projection.  This is the contour-shift/residue input for this lane; it intentionally does
not assert separate top-edge or bottom-edge reconstruction statements. -/
theorem sampledHorizontalContourTransportShadow_eq_finiteProjection_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourTransportProjection N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
      N f).trans
      (finitePrimeContourVisibleLedger_eq_projection N f)

/-- The combined sampled-horizontal contour-transport reconstruction map.

This is the real shadow of the top-minus-bottom horizontal contour sample with the
outside-window coordinate-remainder tail restored.  It is the tomography object owned by
this file; it deliberately does not split into separate top-edge and bottom-edge
reconstruction statements. -/
noncomputable def sampledHorizontalContourTransportReconstruction
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f) +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The sampled-horizontal reconstruction map unfolds to the real top-minus-bottom sample
with the omitted coordinate-remainder tail restored. -/
theorem sampledHorizontalContourTransportReconstruction_eq_complex_re_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The reconstruction map is the sampled-horizontal contour-transport shadow. -/
theorem sampledHorizontalContourTransportReconstruction_eq_shadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      sampledHorizontalContourTransportShadow N f := by
  rfl

/-- Analytic sampled-horizontal tomography root in owner-map form.

The single combined sampled-horizontal reconstruction map recovers the finite
contour-transport remainder.  This is the contour-shift/residue input for the prime
finite-edge tomography lane; no individual edge reconstruction is asserted. -/
theorem sampledHorizontalContourTransportReconstruction_eq_contourTransportRemainder_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      finitePrimeContourTransportRemainder N f := by
  calc
    sampledHorizontalContourTransportReconstruction N f =
        sampledHorizontalContourTransportShadow N f := by
      exact sampledHorizontalContourTransportReconstruction_eq_shadow N f
    _ = finitePrimeContourTransportProjection N f := by
      exact sampledHorizontalContourTransportShadow_eq_finiteProjection_ownerTomography_root
        N f
    _ = finitePrimeContourTransportRemainder N f := by
      exact finitePrimeContourTransportProjection_eq_contourTransportRemainder N f

/-- The top and bottom real edge reconstructions imply the sampled-horizontal real
contour-transport reconstruction. -/
theorem sampledHorizontalDifferenceComplex_re_add_tail_eq_contourTransportRemainder_of_edgeRealReconstructions
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (htop :
      Complex.re (sampledHorizontalTopIntegral N f) =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
    (hbottom :
      Complex.re (sampledHorizontalBottomIntegral N f) =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          completedPrimeContourTransportCoordinateRemainderTail N f) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  let T : ℝ :=
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let τ : ℝ :=
    completedPrimeContourTransportCoordinateRemainderTail N f
  have hre :
      Complex.re (sampledHorizontalDifferenceComplex N f) =
        C - (T + τ) := by
    exact complex_re_sub_eq_real_difference_of_re_eq htop hbottom
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) + τ =
        (C - (T + τ)) + τ := by
      exact congrArg (fun x : ℝ => x + τ) hre
    _ = C - T := by
      exact real_sub_add_tail_cancel C T τ
    _ = finitePrimeContourTransportRemainder N f := by
      exact (finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f).symm

/-- Analytic sampled-horizontal tomography root in real-shadow form.

The finite top-minus-bottom horizontal contour sample reconstructs the finite
contour-transport remainder after the omitted coordinate-remainder tail is restored.
This is the actual analytic reconstruction input used downstream; it does not assert
separate pointwise reconstructions of the top and bottom edges. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    (sampledHorizontalContourTransportReconstruction_eq_complex_re_add_tail
      N f).symm.trans
      (sampledHorizontalContourTransportReconstruction_eq_contourTransportRemainder_ownerTomography_root
        N f)

/-- Real-part sampled contour tomography reconstructs the finite contour-transport
remainder after restoring the omitted coordinate-remainder tail. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_root
      N f

/-- Real-part sampled contour tomography reconstructs the coordinate-remainder window after
adding the omitted coordinate-remainder tail.

This is the finite-window form of the sampled-horizontal reconstruction. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    real_add_eq_of_left_eq_of_add_eq
      rfl
      ((sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_core
        N f).trans
        (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f))

/-- Real-part sampled contour tomography reconstructs the finite residue defect.

This is the subtraction form obtained from additive window reconstruction. -/
theorem sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportResidueDefect N f := by
  exact
    (real_left_eq_sub_of_add_eq
      (sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography_core
        N f)).trans
      (finitePrimeContourTransportResidueDefect_eq_window_sub_tail N f).symm

/-- The Hermitian-reflection spectral parameter is involutive. -/
theorem complex_neg_star_neg_star
    (z : ℂ) :
    -star (-star z) = z := by
  calc
    -star (-star z) = -(-star (star z)) := by
      exact congrArg Neg.neg (map_neg star (star z))
    _ = -(-z) := by
      exact congrArg (fun w : ℂ => -(-w)) (star_star z)
    _ = z := by
      exact neg_neg z

/-- Conjugating a Hermitian product reverses its two factors. -/
theorem complex_star_mul_star_right_comm
    (A B : ℂ) :
    star (A * star B) = B * star A := by
  calc
    star (A * star B) = star A * star (star B) := by
      exact map_mul star A (star B)
    _ = star A * B := by
      exact congrArg (fun w : ℂ => star A * w) (star_star B)
    _ = B * star A := by
      exact mul_comm (star A) B

/-- Pointwise transport from the spectral Laplace transform notation to the `Φ` notation. -/
theorem zetaCompletedSpectralLaplaceTransform_eq_explicitFormulaPhi
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedSpectralLaplaceTransform f z =
      zetaCompletedExplicitFormulaPhi f z := by
  exact
    (congrFun
      (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
      z).symm

/-- Pointwise transport from the `Φ` notation to the spectral Laplace transform notation. -/
theorem zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform_apply
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi f z =
      zetaCompletedSpectralLaplaceTransform f z := by
  exact
    congrFun
      (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform f)
      z

/-- The completed spectral Laplace transform of an autocorrelation factors into the
Hermitian product of the seed transform at paired spectral points. -/
theorem zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_factorization_ownerTomography
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) z =
      zetaCompletedSpectralLaplaceTransform f z *
        star (zetaCompletedSpectralLaplaceTransform f (-star z)) := by
  calc
    zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) z =
        zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z := by
      exact
        zetaCompletedSpectralLaplaceTransform_eq_explicitFormulaPhi
          (convolutionAutocorrelation f) z
    _ =
        zetaCompletedExplicitFormulaPhi f z *
          star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
      exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f z
    _ =
        zetaCompletedSpectralLaplaceTransform f z *
          star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
      exact congrArg
        (fun w : ℂ => w * star (zetaCompletedExplicitFormulaPhi f (-star z)))
        (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform_apply f z)
    _ =
        zetaCompletedSpectralLaplaceTransform f z *
          star (zetaCompletedSpectralLaplaceTransform f (-star z)) := by
      exact congrArg
        (fun w : ℂ => zetaCompletedSpectralLaplaceTransform f z * star w)
        (zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform_apply f (-star z))

/-- The factorization at the Hermitian-reflected parameter is the reversed Hermitian
product. -/
theorem zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_factorization_neg_star
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedSpectralLaplaceTransform
        (convolutionAutocorrelation f) (-star z) =
      zetaCompletedSpectralLaplaceTransform f (-star z) *
        star (zetaCompletedSpectralLaplaceTransform f z) := by
  calc
    zetaCompletedSpectralLaplaceTransform
        (convolutionAutocorrelation f) (-star z) =
        zetaCompletedSpectralLaplaceTransform f (-star z) *
          star (zetaCompletedSpectralLaplaceTransform f (-star (-star z))) := by
      exact
        zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_factorization_ownerTomography
          f (-star z)
    _ =
        zetaCompletedSpectralLaplaceTransform f (-star z) *
          star (zetaCompletedSpectralLaplaceTransform f z) := by
      exact congrArg
        (fun w : ℂ =>
          zetaCompletedSpectralLaplaceTransform f (-star z) *
            star (zetaCompletedSpectralLaplaceTransform f w))
        (complex_neg_star_neg_star z)

/-- The autocorrelation spectral Laplace transform has Hermitian conjugation symmetry. -/
theorem zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_star_eq_at_neg_star_ownerTomography
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    star (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) z) =
      zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) (-star z) := by
  calc
    star (zetaCompletedSpectralLaplaceTransform
        (convolutionAutocorrelation f) z) =
        star
          (zetaCompletedSpectralLaplaceTransform f z *
            star (zetaCompletedSpectralLaplaceTransform f (-star z))) := by
      exact congrArg star
        (zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_factorization_ownerTomography
          f z)
    _ =
        zetaCompletedSpectralLaplaceTransform f (-star z) *
          star (zetaCompletedSpectralLaplaceTransform f z) := by
      exact complex_star_mul_star_right_comm
        (zetaCompletedSpectralLaplaceTransform f z)
        (zetaCompletedSpectralLaplaceTransform f (-star z))
    _ =
        zetaCompletedSpectralLaplaceTransform
          (convolutionAutocorrelation f) (-star z) := by
      exact
        (zetaCompletedSpectralLaplaceTransform_convolutionAutocorrelation_factorization_neg_star
          f z).symm

/-- Complex sampled contour tomography reconstructs the finite residue defect after taking
the real part.

This is the analytic tomography root: the horizontal top-minus-bottom contour sample
reconstructs the sign-sensitive residue defect.  The coordinate-window plus omitted-tail
balance below is only real algebra after this theorem. -/
theorem sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportResidueDefect N f := by
  exact
    sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography_core
      N f

/-- Complex sampled contour tomography reconstructs the coordinate-remainder
window after adding the omitted coordinate-remainder tail. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography_core
      N f

/-- The finite tomographic error is the finite contour-transport remainder minus the
sampled horizontal contour difference. -/
theorem finitePrimeContourTransportTomographicError_eq_remainder_sub_sampled
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportTomographicError N f =
      finitePrimeContourTransportRemainder N f -
        sampledHorizontalDifference N f := by
  rfl

/-- Finite contour-residue tomography reconstructs the residue defect.

The sampled horizontal top-minus-bottom contour term is not the raw finite coordinate
window.  It is the finite residue defect: the finite coordinate-remainder window with the
outside-window coordinate tail subtracted. -/
theorem sampledHorizontalDifference_eq_finitePrimeContourTransportResidueDefect_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeContourTransportResidueDefect N f := by
  exact
    (sampledHorizontalDifference_eq_complex_re N f).trans
      (sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography
        N f)

/-- Transport the additive contour-residue balance from the complex real part to the named
real sampled horizontal difference. -/
theorem sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_of_complex_re
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcomplex :
      Complex.re (sampledHorizontalDifferenceComplex N f) +
          completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f) :
    sampledHorizontalDifference N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x + completedPrimeContourTransportCoordinateRemainderTail N f =
          finitePrimeContourTransportCoordinateRemainderWindow N f)
      (sampledHorizontalDifference_eq_complex_re N f).symm
      hcomplex

/-- Additive contour-residue tomography balance.

The sampled horizontal top-minus-bottom contour term plus the omitted outside-window
coordinate-remainder tail reconstructs the finite coordinate-remainder window. -/
theorem sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_of_complex_re
    N f
    (sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
      N f)

/-- Contour-residue reconstruction of the sampled horizontal term.

The complex sampled horizontal term reconstructs the finite real coordinate remainder after
taking the real shadow.  This is the precise tomography theorem; the additive real form below
is algebraic packaging for downstream tail estimates. -/
theorem sampledHorizontalDifferenceComplex_re_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    real_left_eq_sub_of_add_eq
      (sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
        N f)

/-- Contour-residue reconstruction of the sampled horizontal term.

The sampled horizontal term plus the outside-window coordinate-remainder tail reconstructs the
finite coordinate-remainder window.  This additive form is the direct residue-balance statement;
the subtraction form below is only algebraic packaging for downstream tail estimates. -/
theorem sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
      N f

/-- Contour-residue tomography identifies the finite residual error with the omitted
coordinate-remainder tail.

This is the subtraction form of the additive residue-balance theorem above.  The analytic
content is the additive reconstruction statement; this theorem only transports it through
the definition of the finite residual error. -/
theorem finitePrimeContourTransportTomographicError_eq_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportTomographicError N f =
      completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeContourTransportTomographicError N f =
        finitePrimeContourTransportRemainder N f -
          sampledHorizontalDifference N f := by
      exact finitePrimeContourTransportTomographicError_eq_remainder_sub_sampled N f
    _ = completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact
        real_residual_eq_tail_of_window_eq_of_add_eq
          (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f)
          (sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow
            N f)

/-- Contour-residue reconstruction of the sampled horizontal term.

The sampled horizontal top-minus-bottom contour term is the finite coordinate-remainder
window minus the outside-window coordinate-remainder tail.  This is the precise analytic
content behind the finite tomographic residual estimate. -/
theorem sampledHorizontalDifference_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    real_left_eq_sub_of_add_eq
      (sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow
        N f)

/-- A target splits as a sampled reference plus a named error when the error is the
corresponding residual. -/
theorem real_target_eq_reference_add_error_of_error_eq_residual
    {R H E : ℝ} (hE : E = R - H) :
    R = H + E := by
  calc
    R = H + (R - H) := by
      exact real_eq_reference_add_residual R H
    _ = H + E := by
      exact congrArg (fun x : ℝ => H + x) hE.symm

/-- The finite prime contour-transport remainder splits as sampled horizontal difference
plus residual finite tomography error. -/
theorem finitePrimeContourTransportRemainder_eq_sampledHorizontalDifference_add_error
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      sampledHorizontalDifference N f +
        finitePrimeContourTransportTomographicError N f := by
  exact
    real_target_eq_reference_add_error_of_error_eq_residual
      (finitePrimeContourTransportTomographicError_eq_remainder_sub_sampled N f)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

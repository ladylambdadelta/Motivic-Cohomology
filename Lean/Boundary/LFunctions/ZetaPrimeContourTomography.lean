import Boundary.LFunctions.ZetaPrimeDistributionTransport

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

/-- The coordinatewise majorant for the completed contour-transport remainder. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖completedPrimeContourTransportCoordinateRemainder ι f‖

/-- The completed contour-transport coordinate-remainder majorant family. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderMajorantFamily
    (f : ZetaAdmissibleFunction) : ZetaPrimePowerIndex → ℝ :=
  fun ι => completedPrimeContourTransportCoordinateRemainderMajorant ι f

/-- The coordinate-remainder majorant family evaluates to the coordinate majorant. -/
theorem completedPrimeContourTransportCoordinateRemainderMajorantFamily_apply
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderMajorantFamily f ι =
      completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  rfl

/-- The coordinate-remainder majorant is the norm of the coordinate remainder. -/
theorem completedPrimeContourTransportCoordinateRemainderMajorant_eq_norm
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderMajorant ι f =
      ‖completedPrimeContourTransportCoordinateRemainder ι f‖ := by
  rfl

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

/-- The contour-transport coordinate remainder is bounded by its explicit majorant. -/
theorem norm_completedPrimeContourTransportCoordinateRemainder_le_remainderMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ ≤
      completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  exact
    le_of_eq
      (completedPrimeContourTransportCoordinateRemainderMajorant_eq_norm ι f).symm

/-- The contour-transport coordinate remainder majorant is nonnegative. -/
theorem completedPrimeContourTransportCoordinateRemainderMajorant_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  calc
    0 ≤ ‖completedPrimeContourTransportCoordinateRemainder ι f‖ := by
      exact norm_nonneg _
    _ = completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
      exact (completedPrimeContourTransportCoordinateRemainderMajorant_eq_norm ι f).symm

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

/-- The outside-window coordinate-remainder tail. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    ZetaPrimePowerIndex.spectralTail
      (completedPrimeContourTransportCoordinateRemainderFamily f) N ι

/-- The outside-window coordinate-remainder tail is the `tsum` of the owner spectral tail. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_eq_spectralTail_tsum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      ∑' ι : ZetaPrimePowerIndex,
        ZetaPrimePowerIndex.spectralTail
          (completedPrimeContourTransportCoordinateRemainderFamily f) N ι := by
  rfl

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

/-- The owner horizontal-edge reconstruction package for a finite prime contour
transport rectangle.

The three fields are the actual analytic tomography inputs:
top-edge reconstruction of the contour-realized coordinates, bottom-edge
reconstruction of the time-side coordinates plus omitted tail, and oriented
top/bottom conjugation. Downstream sampled-horizontal theorems are algebraic
projections from this package. -/
structure PrimeContourHorizontalReconstruction
    (N : ℕ) (f : ZetaAdmissibleFunction) where
  top_re :
    Complex.re
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)
  bottom_re :
    Complex.re
        (zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f
  top_star_eq_neg_bottom :
    star
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      -zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ))

/-- Owner construction of the horizontal reconstruction package for the finite prime
contour transport rectangle. -/
theorem primeContourHorizontalReconstruction
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    PrimeContourHorizontalReconstruction N f := by
  sorry

/-- Top-edge owner reconstruction for the finite prime contour transport rectangle. -/
theorem primeContourHorizontalReconstruction_top_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact (primeContourHorizontalReconstruction N f).top_re

/-- Bottom-edge owner reconstruction for the finite prime contour transport rectangle.

The bottom edge reconstructs the time-side finite window together with the omitted
outside-window contour-transport tail. -/
theorem primeContourHorizontalReconstruction_bottom_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact (primeContourHorizontalReconstruction N f).bottom_re

/-- Oriented top/bottom conjugation for the finite prime contour transport rectangle. -/
theorem primeContourHorizontalReconstruction_top_star_eq_neg_bottom
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      -zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) := by
  exact (primeContourHorizontalReconstruction N f).top_star_eq_neg_bottom

/-- The real part of the top line integral over the prime transport rectangle reconstructs
the finite sum of contour-realized prime coordinates. -/
theorem primeTransportTopLineIntegral_re_eq_contourRealizedCoordinateSum_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact (primeContourHorizontalReconstruction N f).top_re

/-- The real part of the top line integral over the prime transport rectangle reconstructs
the finite contour-realized prime window. -/
theorem primeTransportTopLineIntegral_re_eq_contourRealizedWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    (primeTransportTopLineIntegral_re_eq_contourRealizedCoordinateSum_ownerTomography
      N f).trans
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate
        N (convolutionAutocorrelation f)).symm

/-- The real part of the sampled top horizontal edge reconstructs the finite
contour-realized prime window. -/
theorem sampledHorizontalTopIntegral_re_eq_contourRealizedWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalTopIntegral N f) =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
      (sampledHorizontalTopIntegral_eq_topLineIntegral N f).symm
      (primeTransportTopLineIntegral_re_eq_contourRealizedWindow_ownerTomography
        N f)

/-- The real part of the bottom line integral over the prime transport rectangle reconstructs
the finite sum of time-side coordinates together with the omitted coordinate-remainder tail. -/
theorem primeTransportBottomLineIntegral_re_eq_timeCoordinateSum_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact (primeContourHorizontalReconstruction N f).bottom_re

/-- The real part of the bottom line integral over the prime transport rectangle reconstructs
the finite time-side prime window together with the omitted coordinate-remainder tail. -/
theorem primeTransportBottomLineIntegral_re_eq_timeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (primeTransportBottomLineIntegral_re_eq_timeCoordinateSum_add_tail_ownerTomography
      N f).trans
      (congrArg
        (fun x : ℝ => x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeTimeDistributionWindow_eq_sum_coordinate
          N (convolutionAutocorrelation f)).symm)

/-- The real part of the sampled bottom horizontal edge reconstructs the finite time-side
prime window together with the omitted coordinate-remainder tail. -/
theorem sampledHorizontalBottomIntegral_re_eq_timeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalBottomIntegral N f) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
            completedPrimeContourTransportCoordinateRemainderTail N f)
      (sampledHorizontalBottomIntegral_eq_bottomLineIntegral N f).symm
      (primeTransportBottomLineIntegral_re_eq_timeWindow_add_tail_ownerTomography
        N f)

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

/-- Real-part sampled contour tomography reconstructs the finite contour-transport
remainder after restoring the omitted coordinate-remainder tail. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    sampledHorizontalDifferenceComplex_re_add_tail_eq_contourTransportRemainder_of_edgeRealReconstructions
      N f
      (sampledHorizontalTopIntegral_re_eq_contourRealizedWindow_ownerTomography N f)
      (sampledHorizontalBottomIntegral_re_eq_timeWindow_add_tail_ownerTomography N f)

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

/-- A complex number fixed by conjugation has zero imaginary part. -/
theorem complex_im_eq_zero_of_star_eq_self
    (z : ℂ) (hstar : star z = z) :
    Complex.im z = 0 := by
  have him_star : Complex.im (star z) = Complex.im z :=
    congrArg Complex.im hstar
  have him_neg : Complex.im (star z) = -Complex.im z :=
    Complex.conj_im z
  have hneg_eq : -Complex.im z = Complex.im z :=
    him_neg.symm.trans him_star
  have hsum_zero : Complex.im z + Complex.im z = 0 := by
    calc
      Complex.im z + Complex.im z = Complex.im z + -Complex.im z := by
        exact congrArg (fun x : ℝ => Complex.im z + x) hneg_eq.symm
      _ = 0 := by
        exact add_right_neg (Complex.im z)
  have htwo_zero : (2 : ℝ) * Complex.im z = 0 := by
    calc
      (2 : ℝ) * Complex.im z = Complex.im z + Complex.im z := by
        exact two_mul (Complex.im z)
      _ = 0 := by
        exact hsum_zero
  exact
    match mul_eq_zero.mp htwo_zero with
    | Or.inl htwo => False.elim (two_ne_zero htwo)
    | Or.inr him => him

/-- The top line integral over the prime transport rectangle is conjugate to the oppositely
oriented bottom line integral. -/
theorem primeTransportTopLineIntegral_star_eq_neg_bottomLineIntegral_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star
        (zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ))) =
      -zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) := by
  exact (primeContourHorizontalReconstruction N f).top_star_eq_neg_bottom

/-- The sampled top horizontal edge is conjugate to the oppositely oriented bottom edge. -/
theorem sampledHorizontalTopIntegral_star_eq_neg_bottom_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star (sampledHorizontalTopIntegral N f) =
      -sampledHorizontalBottomIntegral N f := by
  exact
    Eq.trans
      (congrArg star (sampledHorizontalTopIntegral_eq_topLineIntegral N f))
      ((primeTransportTopLineIntegral_star_eq_neg_bottomLineIntegral_ownerTomography
        N f).trans
        (congrArg Neg.neg
          (sampledHorizontalBottomIntegral_eq_bottomLineIntegral N f).symm))

/-- Oriented conjugation of one edge gives the reverse oriented conjugation of the paired
edge. -/
theorem complex_star_eq_neg_left_of_star_eq_neg_right
    (top bottom : ℂ)
    (h : star top = -bottom) :
    star bottom = -top := by
  have hstar :
      star (star top) = star (-bottom) :=
    congrArg star h
  have htop_eq_neg_star_bottom :
      top = -star bottom := by
    calc
      top = star (star top) := by
        exact (star_star top).symm
      _ = star (-bottom) := hstar
      _ = -star bottom := by
        exact map_neg star bottom
  calc
    star bottom = -(-star bottom) := by
      exact (neg_neg (star bottom)).symm
    _ = -top := by
      exact congrArg Neg.neg htop_eq_neg_star_bottom.symm

/-- The sampled bottom horizontal edge is conjugate to the oppositely oriented top edge. -/
theorem sampledHorizontalBottomIntegral_star_eq_neg_top_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star (sampledHorizontalBottomIntegral N f) =
      -sampledHorizontalTopIntegral N f := by
  exact
    complex_star_eq_neg_left_of_star_eq_neg_right
      (sampledHorizontalTopIntegral N f)
      (sampledHorizontalBottomIntegral N f)
      (sampledHorizontalTopIntegral_star_eq_neg_bottom_ownerTomography N f)

/-- If two horizontal edge terms are conjugate after reversing orientation, then their
top-minus-bottom difference is self-adjoint. -/
theorem complex_star_sub_eq_self_of_star_eq_neg_cross
    (top bottom : ℂ)
    (htop : star top = -bottom)
    (hbottom : star bottom = -top) :
    star (top - bottom) = top - bottom := by
  calc
    star (top - bottom) = star top - star bottom := by
      exact map_sub star top bottom
    _ = -bottom - star bottom := by
      exact congrArg (fun z : ℂ => z - star bottom) htop
    _ = -bottom - -top := by
      exact congrArg (fun z : ℂ => -bottom - z) hbottom
    _ = top - bottom := by
      exact neg_sub_neg bottom top

/-- Oriented edge conjugation makes the sampled horizontal difference self-adjoint. -/
theorem sampledHorizontalDifferenceComplex_star_eq_self_of_orientedEdgeConjugation
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star (sampledHorizontalDifferenceComplex N f) =
      sampledHorizontalDifferenceComplex N f := by
  exact
    Eq.trans
      (congrArg star (sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f))
      ((complex_star_sub_eq_self_of_star_eq_neg_cross
        (sampledHorizontalTopIntegral N f)
        (sampledHorizontalBottomIntegral N f)
        (sampledHorizontalTopIntegral_star_eq_neg_bottom_ownerTomography N f)
        (sampledHorizontalBottomIntegral_star_eq_neg_top_ownerTomography N f)).trans
        (sampledHorizontalDifferenceComplex_eq_top_sub_bottom N f).symm)

/-- The real-normalized sampled horizontal contour difference is self-adjoint. -/
theorem sampledHorizontalDifferenceComplex_star_eq_self_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    star (sampledHorizontalDifferenceComplex N f) =
      sampledHorizontalDifferenceComplex N f := by
  exact sampledHorizontalDifferenceComplex_star_eq_self_of_orientedEdgeConjugation N f

/-- The sampled horizontal contour difference has no imaginary residue defect component.

This is the imaginary-part contour symmetry input needed to upgrade real tomography to the
complex representative equality. -/
theorem sampledHorizontalDifferenceComplex_im_eq_zero_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (sampledHorizontalDifferenceComplex N f) = 0 := by
  exact
    complex_im_eq_zero_of_star_eq_self
      (sampledHorizontalDifferenceComplex N f)
      (sampledHorizontalDifferenceComplex_star_eq_self_ownerTomography N f)

/-- A real-part residue-defect identity and imaginary vanishing identify the sampled
complex horizontal difference with the complex residue-defect representative. -/
theorem sampledHorizontalDifferenceComplex_eq_complexResidueDefect_of_re_im
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hre :
      Complex.re (sampledHorizontalDifferenceComplex N f) =
        finitePrimeContourTransportResidueDefect N f)
    (him :
      Complex.im (sampledHorizontalDifferenceComplex N f) = 0) :
    sampledHorizontalDifferenceComplex N f =
      finitePrimeContourTransportComplexResidueDefect N f := by
  exact Complex.ext
    (hre.trans (finitePrimeContourTransportComplexResidueDefect_re N f).symm)
    (him.trans (finitePrimeContourTransportComplexResidueDefect_im N f).symm)

/-- Complex sampled contour tomography reconstructs the complex finite residue defect.

This is the analytic tomography root before passing to the real shadow used by the prime
descent inequalities. -/
theorem sampledHorizontalDifferenceComplex_eq_complexResidueDefect_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplex N f =
      finitePrimeContourTransportComplexResidueDefect N f := by
  exact
    sampledHorizontalDifferenceComplex_eq_complexResidueDefect_of_re_im
      N f
      (sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography_core
        N f)
      (sampledHorizontalDifferenceComplex_im_eq_zero_ownerTomography N f)

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

/-- The residual finite prime tomography error after subtracting the sampled horizontal
contour difference from the finite prime contour-transport remainder.

This object is deliberately explicit: the finite prime-window remainder is not asserted to
be literally the horizontal contour difference.  The residual error is identified with the
omitted coordinate-remainder tail by the residue-balance theorem below. -/
noncomputable def finitePrimeContourTransportTomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportRemainder N f -
    sampledHorizontalDifference N f

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

/-- A nonnegative majorant for the finite prime tomographic residual error. -/
noncomputable def finitePrimeContourTransportTomographicErrorMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖finitePrimeContourTransportTomographicError N f‖

/-- The finite tomographic-error majorant is the norm of the finite tomographic error. -/
theorem finitePrimeContourTransportTomographicErrorMajorant_eq_norm
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportTomographicErrorMajorant N f =
      ‖finitePrimeContourTransportTomographicError N f‖ := by
  rfl

/-- The coordinate-remainder tail majorant controlling the finite prime tomographic residual.

The finite residual is a completed prime-window tomography error, so its decay is controlled
by the tail of the coordinate-remainder majorant outside the finite prime-power window. -/
noncomputable def finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    ZetaPrimePowerIndex.spectralTail
      (completedPrimeContourTransportCoordinateRemainderMajorantFamily f) N ι

/-- The tomographic coordinate-remainder tail majorant is the `tsum` of the owner spectral
tail of the coordinate-remainder majorant family. -/
theorem finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant_eq_spectralTail_tsum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant N f =
      ∑' ι : ZetaPrimePowerIndex,
        ZetaPrimePowerIndex.spectralTail
          (completedPrimeContourTransportCoordinateRemainderMajorantFamily f) N ι := by
  rfl

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

/-- The finite prime tomographic residual error is controlled by its explicit majorant. -/
theorem norm_finitePrimeContourTransportTomographicError_le_majorant
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      finitePrimeContourTransportTomographicErrorMajorant N f := by
  exact
    le_of_eq
      (finitePrimeContourTransportTomographicErrorMajorant_eq_norm N f).symm

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

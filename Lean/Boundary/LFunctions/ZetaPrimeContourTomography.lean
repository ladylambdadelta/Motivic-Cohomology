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

/-- The real part of a complex number plus an embedded real scalar. -/
theorem complex_re_add_ofReal
    (z : ℂ) (r : ℝ) :
    Complex.re (z + (r : ℂ)) = Complex.re z + r := by
  calc
    Complex.re (z + (r : ℂ)) = Complex.re z + Complex.re (r : ℂ) := by
      exact Complex.add_re z (r : ℂ)
    _ = Complex.re z + r := by
      exact congrArg (fun x : ℝ => Complex.re z + x) (Complex.ofReal_re r)

/-- A complex subtraction vanishes exactly when the two terms are equal, in the
orientation used by tomography errors. -/
theorem complex_eq_of_sub_eq_zero
    (L W : ℂ)
    (h : L - W = 0) :
    L = W := by
  have hsub_add : L - W + W = 0 + W := by
    exact congrArg (fun z : ℂ => z + W) h
  have hleft : L - W + W = L := by
    calc
      L - W + W = (L + -W) + W := by
        exact congrArg (fun z : ℂ => z + W) (sub_eq_add_neg L W)
      _ = L + (-W + W) := by
        exact add_assoc L (-W) W
      _ = L + 0 := by
        exact congrArg (fun z : ℂ => L + z) (neg_add_cancel W)
      _ = L := by
        exact add_zero L
  have hright : 0 + W = W := by
    exact zero_add W
  exact Eq.trans hleft.symm (Eq.trans hsub_add hright)

/-- A complex subtraction vanishes when the two terms are equal, in the orientation used
by tomography errors. -/
theorem complex_sub_eq_zero_of_eq
    (L W : ℂ)
    (h : L = W) :
    L - W = 0 := by
  calc
    L - W = W - W := by
      exact congrArg (fun z : ℂ => z - W) h
    _ = W + -W := by
      exact sub_eq_add_neg W W
    _ = 0 := by
      exact add_neg_cancel W

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

/-- The top horizontal tomography error measured against the symmetrized spectral prime
boundary window. -/
noncomputable def primeTransportTopLineIntegralSymmetrizedWindowTomographyError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
    finitePrimeSymmetrizedComplexWindow N
      (fun a : ℝ =>
        zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a)

/-- The top symmetrized-window tomography error unfolds to line integral minus the
symmetrized spectral prime boundary window. -/
theorem primeTransportTopLineIntegralSymmetrizedWindowTomographyError_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopLineIntegralSymmetrizedWindowTomographyError N f =
      zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
        finitePrimeSymmetrizedComplexWindow N
          (fun a : ℝ =>
            zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a) := by
  rfl

/-- The top horizontal tomography error: the difference between the actual top
line integral and the named finite contour-realized complex window. -/
noncomputable def primeTransportTopLineIntegralTomographyError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
    finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f)

/-- The top tomography error unfolds to top line integral minus contour-realized
window. -/
theorem primeTransportTopLineIntegralTomographyError_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopLineIntegralTomographyError N f =
      zetaCompletedExplicitFormulaTopLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
        finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f) := by
  rfl

/-- The named top tomography error is the symmetrized spectral-window tomography error. -/
theorem primeTransportTopLineIntegralTomographyError_eq_symmetrizedWindowError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopLineIntegralTomographyError N f =
      primeTransportTopLineIntegralSymmetrizedWindowTomographyError N f := by
  rfl

/-- Vanishing of the top tomography error is exactly the top finite-window
reconstruction statement. -/
theorem primeTransportTopLineIntegral_eq_contourRealizedComplexWindow_of_tomographyError_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (herror : primeTransportTopLineIntegralTomographyError N f = 0) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f) := by
  exact
    complex_eq_of_sub_eq_zero
      (zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))
      (finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f))
      herror

/-- The top contour-integrand integral reconstructs the symmetrized spectral prime
boundary window. -/
theorem primeTransportTopContourIntegrand_integral_eq_symmetrizedSpectralWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c),
      primeTransportTopContourIntegrand N f x) =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a) := by
  sorry

/-- The named top contour integral reconstructs the symmetrized spectral prime boundary
window. -/
theorem primeTransportTopContourIntegral_eq_symmetrizedSpectralWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopContourIntegral N f =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a) := by
  exact
    (primeTransportTopContourIntegral_eq_integral N f).trans
      (primeTransportTopContourIntegrand_integral_eq_symmetrizedSpectralWindow_ownerTomography
        N f)

/-- The top horizontal line integral reconstructs the symmetrized spectral prime boundary
window. -/
theorem primeTransportTopLineIntegral_eq_symmetrizedSpectralWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a) := by
  exact
    (primeTransportTopLineIntegral_eq_topContourIntegral N f).trans
      (primeTransportTopContourIntegral_eq_symmetrizedSpectralWindow_ownerTomography
        N f)

/-- The top symmetrized spectral-window tomography error vanishes. -/
theorem primeTransportTopLineIntegralSymmetrizedWindowTomographyError_eq_zero_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopLineIntegralSymmetrizedWindowTomographyError N f = 0 := by
  exact
    complex_sub_eq_zero_of_eq
      (zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))
      (finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f) a))
      (primeTransportTopLineIntegral_eq_symmetrizedSpectralWindow_ownerTomography
        N f)

/-- The top horizontal tomography error vanishes. -/
theorem primeTransportTopLineIntegralTomographyError_eq_zero_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopLineIntegralTomographyError N f = 0 := by
  exact
    Eq.subst
      (motive := fun z : ℂ => z = 0)
      (primeTransportTopLineIntegralTomographyError_eq_symmetrizedWindowError N f).symm
      (primeTransportTopLineIntegralSymmetrizedWindowTomographyError_eq_zero_ownerTomography
        N f)

/-- The top horizontal line integral reconstructs the named finite contour-realized complex
window. -/
theorem primeTransportTopLineIntegral_eq_contourRealizedComplexWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f) := by
  exact
    (primeTransportTopLineIntegral_eq_symmetrizedSpectralWindow_ownerTomography
      N f).trans
      (finitePrimeContourRealizedComplexWindow_eq_symmetrizedSpectral
        N (convolutionAutocorrelation f)).symm

/-- The top horizontal line integral reconstructs the finite contour-realized complex
coordinate sum. -/
theorem primeTransportTopLineIntegral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaTopLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    primeTransportTopLineIntegral_eq_contourRealizedComplexWindow_ownerTomography
      N f

/-- The top contour-integrand integral reconstructs the finite contour-realized complex
coordinate window. -/
theorem primeTransportTopContourIntegrand_integral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c),
      primeTransportTopContourIntegrand N f x) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    primeTransportTopContourIntegrand_integral_eq_symmetrizedSpectralWindow_ownerTomography
      N f

/-- The top contour-integrand integral reconstructs the finite contour-realized real
coordinate window after taking real parts. -/
theorem primeTransportTopContourIntegrand_integral_re_eq_sum_contourRealizedComplexCoordinates_re_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportTopContourIntegrand N f x) =
      Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeContourRealizedComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
  exact congrArg Complex.re
    (primeTransportTopContourIntegrand_integral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
      N f)

/-- The top contour-integrand integral reconstructs the finite contour-realized real
coordinate sum. -/
theorem primeTransportTopContourIntegrand_integral_re_eq_sum_contourRealizedCoordinates_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportTopContourIntegrand N f x) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    (primeTransportTopContourIntegrand_integral_re_eq_sum_contourRealizedComplexCoordinates_re_ownerTomography
      N f).trans
      (finitePrimeContourRealizedComplexCoordinateSum_re_eq_coordinateSum
        N (convolutionAutocorrelation f))

/-- The top contour integral reconstructs the finite contour-realized real coordinate
sum. -/
theorem primeTransportTopContourIntegral_re_eq_sum_contourRealizedCoordinates_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportTopContourIntegral N f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f))
      (primeTransportTopContourIntegral_eq_integral N f)
      (primeTransportTopContourIntegrand_integral_re_eq_sum_contourRealizedCoordinates_ownerTomography
        N f)

/-- The top contour-integrand integral has the same imaginary part as the finite complex
contour-realized coordinate window. -/
theorem primeTransportTopContourIntegrand_integral_im_eq_sum_contourRealizedComplexCoordinates_im_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportTopContourIntegrand N f x) =
      Complex.im
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeContourRealizedComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
  exact congrArg Complex.im
    (primeTransportTopContourIntegrand_integral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
      N f)

/-- The top contour integral has the same imaginary part as the finite complex
contour-realized coordinate window. -/
theorem primeTransportTopContourIntegral_im_eq_sum_contourRealizedComplexCoordinates_im_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (primeTransportTopContourIntegral N f) =
      Complex.im
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeContourRealizedComplexCoordinate
            ι (convolutionAutocorrelation f)) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.im z =
          Complex.im
            (∑ ι in ZetaPrimePowerIndex.window N,
              finitePrimeContourRealizedComplexCoordinate
                ι (convolutionAutocorrelation f)))
      (primeTransportTopContourIntegral_eq_integral N f)
      (primeTransportTopContourIntegrand_integral_im_eq_sum_contourRealizedComplexCoordinates_im_ownerTomography
        N f)

/-- The top contour integral reconstructs the finite complex contour-realized prime
window. -/
theorem primeTransportTopContourIntegral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopContourIntegral N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeContourRealizedComplexCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        z =
          ∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeContourRealizedComplexCoordinate
              ι (convolutionAutocorrelation f))
      (primeTransportTopContourIntegral_eq_integral N f)
      (primeTransportTopContourIntegrand_integral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
        N f)

/-- The top contour integral reconstructs the finite complex contour-realized prime
window. -/
theorem primeTransportTopContourIntegral_eq_contourRealizedComplexWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportTopContourIntegral N f =
      finitePrimeContourRealizedComplexWindow N (convolutionAutocorrelation f) := by
  exact primeTransportTopContourIntegral_eq_sum_contourRealizedComplexCoordinates_ownerTomography
    N f

/-- The real part of the top contour integral reconstructs the finite sum of
contour-realized prime coordinates. -/
theorem primeTransportTopContourIntegral_re_eq_contourRealizedCoordinateSum_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportTopContourIntegral N f) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    primeTransportTopContourIntegral_re_eq_sum_contourRealizedCoordinates_ownerTomography
      N f

/-- The real part of the top contour integral reconstructs the finite contour-realized
prime window. -/
theorem primeTransportTopContourIntegral_re_eq_contourRealizedWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportTopContourIntegral N f) =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  exact
    (primeTransportTopContourIntegral_re_eq_contourRealizedCoordinateSum_ownerTomography
      N f).trans
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate
        N (convolutionAutocorrelation f)).symm

/-- The real part of the top contour-integrand integral reconstructs the finite sum of
contour-realized prime coordinates. -/
theorem primeTransportTopContourIntegrand_integral_re_eq_contourRealizedCoordinateSum_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportTopContourIntegrand N f x) =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f))
      (primeTransportTopContourIntegral_eq_integral N f)
      (primeTransportTopContourIntegral_re_eq_contourRealizedCoordinateSum_ownerTomography
        N f)

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
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f))
      (primeTransportTopLineIntegral_eq_integral_topContourIntegrand N f).symm
      (primeTransportTopContourIntegrand_integral_re_eq_contourRealizedCoordinateSum_ownerTomography
        N f)

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

/-- The bottom horizontal tomography error measured against the symmetrized time-boundary
prime window with the omitted real tail. -/
noncomputable def primeTransportBottomLineIntegralSymmetrizedWindowTomographyError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
    (finitePrimeSymmetrizedComplexWindow N
      (fun a : ℝ =>
        zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
      (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ))

/-- The bottom symmetrized-window tomography error unfolds to bottom line integral minus
the symmetrized time-boundary prime window with tail. -/
theorem primeTransportBottomLineIntegralSymmetrizedWindowTomographyError_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomLineIntegralSymmetrizedWindowTomographyError N f =
      zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
        (finitePrimeSymmetrizedComplexWindow N
          (fun a : ℝ =>
            zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
          (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)) := by
  rfl

/-- The bottom horizontal tomography error: the difference between the actual bottom
line integral and the named finite time-side complex window with tail. -/
noncomputable def primeTransportBottomLineIntegralTomographyError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
    finitePrimeTimeDistributionComplexWindowWithTail N f

/-- The bottom tomography error unfolds to bottom line integral minus the time-side
complex window with tail. -/
theorem primeTransportBottomLineIntegralTomographyError_eq
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomLineIntegralTomographyError N f =
      zetaCompletedExplicitFormulaBottomLineIntegral
          (convolutionAutocorrelation f)
          (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
        finitePrimeTimeDistributionComplexWindowWithTail N f := by
  rfl

/-- The named bottom tomography error is the symmetrized time-window tomography error. -/
theorem primeTransportBottomLineIntegralTomographyError_eq_symmetrizedWindowError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomLineIntegralTomographyError N f =
      primeTransportBottomLineIntegralSymmetrizedWindowTomographyError N f := by
  rfl

/-- Vanishing of the bottom tomography error is exactly the bottom finite-window
reconstruction statement. -/
theorem primeTransportBottomLineIntegral_eq_timeComplexWindowWithTail_of_tomographyError_eq_zero
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (herror : primeTransportBottomLineIntegralTomographyError N f = 0) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeTimeDistributionComplexWindowWithTail N f := by
  exact
    complex_eq_of_sub_eq_zero
      (zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))
      (finitePrimeTimeDistributionComplexWindowWithTail N f)
      herror

/-- The bottom contour-integrand integral reconstructs the symmetrized time-boundary
prime window with the omitted real tail. -/
theorem primeTransportBottomContourIntegrand_integral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c),
      primeTransportBottomContourIntegrand N f x) =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  sorry

/-- The named bottom contour integral reconstructs the symmetrized time-boundary prime
window with the omitted real tail. -/
theorem primeTransportBottomContourIntegral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomContourIntegral N f =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  exact
    (primeTransportBottomContourIntegral_eq_integral N f).trans
      (primeTransportBottomContourIntegrand_integral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
        N f)

/-- The bottom horizontal line integral reconstructs the symmetrized time-boundary prime
window with the omitted real tail. -/
theorem primeTransportBottomLineIntegral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  exact
    (primeTransportBottomLineIntegral_eq_bottomContourIntegral N f).trans
      (primeTransportBottomContourIntegral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
        N f)

/-- The bottom symmetrized time-window tomography error vanishes. -/
theorem primeTransportBottomLineIntegralSymmetrizedWindowTomographyError_eq_zero_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomLineIntegralSymmetrizedWindowTomographyError N f = 0 := by
  exact
    complex_sub_eq_zero_of_eq
      (zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)))
      (finitePrimeSymmetrizedComplexWindow N
        (fun a : ℝ =>
          zetaCompletedTimeBoundaryValue (convolutionAutocorrelation f) a) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ))
      (primeTransportBottomLineIntegral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
        N f)

/-- The bottom horizontal tomography error vanishes. -/
theorem primeTransportBottomLineIntegralTomographyError_eq_zero_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomLineIntegralTomographyError N f = 0 := by
  exact
    Eq.subst
      (motive := fun z : ℂ => z = 0)
      (primeTransportBottomLineIntegralTomographyError_eq_symmetrizedWindowError N f).symm
      (primeTransportBottomLineIntegralSymmetrizedWindowTomographyError_eq_zero_ownerTomography
        N f)

/-- The bottom horizontal line integral reconstructs the named finite time-side complex
window with the omitted real tail. -/
theorem primeTransportBottomLineIntegral_eq_timeComplexWindowWithTail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      finitePrimeTimeDistributionComplexWindowWithTail N f := by
  exact
    (primeTransportBottomLineIntegral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
      N f).trans
      ((congrArg
        (fun z : ℂ =>
          z + (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ))
        (finitePrimeTimeDistributionComplexWindow_eq_symmetrizedTime
          N (convolutionAutocorrelation f)).symm).trans
        (finitePrimeTimeDistributionComplexWindowWithTail_eq_complexWindow_add_tail
          N f).symm)

/-- The bottom horizontal line integral reconstructs the finite time-side complex
coordinate sum with the omitted real tail. -/
theorem primeTransportBottomLineIntegral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBottomLineIntegral
        (convolutionAutocorrelation f)
        (completedPrimeContourTransportFamily.rectangle (N : ℝ)) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate
          ι (convolutionAutocorrelation f)) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  exact
    primeTransportBottomLineIntegral_eq_timeComplexWindowWithTail_ownerTomography
      N f

/-- The bottom contour-integrand integral reconstructs the finite time-side complex
coordinate window with the omitted real tail. -/
theorem primeTransportBottomContourIntegrand_integral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c),
      primeTransportBottomContourIntegrand N f x) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate
          ι (convolutionAutocorrelation f)) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  exact
    primeTransportBottomContourIntegrand_integral_eq_symmetrizedTimeWindow_add_tail_ownerTomography
      N f

/-- The bottom contour-integrand integral reconstructs the finite time-side real
coordinate window with tail after taking real parts. -/
theorem primeTransportBottomContourIntegrand_integral_re_eq_sum_timeComplexCoordinates_add_tail_re_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportBottomContourIntegrand N f x) =
      Complex.re
        ((∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTimeDistributionComplexCoordinate
            ι (convolutionAutocorrelation f)) +
          (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)) := by
  exact congrArg Complex.re
    (primeTransportBottomContourIntegrand_integral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
      N f)

/-- The bottom contour-integrand integral reconstructs the finite time-side real
coordinate sum together with the omitted contour-transport tail. -/
theorem primeTransportBottomContourIntegrand_integral_re_eq_sum_timeCoordinates_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportBottomContourIntegrand N f x) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (primeTransportBottomContourIntegrand_integral_re_eq_sum_timeComplexCoordinates_add_tail_re_ownerTomography
      N f).trans
      (finitePrimeTimeDistributionComplexWindowWithTail_re_eq_coordinateSum_add_tail
        N f)

/-- The bottom contour integral reconstructs the finite time-side real coordinate sum
together with the omitted contour-transport tail. -/
theorem primeTransportBottomContourIntegral_re_eq_sum_timeCoordinates_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportBottomContourIntegral N f) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          (∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
            completedPrimeContourTransportCoordinateRemainderTail N f)
      (primeTransportBottomContourIntegral_eq_integral N f)
      (primeTransportBottomContourIntegrand_integral_re_eq_sum_timeCoordinates_add_tail_ownerTomography
        N f)

/-- The bottom contour-integrand integral has the same imaginary part as the finite
time-side complex coordinate window with the real tail added. -/
theorem primeTransportBottomContourIntegrand_integral_im_eq_sum_timeComplexCoordinates_add_tail_im_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportBottomContourIntegrand N f x) =
      Complex.im
        ((∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTimeDistributionComplexCoordinate
            ι (convolutionAutocorrelation f)) +
          (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)) := by
  exact congrArg Complex.im
    (primeTransportBottomContourIntegrand_integral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
      N f)

/-- The bottom contour integral has the same imaginary part as the finite time-side complex
coordinate window with the real tail added. -/
theorem primeTransportBottomContourIntegral_im_eq_sum_timeComplexCoordinates_add_tail_im_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.im (primeTransportBottomContourIntegral N f) =
      Complex.im
        ((∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTimeDistributionComplexCoordinate
            ι (convolutionAutocorrelation f)) +
          (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.im z =
          Complex.im
            ((∑ ι in ZetaPrimePowerIndex.window N,
              finitePrimeTimeDistributionComplexCoordinate
                ι (convolutionAutocorrelation f)) +
              (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ)))
      (primeTransportBottomContourIntegral_eq_integral N f)
      (primeTransportBottomContourIntegrand_integral_im_eq_sum_timeComplexCoordinates_add_tail_im_ownerTomography
        N f)

/-- The bottom contour integral reconstructs the finite time-side complex coordinate sum
together with the omitted contour-transport tail. -/
theorem primeTransportBottomContourIntegral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomContourIntegral N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTimeDistributionComplexCoordinate
          ι (convolutionAutocorrelation f)) +
        (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ) := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        z =
          (∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeTimeDistributionComplexCoordinate
              ι (convolutionAutocorrelation f)) +
            (completedPrimeContourTransportCoordinateRemainderTail N f : ℂ))
      (primeTransportBottomContourIntegral_eq_integral N f)
      (primeTransportBottomContourIntegrand_integral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
        N f)

/-- The bottom contour integral reconstructs the finite time-side complex window together
with the omitted contour-transport tail. -/
theorem primeTransportBottomContourIntegral_eq_timeComplexWindowWithTail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportBottomContourIntegral N f =
      finitePrimeTimeDistributionComplexWindowWithTail N f := by
  exact primeTransportBottomContourIntegral_eq_sum_timeComplexCoordinates_add_tail_ownerTomography
    N f

/-- The real part of the bottom contour integral reconstructs the finite time-side
coordinate sum together with the omitted coordinate-remainder tail. -/
theorem primeTransportBottomContourIntegral_re_eq_timeCoordinateSum_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportBottomContourIntegral N f) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    primeTransportBottomContourIntegral_re_eq_sum_timeCoordinates_add_tail_ownerTomography
      N f

/-- The real part of the bottom contour integral reconstructs the finite time-side prime
window together with the omitted coordinate-remainder tail. -/
theorem primeTransportBottomContourIntegral_re_eq_timeWindow_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (primeTransportBottomContourIntegral N f) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (primeTransportBottomContourIntegral_re_eq_timeCoordinateSum_add_tail_ownerTomography
      N f).trans
      (congrArg
        (fun x : ℝ => x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeTimeDistributionWindow_eq_sum_coordinate
          N (convolutionAutocorrelation f)).symm)

/-- The real part of the bottom contour-integrand integral reconstructs the finite
time-side coordinate sum together with the omitted coordinate-remainder tail. -/
theorem primeTransportBottomContourIntegrand_integral_re_eq_timeCoordinateSum_add_tail_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (∫ x in Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c),
          primeTransportBottomContourIntegrand N f x) =
      (∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          (∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
            completedPrimeContourTransportCoordinateRemainderTail N f)
      (primeTransportBottomContourIntegral_eq_integral N f)
      (primeTransportBottomContourIntegral_re_eq_timeCoordinateSum_add_tail_ownerTomography
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
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        Complex.re z =
          (∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)) +
            completedPrimeContourTransportCoordinateRemainderTail N f)
      (primeTransportBottomLineIntegral_eq_integral_bottomContourIntegrand N f).symm
      (primeTransportBottomContourIntegrand_integral_re_eq_timeCoordinateSum_add_tail_ownerTomography
        N f)

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

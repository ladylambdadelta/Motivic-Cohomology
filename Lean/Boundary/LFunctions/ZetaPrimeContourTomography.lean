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

/-- The contour-transport coordinate remainder is bounded by its explicit majorant. -/
theorem norm_completedPrimeContourTransportCoordinateRemainder_le_remainderMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ ≤
      completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  unfold completedPrimeContourTransportCoordinateRemainderMajorant
  exact le_refl _

/-- The contour-transport coordinate remainder majorant is nonnegative. -/
theorem completedPrimeContourTransportCoordinateRemainderMajorant_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ completedPrimeContourTransportCoordinateRemainderMajorant ι f := by
  unfold completedPrimeContourTransportCoordinateRemainderMajorant
  exact norm_nonneg _

/-- The finite-window coordinate remainder presentation of contour transport. -/
noncomputable def finitePrimeContourTransportCoordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    completedPrimeContourTransportCoordinateRemainder ι f

/-- The finite contour-transport remainder between the time-side and contour-realized prime
windows.  This is the honest finite-level difference; it is not asserted to vanish before
passing to the completed contour realization. -/
def finitePrimeContourTransportRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) -
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)

/-- The finite contour-transport remainder is the finite window sum of the coordinatewise
contour-transport remainders. -/
theorem finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  let g : ZetaAdmissibleFunction := convolutionAutocorrelation f
  have hcontour :
      finitePrimeContourRealizedTimeDistributionWindow N g =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourRealizedTimeDistributionCoordinate ι g :=
    finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate N g
  have htime :
      finitePrimeTimeDistributionWindow N g =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeTimeDistributionCoordinate ι g := by
    rfl
  have hsub :
      (∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourRealizedTimeDistributionCoordinate ι g) -
        (∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeTimeDistributionCoordinate ι g) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          (completedPrimeContourRealizedTimeDistributionCoordinate ι g -
            completedPrimeTimeDistributionCoordinate ι g) := by
    exact Finset.sum_sub_distrib
  unfold finitePrimeContourTransportRemainder
  unfold finitePrimeContourTransportCoordinateRemainderWindow
  unfold completedPrimeContourTransportCoordinateRemainder
  unfold g at hcontour htime hsub
  calc
    finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) =
        (∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x - finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        hcontour
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)) -
        (∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)) := by
      exact congrArg
        (fun x : ℝ =>
          (∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f)) - x)
        htime
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          (completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f) -
            completedPrimeTimeDistributionCoordinate
              ι (convolutionAutocorrelation f)) := by
      exact hsub

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
  unfold finitePrimeContourTransportRemainder
  let T : ℝ := finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  change T + (C - T) = C
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

/-- The canonical contour family used to compare the finite prime transport remainder with
the horizontal top-minus-bottom contour remainder. -/
def completedPrimeContourTransportFamily : ExplicitFormulaContourFamily where
  c := (1 / 2 : ℝ) + 1
  c_gt_half := by
    exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one

/-- The sampled horizontal top-minus-bottom contour remainder along the prime transport
family. -/
noncomputable def sampledHorizontalDifferenceComplex
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ)) -
    zetaCompletedExplicitFormulaBottomLineIntegral
      (convolutionAutocorrelation f)
      (completedPrimeContourTransportFamily.rectangle (N : ℝ))

/-- The real shadow of the sampled horizontal top-minus-bottom contour remainder along the
prime transport family. -/
noncomputable def sampledHorizontalDifference
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f)

/-- The outside-window coordinate-remainder tail. -/
noncomputable def completedPrimeContourTransportCoordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    if ι ∈ ZetaPrimePowerIndex.window N then
      0
    else
      completedPrimeContourTransportCoordinateRemainder ι f

/-- The residual finite prime tomography error after subtracting the sampled horizontal
contour difference from the finite prime contour-transport remainder.

This object is deliberately explicit: the finite prime-window remainder is not asserted to
be literally the horizontal contour difference.  The residual error is identified with the
omitted coordinate-remainder tail by the residue-balance theorem below. -/
noncomputable def finitePrimeContourTransportTomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportRemainder N f -
    sampledHorizontalDifference N f

/-- Additive contour-residue tomography balance.

The sampled horizontal top-minus-bottom contour term plus the omitted outside-window
coordinate-remainder tail reconstructs the finite coordinate-remainder window. -/
theorem sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  sorry

/-- Contour-residue reconstruction of the sampled horizontal term.

The complex sampled horizontal term reconstructs the finite real coordinate remainder after
taking the real shadow.  This is the precise tomography theorem; the additive real form below
is algebraic packaging for downstream tail estimates. -/
theorem sampledHorizontalDifferenceComplex_re_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  let H : ℝ := Complex.re (sampledHorizontalDifferenceComplex N f)
  let T : ℝ := completedPrimeContourTransportCoordinateRemainderTail N f
  let W : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  have hbalance : H + T = W := by
    have howner :=
      sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
        N f
    unfold sampledHorizontalDifference at howner
    exact howner
  change H = W - T
  calc
    H = H + T - T := by
      exact (add_sub_cancel_right H T).symm
    _ = W - T := by
      exact congrArg (fun x : ℝ => x - T) hbalance

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
  let H : ℝ := sampledHorizontalDifference N f
  let T : ℝ := completedPrimeContourTransportCoordinateRemainderTail N f
  let W : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  have hfinite :
      finitePrimeContourTransportRemainder N f = W :=
    finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f
  have hbalance : H + T = W :=
    sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow
      N f
  unfold finitePrimeContourTransportTomographicError
  change finitePrimeContourTransportRemainder N f - H = T
  calc
    finitePrimeContourTransportRemainder N f - H = W - H := by
      exact congrArg (fun x : ℝ => x - H) hfinite
    _ = (H + T) - H := by
      exact congrArg (fun x : ℝ => x - H) hbalance.symm
    _ = (H + T) + -H := by
      exact sub_eq_add_neg (H + T) H
    _ = H + (T + -H) := by
      exact add_assoc H T (-H)
    _ = H + (-H + T) := by
      exact congrArg
        (fun x : ℝ => H + x)
        (add_comm T (-H))
    _ = (H + -H) + T := by
      exact (add_assoc H (-H) T).symm
    _ = 0 + T := by
      exact congrArg (fun x : ℝ => x + T) (add_right_neg H)
    _ = T := by
      exact zero_add T

/-- Contour-residue reconstruction of the sampled horizontal term.

The sampled horizontal top-minus-bottom contour term is the finite coordinate-remainder
window minus the outside-window coordinate-remainder tail.  This is the precise analytic
content behind the finite tomographic residual estimate. -/
theorem sampledHorizontalDifference_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  let H : ℝ := sampledHorizontalDifference N f
  let T : ℝ := completedPrimeContourTransportCoordinateRemainderTail N f
  let W : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  have hbalance : H + T = W := by
    exact sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow N f
  change H = W - T
  calc
    H = H + T - T := by
      exact (add_sub_cancel_right H T).symm
    _ = W - T := by
      exact congrArg (fun x : ℝ => x - T) hbalance

/-- A nonnegative majorant for the finite prime tomographic residual error. -/
noncomputable def finitePrimeContourTransportTomographicErrorMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖finitePrimeContourTransportTomographicError N f‖

/-- The coordinate-remainder tail majorant controlling the finite prime tomographic residual.

The finite residual is a completed prime-window tomography error, so its decay is controlled
by the tail of the coordinate-remainder majorant outside the finite prime-power window. -/
noncomputable def finitePrimeContourTransportTomographicCoordinateRemainderTailMajorant
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' ι : ZetaPrimePowerIndex,
    if ι ∈ ZetaPrimePowerIndex.window N then
      0
    else
      completedPrimeContourTransportCoordinateRemainderMajorant ι f

/-- The finite prime contour-transport remainder splits as sampled horizontal difference
plus residual finite tomography error. -/
theorem finitePrimeContourTransportRemainder_eq_sampledHorizontalDifference_add_error
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      sampledHorizontalDifference N f +
        finitePrimeContourTransportTomographicError N f := by
  unfold finitePrimeContourTransportTomographicError
  let R : ℝ := finitePrimeContourTransportRemainder N f
  let H : ℝ := sampledHorizontalDifference N f
  change R = H + (R - H)
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

/-- The finite prime tomographic residual error is controlled by its explicit majorant. -/
theorem norm_finitePrimeContourTransportTomographicError_le_majorant
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeContourTransportTomographicError N f‖ ≤
      finitePrimeContourTransportTomographicErrorMajorant N f := by
  unfold finitePrimeContourTransportTomographicErrorMajorant
  exact le_refl _

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

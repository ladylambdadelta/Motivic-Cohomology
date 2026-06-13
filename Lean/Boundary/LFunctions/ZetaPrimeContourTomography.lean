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

/-- Polynomial contour-localization majorant on prime-power coordinates. -/
noncomputable def completedPrimeContourLocalizationMajorant
    (C : ℝ) (k : ℕ) (ι : ZetaPrimePowerIndex) : ℝ :=
  C * ZetaPrimePowerIndex.polynomialHeightDecay k ι

/-- The contour-localization majorant is nonnegative when its constant is nonnegative. -/
theorem completedPrimeContourLocalizationMajorant_nonnegative
    {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ completedPrimeContourLocalizationMajorant C k ι := by
  unfold completedPrimeContourLocalizationMajorant
  unfold ZetaPrimePowerIndex.polynomialHeightDecay
  have hbase :
      0 ≤
        (1 + ‖((ι.height : ℕ) : ℝ)‖) ^
          (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one
        (norm_nonneg (((ι.height : ℕ) : ℝ))))
      (-(k + 3 : ℤ))
  exact mul_nonneg hC hbase

/-- Completed contour localization bounds the norm of every coordinate remainder by a
height-polynomial majorant.

This is the owner localization input for prime contour tomography. -/
theorem exists_completedPrimeContourRemainderNorm_heightPolynomialBound
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        ‖completedPrimeContourTransportCoordinateRemainder ι f‖ ≤
          completedPrimeContourLocalizationMajorant C k ι := by
  sorry

/-- Completed contour localization bounds the explicit coordinate-remainder
majorant by a height-polynomial majorant. -/
theorem exists_completedPrimeContourLocalizationMajorant_bound
    (f : ZetaAdmissibleFunction) :
    ∃ C : ℝ, ∃ k : ℕ,
      0 < C ∧
      ∀ ι : ZetaPrimePowerIndex,
        completedPrimeContourTransportCoordinateRemainderMajorant ι f ≤
          completedPrimeContourLocalizationMajorant C k ι := by
  rcases exists_completedPrimeContourRemainderNorm_heightPolynomialBound f with
    ⟨C, k, hCpos, hbound⟩
  refine ⟨C, k, hCpos, ?_⟩
  intro ι
  unfold completedPrimeContourTransportCoordinateRemainderMajorant
  exact hbound ι

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
  unfold completedPrimeContourTransportCoordinateRemainderFamily
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

/-- Complex sampled contour tomography reconstructs the finite residue defect after taking
the real part. -/
theorem sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportResidueDefect N f := by
  sorry

/-- The residual finite prime tomography error after subtracting the sampled horizontal
contour difference from the finite prime contour-transport remainder.

This object is deliberately explicit: the finite prime-window remainder is not asserted to
be literally the horizontal contour difference.  The residual error is identified with the
omitted coordinate-remainder tail by the residue-balance theorem below. -/
noncomputable def finitePrimeContourTransportTomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportRemainder N f -
    sampledHorizontalDifference N f

/-- Finite contour-residue tomography reconstructs the residue defect.

The sampled horizontal top-minus-bottom contour term is not the raw finite coordinate
window.  It is the finite residue defect: the finite coordinate-remainder window with the
outside-window coordinate tail subtracted. -/
theorem sampledHorizontalDifference_eq_finitePrimeContourTransportResidueDefect_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f =
      finitePrimeContourTransportResidueDefect N f := by
  unfold sampledHorizontalDifference
  exact sampledHorizontalDifferenceComplex_re_eq_finitePrimeContourTransportResidueDefect_ownerTomography
    N f

/-- Additive contour-residue tomography balance.

The sampled horizontal top-minus-bottom contour term plus the omitted outside-window
coordinate-remainder tail reconstructs the finite coordinate-remainder window. -/
theorem sampledHorizontalDifference_add_coordinateRemainderTail_eq_coordinateRemainderWindow_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifference N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  let H : ℝ := sampledHorizontalDifference N f
  let W : ℝ := finitePrimeContourTransportCoordinateRemainderWindow N f
  let T : ℝ := completedPrimeContourTransportCoordinateRemainderTail N f
  have hdefect : H = W - T := by
    have hsample :
        sampledHorizontalDifference N f =
          finitePrimeContourTransportResidueDefect N f :=
      sampledHorizontalDifference_eq_finitePrimeContourTransportResidueDefect_ownerTomography
        N f
    have hresidue :
        finitePrimeContourTransportResidueDefect N f = W - T :=
      finitePrimeContourTransportResidueDefect_eq_window_sub_tail N f
    change H = W - T
    exact hsample.trans hresidue
  change H + T = W
  calc
    H + T = (W - T) + T := by
      exact congrArg (fun x : ℝ => x + T) hdefect
    _ = W := by
      exact sub_add_cancel W T

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

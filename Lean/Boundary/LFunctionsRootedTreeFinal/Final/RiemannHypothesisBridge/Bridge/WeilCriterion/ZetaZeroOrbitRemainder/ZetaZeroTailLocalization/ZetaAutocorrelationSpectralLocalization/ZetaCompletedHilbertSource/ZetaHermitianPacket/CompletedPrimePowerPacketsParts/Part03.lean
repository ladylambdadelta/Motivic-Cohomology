import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPacketsParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Spectral-coordinate majorant summability gives completed positive-coordinate
complex summability. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralMajorant_part03
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) :=
  summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
    f hmajorant

/-- The real completed positive-coordinate stream is summable. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_summable_of_spectralMajorant_part03
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) :=
  let hcomplex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralMajorant_part03
      f hmajorant
  let hnormComplex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          ‖zetaCompletedPrimeDefectKernelPositiveCoordinate ι f‖) :=
    hcomplex.norm
  let hnormRe :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          ‖Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)‖) :=
    Summable.of_nonneg_of_le
      (fun ι : ZetaPrimePowerIndex =>
        norm_nonneg
          (Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)))
      (fun ι : ZetaPrimePowerIndex => by
        exact Complex.abs_re_le_abs
          (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f))
      hnormComplex
  hnormRe.of_norm

/-- Non-genuine completed prime-power indices have zero real positive coordinate. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_eq_zero_of_not_isGenuine_part03
    (f : ZetaAdmissibleFunction)
    (ι : ZetaPrimePowerIndex)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) = 0 :=
  (congrArg Complex.re
    (zetaCompletedPrimeDefectKernelPositiveCoordinate_eq_zero_of_not_isGenuine
      ι f hι)).trans
    Complex.zero_re

/-- Completed positive real windows are finite windows of the real coordinate stream. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_eq_sum_re_part03
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  calc
    zetaCompletedPrimeDefectKernelPositiveRealWindow N f =
        Complex.re (zetaCompletedPrimeDefectKernelPositiveWindow N f) := by
      exact Eq.refl _
    _ = ∑ ι in ZetaPrimePowerIndex.window N,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
      exact Complex.re_sum
        (ZetaPrimePowerIndex.window N)
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)

/-- Completed positive real windows converge to the real coordinate-stream tsum. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_re_tsum_of_spectralMajorant_part03
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝
        (∑' ι : ZetaPrimePowerIndex,
          Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f))) := by
  let u : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
  have hsum_re : Summable u := by
    unfold u
    exact
      zetaCompletedPrimeDefectKernelPositiveCoordinate_re_summable_of_spectralMajorant_part03
        f hmajorant
  have hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι → u ι = 0 := by
    intro ι hι
    unfold u
    exact
      zetaCompletedPrimeDefectKernelPositiveCoordinate_re_eq_zero_of_not_isGenuine_part03
        f ι hι
  have hwindow :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f) =
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι) := by
    exact funext
      (fun N : ℕ => by
        unfold u
        exact zetaCompletedPrimeDefectKernelPositiveRealWindow_eq_sum_re_part03
          N f)
  have hlimit :
      Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      u hsum_re hzero
  exact Eq.subst
    (motive := fun v : ℕ → ℝ =>
      Tendsto v atTop (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)))
    hwindow.symm
    hlimit

/-- The real coordinate-stream tsum is the named positive coordinate-presentation
real scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re_part03
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
    f
    (zetaCompletedPrimeDefectKernelPositiveCoordinate_summable_of_spectralMajorant_part03
      f hmajorant)

/-- Completed positive prime defect-square windows exhaust the real coordinate presentation,
provided the completed spectral-coordinate majorant is summable.

This is only a Hermitian prime-power window exhaustion theorem. It does not identify these
spectral windows with a physical time-domain stream. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) := by
  have hlimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝
          (∑' ι : ZetaPrimePowerIndex,
            Complex.re
              (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f))) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_re_tsum_of_spectralMajorant_part03
      f hmajorant
  have htarget :
      (∑' ι : ZetaPrimePowerIndex,
          Complex.re
            (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re_part03
      f hmajorant
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 x))
    htarget
    hlimit

/-- Completed diagonal-debt windows exhaust the real diagonal-debt coordinate presentation,
provided the completed spectral-coordinate majorant is summable. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) := by
  let u : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)
  have hsum_complex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) :=
    summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
      f hmajorant
  have hsum_re : Summable u :=
    (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hsum_complex
  have hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι → u ι = 0 := by
    intro ι hι
    exact
      (congrArg Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine
          ι f hι)).trans
        Complex.zero_re
  have hwindow :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι) := by
    exact funext
      (fun N : ℕ => by
        calc
          zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
              Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f) := by
            exact Eq.refl _
          _ = ∑ ι in ZetaPrimePowerIndex.window N, u ι := by
            exact Complex.re_sum
              (ZetaPrimePowerIndex.window N)
              (fun ι : ZetaPrimePowerIndex =>
                zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f))
  have hlimit :
      Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      u hsum_re hzero
  have htarget :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_tsum_eq_coordinateTsum_re
      f hsum_complex
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 x))
    htarget
    (Eq.subst
      (motive := fun v : ℕ → ℝ =>
        Tendsto v atTop (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)))
      hwindow.symm
      hlimit)

/-- Under spectral-majorant summability, convergence of the completed positive prime-power
windows to the owner positive channel is exactly the comparison between the raw positive
coordinate presentation and the completed positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_iff_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  constructor
  · intro hpositive
    have hcoordinate :
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
      zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
        f hmajorant
    exact tendsto_nhds_unique hcoordinate hpositive
  · intro hcoordinate
    have hlimit :
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
      zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
        f hmajorant
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 x))
      hcoordinate
      hlimit

/-- The coordinate-presentation comparison turns completed positive prime-power window
convergence into convergence to the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hcoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  exact
    (zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_iff_coordinateTsum_re
      f hmajorant).mpr
      hcoordinate

/-- Dagger commutes with the completed oriented prime-power sum. -/
theorem zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_star_tsum
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)) =
      star
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    (tsum_star
      (f := fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)).symm

/-- A complex number with zero imaginary part is its real part embedded in `ℂ`. -/
theorem complex_eq_ofReal_re_of_im_eq_zero
    (z : ℂ) (hz : Complex.im z = 0) :
    z = (Complex.re z : ℂ) := by
  exact Complex.ext
    (Complex.ofReal_re (Complex.re z)).symm
    (hz.trans (Complex.ofReal_im (Complex.re z)).symm)

/-- The imaginary part of a completed complex sum vanishes when every coordinate is
real-valued. -/
theorem complex_im_tsum_eq_zero_of_forall_im_eq_zero
    {ι : Type*} (u : ι → ℂ)
    (hzero : ∀ i : ι, Complex.im (u i) = 0) :
    Complex.im (∑' i : ι, u i) = 0 := by
  have hpoint :
      (fun i : ι => u i) =
        (fun i : ι => (Complex.re (u i) : ℂ)) :=
    funext
      (fun i : ι =>
        complex_eq_ofReal_re_of_im_eq_zero (u i) (hzero i))
  calc
    Complex.im (∑' i : ι, u i) =
        Complex.im (∑' i : ι, (Complex.re (u i) : ℂ)) := by
      exact congrArg
        (fun v : ι → ℂ => Complex.im (∑' i : ι, v i))
        hpoint
    _ =
        Complex.im ((∑' i : ι, Complex.re (u i) : ℝ) : ℂ) := by
      exact congrArg Complex.im
        (Complex.ofReal_tsum
          (fun i : ι => Complex.re (u i))).symm
    _ = 0 := by
      exact Complex.ofReal_im (∑' i : ι, Complex.re (u i))

/-- Finite completed prime defect-square windows expand as diagonal debt minus the
symmetrized two-face window. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let P : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelPositiveCoordinate ι f
  let C : ZetaPrimePowerIndex → ℂ :=
    fun ι =>
      zetaCompletedPrimeSpectralAmplitudeIndex ι f *
        star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)
  let D : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f
  calc
    (∑ ι in s, P ι) + ((∑ ι in s, C ι) + star (∑ ι in s, C ι)) =
        (∑ ι in s, P ι) + ((∑ ι in s, C ι) + (∑ ι in s, star (C ι))) := by
      exact congrArg
        (fun z : ℂ => (∑ ι in s, P ι) + ((∑ ι in s, C ι) + z))
        (star_sum s C)
    _ =
        ((∑ ι in s, P ι) + (∑ ι in s, C ι)) +
          (∑ ι in s, star (C ι)) := by
      exact (add_assoc (∑ ι in s, P ι) (∑ ι in s, C ι) (∑ ι in s, star (C ι))).symm
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => P ι + C ι) +
          Finset.sum s (fun ι : ZetaPrimePowerIndex => star (C ι)) := by
      exact congrArg
        (fun z : ℂ => z + Finset.sum s (fun ι : ZetaPrimePowerIndex => star (C ι)))
        ((Finset.sum_add_distrib (s := s) (f := P) (g := C)).symm)
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => (P ι + C ι) + star (C ι)) := by
      exact
        ((Finset.sum_add_distrib
          (s := s)
          (f := fun ι : ZetaPrimePowerIndex => P ι + C ι)
          (g := fun ι : ZetaPrimePowerIndex => star (C ι))).symm)
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => P ι + (C ι + star (C ι))) := by
      exact Finset.sum_congr (Eq.refl s)
        (fun (ι : ZetaPrimePowerIndex) (_ : ι ∈ s) =>
          add_assoc (P ι) (C ι) (star (C ι)))
    _ = ∑ ι in s, D ι := by
      exact Finset.sum_congr (Eq.refl s)
        (fun (ι : ZetaPrimePowerIndex) (_ : ι ∈ s) =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
            ι f)

/-- The completed sum of negative symmetrized two-face coordinates is the completed prime
boundary coefficient.

This is now the owner completed-channel comparison: the boundary coefficient is defined from
the completed spectral-sample channel, and the coordinatewise two-face expression is only a
presentation of that channel. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  calc
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          -((ZetaPrimePowerIndex.weight ι : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedExplicitFormulaPhi
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  (ZetaPrimePowerIndex.center ι)))) := by
      exact tsum_congr
        (fun ι : ZetaPrimePowerIndex =>
          (zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
            ι f).symm)

/-- The completed symmetrized two-face cross-coordinate sum is the completed matrix
coefficient.

This is the unsigned form of
`zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient`, transported
through the explicit sign theorem for the completed boundary coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
  have hboundary :
      (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  have hneg :
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
    have htsum :
        (∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) :=
      tsum_neg
        (f := fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
    calc
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (-(∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) := by
        exact congrArg Neg.neg htsum
      _ =
          ∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
        exact neg_neg
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
  have hmatrix :
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
    calc
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
          -(-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact congrArg Neg.neg
          (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
      _ = zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
        exact neg_neg (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  exact hneg.symm.trans
    ((congrArg Neg.neg hboundary).trans hmatrix)

/-- The completed coordinatewise defect expansion may be summed over all prime powers. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFaceCoordinate_tsum_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
  exact tsum_congr
    (fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
        ι f)

/-- The completed coordinatewise defect expansion separates into the positive coordinate
presentation plus the completed two-face matrix coefficient. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
  let P : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate ι f
  let T : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f
  have hP : Summable P :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f hmajorant
  have hT : Summable T :=
    summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f hmajorant
  have hsum :
      (∑' ι : ZetaPrimePowerIndex, (P ι + T ι)) =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          (∑' ι : ZetaPrimePowerIndex, T ι) :=
    tsum_add hP hT
  have hdiagonal :
      (∑' ι : ZetaPrimePowerIndex, (P ι + T ι)) =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFaceCoordinate_tsum_eq_diagonalDebt
      f
  have htwoFace :
      (∑' ι : ZetaPrimePowerIndex, T ι) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient f
  calc
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
      exact Eq.refl _
    _ =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          (∑' ι : ZetaPrimePowerIndex, T ι) := by
      exact congrArg
        (fun z : ℂ => (∑' ι : ZetaPrimePowerIndex, P ι) + z)
        htwoFace.symm
    _ = ∑' ι : ZetaPrimePowerIndex, (P ι + T ι) := by
      exact hsum.symm
    _ = zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
      exact hdiagonal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

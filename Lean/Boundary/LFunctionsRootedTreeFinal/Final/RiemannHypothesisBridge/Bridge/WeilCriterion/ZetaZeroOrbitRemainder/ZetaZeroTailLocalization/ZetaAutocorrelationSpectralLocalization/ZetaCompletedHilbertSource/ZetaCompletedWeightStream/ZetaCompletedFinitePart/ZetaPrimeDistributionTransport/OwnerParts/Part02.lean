import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaPrimeDistributionTransport.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real spectral prime off-diagonal coordinate in the completed prime-power
explicit-formula distribution. -/
def zetaSpectralPrimeOffDiagonalCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (-((ι.weight : ℂ) *
      (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
        star
          (zetaCompletedExplicitFormulaPhi
            (convolutionAutocorrelation f) ι.center))))

/-- The completed spectral prime off-diagonal channel, obtained from the completed
explicit-formula prime-power distribution on the convolution-autocorrelation probe. -/
noncomputable def completedSpectralPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (convolutionAutocorrelation f))

/-- The completed spectral prime channel is the autocorrelation specialization of the
spectral completed prime distribution. -/
theorem completedSpectralPrimeOffDiagonalChannel_eq_spectralDistributionPairing
    (f : ZetaAdmissibleFunction) :
    completedSpectralPrimeOffDiagonalChannel f =
      completedPrimeSpectralDistributionPairing
        (zetaCompletedSpectralLaplaceTransform (convolutionAutocorrelation f)) := by
  unfold completedSpectralPrimeOffDiagonalChannel
  unfold completedPrimeSpectralDistributionPairing
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  unfold zetaCompletedSpectralLaplaceTransform
  rfl

/-- The finite physical prime off-diagonal window. -/
def finitePhysicalPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePartPrimeOffDiagonalWindow N f

/-- The finite spectral prime off-diagonal window attached to the completed explicit-formula
prime-power distribution. -/
def finiteSpectralPrimeOffDiagonalWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (∑ ι in ZetaPrimePowerIndex.window N,
      -((ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center))))

/-- The finite spectral prime window is the finite sum of spectral prime coordinates. -/
theorem finiteSpectralPrimeOffDiagonalWindow_eq_sum_coordinates
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finiteSpectralPrimeOffDiagonalWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        zetaSpectralPrimeOffDiagonalCoordinate ι f := by
  unfold finiteSpectralPrimeOffDiagonalWindow
  unfold zetaSpectralPrimeOffDiagonalCoordinate
  exact Complex.re_sum
    (ZetaPrimePowerIndex.window N)
    (fun ι : ZetaPrimePowerIndex =>
      -((ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) ι.center))))

/-- Nongenuine indices have zero spectral prime off-diagonal coordinate. -/
theorem zetaSpectralPrimeOffDiagonalCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaSpectralPrimeOffDiagonalCoordinate ι f = 0 := by
  have hweight : ι.weight = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  unfold zetaSpectralPrimeOffDiagonalCoordinate
  calc
    Complex.re
        (-((ι.weight : ℂ) *
          (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center)))) =
        Complex.re
          (-((0 : ℂ) *
            (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
              star
                (zetaCompletedExplicitFormulaPhi
                  (convolutionAutocorrelation f) ι.center)))) := by
      exact congrArg
        (fun x : ℝ =>
          Complex.re
            (-((x : ℂ) *
              (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
                star
                  (zetaCompletedExplicitFormulaPhi
                    (convolutionAutocorrelation f) ι.center)))))
        hweight
    _ = Complex.re (-(0 : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re (-x))
        (zero_mul
          (zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedExplicitFormulaPhi
                (convolutionAutocorrelation f) ι.center)))
    _ = Complex.re (0 : ℂ) := by
      exact congrArg Complex.re (neg_zero : -(0 : ℂ) = 0)
    _ = 0 := by
      exact Complex.zero_re

/-- The finite physical prime window is the kernel off-diagonal window. -/
theorem finitePhysicalPrimeOffDiagonalWindow_eq_kernelWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePhysicalPrimeOffDiagonalWindow N f =
      primeKernelOffDiagonalBoundaryWindow N f := by
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  exact (primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal N f).symm

/-- The finite physical prime windows exhaust the completed physical prime off-diagonal
channel. -/
theorem finitePhysicalPrimeOffDiagonalWindow_tendsto_completedPhysicalPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => finitePhysicalPrimeOffDiagonalWindow N f)
      atTop
      (𝓝 (completedPhysicalPrimeOffDiagonalChannel f)) := by
  unfold finitePhysicalPrimeOffDiagonalWindow
  unfold finitePartPrimeOffDiagonalWindow
  unfold completedPhysicalPrimeOffDiagonalChannel
  exact zetaPrimeOffDiagonalChannel_tendsto_completedPrimeOffDiagonalChannel f

/-- Compatibility wrapper for the historical prime-power contribution statement. -/
theorem completedPrimeOffDiagonalChannel_eq_primePowerContribution_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      Complex.re
        (zetaCompletedExplicitFormulaPrimePowerContribution
          (convolutionAutocorrelation f)) := by
  have htime :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  have howner :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) :=
    completedPrimeTimeDistributionPairing_eq_primePowerContribution_re
      (convolutionAutocorrelation f)
  exact htime.trans howner

/-- The completed prime off-diagonal channel is the negative real part of the
explicit-formula prime boundary channel on the convolution-autocorrelation
probe. -/
theorem completedPrimeOffDiagonalChannel_eq_neg_primeBoundaryChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeOffDiagonalChannel f =
      -Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) := by
  have howner :
      zetaCompletedExplicitFormulaPrimePowerContribution (convolutionAutocorrelation f) =
        -zetaCompletedExplicitFormulaPrimeContribution (convolutionAutocorrelation f) :=
    zetaCompletedExplicitFormulaPrimePowerContribution_eq_neg_primeContribution
      (convolutionAutocorrelation f)
  have hphysical :
      completedPrimeOffDiagonalChannel f =
        Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) := by
    exact completedPrimeOffDiagonalChannel_eq_primePowerContribution_re f
  have hprime :
      primeBoundaryChannel (convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaPrimeContribution (convolutionAutocorrelation f) :=
    primeBoundaryChannel_unfold (convolutionAutocorrelation f)
  have hownerRe :
      Complex.re
          (zetaCompletedExplicitFormulaPrimePowerContribution
            (convolutionAutocorrelation f)) =
        Complex.re
          (-zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f)) :=
    congrArg Complex.re howner
  have hnegRe :
      Complex.re
          (-zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f)) =
        -Complex.re
          (zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f)) :=
    Complex.neg_re
      (zetaCompletedExplicitFormulaPrimeContribution
        (convolutionAutocorrelation f))
  have hprimeRe :
      -Complex.re
          (zetaCompletedExplicitFormulaPrimeContribution
            (convolutionAutocorrelation f)) =
        -Complex.re (primeBoundaryChannel (convolutionAutocorrelation f)) :=
    congrArg Neg.neg (congrArg Complex.re hprime.symm)
  exact hphysical.trans (hownerRe.trans (hnegRe.trans hprimeRe))

/-- The completed time-side prime distribution is the completed off-diagonal channel. -/
theorem completedPrimeTimeDistributionPairing_eq_completedPrimeOffDiagonalChannel
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeOffDiagonalChannel f := by
  have hphysical :
      completedPhysicalPrimeOffDiagonalChannel f =
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) :=
    completedPhysicalPrimeOffDiagonalChannel_eq_timeDistributionPairing f
  unfold completedPhysicalPrimeOffDiagonalChannel at hphysical
  exact hphysical.symm

/-- Concrete owner data for completed finite-window prime distribution reconstruction.

The datum records the common finite reconstruction stream, its time/log and
contour-realized presentations, and convergence of both presentations to their completed
pairings.  It is deliberately lower than tomography: scheduled contour machinery may build
this object downstream, while this distribution file only consumes the explicit
finite-window reconstruction data and never identifies raw time boundary values with
spectral Laplace samples coordinatewise. -/
structure CompletedFiniteWindowPrimeDistributionReconstruction
    (f : ZetaAdmissibleFunction) where
  finiteWindow : ℕ → ℝ
  finiteWindow_eq_timeWindow :
    ∀ N : ℕ,
      finiteWindow N =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  finiteWindow_eq_contourWindow :
    ∀ N : ℕ,
      finiteWindow N =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)
  timeWindow_tendsto :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f)))
  contourWindow_tendsto :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f)))

/-- The reconstructed finite-window stream tends to the completed time/log pairing. -/
theorem CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_timePairing
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto D.finiteWindow atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      D.finiteWindow =
        fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
    funext N
    exact D.finiteWindow_eq_timeWindow N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    D.timeWindow_tendsto

/-- The reconstructed finite-window stream tends to the completed contour-realized
pairing. -/
theorem CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_contourPairing
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto D.finiteWindow atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f))) := by
  have hfun :
      D.finiteWindow =
        fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) := by
    funext N
    exact D.finiteWindow_eq_contourWindow N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))))
    hfun.symm
    D.contourWindow_tendsto

/-- Completed finite-window prime transport identifies the time/log pairing with the
contour-realized spectral pairing.

This is the owner reconstruction theorem for the completed prime distribution: finite
prime windows are transported through the completed contour realization, the omitted tails
converge, and the resulting completed contour pairing is the same scalar as the completed
time/log distribution pairing.

The proof is not coordinatewise: it must pass through the completed distribution and
contour-realization construction, rather than identifying raw time boundary values with
Laplace samples. -/
theorem completedPrimeDistributionTransport_finiteWindow_contourReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  have htime :
      Tendsto D.finiteWindow atTop
        (𝓝 (completedPrimeTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_timePairing
      f D
  have hcontour :
      Tendsto D.finiteWindow atTop
        (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
    CompletedFiniteWindowPrimeDistributionReconstruction.finiteWindow_tendsto_contourPairing
      f D
  exact tendsto_nhds_unique htime hcontour

/-- Completed finite-window prime transport identifies the time/log pairing with the
contour-realized spectral pairing.

This is the genuine transport statement behind the real-part presentation theorem below:
the finite-window prime distribution is reconstructed through the completed contour
realization before passing to the completed limit.  It is not a pointwise identification of
raw time boundary values with spectral samples. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact completedPrimeDistributionTransport_finiteWindow_contourReconstruction f D

/-- Summed finite-window prime reconstruction data with the contour/time remainder visible.

The two finite presentations are not required to be equal at a fixed window.  The datum
records the exact finite additive transport through a named remainder and separately records
the completed limits of the time/log and contour-realized streams. -/
structure CompletedSummedPrimeContourTimeTransport
    (f : ZetaAdmissibleFunction) where
  timeWindow : ℕ → ℝ
  contourWindow : ℕ → ℝ
  remainderWindow : ℕ → ℝ
  timeWindow_eq :
    ∀ N : ℕ,
      timeWindow N =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  contourWindow_eq :
    ∀ N : ℕ,
      contourWindow N =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)
  finite_additive_transport :
    ∀ N : ℕ,
      timeWindow N + remainderWindow N = contourWindow N
  timeWindow_tendsto :
    Tendsto timeWindow atTop
      (𝓝 (completedPrimeTimeDistributionPairing
        (convolutionAutocorrelation f)))
  remainderWindow_tendsto_zero :
    Tendsto remainderWindow atTop (𝓝 0)
  contourWindow_tendsto :
    Tendsto contourWindow atTop
      (𝓝 (completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f)))

/-- The visible-remainder transport identifies the completed time/log and contour-realized
prime pairings by uniqueness of the completed summed finite-window limits. -/
theorem CompletedSummedPrimeContourTimeTransport.timePairing_eq_contourPairing
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  let timeLimit : ℝ :=
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f)
  let contourLimit : ℝ :=
    completedPrimeContourRealizedTimeDistributionPairing
      (convolutionAutocorrelation f)
  have hsum_tendsto :
      Tendsto
        (fun N : ℕ => D.timeWindow N + D.remainderWindow N)
        atTop
        (𝓝 (timeLimit + 0)) := by
    exact D.timeWindow_tendsto.add D.remainderWindow_tendsto_zero
  have hsum_tendsto_time :
      Tendsto
        (fun N : ℕ => D.timeWindow N + D.remainderWindow N)
        atTop
        (𝓝 timeLimit) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => D.timeWindow N + D.remainderWindow N)
          atTop
          (𝓝 x))
      (add_zero timeLimit)
      hsum_tendsto
  have hsum_eq_contour :
      (fun N : ℕ => D.timeWindow N + D.remainderWindow N) =
        D.contourWindow := by
    funext N
    exact D.finite_additive_transport N
  have hcontour_from_sum :
      Tendsto
        (fun N : ℕ => D.timeWindow N + D.remainderWindow N)
        atTop
        (𝓝 contourLimit) := by
    exact Eq.subst
      (motive := fun u : ℕ → ℝ =>
        Tendsto u atTop (𝓝 contourLimit))
      hsum_eq_contour.symm
      D.contourWindow_tendsto
  exact tendsto_nhds_unique hsum_tendsto_time hcontour_from_sum

/-- The visible-remainder provider supplies the same completed prime distribution transport
as the older common-stream provider, without asserting finite physical/spectral equality. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerSummedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) := by
  exact CompletedSummedPrimeContourTimeTransport.timePairing_eq_contourPairing f D

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary

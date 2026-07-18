import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.HorizontalContour.Owner

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

/-- The boxed coordinate-shadow remainder is the finite coordinate-remainder window
minus the horizontal residue shadow.

This is the owner-level algebraic reduction used by the analytic tail estimate: support
reduction turns the raw box into the genuine window, and the coordinate-shadow window is
the finite coordinate-remainder window. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_coordinateRemainderWindow_sub_residueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f := by
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

/-- The coordinate-remainder window differs from the horizontal residue shadow by the
named outside-window coordinate tail.

This is the exact algebraic owner comparison needed by prime tomography: the coordinate
window is first transported to the horizontal coordinate-shadow ledger, after which the
definition of `completedPrimeContourTransportCoordinateRemainderTail` applies. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_eq_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f =
      completedPrimeContourTransportCoordinateRemainderTail N f := by
  have hwindow :
      finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
      N f
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f := by
      exact congrArg
        (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
        hwindow
    _ = completedPrimeContourTransportCoordinateRemainderTail N f := by
      rfl

/-- Transport tail convergence through the exact coordinate-window comparison.

After the preceding algebraic comparison, no finite-ledger bookkeeping remains: convergence
of the window-minus-shadow remainder is exactly convergence of the named outside-window
coordinate tail. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_of_coordinateRemainderTail
    (f : ZetaAdmissibleFunction)
    (htail :
      Tendsto
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hfun :
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) := by
    funext N
    exact
      finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_eq_coordinateRemainderTail
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htail

/-- The contour-realized prime windows exhaust the completed contour-realized pairing.

This is the lower finite-window convergence input for contour tomography.  It is proved
directly from the summability of the contour-realized prime coordinates and the
nongenuine-coordinate support reduction, before any coordinate-remainder tail theorem is
used. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) := by
  have hsum_complex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourRealizedSpectralCoordinate ι
            (convolutionAutocorrelation f)) := by
    exact
      summable_complex_family_of_norm_le_two_spectralMajorant
        f
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourRealizedSpectralCoordinate ι
            (convolutionAutocorrelation f))
        hmajorant
        (fun ι : ZetaPrimePowerIndex =>
          norm_completedPrimeContourRealizedSpectralCoordinate_le_two_spectralMajorant
            ι f)
  have hsum_re :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f)) := by
    have hmap :
        Summable
          (fun ι : ZetaPrimePowerIndex =>
            Complex.re
              (completedPrimeContourRealizedSpectralCoordinate ι
                (convolutionAutocorrelation f))) :=
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hsum_complex
    exact hmap.congr
      (fun ι : ZetaPrimePowerIndex =>
        (completedPrimeContourRealizedTimeDistributionCoordinate_eq_spectralCoordinate_re
          ι (convolutionAutocorrelation f)).symm)
  have hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι →
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) = 0 := by
    intro ι hι
    exact
      completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
        ι (convolutionAutocorrelation f) hι
  have hwindow :
      Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate ι
              (convolutionAutocorrelation f))
        atTop
        (𝓝
          (∑' ι : ZetaPrimePowerIndex,
            completedPrimeContourRealizedTimeDistributionCoordinate ι
              (convolutionAutocorrelation f))) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourRealizedTimeDistributionCoordinate ι
          (convolutionAutocorrelation f))
      hsum_re
      hzero
  have hfinite :
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)) =
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate ι
              (convolutionAutocorrelation f)) := by
    funext N
    exact finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate
      N (convolutionAutocorrelation f)
  have hcompleted :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) := by
    exact Complex.re_tsum hsum_complex
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Tendsto u atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))))
    hfinite.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            ∑ ι in ZetaPrimePowerIndex.window N,
              completedPrimeContourRealizedTimeDistributionCoordinate ι
                (convolutionAutocorrelation f))
          atTop
          (𝓝 x))
      hcompleted.symm
      hwindow)

/-- The finite coordinate-remainder windows tend to zero.

The proof subtracts the two finite-window limits: the contour-realized windows and the
time-side windows converge to the same completed prime scalar by the completed
distribution transport theorem. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) := by
  have hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))) :=
    D.contourWindow_tendsto
  have htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  have htransport :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          0 := by
    have hpairing :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f) :=
      completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
        f D
    exact sub_eq_zero.mpr hpairing.symm
  have hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 0) := by
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            finitePrimeContourRealizedTimeDistributionWindow N
                (convolutionAutocorrelation f) -
              finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
          atTop
          (𝓝 x))
      htransport
      (hcontour.sub htime)
  have hfun :
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) =
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) := by
    funext N
    exact
      finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hsub

/-- The completed finite-window reconstruction supplies the visible summed
contour/time transport datum with the coordinate-remainder window exposed.

This is the durable prime transport provider: finite contour-realized windows
are the time/log windows plus the named coordinate remainder, and that
remainder tends to zero at the completed boundary. -/
def completedSummedPrimeContourTimeTransport_of_finiteWindowReconstruction
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    CompletedSummedPrimeContourTimeTransport f where
  timeWindow :=
    fun N : ℕ =>
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  contourWindow :=
    fun N : ℕ =>
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f)
  remainderWindow :=
    fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f
  timeWindow_eq := by
    intro N
    rfl
  contourWindow_eq := by
    intro N
    rfl
  finite_additive_transport := by
    intro N
    exact finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f
  timeWindow_tendsto :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  remainderWindow_tendsto_zero :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
      f D
  contourWindow_tendsto :=
    D.contourWindow_tendsto

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

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

/-- Scheduled owner data for the canonical prime contour-transport family.

This is genuine construction data: the contour construction must supply the deterministic
height schedule, and downstream prime tomography consumes this record instead of
extracting a function from countable avoidance. -/
structure CompletedPrimeContourTransportScheduledFamily where
  height_schedule : ExplicitFormulaCofinalHeightSchedule completedPrimeContourTransportFamily
  horizontal_excisedStrip :
    CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
  horizontal_top_mem :
    ∀ (T x : ℝ),
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaTopPath
            (completedPrimeContourTransportFamily.rectangle T) x ∈
          horizontal_excisedStrip.carrier
  horizontal_bottom_mem :
    ∀ (T x : ℝ),
      x ∈ Set.uIcc completedPrimeContourTransportFamily.c
          (1 - completedPrimeContourTransportFamily.c) →
        zetaCompletedExplicitFormulaBottomPath
            (completedPrimeContourTransportFamily.rectangle T) x ∈
          horizontal_excisedStrip.carrier
  horizontal_decay_order : ℕ
  primeDistributionReconstruction :
    ∀ f : ZetaAdmissibleFunction,
      CompletedFiniteWindowPrimeDistributionReconstruction f

/-- Scheduled contour data construct the completed finite-window prime distribution
reconstruction datum consumed by the distribution-transport owner theorem. -/
def completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    CompletedFiniteWindowPrimeDistributionReconstruction f :=
  S.primeDistributionReconstruction f

/-- The scheduled-family reconstruction stream is the common finite-window stream stored
in the scheduled contour data. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_finiteWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow =
      (S.primeDistributionReconstruction f).finiteWindow := by
  rfl

/-- The scheduled-family reconstruction stream has the time-window presentation. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_timeWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow N =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).finiteWindow_eq_timeWindow N

/-- The scheduled-family reconstruction stream has the contour-window presentation. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_contourWindow
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (N : ℕ) :
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f).finiteWindow N =
      finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).finiteWindow_eq_contourWindow N

/-- The scheduled-family time finite windows converge to the completed time pairing. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_timeWindow_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝 (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).timeWindow_tendsto

/-- The scheduled-family contour finite windows converge to the completed contour
pairing. -/
theorem completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily_contourWindow_tendsto
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f))
      atTop
      (𝓝
        (completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f))) :=
  (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
    S f).contourWindow_tendsto

/-- Scheduled contour data route the completed prime distribution transport theorem through
the explicit finite-window reconstruction datum. -/
theorem completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_of_scheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction) :
    completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
      completedPrimeContourRealizedTimeDistributionPairing
        (convolutionAutocorrelation f) :=
  completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
    f
    (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily S f)

/-- The scheduled contour-family object associated to prime contour transport data. -/
def CompletedPrimeContourTransportScheduledFamily.toScheduledContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily) :
    ExplicitFormulaScheduledContourFamily :=
  { toContourFamily := completedPrimeContourTransportFamily
    height_schedule := S.height_schedule }

/-- The scheduled contour-family projection of prime transport data is the canonical
prime contour-transport family. -/
theorem CompletedPrimeContourTransportScheduledFamily.toScheduledContourFamily_toContourFamily
    (S : CompletedPrimeContourTransportScheduledFamily) :
    S.toScheduledContourFamily.toContourFamily =
      completedPrimeContourTransportFamily := by
  rfl

/-- The scheduled contour-family object associated to prime transport data carries the
stored prime transport height schedule. -/
theorem CompletedPrimeContourTransportScheduledFamily.toScheduledContourFamily_height_schedule
    (S : CompletedPrimeContourTransportScheduledFamily) :
    S.toScheduledContourFamily.height_schedule =
      S.height_schedule := by
  rfl

/-- Family analytic package for the convolution autocorrelation and the completed prime
contour-transport family, using supplied scheduled contour data. -/
noncomputable def completedPrimeContourTransportFamilyAnalyticPackage
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily :=
  { phi_control := hPhi
    logderiv_control := hLog
    height_schedule := S.height_schedule }

/-- The prime contour-transport package has the supplied cofinal height schedule as its
schedule field. -/
theorem completedPrimeContourTransportFamilyAnalyticPackage_height_schedule
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog).height_schedule =
      S.height_schedule := by
  rfl

/-- The prime contour-transport package is the scheduled-contour-family analytic package
for the scheduled prime transport object when the same analytic controls are supplied. -/
theorem completedPrimeContourTransportFamilyAnalyticPackage_eq_scheduledContourFamilyPackage_of_controls
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog =
      explicitFormulaFamilyAnalyticPackage_of_scheduledContourFamily hPhi hLog
        S.toScheduledContourFamily := by
  rfl

/-- The finite horizontal residue shadow tends to zero by horizontal decay from an explicit
family analytic package. -/
theorem finitePrimeHorizontalResidueShadow_tendsto_zero_of_package
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (E : CompletedZetaZeroExcisedStrip
      (min completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c))
      (max completedPrimeContourTransportFamily.c
        (1 - completedPrimeContourTransportFamily.c)))
    (hTopMem :
      ∀ (T x : ℝ),
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaTopPath
              (completedPrimeContourTransportFamily.rectangle T) x ∈
            E.carrier)
    (hBottomMem :
      ∀ (T x : ℝ),
        x ∈ Set.uIcc completedPrimeContourTransportFamily.c
            (1 - completedPrimeContourTransportFamily.c) →
          zetaCompletedExplicitFormulaBottomPath
              (completedPrimeContourTransportFamily.rectangle T) x ∈
            E.carrier)
    (M : ℕ) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hcomplex :
      Tendsto
        (fun N : ℕ =>
          explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ))
        atTop
        (𝓝 0) := by
    exact
        (explicitFormulaFamilyHorizontalResidueWindowError_tendsto_zero
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          h
          E
          hTopMem
          hBottomMem
          M).comp tendsto_natCast_atTop_atTop
  have hre :
      Tendsto
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)))
        atTop
        (𝓝 (Complex.re 0)) :=
    (RCLike.continuous_re.tendsto (0 : ℂ)).comp hcomplex
  have hzero : Complex.re (0 : ℂ) = (0 : ℝ) :=
    Complex.zero_re
  have hshadow :
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ =>
          Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ))) := by
    funext N
    exact finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
      N f
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hshadow.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            Complex.re
              (explicitFormulaFamilyHorizontalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)))
          atTop
          (𝓝 x))
      hzero
      hre)

/-- The finite horizontal residue shadow tends to zero by supplied scheduled prime
contour-transport data. -/
theorem finitePrimeHorizontalResidueShadow_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  exact
    finitePrimeHorizontalResidueShadow_tendsto_zero_of_package
      f
      (completedPrimeContourTransportFamilyAnalyticPackage S f hPhi hLog)
      S.horizontal_excisedStrip
      S.horizontal_top_mem
      S.horizontal_bottom_mem
      S.horizontal_decay_order

/-- The finite coordinate-remainder window converges to the horizontal residue shadow.

This is the upstream prime tomography convergence theorem: the analytic tail estimate is
owned at the coordinate-remainder-window level, before box support bookkeeping or norm
packaging. -/
theorem finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
        atTop
        (𝓝 0) :=
    finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
      f
      (completedFiniteWindowPrimeDistributionReconstruction_of_scheduledContourFamily
        S f)
  have hshadow :
      Tendsto
        (fun N : ℕ => finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 0) := by
    exact
      finitePrimeHorizontalResidueShadow_tendsto_zero_ownerTailEstimate
        S
        f
        hPhi
        hLog
  have hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 (0 - 0)) :=
    hwindow.sub hshadow
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 x))
    (sub_zero 0)
    hsub

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

/-- The boxed coordinate-shadow remainder has norm tending to zero.

This is the exact tail-localization estimate behind the finite tomographic majorant: after
support reduction, the only omitted term is the boxed coordinate-shadow remainder against
the horizontal residue shadow. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_tendsto_zero_ownerTailEstimate
    (S : CompletedPrimeContourTransportScheduledFamily)
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaPhiAnalyticControl (convolutionAutocorrelation f))
    (hLog : CompletedZetaNegLogDerivControl (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖)
      atTop
      (𝓝 0) := by
  have hwindow :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f)
        atTop
        (𝓝 0) :=
    finitePrimeHorizontalResidueCoordinateRemainderWindow_sub_residueShadow_tendsto_zero_ownerTailEstimate
      S
      f
      hPhi
      hLog
  have hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f‖)
        atTop
        (𝓝 ‖(0 : ℝ)‖) :=
    hwindow.norm
  have hfun :
      (fun N : ℕ => ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖) =
        (fun N : ℕ =>
          ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
            finitePrimeHorizontalResidueShadow N f‖) := by
    funext N
    exact congrArg norm
      (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_coordinateRemainderWindow_sub_residueShadow
        N f)
  exact Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ =>
            ‖finitePrimeContourTransportCoordinateRemainderWindow N f -
              finitePrimeHorizontalResidueShadow N f‖)
          atTop
          (𝓝 x))
      (norm_zero : ‖(0 : ℝ)‖ = 0)
      hnorm)


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

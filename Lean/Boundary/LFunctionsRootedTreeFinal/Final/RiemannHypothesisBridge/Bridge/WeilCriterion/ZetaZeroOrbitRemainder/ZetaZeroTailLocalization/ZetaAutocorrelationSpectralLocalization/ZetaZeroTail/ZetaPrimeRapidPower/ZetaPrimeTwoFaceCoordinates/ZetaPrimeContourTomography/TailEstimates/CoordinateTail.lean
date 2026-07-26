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
        finitePrimeHorizontalResidueShadow N f‖ :=
  Eq.refl ‖completedPrimeContourTransportCoordinateRemainderTail N f‖

/-- Remainder-bound presentation for the omitted coordinate tail.

This is the explicit finite-window bound shape used by the tail estimate: the omitted tail is
controlled by the norm of the window coordinate-shadow remainder against the horizontal
residue shadow. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_remainderBound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainderTail N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
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
        finitePrimeHorizontalResidueCoordinateShadow ι f :=
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
        finitePrimeHorizontalResidueShadow N f :=
  let hbox :
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum N f
  let hstart :
      completedPrimeContourTransportCoordinateRemainderTail N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    Eq.refl (completedPrimeContourTransportCoordinateRemainderTail N f)
  let hboxSub :
      (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hbox.symm
  hstart.trans hboxSub

/-- Support reduction for the omitted coordinate-remainder tail.

This theorem contains only the support bookkeeping: nongenuine coordinates vanish, so the
tail can be presented using the raw rectangular box.  The analytic convergence of that
boxed remainder is kept separate below. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_supportReduction
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f :=
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
        finitePrimeHorizontalResidueShadow N f‖ :=
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
        finitePrimeHorizontalResidueShadow N f :=
  Eq.refl (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f)

/-- The omitted coordinate tail is the boxed finite-window remainder after support
reduction. -/
theorem completedPrimeContourTransportCoordinateRemainderTail_eq_boxRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f :=
  (completedPrimeContourTransportCoordinateRemainderTail_supportReduction
    N f).trans
    (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f).symm

/-- Norm-bound form of the boxed finite-window remainder. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_norm_bound
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    ‖finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f‖ ≤
      ‖(∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
        finitePrimeHorizontalResidueShadow N f‖ :=
  le_of_eq
    (congrArg norm
      (finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f))

/-- The boxed coordinate-shadow remainder is the finite tomographic residual. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_tomographicError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
      finitePrimeContourTransportTomographicError N f :=
  let hbox :
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum N f
  let hwindow :
      finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
      N f
  let hshadow :
      sampledHorizontalDifference N f =
        finitePrimeHorizontalResidueShadow N f :=
    sampledHorizontalDifference_eq_finitePrimeHorizontalResidueShadow N f
  let hrem :
      finitePrimeContourTransportRemainder N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f :=
    finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f
  let hstart :
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f
  let hboxSub :
      (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hbox
  let hwindowSub :
      (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hwindow.symm
  let hshadowSub :
      finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          sampledHorizontalDifference N f :=
    congrArg
      (fun x : ℝ => finitePrimeContourTransportCoordinateRemainderWindow N f - x)
      hshadow.symm
  let hremSub :
      finitePrimeContourTransportCoordinateRemainderWindow N f -
          sampledHorizontalDifference N f =
        finitePrimeContourTransportRemainder N f -
          sampledHorizontalDifference N f :=
    congrArg
      (fun x : ℝ => x - sampledHorizontalDifference N f)
      hrem.symm
  let hfinish :
      finitePrimeContourTransportRemainder N f -
          sampledHorizontalDifference N f =
        finitePrimeContourTransportTomographicError N f :=
    Eq.refl (finitePrimeContourTransportTomographicError N f)
  hstart.trans
    (hboxSub.trans
      (hwindowSub.trans (hshadowSub.trans (hremSub.trans hfinish))))

/-- The boxed coordinate-shadow remainder is the finite coordinate-remainder window
minus the horizontal residue shadow.

This is the owner-level algebraic reduction used by the analytic tail estimate: support
reduction turns the raw box into the genuine window, and the coordinate-shadow window is
the finite coordinate-remainder window. -/
theorem finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq_coordinateRemainderWindow_sub_residueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f :=
  let hbox :
      (∑ ι in ZetaPrimePowerIndex.box N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeHorizontalResidueCoordinateShadow_box_sum_eq_window_sum N f
  let hwindow :
      finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
      N f
  let hstart :
      finitePrimeHorizontalResidueCoordinateShadowBoxRemainder N f =
        (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    finitePrimeHorizontalResidueCoordinateShadowBoxRemainder_eq N f
  let hboxSub :
      (∑ ι in ZetaPrimePowerIndex.box N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hbox
  let hwindowSub :
      (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hwindow.symm
  hstart.trans (hboxSub.trans hwindowSub)

/-- The coordinate-remainder window differs from the horizontal residue shadow by the
named outside-window coordinate tail.

This is the exact algebraic owner comparison needed by prime tomography: the coordinate
window is first transported to the horizontal coordinate-shadow ledger, after which the
definition of `completedPrimeContourTransportCoordinateRemainderTail` applies. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_eq_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f -
        finitePrimeHorizontalResidueShadow N f =
      completedPrimeContourTransportCoordinateRemainderTail N f :=
  let hwindow :
      finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f :=
    finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
      N f
  let hwindowSub :
      finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f :=
    congrArg
      (fun x : ℝ => x - finitePrimeHorizontalResidueShadow N f)
      hwindow
  let htail :
      (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          finitePrimeHorizontalResidueShadow N f =
        completedPrimeContourTransportCoordinateRemainderTail N f :=
    Eq.refl (completedPrimeContourTransportCoordinateRemainderTail N f)
  hwindowSub.trans htail

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
      (𝓝 0) :=
  let hfun :
      (fun N : ℕ =>
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          finitePrimeHorizontalResidueShadow N f) =
        (fun N : ℕ => completedPrimeContourTransportCoordinateRemainderTail N f) :=
    funext
      (fun N : ℕ =>
      finitePrimeContourTransportCoordinateRemainderWindow_sub_residueShadow_eq_coordinateRemainderTail
        N f)
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    htail

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
          (convolutionAutocorrelation f))) :=
  let hsum_complex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourRealizedSpectralCoordinate ι
            (convolutionAutocorrelation f)) :=
    summable_complex_family_of_norm_le_two_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeContourRealizedSpectralCoordinate ι
          (convolutionAutocorrelation f))
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_completedPrimeContourRealizedSpectralCoordinate_le_two_spectralMajorant
          ι f)
  let hsum_re :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f)) :=
    let hmap :
        Summable
          (fun ι : ZetaPrimePowerIndex =>
            Complex.re
              (completedPrimeContourRealizedSpectralCoordinate ι
                (convolutionAutocorrelation f))) :=
      (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hsum_complex
    hmap.congr
      (fun ι : ZetaPrimePowerIndex =>
        (completedPrimeContourRealizedTimeDistributionCoordinate_eq_spectralCoordinate_re
          ι (convolutionAutocorrelation f)).symm)
  let hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι →
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) = 0 :=
    fun ι hι =>
      completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
        ι (convolutionAutocorrelation f) hι
  let hwindow :
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
  let hfinite :
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f)) =
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.window N,
            completedPrimeContourRealizedTimeDistributionCoordinate ι
              (convolutionAutocorrelation f)) :=
    funext
      (fun N : ℕ =>
        finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate
          N (convolutionAutocorrelation f))
  let hcompleted :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) =
        ∑' ι : ZetaPrimePowerIndex,
          completedPrimeContourRealizedTimeDistributionCoordinate ι
            (convolutionAutocorrelation f) :=
    Complex.re_tsum hsum_complex
  Eq.subst
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

/-- The visible transport remainder is the canonical coordinate-remainder window.

The proof uses only the finite additive transport equation and the two named finite-window
presentations stored in the summed transport datum. -/
theorem CompletedSummedPrimeContourTimeTransport.remainderWindow_eq_coordinateRemainderWindow
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f)
    (N : ℕ) :
    D.remainderWindow N = finitePrimeContourTransportCoordinateRemainderWindow N f :=
  let hadd :
      D.timeWindow N + D.remainderWindow N = D.contourWindow N :=
    D.finite_additive_transport N
  let hcanonical :
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          finitePrimeContourTransportCoordinateRemainderWindow N f =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) :=
    finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f
  let hstep1 :
      D.timeWindow N + D.remainderWindow N =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) :=
    hadd.trans (D.contourWindow_eq N)
  let hstep2 :
      finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          finitePrimeContourTransportCoordinateRemainderWindow N f :=
    hcanonical.symm
  let hstep3 :
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          finitePrimeContourTransportCoordinateRemainderWindow N f =
        D.timeWindow N + finitePrimeContourTransportCoordinateRemainderWindow N f :=
    congrArg
      (fun x : ℝ =>
        x + finitePrimeContourTransportCoordinateRemainderWindow N f)
      (D.timeWindow_eq N).symm
  let hleft :
      D.timeWindow N + D.remainderWindow N =
        D.timeWindow N + finitePrimeContourTransportCoordinateRemainderWindow N f :=
    hstep1.trans (hstep2.trans hstep3)
  add_left_cancel hleft

/-- The canonical coordinate-remainder windows tend to zero when supplied by a visible
summed transport datum. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_of_summedTransport
    (f : ZetaAdmissibleFunction)
    (D : CompletedSummedPrimeContourTimeTransport f) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  let hfun :
      (fun N : ℕ => D.remainderWindow N) =
        (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) :=
    funext
      (fun N : ℕ =>
        CompletedSummedPrimeContourTimeTransport.remainderWindow_eq_coordinateRemainderWindow
          f D N)
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun
    D.remainderWindow_tendsto_zero

theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_ownerTailEstimate
    (f : ZetaAdmissibleFunction)
    (D : CompletedFiniteWindowPrimeDistributionReconstruction f) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  let hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))) :=
    D.contourWindow_tendsto
  let htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  let htransport :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          0 :=
    let hpairing :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f) :=
      completedPrimeDistributionTransport_timePairing_eq_contourRealizedPairing_ownerFiniteWindowTransport
        f D
    sub_eq_zero.mpr hpairing.symm
  let hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
              finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 0) :=
    Eq.subst
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
  let hfun :
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) =
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) :=
    funext
      (fun N : ℕ =>
      finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
        N f)
  Eq.subst
    (motive := fun u : ℕ → ℝ => Tendsto u atTop (𝓝 0))
    hfun.symm
    hsub

theorem finitePrimeContourTransportCoordinateRemainderWindow_tendsto_zero_of_pairingEquality
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι
            f))
    (hpairing :
      completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
        completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f)) :
    Tendsto
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f)
      atTop
      (𝓝 0) :=
  let hcontour :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeContourRealizedTimeDistributionPairing
            (convolutionAutocorrelation f))) :=
    finitePrimeContourRealizedTimeDistributionWindow_tendsto_completedPairing_ownerTailEstimate
      f hmajorant
  let htime :
      Tendsto
        (fun N : ℕ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝
          (completedPrimeTimeDistributionPairing (convolutionAutocorrelation f))) :=
    finitePrimeTimeDistributionWindow_tendsto_completed f
  let htransport :
      completedPrimeContourRealizedTimeDistributionPairing
          (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionPairing (convolutionAutocorrelation f) =
          0 :=
    sub_eq_zero.mpr hpairing.symm
  let hsub :
      Tendsto
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
              finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
        atTop
        (𝓝 0) :=
    Eq.subst
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
  let hfun :
      (fun N : ℕ => finitePrimeContourTransportCoordinateRemainderWindow N f) =
        (fun N : ℕ =>
          finitePrimeContourRealizedTimeDistributionWindow N
              (convolutionAutocorrelation f) -
            finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)) :=
    funext
      (fun N : ℕ =>
      finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
        N f)
  Eq.subst
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
  timeWindow_eq :=
    fun N : ℕ =>
      Eq.refl (finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f))
  contourWindow_eq :=
    fun N : ℕ =>
      Eq.refl
        (finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f))
  finite_additive_transport :=
    fun N : ℕ =>
      finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f
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

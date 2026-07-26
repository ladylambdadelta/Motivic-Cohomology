import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.GNSNormalization.Owner

/-!
# Prime contour residue ledger basics

This file owns the first finite ledger definitions and projection identities.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

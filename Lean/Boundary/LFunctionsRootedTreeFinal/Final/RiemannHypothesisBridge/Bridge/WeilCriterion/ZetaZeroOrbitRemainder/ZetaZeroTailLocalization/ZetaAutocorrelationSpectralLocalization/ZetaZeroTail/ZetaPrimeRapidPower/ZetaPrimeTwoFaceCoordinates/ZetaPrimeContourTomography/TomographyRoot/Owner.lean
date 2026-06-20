import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.ResidueLedger.Owner

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

/-- Combined finite rectangle residue-window tomography for the prime transport family,
after consuming the scheduled finite rectangle residue equality.

The residue-window shadow produced by the scheduled finite rectangle residue layer is the
finite coordinate-remainder window.  This is prime-window accounting: it matches the
residue-window presentation to the coordinate remainder ledger, with the tail kept
visible. -/
theorem finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow_of_scheduledRectangleResidueEquality
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (_hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    (primeTransportCombinedResidueWindowShadow_eq_horizontalResidueWindowError_add_tail
      N f).trans
      (finitePrimeHorizontalResidueWindowError_re_add_tail_eq_coordinateRemainderWindow
        N f)

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

The scheduled package and its finite-rectangle residue convergence are explicit inputs;
this theorem does not choose a contour schedule. -/
theorem finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow_of_scheduledRectangleResidueEquality
      N f h hfinite

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

This is the prime-window accounting bridge after the scheduled finite rectangle residue
equality has supplied the residue-window objects: it identifies the combined
residue-window shadow with the finite contour-visible prime ledger. -/
theorem finitePrimeTransportWindowAccounting_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (finitePrimeResidueWindowShadow_eq_coordinateRemainderWindow
      N f h hfinite).trans
      (finitePrimeContourTransportCoordinateRemainderWindow_eq_visibleLedger N f)

/-- Combined finite rectangle residue-window tomography for the prime transport family,
relative to explicit scheduled contour-realization data.

After the finite Cauchy/residue decomposition has isolated the full residue-window error
and the vertical residue-window error, their combined horizontal real shadow with the
coordinate-remainder tail restored is the contour-visible finite prime ledger. -/
theorem primeTransportCombinedResidueWindowShadow_eq_visiblePrimeLedger_ownerContourResidue_root
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact finitePrimeTransportWindowAccounting_realizes_visiblePrimeLedger
    N f h hfinite

/-- Explicit scheduled contour measurement reconstructs the finite visible prime ledger.

The scheduled contour package is the finite-window measurement channel.  The theorem
identifies the reconstructed finite GNS/contour ledger, not coordinatewise data attached to
a particular schedule. -/
theorem explicitScheduledPrimeContourMeasurement_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily)
    (hfinite :
      Tendsto
        (fun u : ℝ =>
          explicitFormulaScheduledRectangleResidueEqualityError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            h
            u)
        atTop
        (𝓝 0)) :
    primeTransportCombinedResidueWindowShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    primeTransportCombinedResidueWindowShadow_eq_visiblePrimeLedger_ownerContourResidue_root
      N f h hfinite

/-- Combined finite-prime packet comparison for the prime transport rectangle.

The top-minus-bottom horizontal contour sample, after taking its real shadow and restoring
the outside-window coordinate-remainder tail, is the contour-visible finite prime ledger.
This is routed through the finite prime horizontal residue-shadow realization; no
individual horizontal edge is reconstructed here. -/
theorem combinedHorizontalSampleWithTail_eq_visiblePrimeLedger_ownerContourResidue_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeHorizontalResidueShadow N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      have hshadow :
          Complex.re (sampledHorizontalDifferenceComplex N f) =
            finitePrimeHorizontalResidueShadow N f := by
        calc
          Complex.re (sampledHorizontalDifferenceComplex N f) =
              Complex.re
                (explicitFormulaFamilyHorizontalResidueWindowError
                  (convolutionAutocorrelation f)
                  completedPrimeContourTransportFamily
                  (N : ℝ)) := by
            exact
              (finitePrimeHorizontalResidueWindowError_re_eq_sampledHorizontalDifferenceComplex_re
                N f).symm
          _ = finitePrimeHorizontalResidueShadow N f := by
            exact
              (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
                N f).symm
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        hshadow
    _ = finitePrimeContourVisibleLedger N f := by
      exact
        primeTransportHorizontalResidueShadow_add_tail_realizes_visiblePrimeLedger
          N f

/-- The combined horizontal contour shadow realizes the contour-visible finite prime ledger.

This is the owner analytic input for finite prime contour tomography: the top-minus-bottom
horizontal sample, after restoring the outside-window coordinate-remainder tail, is the
single contour-visible ledger.  It does not assert reconstruction of either horizontal
edge separately. -/
theorem combinedHorizontalContourShadow_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_complex_re_add_tail N f).trans
      (combinedHorizontalSampleWithTail_eq_visiblePrimeLedger_ownerContourResidue_root
        N f)

/-- Analytic sampled-horizontal ledger reconstruction root.

The combined horizontal contour shadow reconstructs the contour-visible finite prime
ledger.  This is the single contour-visible tomography input; it does not split into
individual edge reconstructions. -/
theorem sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourVisibleLedger N f := by
  exact combinedHorizontalContourShadow_realizes_visiblePrimeLedger N f

/-- The sampled-horizontal shadow evaluates to the combined contour-ledger evaluator. -/
theorem sampledHorizontalContourTransportShadow_eq_combinedLedgerEvaluator_ownerTomography
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeCombinedContourLedgerEvaluator N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
      N f).trans
      (finitePrimeContourVisibleLedger_eq_combinedLedgerEvaluator N f)

/-- Analytic sampled-horizontal tomography root in shadow/projection form.

The combined horizontal contour shadow reconstructs the finite contour-transport
projection.  This is the contour-shift/residue input for this lane; it intentionally does
not assert separate top-edge or bottom-edge reconstruction statements. -/
theorem sampledHorizontalContourTransportShadow_eq_finiteProjection_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportShadow N f =
      finitePrimeContourTransportProjection N f := by
  exact
    (sampledHorizontalContourTransportShadow_eq_visibleLedger_ownerTomography_root
      N f).trans
      (finitePrimeContourVisibleLedger_eq_projection N f)

/-- The combined sampled-horizontal contour-transport reconstruction map.

This is the real shadow of the top-minus-bottom horizontal contour sample with the
outside-window coordinate-remainder tail restored.  It is the tomography object owned by
this file; it deliberately does not split into separate top-edge and bottom-edge
reconstruction statements. -/
noncomputable def sampledHorizontalContourTransportReconstruction
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (sampledHorizontalDifferenceComplex N f) +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The sampled-horizontal reconstruction map unfolds to the real top-minus-bottom sample
with the omitted coordinate-remainder tail restored. -/
theorem sampledHorizontalContourTransportReconstruction_eq_complex_re_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The reconstruction map is the sampled-horizontal contour-transport shadow. -/
theorem sampledHorizontalContourTransportReconstruction_eq_shadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      sampledHorizontalContourTransportShadow N f := by
  rfl

/-- Analytic sampled-horizontal tomography root in owner-map form.

The single combined sampled-horizontal reconstruction map recovers the finite
contour-transport remainder.  This is the contour-shift/residue input for the prime
finite-edge tomography lane; no individual edge reconstruction is asserted. -/
theorem sampledHorizontalContourTransportReconstruction_eq_contourTransportRemainder_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalContourTransportReconstruction N f =
      finitePrimeContourTransportRemainder N f := by
  calc
    sampledHorizontalContourTransportReconstruction N f =
        sampledHorizontalContourTransportShadow N f := by
      exact sampledHorizontalContourTransportReconstruction_eq_shadow N f
    _ = finitePrimeContourTransportProjection N f := by
      exact sampledHorizontalContourTransportShadow_eq_finiteProjection_ownerTomography_root
        N f
    _ = finitePrimeContourTransportRemainder N f := by
      exact finitePrimeContourTransportProjection_eq_contourTransportRemainder N f

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

/-- Analytic sampled-horizontal tomography root in real-shadow form.

The finite top-minus-bottom horizontal contour sample reconstructs the finite
contour-transport remainder after the omitted coordinate-remainder tail is restored.
This is the actual analytic reconstruction input used downstream; it does not assert
separate pointwise reconstructions of the top and bottom edges. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_root
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    (sampledHorizontalContourTransportReconstruction_eq_complex_re_add_tail
      N f).symm.trans
      (sampledHorizontalContourTransportReconstruction_eq_contourTransportRemainder_ownerTomography_root
        N f)

/-- Real-part sampled contour tomography reconstructs the finite contour-transport
remainder after restoring the omitted coordinate-remainder tail. -/
theorem sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_core
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportRemainder N f := by
  exact
    sampledHorizontalDifferenceComplex_re_add_coordinateRemainderTail_eq_contourTransportRemainder_ownerTomography_root
      N f

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

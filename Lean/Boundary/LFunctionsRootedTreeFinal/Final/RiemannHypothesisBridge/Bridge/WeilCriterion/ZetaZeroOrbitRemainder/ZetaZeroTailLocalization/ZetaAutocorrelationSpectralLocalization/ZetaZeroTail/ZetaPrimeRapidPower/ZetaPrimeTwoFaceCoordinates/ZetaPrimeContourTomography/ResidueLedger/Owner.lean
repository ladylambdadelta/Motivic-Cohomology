import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.ResidueLedger.Basic

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

/-- In a complex additive decomposition `E = V + H`, the horizontal summand is the
full residue-window error with the vertical summand subtracted. -/
theorem complex_right_eq_sub_left_of_eq_left_add_right
    {E V H : ℂ} (h : E = V + H) :
    H = E - V := by
  calc
    H = 0 + H := by
      exact (zero_add H).symm
    _ = (-V + V) + H := by
      exact congrArg (fun x : ℂ => x + H) (neg_add_cancel V).symm
    _ = -V + (V + H) := by
      exact add_assoc (-V) V H
    _ = -V + E := by
      exact congrArg (fun x : ℂ => -V + x) h.symm
    _ = E + -V := by
      exact add_comm (-V) E
    _ = E - V := by
      exact (sub_eq_add_neg E V).symm

/-- The horizontal residue-window error is the full finite rectangle residue-window error
after subtracting the vertical residue-window error. -/
theorem explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
    (g : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    explicitFormulaFamilyHorizontalResidueWindowError g F T =
      explicitFormulaFamilyResidueWindowError g F T -
        explicitFormulaFamilyVerticalResidueWindowError g F T := by
  exact
    complex_right_eq_sub_left_of_eq_left_add_right
      (explicitFormulaFamilyResidueWindowError_eq_vertical_add_horizontal g F T)

/-- The sampled horizontal difference is the horizontal residue-window error for the
prime transport rectangle. -/
theorem sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    sampledHorizontalDifferenceComplex N f =
      explicitFormulaFamilyHorizontalResidueWindowError
        (convolutionAutocorrelation f)
        completedPrimeContourTransportFamily
        (N : ℝ) := by
  rfl

/-- The prime transport combined residue-window shadow: the real part of the full
finite rectangle residue-window error after removing the vertical residue-window error,
with the coordinate-remainder tail restored. -/
noncomputable def primeTransportCombinedResidueWindowShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
      (explicitFormulaFamilyResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ) -
        explicitFormulaFamilyVerticalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The explicit horizontal sample with restored tail is the prime transport combined
residue-window shadow. -/
theorem combinedHorizontalSampleWithTail_eq_residueWindowShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      primeTransportCombinedResidueWindowShadow N f := by
  calc
    Complex.re (sampledHorizontalDifferenceComplex N f) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError N f)
    _ =
        Complex.re
          (explicitFormulaFamilyResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ) -
            explicitFormulaFamilyVerticalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ))
    _ = primeTransportCombinedResidueWindowShadow N f := by
      rfl

/-- The combined residue-window shadow is the real horizontal residue-window error with
the coordinate-remainder tail restored. -/
theorem primeTransportCombinedResidueWindowShadow_eq_horizontalResidueWindowError_add_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeTransportCombinedResidueWindowShadow N f =
      Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    primeTransportCombinedResidueWindowShadow N f =
        Complex.re
            (explicitFormulaFamilyResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ) -
              explicitFormulaFamilyVerticalResidueWindowError
                (convolutionAutocorrelation f)
                completedPrimeContourTransportFamily
                (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      rfl
    _ =
        Complex.re
            (explicitFormulaFamilyHorizontalResidueWindowError
              (convolutionAutocorrelation f)
              completedPrimeContourTransportFamily
              (N : ℝ)) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun z : ℂ =>
          Complex.re z + completedPrimeContourTransportCoordinateRemainderTail N f)
        (explicitFormulaFamilyHorizontalResidueWindowError_eq_residue_sub_vertical
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)).symm

/-- The horizontal residue-window error is the sampled horizontal difference for the prime
transport family, after taking real parts. -/
theorem finitePrimeHorizontalResidueWindowError_re_eq_sampledHorizontalDifferenceComplex_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      Complex.re (sampledHorizontalDifferenceComplex N f) := by
  exact congrArg Complex.re
    (sampledHorizontalDifferenceComplex_eq_horizontalResidueWindowError N f).symm

/-- The finite prime transport packet, with its analytic horizontal residue-shadow
presentation and its algebraic residue-defect and visible-ledger presentations.

This is a concrete packet of values, not an assumption interface: each field is populated
from the finite prime transport definitions below. -/
structure FinitePrimeTransportPacket where
  horizontalResidueShadow : ℝ
  residueDefectLedger : ℝ
  visiblePrimeLedger : ℝ
  coordinateRemainderTail : ℝ

/-- The finite prime residue-defect ledger.

This is the owner ledger for the finite prime residue defect: the finite
coordinate-remainder window with the outside-window coordinate-remainder tail subtracted. -/
noncomputable def finitePrimeResidueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourTransportResidueDefect N f

/-- The finite prime transport packet attached to the prime transport family and cutoff. -/
noncomputable def finitePrimeTransportPacket
    (N : ℕ) (f : ZetaAdmissibleFunction) : FinitePrimeTransportPacket where
  horizontalResidueShadow := finitePrimeHorizontalResidueShadow N f
  residueDefectLedger := finitePrimeResidueDefectLedger N f
  visiblePrimeLedger := finitePrimeContourVisibleLedger N f
  coordinateRemainderTail := completedPrimeContourTransportCoordinateRemainderTail N f

/-- The finite prime transport packet's analytic presentation is the horizontal residue
shadow. -/
theorem finitePrimeTransportPacket_horizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).horizontalResidueShadow =
      finitePrimeHorizontalResidueShadow N f := by
  rfl

/-- The finite prime transport packet's algebraic presentation is the residue-defect
ledger. -/
theorem finitePrimeTransportPacket_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).residueDefectLedger =
      finitePrimeResidueDefectLedger N f := by
  rfl

/-- The finite prime transport packet's visible presentation is the visible prime ledger. -/
theorem finitePrimeTransportPacket_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).visiblePrimeLedger =
      finitePrimeContourVisibleLedger N f := by
  rfl

/-- The finite prime transport packet's tail field is the outside-window coordinate-remainder
tail. -/
theorem finitePrimeTransportPacket_coordinateRemainderTail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).coordinateRemainderTail =
      completedPrimeContourTransportCoordinateRemainderTail N f := by
  rfl

/-- The finite prime residue-defect ledger is the named finite contour-transport residue
defect. -/
theorem finitePrimeResidueDefectLedger_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      finitePrimeContourTransportResidueDefect N f := by
  rfl

/-- The finite prime residue-defect ledger is the coordinate-remainder window with the
outside-window coordinate-remainder tail subtracted. -/
theorem finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (finitePrimeResidueDefectLedger_eq_residueDefect N f).trans
      (finitePrimeContourTransportResidueDefect_eq_window_sub_tail N f)

/-- The finite prime residue-defect ledger is the packet coordinate-ledger window with the
outside-window tail subtracted. -/
theorem finitePrimeResidueDefectLedger_eq_packetCoordinateLedger_sum_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeResidueDefectLedger N f =
        finitePrimeContourTransportCoordinateRemainderWindow N f -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
          N f)

/-- Restoring the outside-window tail to the finite prime residue-defect ledger recovers the
finite coordinate-remainder ledger. -/
theorem finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        (finitePrimeContourTransportCoordinateRemainderWindow N f -
            completedPrimeContourTransportCoordinateRemainderTail N f) +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f)
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact sub_add_cancel
        (finitePrimeContourTransportCoordinateRemainderWindow N f)
        (completedPrimeContourTransportCoordinateRemainderTail N f)

/-- Restoring the outside-window tail to the finite prime residue-defect ledger recovers the
visible finite prime ledger. -/
theorem finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  exact
    (finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow
      N f).trans
      (finitePrimeContourTransportCoordinateRemainderWindow_eq_visibleLedger N f)

/-- In the finite prime transport packet, the algebraic residue-defect ledger with the tail
restored is the visible prime ledger. -/
theorem finitePrimeTransportPacket_residueDefectLedger_add_tail_eq_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (finitePrimeTransportPacket N f).residueDefectLedger +
        (finitePrimeTransportPacket N f).coordinateRemainderTail =
      (finitePrimeTransportPacket N f).visiblePrimeLedger := by
  calc
    (finitePrimeTransportPacket N f).residueDefectLedger +
        (finitePrimeTransportPacket N f).coordinateRemainderTail =
        finitePrimeResidueDefectLedger N f +
          (finitePrimeTransportPacket N f).coordinateRemainderTail := by
      exact congrArg
        (fun x : ℝ =>
          x + (finitePrimeTransportPacket N f).coordinateRemainderTail)
        (finitePrimeTransportPacket_residueDefectLedger N f)
    _ =
        finitePrimeResidueDefectLedger N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ => finitePrimeResidueDefectLedger N f + x)
        (finitePrimeTransportPacket_coordinateRemainderTail N f)
    _ = finitePrimeContourVisibleLedger N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger N f
    _ = (finitePrimeTransportPacket N f).visiblePrimeLedger := by
      exact (finitePrimeTransportPacket_visiblePrimeLedger N f).symm

/-- The full finite horizontal coordinate-shadow ledger visible at cutoff `N`.

This is the full horizontal residue shadow with the omitted outside-window tail restored.
The partition theorem below identifies this full ledger with the finite window of
coordinate shadows. -/
noncomputable def finitePrimeHorizontalFullCoordinateShadowLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeHorizontalResidueShadow N f +
    completedPrimeContourTransportCoordinateRemainderTail N f

/-- The full finite horizontal coordinate-shadow ledger is the window sum of coordinate
shadows. -/
theorem finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalFullCoordinateShadowLedger N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  calc
    finitePrimeHorizontalFullCoordinateShadowLedger N f =
        finitePrimeHorizontalResidueShadow N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      rfl
    _ =
        finitePrimeHorizontalResidueShadow N f +
          ((∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeHorizontalResidueCoordinateShadow ι f) -
            finitePrimeHorizontalResidueShadow N f) := by
      exact congrArg
        (fun x : ℝ => finitePrimeHorizontalResidueShadow N f + x)
        (completedPrimeContourTransportCoordinateRemainderTail_eq_coordinateShadow_sum_sub_shadow
          N f)
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f := by
      exact
        real_reference_add_complementary_residual
          (finitePrimeHorizontalResidueShadow N f)
          (∑ ι in ZetaPrimePowerIndex.window N,
            finitePrimeHorizontalResidueCoordinateShadow ι f)

/-- The finite horizontal residue shadow plus the omitted outside-window tail is the full
coordinate-shadow ledger. -/
theorem finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeHorizontalFullCoordinateShadowLedger N f := by
  rfl

/-- The finite horizontal residue shadow is the full coordinate-shadow ledger after
subtracting the omitted outside-window tail. -/
theorem finitePrimeHorizontalResidueShadow_eq_fullCoordinateShadowLedger_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeHorizontalFullCoordinateShadowLedger N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    real_left_eq_sub_of_add_eq
      (finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
        N f)

/-- The finite horizontal residue shadow plus the omitted outside-window tail is the window
sum of coordinate shadows. -/
theorem finitePrimeHorizontalResidueShadow_add_tail_eq_sum_coordinateShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  exact
    (finitePrimeHorizontalResidueShadow_add_tail_eq_fullCoordinateShadowLedger
      N f).trans
      (finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow N f)

/-- Finite prime horizontal residue shadow in coordinate-shadow window presentation.

The combined horizontal residue shadow for the prime transport family is the finite
coordinate-shadow window with the outside-window tail subtracted.  This is the single
analytic finite-prime packet-normalization root in this lane. -/
theorem finitePrimeHorizontalResidueShadow_eq_sum_coordinateShadow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeHorizontalResidueShadow N f =
        finitePrimeHorizontalFullCoordinateShadowLedger N f -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeHorizontalResidueShadow_eq_fullCoordinateShadowLedger_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalFullCoordinateShadowLedger_eq_sum_coordinateShadow N f)

/-- Prime transport horizontal residue shadow in packet coordinate-ledger presentation.

The coordinate-shadow presentation of the horizontal residue shadow is the packet
coordinate-ledger presentation. -/
theorem primeTransportHorizontalResidueShadow_eq_packetCoordinateLedger_sum_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      (∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f) -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  calc
    finitePrimeHorizontalResidueShadow N f =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact finitePrimeHorizontalResidueShadow_eq_sum_coordinateShadow_sub_tail N f
    _ =
        (∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f) -
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeContourTransportCoordinateRemainderTail N f)
        (Finset.sum_congr
          rfl
          (fun ι _ =>
            finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
              ι f))

/-- Prime transport horizontal residue normalization.

The combined horizontal residue shadow for the prime transport family realizes the finite
prime residue-defect ledger. -/
theorem primeTransportHorizontalResidueShadow_realizes_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeResidueDefectLedger N f := by
  exact
    (primeTransportHorizontalResidueShadow_eq_packetCoordinateLedger_sum_sub_tail
      N f).trans
      (finitePrimeResidueDefectLedger_eq_packetCoordinateLedger_sum_sub_tail N f).symm

/-- Combined finite-prime horizontal residue normalization.

The finite prime horizontal residue shadow realizes the finite prime residue-defect
ledger. -/
theorem finitePrimeHorizontalResidueShadow_eq_residueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      finitePrimeResidueDefectLedger N f := by
  exact primeTransportHorizontalResidueShadow_realizes_residueDefectLedger N f

/-- Restoring the outside-window tail to the realized horizontal residue shadow gives the
visible finite prime ledger. -/
theorem primeTransportHorizontalResidueShadow_add_tail_realizes_visiblePrimeLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourVisibleLedger N f := by
  calc
    finitePrimeHorizontalResidueShadow N f +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeResidueDefectLedger N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalResidueShadow_eq_residueDefectLedger N f)
    _ = finitePrimeContourVisibleLedger N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_visiblePrimeLedger N f

/-- Prime residue-defect normalization.

The real shadow of the combined horizontal prime residue-window contribution is the finite
prime residue-defect ledger. -/
theorem finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeResidueDefectLedger N f := by
  exact
    (finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
      N f).symm.trans
      (finitePrimeHorizontalResidueShadow_eq_residueDefectLedger N f)

/-- Prime residue-defect normalization in exposed finite-window form.

The real shadow of the combined horizontal prime residue-window contribution is the
finite coordinate-remainder window after subtracting the outside-window tail. -/
theorem finitePrimeHorizontalResidueWindow_realShadow_eq_coordinateRemainderWindow_sub_tail
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeContourTransportCoordinateRemainderWindow N f -
        completedPrimeContourTransportCoordinateRemainderTail N f := by
  exact
    (finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
      N f).trans
      (finitePrimeResidueDefectLedger_eq_coordinateRemainderWindow_sub_tail N f)

/-- Prime sampled-horizontal real-shadow normalization.

The real shadow of the combined sampled horizontal prime transport contribution is the
finite residue defect ledger, transported to the historical residue-defect name. -/
theorem finitePrimeSampledHorizontalRealShadow_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (sampledHorizontalDifferenceComplex N f) =
      finitePrimeContourTransportResidueDefect N f := by
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
    _ = finitePrimeResidueDefectLedger N f := by
      exact finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger N f
    _ = finitePrimeContourTransportResidueDefect N f := by
      exact finitePrimeResidueDefectLedger_eq_residueDefect N f

/-- Prime residue-defect normalization in horizontal residue-window form.

The real shadow of the combined horizontal residue-window contribution is the finite
residue defect. -/
theorem finitePrimeHorizontalResidueWindowError_re_eq_residueDefect
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) =
      finitePrimeContourTransportResidueDefect N f := by
  exact
    (finitePrimeHorizontalResidueWindow_realShadow_eq_primeResidueDefectLedger
      N f).trans
      (finitePrimeResidueDefectLedger_eq_residueDefect N f)

/-- Restoring the coordinate-remainder tail to the horizontal residue-window real shadow
recovers the finite coordinate-remainder window. -/
theorem finitePrimeHorizontalResidueWindowError_re_add_tail_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    Complex.re
          (explicitFormulaFamilyHorizontalResidueWindowError
            (convolutionAutocorrelation f)
            completedPrimeContourTransportFamily
            (N : ℝ)) +
        completedPrimeContourTransportCoordinateRemainderTail N f =
        finitePrimeContourTransportResidueDefect N f +
          completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeHorizontalResidueWindowError_re_eq_residueDefect N f)
    _ = finitePrimeResidueDefectLedger N f +
        completedPrimeContourTransportCoordinateRemainderTail N f := by
      exact congrArg
        (fun x : ℝ =>
          x + completedPrimeContourTransportCoordinateRemainderTail N f)
        (finitePrimeResidueDefectLedger_eq_residueDefect N f).symm
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact finitePrimeResidueDefectLedger_add_tail_eq_coordinateRemainderWindow N f


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

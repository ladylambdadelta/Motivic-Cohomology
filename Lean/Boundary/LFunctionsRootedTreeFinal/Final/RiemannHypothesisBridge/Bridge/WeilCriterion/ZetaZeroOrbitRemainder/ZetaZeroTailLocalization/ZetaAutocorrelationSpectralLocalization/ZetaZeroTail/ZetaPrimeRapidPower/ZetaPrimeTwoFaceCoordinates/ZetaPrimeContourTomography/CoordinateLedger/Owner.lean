import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.Core.Owner

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

/-- The canonical contour family used to compare the finite prime transport remainder with
the horizontal top-minus-bottom contour remainder. -/
def completedPrimeContourTransportFamily : ExplicitFormulaContourFamily where
  c := (1 / 2 : ℝ) + 1
  c_gt_one := by
    have hhalf_pos : (0 : ℝ) < 1 / 2 :=
      real_half_pos_for_contourGeometry
    have hadd :
        (0 : ℝ) + 1 < (1 / 2 : ℝ) + 1 :=
      add_lt_add_right hhalf_pos 1
    exact Eq.subst
      (motive := fun x : ℝ => x < (1 / 2 : ℝ) + 1)
      (zero_add (1 : ℝ))
      hadd
  c_gt_half := by
    exact lt_add_of_pos_right (1 / 2 : ℝ) zero_lt_one
  c_ne_one := by
    intro h
    have hhalf_zero : (1 / 2 : ℝ) = 0 := by
      have hone : (1 / 2 : ℝ) + 1 = 0 + 1 := by
        exact h.trans (zero_add (1 : ℝ)).symm
      exact add_right_cancel hone
    exact (ne_of_gt real_half_pos_for_contourGeometry) hhalf_zero

/-- The coordinatewise contour-transport remainder between the contour-realized and
time-side prime distributions. -/
noncomputable def completedPrimeContourTransportCoordinateRemainder
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeContourRealizedTimeDistributionCoordinate
      ι (convolutionAutocorrelation f) -
    completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)

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

/-- The contour-transport coordinate remainder unfolds to the contour-realized coordinate
minus the time-side coordinate. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeContourTransportCoordinateRemainder ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  rfl

/-- The coordinate ledger of the finite prime transport packet.

This is the coordinate-level algebraic presentation of the finite prime residue-defect
packet before the outside-window tail is subtracted. -/
noncomputable def finitePrimeTransportPacketCoordinateLedger
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  completedPrimeContourTransportCoordinateRemainderFamily f ι

/-- The finite prime transport packet coordinate ledger is the coordinate-remainder family. -/
theorem finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeTransportPacketCoordinateLedger ι f =
      completedPrimeContourTransportCoordinateRemainderFamily f ι := by
  rfl

/-- The finite prime transport packet coordinate ledger is the contour-realized coordinate
minus the time-side coordinate. -/
theorem finitePrimeTransportPacketCoordinateLedger_eq_contour_sub_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeTransportPacketCoordinateLedger ι f =
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) -
        completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
  exact
    (finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
      ι f).trans
      ((completedPrimeContourTransportCoordinateRemainderFamily_apply ι f).trans
        (completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f))

/-- The coordinate shadow of the finite prime horizontal residue packet.

This is the coordinate presentation used by the horizontal residue-shadow window.  Its
coordinate ledger value is the finite prime transport packet coordinate ledger; the
remaining analytic content is the window presentation of the global horizontal residue
shadow, not a top/bottom edge reconstruction. -/
noncomputable def finitePrimeHorizontalResidueCoordinateShadow
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeTransportPacketCoordinateLedger ι f

/-- The finite prime horizontal residue coordinate shadow is the packet coordinate ledger. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueCoordinateShadow ι f =
      finitePrimeTransportPacketCoordinateLedger ι f := by
  rfl

/-- The finite prime horizontal residue shadow.

This is the combined top-minus-bottom horizontal prime transport contribution after taking
the real shadow. -/
noncomputable def finitePrimeHorizontalResidueShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (explicitFormulaFamilyHorizontalResidueWindowError
      (convolutionAutocorrelation f)
      completedPrimeContourTransportFamily
      (N : ℝ))

/-- The finite prime horizontal residue shadow unfolds to the real part of the combined
horizontal residue-window error. -/
theorem finitePrimeHorizontalResidueShadow_eq_horizontalResidueWindowError_re
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeHorizontalResidueShadow N f =
      Complex.re
        (explicitFormulaFamilyHorizontalResidueWindowError
          (convolutionAutocorrelation f)
          completedPrimeContourTransportFamily
          (N : ℝ)) := by
  exact rfl

/-- The norm of a contour-transport coordinate remainder is bounded by the two coordinate
norms before any height localization estimate is applied. -/
theorem norm_completedPrimeContourTransportCoordinateRemainder_le_contour_add_time
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ ≤
      ‖completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f)‖ +
        ‖completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)‖ := by
  calc
    ‖completedPrimeContourTransportCoordinateRemainder ι f‖ =
        ‖completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f)‖ := by
      exact congrArg norm
        (completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f)
    _ ≤
        ‖completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ +
          ‖completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)‖ := by
      exact norm_sub_le
        (completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f))
        (completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))

/-- Nongenuine prime-power coordinates carry no contour-transport remainder. -/
theorem completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine_ownerTomography
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    completedPrimeContourTransportCoordinateRemainder ι f = 0 := by
  have hcontour :
      completedPrimeContourRealizedTimeDistributionCoordinate
          ι (convolutionAutocorrelation f) =
        0 :=
    completedPrimeContourRealizedTimeDistributionCoordinate_eq_zero_of_not_isGenuine
      ι (convolutionAutocorrelation f) hι
  have htime :
      completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) =
        0 :=
    completedPrimeTimeDistributionCoordinate_eq_zero_of_not_isGenuine
      ι (convolutionAutocorrelation f) hι
  calc
    completedPrimeContourTransportCoordinateRemainder ι f =
        completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact completedPrimeContourTransportCoordinateRemainder_eq_contour_sub_time ι f
    _ = 0 - completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f) := by
      exact congrArg
        (fun x : ℝ =>
          x - completedPrimeTimeDistributionCoordinate ι (convolutionAutocorrelation f))
        hcontour
    _ = 0 - 0 := by
      exact congrArg (fun x : ℝ => 0 - x) htime
    _ = 0 := by
      exact sub_self 0

/-- Nongenuine prime-power coordinates carry no finite horizontal residue coordinate shadow.

This is the support statement for the coordinate-shadow family used by the finite-window
tail: only genuine prime-power indices contribute to the window ledger. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    finitePrimeHorizontalResidueCoordinateShadow ι f = 0 := by
  calc
    finitePrimeHorizontalResidueCoordinateShadow ι f =
        finitePrimeTransportPacketCoordinateLedger ι f := by
      exact finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger ι f
    _ = completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily ι f
    _ = completedPrimeContourTransportCoordinateRemainder ι f := by
      exact completedPrimeContourTransportCoordinateRemainderFamily_apply ι f
    _ = 0 := by
      exact
        completedPrimeContourTransportCoordinateRemainder_eq_zero_of_not_isGenuine_ownerTomography
          ι f hι

/-- The finite horizontal residue coordinate-shadow family is supported on genuine
prime-power indices. -/
theorem finitePrimeHorizontalResidueCoordinateShadow_supportedOn_genuine
    (f : ZetaAdmissibleFunction) :
    ∀ ι : ZetaPrimePowerIndex,
      ¬ ZetaPrimePowerIndex.IsGenuine ι →
        finitePrimeHorizontalResidueCoordinateShadow ι f = 0 := by
  intro ι hι
  exact finitePrimeHorizontalResidueCoordinateShadow_eq_zero_of_not_isGenuine
    ι f hι

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

/-- The finite coordinate-remainder window is the finite sum of the packet coordinate
ledger. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeTransportPacketCoordinateLedger ι f := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          completedPrimeContourTransportCoordinateRemainderFamily f ι := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_windowSum N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f := by
      exact Finset.sum_congr
        rfl
        (fun ι _ =>
          (finitePrimeTransportPacketCoordinateLedger_eq_coordinateRemainderFamily
            ι f).symm)

/-- The finite coordinate-remainder window is the finite window sum of horizontal residue
coordinate shadows. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_coordinateShadow_sum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        finitePrimeHorizontalResidueCoordinateShadow ι f := by
  calc
    finitePrimeContourTransportCoordinateRemainderWindow N f =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeTransportPacketCoordinateLedger ι f := by
      exact finitePrimeContourTransportCoordinateRemainderWindow_eq_packetCoordinateLedger_sum
        N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          finitePrimeHorizontalResidueCoordinateShadow ι f := by
      exact Finset.sum_congr
        rfl
        (fun ι _ =>
          (finitePrimeHorizontalResidueCoordinateShadow_eq_packetCoordinateLedger
            ι f).symm)

/-- The finite coordinate-remainder window is the sum of contour-realized coordinates minus
time-side coordinates. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_sum_coordinate_sub
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      ∑ ι in ZetaPrimePowerIndex.window N,
        (completedPrimeContourRealizedTimeDistributionCoordinate
            ι (convolutionAutocorrelation f) -
          completedPrimeTimeDistributionCoordinate
            ι (convolutionAutocorrelation f)) := by
  rfl

/-- The finite contour-transport remainder between the time-side and contour-realized prime
windows.  This is the honest finite-level difference; it is not asserted to vanish before
passing to the completed contour realization. -/
def finitePrimeContourTransportRemainder
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) -
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)

/-- The finite contour-transport remainder is the contour-realized finite window minus the
time-side finite window. -/
theorem finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      finitePrimeContourRealizedTimeDistributionWindow N (convolutionAutocorrelation f) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
  rfl

/-- The finite time-side prime window is the finite sum of its time-side coordinates. -/
theorem finitePrimeTimeDistributionWindow_eq_sum_coordinate
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        completedPrimeTimeDistributionCoordinate ι g := by
  rfl

/-- Subtracting two finite coordinate windows is the finite sum of the coordinatewise
differences. -/
theorem real_finset_sum_sub_distrib
    (s : Finset ZetaPrimePowerIndex)
    (u v : ZetaPrimePowerIndex → ℝ) :
    (∑ ι in s, u ι) - (∑ ι in s, v ι) =
      ∑ ι in s, (u ι - v ι) := by
  have hneg : ∑ ι in s, (- v ι) = - ∑ ι in s, v ι := by
    exact Finset.sum_neg_distrib
  calc
    (∑ ι in s, u ι) - (∑ ι in s, v ι) =
        (∑ ι in s, u ι) + ∑ ι in s, (- v ι) := by
      exact (sub_eq_add_neg (∑ ι in s, u ι) (∑ ι in s, v ι)).trans
        (congrArg (fun x : ℝ => (∑ ι in s, u ι) + x) hneg.symm)
    _ = ∑ ι in s, (u ι + - v ι) := by
      exact (Finset.sum_add_distrib).symm
    _ = ∑ ι in s, (u ι - v ι) := by
      exact Finset.sum_congr rfl (fun ι _ => (sub_eq_add_neg (u ι) (v ι)).symm)

/-- Transport finite coordinate-window descriptions into a coordinatewise subtraction
description. -/
theorem real_window_sub_eq_sum_coordinate_sub_of_window_eq
    {A B : ℝ} {s : Finset ZetaPrimePowerIndex}
    {u v : ZetaPrimePowerIndex → ℝ}
    (hA : A = ∑ ι in s, u ι)
    (hB : B = ∑ ι in s, v ι) :
    A - B = ∑ ι in s, (u ι - v ι) := by
  calc
    A - B = (∑ ι in s, u ι) - B := by
      exact congrArg (fun x : ℝ => x - B) hA
    _ = (∑ ι in s, u ι) - (∑ ι in s, v ι) := by
      exact congrArg (fun x : ℝ => (∑ ι in s, u ι) - x) hB
    _ = ∑ ι in s, (u ι - v ι) := by
      exact real_finset_sum_sub_distrib s u v

/-- The difference between the finite contour-realized and time-side prime windows is the
sum of the coordinatewise differences. -/
theorem finitePrimeContourRealized_sub_time_window_eq_sum_coordinate_sub
    (N : ℕ) (g : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N g -
        finitePrimeTimeDistributionWindow N g =
      ∑ ι in ZetaPrimePowerIndex.window N,
        (completedPrimeContourRealizedTimeDistributionCoordinate ι g -
          completedPrimeTimeDistributionCoordinate ι g) := by
  exact
    real_window_sub_eq_sum_coordinate_sub_of_window_eq
      (finitePrimeContourRealizedTimeDistributionWindow_eq_sum_coordinate N g)
      (finitePrimeTimeDistributionWindow_eq_sum_coordinate N g)

/-- The finite contour-transport remainder is the finite window sum of the coordinatewise
contour-transport remainders. -/
theorem finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportRemainder N f =
      finitePrimeContourTransportCoordinateRemainderWindow N f := by
  calc
    finitePrimeContourTransportRemainder N f =
        finitePrimeContourRealizedTimeDistributionWindow N
            (convolutionAutocorrelation f) -
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
      exact finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f
    _ =
        ∑ ι in ZetaPrimePowerIndex.window N,
          (completedPrimeContourRealizedTimeDistributionCoordinate
              ι (convolutionAutocorrelation f) -
            completedPrimeTimeDistributionCoordinate
              ι (convolutionAutocorrelation f)) := by
      exact
        finitePrimeContourRealized_sub_time_window_eq_sum_coordinate_sub
          N (convolutionAutocorrelation f)
    _ = finitePrimeContourTransportCoordinateRemainderWindow N f := by
      exact
        (finitePrimeContourTransportCoordinateRemainderWindow_eq_sum_coordinate_sub
          N f).symm

/-- The finite coordinate-remainder window is the contour-realized window minus the
time-side window. -/
theorem finitePrimeContourTransportCoordinateRemainderWindow_eq_contourWindow_sub_timeWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) -
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) := by
  exact
    (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm.trans
      (finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f)

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
  let T : ℝ := finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f)
  let C : ℝ :=
    finitePrimeContourRealizedTimeDistributionWindow N
      (convolutionAutocorrelation f)
  have hrem : finitePrimeContourTransportRemainder N f = C - T :=
    finitePrimeContourTransportRemainder_eq_contourWindow_sub_timeWindow N f
  calc
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportRemainder N f =
        T + (C - T) := by
      exact congrArg
        (fun x : ℝ => T + x)
        hrem
    _ = C := by
      exact real_reference_add_complementary_residual T C

/-- Finite contour realization is the time-side window plus the coordinate-remainder
window. -/
theorem finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
      finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) := by
  calc
    finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f =
        finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
          finitePrimeContourTransportRemainder N f := by
      exact congrArg
        (fun x : ℝ =>
          finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) + x)
        (finitePrimeContourTransportRemainder_eq_coordinateRemainderWindow N f).symm
    _ =
        finitePrimeContourRealizedTimeDistributionWindow N
          (convolutionAutocorrelation f) := by
      exact finitePrimeTimeDistributionWindow_add_contourTransportRemainder N f

/-- The finite contour-realized window is the time-side window plus the
coordinate-remainder window. -/
theorem finitePrimeContourRealizedTimeDistributionWindow_eq_timeWindow_add_coordinateRemainderWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    finitePrimeContourRealizedTimeDistributionWindow N
        (convolutionAutocorrelation f) =
      finitePrimeTimeDistributionWindow N (convolutionAutocorrelation f) +
        finitePrimeContourTransportCoordinateRemainderWindow N f := by
  exact
    (finitePrimeTimeDistributionWindow_add_coordinateRemainderWindow N f).symm

/-- A real subtraction identity can be transported into a top-minus-bottom real-part
identity. -/
theorem complex_re_sub_eq_real_difference_of_re_eq
    {top bottom : ℂ} {a b : ℝ}
    (htop : Complex.re top = a)
    (hbottom : Complex.re bottom = b) :
    Complex.re (top - bottom) = a - b := by
  calc
    Complex.re (top - bottom) = Complex.re top - Complex.re bottom := by
      exact Complex.sub_re top bottom
    _ = a - Complex.re bottom := by
      exact congrArg (fun x : ℝ => x - Complex.re bottom) htop
    _ = a - b := by
      exact congrArg (fun x : ℝ => a - x) hbottom


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

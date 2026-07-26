import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalTransportParts.CoordinateOwnerTransport

/-!
# Completed diagonal-debt window limit

This file owns the finite-window convergence input for transporting the
completed diagonal-debt coordinate presentation to the owner completed
diagonal-debt form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Majorant summability gives summability of the completed diagonal-debt
coordinate stream at the transport owner level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralCoordinateMajorant_summable_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    f
    hmajorant

/-- Majorant summability gives the completed diagonal-debt coordinate stream
with its raw coordinate presentation as sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
  (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralCoordinateMajorant_summable_windowLimit_owner
    f hmajorant).hasSum

/-- Diagonal-debt real-coordinate `HasSum` inputs give summability of the
completed diagonal-debt coordinate stream at the transport owner level. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_diagonalDebtCoordinate_re_hasSum_windowLimit_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_of_spectralCoordinateMajorant_summable_windowLimit_owner
    f hmajorant

/-- Diagonal-debt real-coordinate `HasSum` inputs give the completed
diagonal-debt coordinate stream with its raw coordinate presentation as sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_windowLimit_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
    f hmajorant

/-- The completed diagonal-debt coordinate stream vanishes on nongenuine
prime-power indices. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine_windowLimit_owner
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f = 0 :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine
    index f hindex

/-- The local diagonal-debt coordinate alias has the owner `HasSum`. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_hasSum_coordinateTsum_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (coordinate : ZetaPrimePowerIndex → ℂ)
    (hcoordinate :
      coordinate =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    HasSum coordinate
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
  Eq.subst
    (motive := fun stream : ZetaPrimePowerIndex → ℂ =>
      HasSum stream
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))
    hcoordinate.symm
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_hasSum_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
      f hmajorant)

/-- The local diagonal-debt coordinate alias vanishes off the genuine
prime-power indices. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_eq_zero_of_not_isGenuine_windowLimit_owner
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (coordinate : ZetaPrimePowerIndex → ℂ)
    (hcoordinate :
      coordinate =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    coordinate index = 0 :=
  Eq.subst
    (motive := fun value : ℂ => value = 0)
    (congrFun hcoordinate index).symm
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine_windowLimit_owner
      index f hindex)

/-- Box sums of the local diagonal-debt coordinate alias equal genuine-window
sums. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_box_sum_eq_window_sum_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (coordinate : ZetaPrimePowerIndex → ℂ)
    (hcoordinate :
      coordinate =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :
    (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N,
      coordinate index) =
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N,
        coordinate index) :=
  funext
    (fun N : ℕ =>
      ZetaPrimePowerIndex.sum_box_eq_sum_window_of_zero_not_isGenuine
        coordinate
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_eq_zero_of_not_isGenuine_windowLimit_owner
            index f coordinate hcoordinate)
        N)

/-- The completed diagonal-debt window sequence is the window sum sequence of
the local coordinate alias. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtWindow_eq_coordinateAlias_window_sum_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (coordinate : ZetaPrimePowerIndex → ℂ)
    (hcoordinate :
      coordinate =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :
    (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f) =
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N,
        coordinate index) :=
  funext
    (fun N : ℕ =>
      Eq.subst
        (motive := fun stream : ZetaPrimePowerIndex → ℂ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f =
            ∑ index in ZetaPrimePowerIndex.window N,
              stream index)
        hcoordinate.symm
        (Eq.refl (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)))

/-- Majorant summability makes completed diagonal-debt windows exhaust the raw
coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let coordinate :
      ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f
  let hcoordinate :
      coordinate =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f :=
    Eq.refl coordinate
  let hhasSum :
      HasSum coordinate
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_hasSum_coordinateTsum_windowLimit_owner
      f coordinate hcoordinate hmajorant
  let hbox :
      Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N,
          coordinate index)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      coordinate
      (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)
      hhasSum
  let hbox_window :
      (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N,
        coordinate index) =
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N,
          coordinate index) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateAlias_box_sum_eq_window_sum_windowLimit_owner
      f coordinate hcoordinate
  let hwindow_def :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f) =
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N,
          coordinate index) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtWindow_eq_coordinateAlias_window_sum_windowLimit_owner
      f coordinate hcoordinate
  Eq.subst
    (motive := fun sequence : ℕ → ℂ =>
      Tendsto sequence atTop
        (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)))
    hwindow_def.symm
    (Eq.subst
      (motive := fun sequence : ℕ → ℂ =>
        Tendsto sequence atTop
          (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)))
      hbox_window
      hbox)

/-- Diagonal-debt real-coordinate `HasSum` inputs make completed diagonal-debt
windows exhaust the raw coordinate presentation. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_coordinateTsum_of_diagonalDebtCoordinate_re_hasSum_windowLimit_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
    f hmajorant

/-- Majorant summability transports completed diagonal-debt window convergence
to the owner completed diagonal-debt form. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_owner_of_spectralCoordinateMajorant_summable_transport_owner
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
        atTop
        (𝓝 target))
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_eq_owner_of_spectralCoordinateMajorant_summable_coordinateAssembly
      f hmajorant hcoordinateZero)
    (zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_coordinateTsum_of_spectralCoordinateMajorant_summable_windowLimit_owner
      f hmajorant)

/-- Diagonal-debt real-coordinate `HasSum` inputs transport completed
diagonal-debt window convergence to the owner completed diagonal-debt form. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_owner_of_diagonalDebtCoordinate_re_hasSum_transport_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
  let hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_owner_of_spectralCoordinateMajorant_summable_transport_owner
    f hmajorant hcoordinateZero

/-- The real completed diagonal-debt window sequence is the real part of the
complex completed diagonal-debt window sequence. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_re_window_sequence_transport_owner
    (f : ZetaAdmissibleFunction) :
    (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)) :=
  funext
    (fun N : ℕ =>
      Eq.refl (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f))

/-- Complex diagonal-debt window convergence transports to real diagonal-debt
window convergence. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_of_window_tendsto_owner_transport_owner
    (f : ZetaAdmissibleFunction)
    (hwindow :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)
        atTop
        (𝓝 (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  let hreal :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f))
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    ((RCLike.reCLM : ℂ →L[ℝ] ℝ).continuous.tendsto
      (zetaCompletedPrimeDefectKernelDiagonalDebt f)).comp
      hwindow
  let hseries :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_re_window_sequence_transport_owner
      f
  Eq.subst
    (motive := fun series : ℕ → ℝ =>
      Tendsto series atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))))
    hseries.symm
    hreal

/-- The completed diagonal-debt real windows converge to the owner completed
diagonal-debt real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_transport_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_of_window_tendsto_owner_transport_owner
    f
    (zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_owner_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)

/-- Diagonal-debt real-coordinate `HasSum` inputs give real completed
diagonal-debt window convergence to the owner real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_of_diagonalDebtCoordinate_re_hasSum_transport_owner
    (f : ZetaAdmissibleFunction) (C Creflect : ℝ)
    (hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        C)
    (hhasSumReflect :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
              index (ZetaAdmissibleFunction.reflect f)))
        Creflect)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_of_window_tendsto_owner_transport_owner
    f
    (zetaCompletedPrimeDefectKernelDiagonalDebtWindow_tendsto_owner_of_diagonalDebtCoordinate_re_hasSum_transport_owner
      f C Creflect hhasSum hhasSumReflect hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

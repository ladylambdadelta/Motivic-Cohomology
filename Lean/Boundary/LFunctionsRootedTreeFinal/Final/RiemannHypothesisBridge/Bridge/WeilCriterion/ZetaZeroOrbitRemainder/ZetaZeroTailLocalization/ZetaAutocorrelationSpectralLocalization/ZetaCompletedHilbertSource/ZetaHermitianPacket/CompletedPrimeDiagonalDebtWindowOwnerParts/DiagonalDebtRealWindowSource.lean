import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PositiveWeightedSampleSummabilitySource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalCoordinateOwnerSource
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.DiagonalDebtWindowFiniteSumBound
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Completed prime diagonal-debt real-window source

This file owns the non-circular real-window domination source for completed
prime diagonal debt.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- A finite completed prime diagonal-debt real window is the finite sum of
real diagonal-debt coordinates over that window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_windowSource
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      ∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  Complex.re_sum
    (ZetaPrimePowerIndex.window N)
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)

/-- A finite completed diagonal-debt real window is the sum of the completed
two-face real window and the positive real window. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_windowSource
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
        zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveWindow N f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f
  let hexpansion : P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
      N f
  let hstart :
      zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f =
        Complex.re D :=
    Eq.refl (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
  let hstep1 :
      Complex.re D = Complex.re (P + T) :=
    congrArg Complex.re hexpansion.symm
  let hstep2 :
      Complex.re (P + T) = Complex.re P + Complex.re T :=
    Complex.add_re P T
  let hstep3 :
      Complex.re P + Complex.re T = Complex.re T + Complex.re P :=
    add_comm (Complex.re P) (Complex.re T)
  let hstep4 :
      Complex.re T + Complex.re P =
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
          zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    Eq.refl (Complex.re T + Complex.re P)
  hstart.trans (hstep1.trans (hstep2.trans (hstep3.trans hstep4)))

/-- The completed diagonal-debt coordinate stream is summable. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_windowSource
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
  summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
      f)

/-- Completed diagonal-debt real windows converge to the raw
coordinate-presentation real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_windowSource
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝
        (Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
      f)

/-- Positive prime-defect real windows converge to the owner positive
completed channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_windowSource
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
  zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_coordinateTsum_re
    f
    (zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
      f)
    (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_ownerPositiveChannel_windowSource
      f
      (zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
        f)
      hcoordinateZero
    )

/-- Nongenuine prime-power indices have zero completed two-face/GNS
symmetrized coordinate. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_windowSource
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hindex : ¬ ZetaPrimePowerIndex.IsGenuine index) :
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f = 0 :=
  let C : ℂ := zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f
  let hweight : ZetaPrimePowerIndex.weight index = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine index hindex
  let hC : C = 0 :=
    let hstep1 :
        C =
          (index.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi f index.center *
              star
                (zetaCompletedExplicitFormulaPhi
                  f (-(index.center : ℂ)))) :=
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair
        index f
    let hstep2 :
        (index.weight : ℂ) *
            (zetaCompletedExplicitFormulaPhi f index.center *
              star
                (zetaCompletedExplicitFormulaPhi
                  f (-(index.center : ℂ)))) =
          (0 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f index.center *
              star
                (zetaCompletedExplicitFormulaPhi
                  f (-(index.center : ℂ)))) :=
      congrArg
        (fun value : ℝ =>
          (value : ℂ) *
            (zetaCompletedExplicitFormulaPhi f index.center *
              star
                (zetaCompletedExplicitFormulaPhi
                  f (-(index.center : ℂ)))))
        hweight
    let hstep3 :
        (0 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f index.center *
              star
                (zetaCompletedExplicitFormulaPhi
                  f (-(index.center : ℂ)))) =
          0 :=
      zero_mul
        (zetaCompletedExplicitFormulaPhi f index.center *
          star
            (zetaCompletedExplicitFormulaPhi
              f (-(index.center : ℂ))))
    hstep1.trans (hstep2.trans hstep3)
  let hstart :
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f =
        C + star C :=
    Eq.refl (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
  let hstep1 :
      C + star C = 0 + star 0 :=
    congrArg₂ HAdd.hAdd hC (congrArg star hC)
  let hstep2 :
      0 + star (0 : ℂ) = 0 + 0 :=
    congrArg (fun value : ℂ => 0 + value) (star_zero ℂ)
  let hstep3 :
      (0 : ℂ) + 0 = 0 :=
    zero_add 0
  hstart.trans (hstep1.trans (hstep2.trans hstep3))

/-- The finite sum of completed symmetrized two-face/GNS coordinates is the
completed two-face/GNS matrix window. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_windowSource
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ index in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let C : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate index f
  let hsum :
      (∑ index in s,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        (∑ index in s, C index) + (∑ index in s, star (C index)) :=
    Finset.sum_add_distrib
  let hstar :
      (∑ index in s, star (C index)) =
        star (∑ index in s, C index) :=
    (star_sum s C).symm
  let hstart :
      (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        (∑ index in s,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) :=
    Eq.refl
      (∑ index in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f)
  let hstep1 :
      (∑ index in s,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f) =
        (∑ index in s, C index) + (∑ index in s, star (C index)) :=
    hsum
  let hstep2 :
      (∑ index in s, C index) + (∑ index in s, star (C index)) =
        (∑ index in s, C index) + star (∑ index in s, C index) :=
    congrArg
      (fun value : ℂ => (∑ index in s, C index) + value)
      hstar
  let hstep3 :
      (∑ index in s, C index) + star (∑ index in s, C index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f :=
    Eq.refl ((∑ index in s, C index) + star (∑ index in s, C index))
  hstart.trans (hstep1.trans (hstep2.trans hstep3))

/-- Completed two-face/GNS matrix windows exhaust the owner completed
two-face/GNS matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowSource
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)) :=
  let u : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate index f
  let hsum : Summable u :=
    summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f
      (zetaCompletedPrimeSpectralCoordinateMajorant_summable_windowSource
        f)
  let hzero :
      ∀ index : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine index → u index = 0 :=
    fun index hindex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_eq_zero_of_not_isGenuine_windowSource
        index f hindex
  let hwindow :
      (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) =
        fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N, u index :=
    funext
      (fun N : ℕ =>
        (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_sum_eq_matrixWindow_windowSource
          N f).symm)
  let hlimit :
      Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.window N, u index)
        atTop
        (𝓝 (∑' index : ZetaPrimePowerIndex, u index)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      u hsum hzero
  let htarget :
      (∑' index : ZetaPrimePowerIndex, u index) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
      f
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f)
        atTop
        (𝓝 target))
    htarget
    (Eq.subst
      (motive := fun stream : ℕ → ℂ =>
        Tendsto stream atTop
          (𝓝 (∑' index : ZetaPrimePowerIndex, u index)))
      hwindow.symm
      hlimit)

/-- Completed two-face matrix windows converge in real part to the owner
completed two-face matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_windowSource
    (f : ZetaAdmissibleFunction) :
    Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
  (Complex.continuous_re.tendsto
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)).comp
    (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_tendsto_ownerMatrixCoefficient_windowSource
      f)

/-- The owner completed diagonal-debt real scalar splits into the owner
positive channel and completed two-face real coefficient. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_windowSource
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
      completedPrimeDefectKernelPositiveChannel f +
        Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let hpositive :
      completedPrimeDefectKernelPositiveChannel f = Complex.re P :=
    Eq.refl (completedPrimeDefectKernelPositiveChannel f)
  let hexpansion : P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
      f
  let hstep1 :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re D :=
    Eq.refl (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
  let hstep2 :
      Complex.re D = Complex.re (P + T) :=
    congrArg Complex.re hexpansion.symm
  let hstep3 :
      Complex.re (P + T) = Complex.re P + Complex.re T :=
    Complex.add_re P T
  let hstep4 :
      Complex.re P + Complex.re T =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    congrArg
      (fun value : ℝ =>
        value + Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      hpositive.symm
  hstep1.trans (hstep2.trans (hstep3.trans hstep4))

/-- Completed diagonal-debt real windows converge to the owner completed
diagonal-debt real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_owner_re_windowSource
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
  let htwoFace :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f))
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))) :=
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow_re_tendsto_ownerMatrixCoefficient_re_windowSource
      f
  let hpositive :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (completedPrimeDefectKernelPositiveChannel f)) :=
    zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_ownerPositiveChannel_windowSource
      f hcoordinateZero
  let hadd :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝
          (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
            completedPrimeDefectKernelPositiveChannel f)) :=
    htwoFace.add hpositive
  let htargetOrder :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
          completedPrimeDefectKernelPositiveChannel f =
        completedPrimeDefectKernelPositiveChannel f +
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) :=
    add_comm
      (Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f))
      (completedPrimeDefectKernelPositiveChannel f)
  let howner :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) +
          completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    htargetOrder.trans
      (zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_positiveChannel_add_twoFace_re_windowSource
        f).symm
  let haddOwner :
      Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))) :=
    Eq.subst
      (motive := fun value : ℝ =>
        Tendsto
          (fun N : ℕ =>
            Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
              zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 value))
      howner
      hadd
  let hfun :
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        fun N : ℕ =>
          Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f) +
            zetaCompletedPrimeDefectKernelPositiveRealWindow N f :=
    funext
      (fun N : ℕ =>
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_twoFace_re_add_positiveRealWindow_windowSource
          N f)
  Eq.subst
    (motive := fun stream : ℕ → ℝ =>
      Tendsto stream atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))))
    hfun.symm
    haddOwner

/-- The raw completed diagonal-debt coordinate presentation has the owner
completed diagonal-debt real scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_windowSource
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_windowSourcePrimitive
    f hcoordinateZero

/-- The real completed prime diagonal-debt coordinate stream has the raw
coordinate-presentation real scalar as its sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_windowSource
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
  let hsum :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_summable_windowSource
      f
  let hcoord :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    hsum.hasSum
  (RCLike.reCLM : ℂ →L[ℝ] ℝ).hasSum
    hcoord

/-- The real completed prime diagonal-debt coordinate stream has the owner
completed prime diagonal-debt scalar as its sum. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar_windowSource
    (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
  let hcoord :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_coordinateTsum_windowSource
      f
  Eq.subst
    (motive := fun value : ℝ =>
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        value)
    (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum_re_eq_owner_re_windowSource
      f hcoordinateZero)
    hcoord

/-- The completed prime diagonal-debt real window is dominated by the owner
completed prime diagonal-debt scalar. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar_windowSource
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
  let hhasSum :
      HasSum
        (fun index : ZetaPrimePowerIndex =>
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
        (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_hasSum_ownerScalar_windowSource
      f hcoordinateZero
  let hnonnegative :
      ∀ index : ZetaPrimePowerIndex,
        0 ≤
          Complex.re
            (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f) :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
        index f
  let hsum :
      (∑ index in ZetaPrimePowerIndex.window N,
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f)) ≤
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    finite_window_sum_le_hasSum_of_nonnegative
      (ZetaPrimePowerIndex.window N)
      (fun index : ZetaPrimePowerIndex =>
        Complex.re
          (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate index f))
      hnonnegative
      hhasSum
  Eq.subst
    (motive := fun value : ℝ =>
      value ≤ Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f))
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_eq_sum_re_windowSource
      N f).symm
    hsum

/-- The finite completed prime diagonal-debt real-window complement inside the
owner completed prime diagonal-debt scalar is nonnegative. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_ownerComplement_nonnegative_windowSource
    (N : ℕ) (f : ZetaAdmissibleFunction)
    (hcoordinateZero :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        0) :
    0 ≤
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) -
        zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f :=
  sub_nonneg.mpr
    (zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_le_ownerScalar_windowSource
      N f hcoordinateZero)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryCancellationRealShadowParts.TwoFaceWindowParts.PairedTraceKernel
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeSpectralMajorantSummability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.SpectralMajorant

/-!
# Boundary two-face ledger cancellation source

This file owns the rectangular two-face residue-ledger cancellation input.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Source finite-rectangle cancellation for the total symmetrized completed
two-face autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_symmetrized_boxSum_tendsto_zero_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction)
    (hmajorant : Summable (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            star
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f)))
      Filter.atTop
      (nhds 0) := by
  let symmetrized : ℕ → ℂ :=
    fun N : ℕ =>
      ∑ index in ZetaPrimePowerIndex.box N,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          star
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))
  let paired : ℕ → ℂ :=
    fun N : ℕ =>
      ∑ index in ZetaPrimePowerIndex.box N,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
  have hpaired :
      Filter.Tendsto paired Filter.atTop (nhds 0) := by
    unfold paired
    exact
      zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_pairedTraceKernel_source
        f hmajorant
  have hstream : symmetrized = paired := by
    funext N
    unfold symmetrized
    unfold paired
    exact Finset.sum_congr
      rfl
      (fun index _ =>
        congrArg
          (fun value : ℂ =>
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
                index f +
              value)
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
            index f))
  exact Eq.subst
    (motive := fun stream : ℕ → ℂ =>
      Filter.Tendsto stream Filter.atTop (nhds 0))
    hstream.symm
    hpaired

/-- Source vanishing of the total symmetrized completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_symmetrized_tsum_eq_zero_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction)
    (horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) :
      (∑' index : ZetaPrimePowerIndex,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          star
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f))) = 0 := by
  let s : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f +
        star
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)
  have hsummableStar :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          star
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f)) :=
    horiented.star
  have hsummable : Summable s := by
    unfold s
    exact horiented.add hsummableStar
  have hboxTsum :
      Filter.Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, s index)
        Filter.atTop
        (nhds (∑' index : ZetaPrimePowerIndex, s index)) :=
    ZetaPrimePowerIndex.tendsto_sum_box_of_hasSum_complex
      s
      (∑' index : ZetaPrimePowerIndex, s index)
      hsummable.hasSum
  have hboxZero :
      Filter.Tendsto
        (fun N : ℕ => ∑ index in ZetaPrimePowerIndex.box N, s index)
        Filter.atTop
        (nhds 0) := by
    unfold s
    exact
      zetaCompletedPrimePowerAutocorrelation_symmetrized_boxSum_tendsto_zero_traceKernel_source_primitive
        f hmajorant
  have htarget :
      (∑' index : ZetaPrimePowerIndex, s index) = 0 :=
    tendsto_nhds_unique hboxTsum hboxZero
  unfold s at htarget
  exact htarget

/-- Source anti-Hermitian total orientation for the completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction)
    (horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) :
    star
        (∑' index : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f) =
      -∑' index : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f
  let z : ℂ := ∑' index : ZetaPrimePowerIndex, u index
  have hu : Summable u := by
    exact horiented
  have hstarSummable : Summable (fun index : ZetaPrimePowerIndex => star (u index)) :=
    hu.star
  have hsum :
      (∑' index : ZetaPrimePowerIndex, (u index + star (u index))) = 0 := by
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelation_symmetrized_tsum_eq_zero_traceKernel_source_primitive
        f horiented
  have hsplit :
      (∑' index : ZetaPrimePowerIndex, (u index + star (u index))) =
        z + star z := by
    calc
      (∑' index : ZetaPrimePowerIndex, (u index + star (u index))) =
          (∑' index : ZetaPrimePowerIndex, u index) +
            (∑' index : ZetaPrimePowerIndex, star (u index)) := by
        exact tsum_add hu hstarSummable
      _ = z + star z := by
        exact congrArg
          (fun value : ℂ => z + value)
          hu.hasSum.star.tsum_eq
  have hzero : z + star z = 0 :=
    hsplit.symm.trans hsum
  have hneg_add : -z + z = 0 :=
    neg_add_cancel z
  have hmove : star z = -z := by
    calc
      star z = 0 + star z := by
        exact (zero_add (star z)).symm
      _ = (-z + z) + star z := by
        exact congrArg (fun value : ℂ => value + star z) hneg_add.symm
      _ = -z + (z + star z) := by
        exact add_assoc (-z) z (star z)
      _ = -z + 0 := by
        exact congrArg (fun value : ℂ => -z + value) hzero
      _ = -z := by
        exact add_zero (-z)
  unfold z at hmove
  unfold u at hmove
  exact hmove

/-- Source cancellation for the opposite oriented completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_traceKernel_source
    (f : ZetaAdmissibleFunction)
    (horiented :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f)) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
          index f)
      (-(∑' index : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
          index f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f
  let z : ℂ := ∑' index : ZetaPrimePowerIndex, u index
  have hu_summable : Summable u := by
    exact horiented
  have hu : HasSum u z := by
    exact hu_summable.hasSum
  have hstar : HasSum (fun index : ZetaPrimePowerIndex => star (u index)) (star z) :=
    hu.star
  have hanti : star z = -z := by
    unfold z
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_traceKernel_source_primitive
        f horiented
  have hstar_neg : HasSum (fun index : ZetaPrimePowerIndex => star (u index)) (-z) :=
    Eq.subst
      (motive := fun value : ℂ =>
        HasSum (fun index : ZetaPrimePowerIndex => star (u index)) value)
      hanti
      hstar
  have hpoint :
      (fun index : ZetaPrimePowerIndex => star (u index)) = v := by
    funext index
    unfold u
    unfold v
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        index f
  exact
    Eq.subst
      (motive := fun stream : ZetaPrimePowerIndex → ℂ =>
        HasSum stream (-z))
      hpoint
      hstar_neg

/-- Source total cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f
  exact
    zetaCompletedPrimePowerAutocorrelationPairedTraceKernel_hasSum_zero_of_matrixCoefficient_eq_zero
      f
      (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_eq_zero_pairedTraceKernel_source
        f)

/-- Explicit diagonal-debt real-coordinate `HasSum` inputs give total
cancellation for the paired completed two-face autocorrelation coordinate
stream. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_of_diagonalDebtCoordinate_re_hasSum_traceKernel_source_primitive
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
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      0 := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
        index f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
        index f
  let z : ℂ := ∑' index : ZetaPrimePowerIndex, u index
  have hmajorant :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f) :=
    zetaCompletedPrimeSpectralCoordinateMajorant_summable_of_diagonalDebtCoordinate_re_hasSum_diagonalDebt_owner
      f C Creflect hhasSum hhasSumReflect
  have hu_summable : Summable u :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_of_spectralMajorant
      f hmajorant
  have hu : HasSum u z := by
    exact hu_summable.hasSum
  have hv : HasSum v (-z) := by
    unfold v
    unfold z
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_traceKernel_source
        f hu_summable
  have hpair : HasSum (fun index : ZetaPrimePowerIndex => u index + v index) (z + -z) :=
    hu.add hv
  have hzero : z + -z = 0 :=
    add_neg_cancel z
  have htarget :
      (fun index : ZetaPrimePowerIndex => u index + v index) =
        fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f := by
    funext index
    exact Eq.refl _
  exact
    Eq.subst
      (motive := fun stream : ZetaPrimePowerIndex → ℂ =>
        HasSum stream 0)
      htarget
      (Eq.subst
        (motive := fun value : ℂ =>
          HasSum (fun index : ZetaPrimePowerIndex => u index + v index) value)
        hzero
        hpair)

/-- Source rectangular cancellation for the paired completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ index in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
              index f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
              index f))
      Filter.atTop
      (nhds 0) := by
  exact
    ZetaPrimePowerIndex.tendsto_sum_box_zero_of_hasSum_complex
      (fun index : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate
            index f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate
            index f)
      (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_traceKernel_source_primitive
        f)

/-- Source residue-ledger cancellation for the completed two-face
autocorrelation coordinate stream. -/
theorem zetaCompletedPrimePowerAutocorrelationLedgerCancellation_traceKernel_source_primitive
    (f : ZetaAdmissibleFunction) :
    ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f := by
  exact
    zetaCompletedPrimePowerAutocorrelationTwoFaceCoordinate_boxSum_tendsto_zero_traceKernel_source_primitive
      f

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

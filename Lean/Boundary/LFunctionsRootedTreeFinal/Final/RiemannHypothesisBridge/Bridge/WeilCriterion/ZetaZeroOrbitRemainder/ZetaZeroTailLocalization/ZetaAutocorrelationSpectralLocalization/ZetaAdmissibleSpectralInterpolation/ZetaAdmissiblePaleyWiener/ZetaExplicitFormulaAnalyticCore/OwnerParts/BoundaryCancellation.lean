import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ContourTomography

/-!
# Boundary explicit-formula analytic core

This file fixes the analytic vocabulary used by the completed Guinand--Weil
route:

* the involution `f†`,
* the autocorrelation kernel `g_f`,
* the spectral transform `Φ_f`,
* the completed zeta logarithmic derivative integrand,
* and the named prime / archimedean / correction pieces.

The file is intentionally definitional. The contour, residue, and decay
arguments will consume these owner-level objects.
-/

/-! This owner part contains the boundary cancellation and completed prime-power sums. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Public analytic-core wrapper for the contour-tomography real-shadow cancellation. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (nhds 0) :=
  zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
    f hledger

/-- Rectangular windows of the two opposite oriented faces cancel in the completed boundary
limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f))
      Filter.atTop
      (nhds 0) := by
  have hshadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_boundaryCancellation
      f hledger
  have hfun :
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)) =
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) := by
    funext N
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
        N f
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (nhds 0))
    hfun.symm
    hshadow

/-- The sum of the two oriented-face series is zero in the completed boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      0 := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f
  have hu : Summable u := by
    exact horiented
  have hv : Summable v := by
    exact horiented.star.congr
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
          ι f)
  have huv : Summable (fun ι : ZetaPrimePowerIndex => u ι + v ι) :=
    hu.add hv
  have hbox_tsum :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N, (u ι + v ι))
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, (u ι + v ι))) :=
    huv.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hbox_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N, (u ι + v ι))
        Filter.atTop
        (nhds 0) := by
    have hcancel :=
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_boundaryCancellation
        f hledger
    exact hcancel
  have htsum_zero :
      (∑' ι : ZetaPrimePowerIndex, (u ι + v ι)) = 0 :=
    tendsto_nhds_unique hbox_tsum hbox_zero
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) z)
    htsum_zero
    huv.hasSum

/-- The opposite oriented prime-power boundary face cancels the positive oriented face in the
completed boundary pairing. -/
theorem zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_hasSum_neg_tsum_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      (-(∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let v : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f
  have hsum :
      HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) 0 := by
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_boundaryCancellation
        f hledger horiented
  have hu : Summable u := by
    exact horiented
  have hv : Summable v := by
    exact horiented.star.congr
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
          ι f)
  have htarget :
      (0 : ℂ) = (∑' ι : ZetaPrimePowerIndex, u ι) +
          (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
    exact (add_neg_cancel (∑' ι : ZetaPrimePowerIndex, u ι)).symm
  have hv_sum :
      HasSum v (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
    have hadd :
        HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι)
          ((∑' ι : ZetaPrimePowerIndex, u ι) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))) := by
      exact Eq.subst
        (motive := fun z : ℂ =>
          HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) z)
        htarget
        hsum
    have hu_sum : HasSum u (∑' ι : ZetaPrimePowerIndex, u ι) :=
      hu.hasSum
    have hneg_u :
        HasSum (fun ι : ZetaPrimePowerIndex => -u ι)
          (-(∑' ι : ZetaPrimePowerIndex, u ι)) :=
      hu_sum.neg
    have hpoint :
        (fun ι : ZetaPrimePowerIndex => u ι + v ι + -u ι) = v := by
      funext ι
      calc
        u ι + v ι + -u ι = v ι + (u ι + -u ι) := by
          exact Eq.trans
            (add_right_comm (u ι) (v ι) (-u ι))
            (add_comm (u ι + -u ι) (v ι))
        _ = v ι + 0 := by
          exact congrArg (fun z : ℂ => v ι + z) (add_neg_cancel (u ι))
        _ = v ι := by
          exact add_zero (v ι)
    have hadded :
        HasSum
          (fun ι : ZetaPrimePowerIndex => (u ι + v ι) + -u ι)
          (((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))) :=
      hadd.add hneg_u
    have htarget2 :
        ((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι)) =
          -(∑' ι : ZetaPrimePowerIndex, u ι) := by
      calc
        ((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι)) =
            0 + (-(∑' ι : ZetaPrimePowerIndex, u ι)) := by
          exact congrArg
            (fun z : ℂ => z + (-(∑' ι : ZetaPrimePowerIndex, u ι)))
            (add_neg_cancel (∑' ι : ZetaPrimePowerIndex, u ι))
        _ = -(∑' ι : ZetaPrimePowerIndex, u ι) := by
          exact zero_add (-(∑' ι : ZetaPrimePowerIndex, u ι))
    exact Eq.subst
      (motive := fun w : ℂ => HasSum v w)
      htarget2
      (Eq.subst
        (motive := fun w : ZetaPrimePowerIndex → ℂ => HasSum w
          (((∑' ι : ZetaPrimePowerIndex, u ι) +
              (-(∑' ι : ZetaPrimePowerIndex, u ι))) +
            (-(∑' ι : ZetaPrimePowerIndex, u ι))))
        hpoint
        hadded)
  exact hv_sum

/-- The conjugated oriented-cross coordinate series sums to the negative completed boundary
value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_hasSum_neg_tsum_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      (-(∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  have hopposite :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
        (-(∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate_hasSum_neg_tsum_boundaryCancellation
      f hledger horiented
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        star (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        ι f
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ =>
      HasSum u
        (-(∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)))
    hpoint.symm
    hopposite

/-- The completed oriented-cross prime-power series is anti-self-conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography
      f hledger horiented

/-- The completed oriented-cross prime-power series has zero real boundary value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) = 0 := by
  exact complex_re_eq_zero_of_star_eq_neg
    (∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
    (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_boundaryCancellation
      f hledger horiented)

/-- The real parts of rectangular oriented-cross windows tend to zero. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart N f)
      Filter.atTop
      (nhds 0) := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    horiented
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (nhds z) := by
    exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hboxRe :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (nhds (Complex.re z)) := by
    exact Complex.continuous_re.tendsto z |>.comp hbox
  have hre : Complex.re z = 0 := by
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_re_eq_zero_boundaryCancellation
        f hledger horiented
  change
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
      Filter.atTop
      (nhds 0)
  exact Eq.subst
    (motive := fun r : ℝ =>
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (nhds r))
    hre
    hboxRe

/-- The complex rectangular oriented-cross windows converge to the summable series value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_tsum
    (f : ZetaAdmissibleFunction)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
      Filter.atTop
      (nhds
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :=
    horiented
  exact hsummable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop

/-- The real parts of rectangular oriented-cross windows tend to zero. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_re_tendsto_zero
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (nhds z) ∧
      Complex.re z = 0 := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (nhds z) := by
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_tsum f horiented
  have hboxRe :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (nhds (Complex.re z)) := by
    exact Complex.continuous_re.tendsto z |>.comp hbox
  have hzero :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f))
        Filter.atTop
        (nhds 0) := by
    change
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart N f)
        Filter.atTop
        (nhds 0)
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxRealPart_tendsto_zero
        f hledger horiented
  have hre : Complex.re z = 0 :=
    tendsto_nhds_unique hboxRe hzero
  exact ⟨z, hbox, hre⟩

/-- Rectangular oriented-cross windows converge to a zero-real completed boundary value. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_tendsto_realPart_zero
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ z : ℂ,
      Filter.Tendsto
        (fun N : ℕ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f)
        Filter.atTop
        (nhds z) ∧
      Complex.re z = 0 := by
  obtain ⟨z, hbox, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum_re_tendsto_zero
      f hledger horiented
  refine ⟨z, hbox, hre⟩

/-- Rectangular prime-power oriented cross windows converge to a completed boundary value
with zero real part.

This packages summability with the finite-window boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable_boxLimit_realPart_zero
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ z : ℂ,
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) ∧
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        Filter.atTop
        (nhds z) ∧
      Complex.re z = 0 :=
  ⟨∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f,
    horiented,
    horiented.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop,
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
      f hledger horiented⟩

/-- The finite-window oriented cross sums determine the completed `HasSum` value with zero
real part. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_of_windowLimit
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ z : ℂ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        z ∧
      Complex.re z = 0 :=
  ⟨∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f,
    horiented.hasSum,
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
      f hledger horiented⟩

/-- The oriented autocorrelation cross series has a completed boundary sum with zero real
part. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ z : ℂ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        z ∧
      Complex.re z = 0 :=
  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_of_windowLimit
    f hledger horiented

/-- The oriented autocorrelation cross series has purely imaginary completed boundary sum. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_pureImaginary_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    ∃ y : ℝ,
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        (Complex.I * (y : ℂ)) := by
  obtain ⟨z, hsum, hre⟩ :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_hasSum_realPart_zero_boundaryCancellation
      f hledger horiented
  refine ⟨Complex.im z, ?_⟩
  have hz : z = Complex.I * (Complex.im z : ℂ) := by
    apply Complex.ext
    · calc
        Complex.re z = 0 := hre
        _ = Complex.re (Complex.I * (Complex.im z : ℂ)) := by
          exact
            (calc
              Complex.re (Complex.I * (Complex.im z : ℂ)) =
                  -Complex.im (Complex.im z : ℂ) := by
                exact Complex.I_mul_re (Complex.im z : ℂ)
              _ = -0 := by
                exact congrArg Neg.neg (Complex.ofReal_im (Complex.im z))
              _ = 0 := by
                exact neg_zero).symm
    · calc
        Complex.im z = Complex.im z := rfl
        _ = Complex.im (Complex.I * (Complex.im z : ℂ)) := by
          exact
            (calc
              Complex.im (Complex.I * (Complex.im z : ℂ)) =
                  Complex.re (Complex.im z : ℂ) := by
                exact Complex.I_mul_im (Complex.im z : ℂ)
              _ = Complex.im z := by
                exact Complex.ofReal_re (Complex.im z)).symm
  · exact Eq.subst
      (motive := fun w : ℂ =>
        HasSum
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
          w)
      hz
      hsum

/-- Completed autocorrelation prime-power spectral-sample coordinate-sum cancellation.

This is the coordinate-level sink for the completed spectral-sample cancellation on
autocorrelation probes. -/
theorem zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_contourTomography
      f hledger horiented

/-- The paired seed-transform prime-power series cancels once the symmetrized cross series
cancels. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
      0 := by
  exact
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
      f hledger horiented

/-- Completed autocorrelation prime-power spectral-sample coordinate-sum cancellation after
folding the paired seed-transform presentation back to autocorrelation coordinates. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      0 := by
  exact
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
      f hledger horiented

/-- The completed autocorrelation prime-power spectral-sample coordinate sum has zero real
scalar. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinateTsum_convolutionAutocorrelation_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have hsum :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        0 :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_boundaryCancellation
      f hledger horiented
  have htsum :
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 :=
    hsum.tsum_eq
  exact (congrArg Complex.re htsum).trans Complex.zero_re


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

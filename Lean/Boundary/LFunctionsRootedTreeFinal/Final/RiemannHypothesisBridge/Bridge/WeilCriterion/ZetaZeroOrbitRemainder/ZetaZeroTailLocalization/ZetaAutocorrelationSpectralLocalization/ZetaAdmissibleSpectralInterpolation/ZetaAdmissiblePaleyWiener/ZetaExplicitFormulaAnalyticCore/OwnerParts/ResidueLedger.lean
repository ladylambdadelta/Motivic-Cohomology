import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ComplexAlgebra

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

/-! This owner part contains the residue-ledger cancellation layer. -/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ZetaAdmissibleFunction

/-- The finite rectangular residue-ledger cancellation for the two oriented prime-power faces.

This is the external contour-ledger input consumed by the analytic-core `tsum` layer. -/
def ZetaCompletedPrimePowerAutocorrelationLedgerCancellation
    (f : ZetaAdmissibleFunction) : Prop :=
  Filter.Tendsto
    (fun N : ℕ =>
      ∑ ι in ZetaPrimePowerIndex.box N,
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f))
    Filter.atTop
    (nhds 0)

/-- Finite-window cancellation of the paired oriented faces at the
residue-ledger source layer.

This is the actual contour-ledger input: rectangular finite windows of the
oriented face plus the opposite oriented face tend to zero.  The real-shadow and
real-part forms are algebraic projections of this ledger. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f))
      Filter.atTop
      (nhds 0) :=
  hledger

/-- Finite-window real-part cancellation at the residue-ledger source layer. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      Filter.atTop
      (nhds 0) := by
  have hledger :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
      f hledger
  have hshadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (nhds 0))
      (funext
        (fun N =>
          zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
            N f))
      hledger
  have htwo_re :
      Filter.Tendsto
        (fun N : ℕ =>
          ((2 : ℝ) *
            Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (nhds 0))
      (funext
        (fun N =>
          zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
            N f))
      hshadow
  have hscale :
      Filter.Tendsto
        (fun N : ℕ =>
          ((1 / (2 : ℝ)) : ℂ) *
            ((2 : ℝ) *
              Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (nhds (((1 / (2 : ℝ)) : ℂ) * 0)) :=
    Filter.Tendsto.const_mul ((1 / (2 : ℝ) : ℂ)) htwo_re
  have hpoint :
      (fun N : ℕ =>
          ((1 / (2 : ℝ)) : ℂ) *
            ((2 : ℝ) *
              Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
        fun N : ℕ =>
          (Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
    exact funext
      (fun N =>
        calc
          ((1 / (2 : ℝ)) : ℂ) *
              (((2 : ℝ) : ℂ) *
                (Complex.re
                  (∑ ι in ZetaPrimePowerIndex.box N,
                    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
              (((1 / (2 : ℝ)) : ℂ) * ((2 : ℝ) : ℂ)) *
                (Complex.re
                  (∑ ι in ZetaPrimePowerIndex.box N,
                    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
            exact (mul_assoc
              ((1 / (2 : ℝ)) : ℂ)
              ((2 : ℝ) : ℂ)
              (Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)).symm
          _ =
              (1 : ℂ) *
                (Complex.re
                  (∑ ι in ZetaPrimePowerIndex.box N,
                    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
            have htwo_ne : ((2 : ℝ) : ℂ) ≠ 0 := by
              exact Complex.ofReal_ne_zero.mpr two_ne_zero
            exact congrArg
              (fun z : ℂ =>
                z *
                  (Complex.re
                    (∑ ι in ZetaPrimePowerIndex.box N,
                      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
              (one_div_mul_cancel htwo_ne)
          _ =
              (Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
            exact one_mul
              (Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)
      )
  have hzero :
      (((1 / (2 : ℝ)) : ℂ) * 0) = 0 := by
    exact mul_zero ((1 / (2 : ℝ)) : ℂ)
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ =>
          (Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (nhds 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (nhds 0))
      hpoint
      (Eq.subst
        (motive := fun z : ℂ =>
          Filter.Tendsto
            (fun N : ℕ =>
              ((1 / (2 : ℝ)) : ℂ) *
                ((2 : ℝ) *
                  Complex.re
                    (∑ ι in ZetaPrimePowerIndex.box N,
                      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
            Filter.atTop
            (nhds z))
        hzero
        hscale)
  have hre :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            ((Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)))
        Filter.atTop
        (nhds 0) :=
    (Complex.continuous_re.tendsto (0 : ℂ)).comp hcomplex
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Filter.Tendsto u Filter.atTop (nhds 0))
    (funext
      (fun N =>
        (Complex.ofReal_re
          (Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))).symm))
    hre

/-- Infinite oriented-face real-part cancellation at the residue-ledger core. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) = 0 := by
  have hsum_re_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f hledger
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        Filter.atTop
        (nhds
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    horiented.hasSum.comp
      ZetaPrimePowerIndex.box_tendsto_atTop
  have hre :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds
          (Complex.re
            (∑' ι : ZetaPrimePowerIndex,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))) :=
    (Complex.continuous_re.tendsto
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)).comp
      hbox
  exact tendsto_nhds_unique hre hsum_re_zero

/-- Infinite oriented-face anti-self-conjugacy at the residue-ledger core. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_core
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
    complex_star_eq_neg_of_re_eq_zero
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
      (zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
        f hledger horiented)

/-- Scalar real-part finite-window cancellation at the residue-ledger core. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_core
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f hledger

/-- Scalar source residue-ledger cancellation for the finite oriented real-shadow windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_core
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_core
      f hledger
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds ((2 : ℝ) * 0)) :=
    Filter.Tendsto.const_mul (2 : ℝ) hreal
  have hzero : ((2 : ℝ) * 0) = 0 :=
    mul_zero (2 : ℝ)
  have htwo_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (nhds 0) :=
    Eq.subst
      (motive := fun y : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
          Filter.atTop
          (nhds y))
      hzero
      htwo
  have hofReal :
      Filter.Tendsto
        (fun N : ℕ =>
          (((2 : ℝ) *
            Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℝ) : ℂ))
        Filter.atTop
        (nhds (0 : ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp htwo_zero
  have hpoint :
      (fun N : ℕ =>
        (((2 : ℝ) *
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℝ) : ℂ)) =
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) := by
    funext N
    have hbox :
        zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f =
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
      exact Eq.refl _
    calc
      (((2 : ℝ) *
        Complex.re
          (∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℝ) : ℂ) =
          ((2 : ℝ) : ℂ) *
            (Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
        exact Complex.ofReal_mul
          (2 : ℝ)
          (Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      _ =
          ((2 : ℝ) : ℂ) *
            (Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f) : ℂ) := by
        exact congrArg
          (fun z : ℂ => ((2 : ℝ) : ℂ) * (Complex.re z : ℂ))
          hbox.symm
      _ =
          ∑ ι in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
        exact
          (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
            N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (nhds 0))
    hpoint
    hofReal

/-- Source residue-ledger cancellation for the finite oriented real-shadow windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_core
      f hledger

/-- Source residue-ledger real-shadow cancellation for the oriented face total.

This is the scalar real projection of the infinite oriented-face residue ledger before
it is repackaged as anti-self-conjugacy. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) = 0 := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
      f hledger horiented

/-- Source contour-tomography anti-self-conjugacy for the oriented face total.

This is the residue-ledger cancellation at the infinite oriented-face level, before
transporting conjugation to the opposite face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_source
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
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_core
      f hledger horiented

/-- Source contour-tomography cancellation for the opposite oriented face.

The opposite face has the negative total orientation of the oriented face after the
completed contour ledger is transported to prime-power coordinates. -/
theorem zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_contourTomography_source
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
  let z : ℂ := ∑' ι : ZetaPrimePowerIndex, u ι
  have hu_summable : Summable u := by
    exact horiented
  have hu : HasSum u z := by
    exact hu_summable.hasSum
  have hstar : HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) (star z) :=
    hu.star
  have hanti : star z = -z := by
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_source
        f hledger horiented
  have hstar_neg : HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) (-z) :=
    Eq.subst
      (motive := fun w : ℂ =>
        HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) w)
      hanti
      hstar
  have hpoint :
      (fun ι : ZetaPrimePowerIndex => star (u ι)) = v := by
    funext ι
    exact
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
        ι f
  exact Eq.subst
    (motive := fun a : ZetaPrimePowerIndex → ℂ => HasSum a (-z))
    hpoint
    hstar_neg

/-- Source contour-tomography cancellation for the infinite paired oriented faces.

This is the residue-ledger statement after the finite rectangular faces have been
transported to the prime-power window language, but before finite box exhaustion is
applied. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_contourTomography_source
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
  let z : ℂ := ∑' ι : ZetaPrimePowerIndex, u ι
  have hu_summable : Summable u := by
    exact horiented
  have hu : HasSum u z := by
    exact hu_summable.hasSum
  have hv : HasSum v (-z) := by
    exact
      zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_contourTomography_source
        f hledger horiented
  have hpair : HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) (z + -z) :=
    hu.add hv
  have hzero : z + -z = 0 :=
    add_neg_cancel z
  have htarget :
      (fun ι : ZetaPrimePowerIndex => u ι + v ι) =
        fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f := by
    funext ι
    exact Eq.refl _
  exact Eq.subst
    (motive := fun a : ZetaPrimePowerIndex → ℂ => HasSum a 0)
    htarget
    (Eq.subst
      (motive := fun w : ℂ => HasSum (fun ι : ZetaPrimePowerIndex => u ι + v ι) w)
      hzero
      hpair)

/-- Source contour-tomography estimate for the paired oriented rectangular
faces.

This is the residue-ledger cancellation before rewriting the two faces as a
real shadow of one oriented face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_contourTomography_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f)
    (horiented :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f))
      Filter.atTop
      (nhds 0) := by
  exact
    ZetaPrimePowerIndex.tendsto_sum_box_zero_of_hasSum_complex
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_contourTomography_source
        f hledger horiented)

/-- Source contour-tomography estimate for the rectangular real-shadow windows.

This is the direct completed vertical-face cancellation statement: the finite
rectangular real shadows tend to zero in the completed boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
    (f : ZetaAdmissibleFunction)
    (hledger : ZetaCompletedPrimePowerAutocorrelationLedgerCancellation f) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (nhds 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_source
      f hledger

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

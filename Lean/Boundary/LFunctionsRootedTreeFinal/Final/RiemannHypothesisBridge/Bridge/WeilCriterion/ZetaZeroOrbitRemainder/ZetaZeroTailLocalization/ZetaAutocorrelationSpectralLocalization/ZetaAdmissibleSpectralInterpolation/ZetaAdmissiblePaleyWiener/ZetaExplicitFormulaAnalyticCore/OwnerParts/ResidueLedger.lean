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

namespace ZetaAdmissibleFunction

/-- Finite-window cancellation of the paired oriented faces at the
residue-ledger source layer.

This is the actual contour-ledger input: rectangular finite windows of the
oriented face plus the opposite oriented face tend to zero.  The real-shadow and
real-part forms are algebraic projections of this ledger. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      Filter.atTop
      (𝓝 0) := by
  let g : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hg_summable : Summable g :=
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hg_star_eq_opposite : ∀ ι,
      star (g ι) = zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f :=
    fun ι => (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite ι f).symm
  have hbox_conv : Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N, g ι)
      Filter.atTop
      (𝓝 (∑' ι : ZetaPrimePowerIndex, g ι)) :=
    hg_summable.hasSum.comp ZetaPrimePowerIndex.box_tendsto_atTop
  have hsum_identity : ∀ N,
      (∑ ι in ZetaPrimePowerIndex.box N, g ι + star (g ι)) =
      (∑ ι in ZetaPrimePowerIndex.box N,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) := by
    intro N
    exact Finset.sum_congr rfl
      (fun ι _ =>
        congrArg (fun z : ℂ => g ι + z) (hg_star_eq_opposite ι))
  have hreal_part : ∀ N,
      (∑ ι in ZetaPrimePowerIndex.box N, g ι + star (g ι)) =
      ((2 : ℝ) *
        Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι) : ℂ) := by
    intro N
    calc
      (∑ ι in ZetaPrimePowerIndex.box N, g ι + star (g ι)) =
          ∑ ι in ZetaPrimePowerIndex.box N, (g ι + star (g ι)) := by
        exact (Finset.sum_add_distrib).symm
      _ = ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) * Complex.re (g ι) : ℂ) := by
        exact Finset.sum_congr rfl
          (fun ι _ => complex_add_star_eq_two_re (g ι))
      _ = ((2 : ℝ) *
          (∑ ι in ZetaPrimePowerIndex.box N, Complex.re (g ι)) : ℝ) := by
        exact (Finset.mul_sum
          (ZetaPrimePowerIndex.box N)
          (fun ι => Complex.re (g ι))
          (2 : ℝ)).symm
      _ = ((2 : ℝ) *
          Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι) : ℂ) := by
        have hre_sum : Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι) =
            ∑ ι in ZetaPrimePowerIndex.box N, Complex.re (g ι) :=
          (Complex.sum_re (ZetaPrimePowerIndex.box N) g).symm
        exact congrArg (fun r : ℝ => ((2 : ℝ) * r : ℝ) : ℂ) hre_sum
  have hre_conv : Filter.Tendsto
      (fun N : ℕ =>
        Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι))
      Filter.atTop
      (𝓝 (Complex.re (∑' ι : ZetaPrimePowerIndex, g ι))) :=
    (Complex.continuous_re.tendsto _).comp hbox_conv
  have hre_zero : Complex.re (∑' ι : ZetaPrimePowerIndex, g ι) = 0 :=
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core f
  have hre_tendsto : Filter.Tendsto
      (fun N : ℕ =>
        Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι))
      Filter.atTop
      (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Filter.Tendsto
          (fun N : ℕ => Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι))
          Filter.atTop
          (𝓝 (Complex.re z)))
      hre_zero.symm
      hre_conv
  have hscale : Filter.Tendsto
      (fun N : ℕ =>
        ((2 : ℝ) *
          Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι) : ℂ))
      Filter.atTop
      (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Filter.Tendsto
          (fun N : ℕ => ((2 : ℝ) * Complex.re (∑ ι in ZetaPrimePowerIndex.box N, g ι) : ℂ))
          Filter.atTop
          (𝓝 (((2 : ℝ) : ℂ) * z)))
      (zero_mul ((2 : ℝ) : ℂ)).symm
      (Filter.Tendsto.const_mul ((2 : ℝ) : ℂ) hre_tendsto)
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (𝓝 0))
    (funext
      (fun N =>
        (hsum_identity N).trans (hreal_part N)))
    hscale

/-- Finite-window real-part cancellation at the residue-ledger source layer. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      Filter.atTop
      (𝓝 0) := by
  have hledger :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
        Filter.atTop
        (𝓝 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
      f
  have hshadow :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            ((2 : ℝ) *
              Complex.re
                (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
        Filter.atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (𝓝 0))
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
        (𝓝 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (𝓝 0))
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
        (𝓝 (((1 / (2 : ℝ)) : ℂ) * 0)) :=
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
        let r : ℝ :=
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        calc
          ((1 / (2 : ℝ)) : ℂ) * (((2 : ℝ) * r : ℝ) : ℂ) =
              (((1 / (2 : ℝ)) * ((2 : ℝ) * r) : ℝ) : ℂ) := by
            exact Complex.ofReal_mul (1 / (2 : ℝ)) ((2 : ℝ) * r)
          _ = r := by
            exact congrArg (fun x : ℝ => (x : ℂ))
              (calc
                (1 / (2 : ℝ)) * ((2 : ℝ) * r) =
                    ((1 / (2 : ℝ)) * (2 : ℝ)) * r := by
                  exact mul_assoc (1 / (2 : ℝ)) (2 : ℝ) r
                _ = 1 * r := by
                  exact congrArg (fun x : ℝ => x * r) (one_div_mul_cancel two_ne_zero)
                _ = r := by
                  exact one_mul r))
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
        (𝓝 0) :=
    Eq.subst
      (motive := fun u : ℕ → ℂ =>
        Filter.Tendsto u Filter.atTop (𝓝 0))
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
            (𝓝 z))
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
        (𝓝 0) :=
    (Complex.continuous_re.tendsto (0 : ℂ)).comp hcomplex
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Filter.Tendsto u Filter.atTop (𝓝 0))
    (funext
      (fun N =>
        (Complex.ofReal_re
          (Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))).symm))
    hre

/-- Infinite oriented-face real-part cancellation at the residue-ledger core. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
    (f : ZetaAdmissibleFunction) :
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
        (𝓝 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f
  have hbox :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)
        Filter.atTop
        (𝓝
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) :=
    (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f).hasSum.comp
      ZetaPrimePowerIndex.box_tendsto_atTop
  have hre :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (𝓝
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
    (f : ZetaAdmissibleFunction) :
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
        f)

/-- Scalar real-part finite-window cancellation at the residue-ledger core. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.re
          (∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
      Filter.atTop
      (𝓝 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_source
      f

/-- Scalar source residue-ledger cancellation for the finite oriented real-shadow windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_core
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) := by
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (𝓝 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_boxSum_re_tendsto_zero_residueLedger_core
      f
  have htwo :
      Filter.Tendsto
        (fun N : ℕ =>
          (2 : ℝ) *
            Complex.re
              (∑ ι in ZetaPrimePowerIndex.box N,
                zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
        Filter.atTop
        (𝓝 ((2 : ℝ) * 0)) :=
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
        (𝓝 0) :=
    Eq.subst
      (motive := fun y : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (2 : ℝ) *
              Complex.re
                (∑ ι in ZetaPrimePowerIndex.box N,
                  zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
          Filter.atTop
          (𝓝 y))
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
        (𝓝 (0 : ℂ)) := by
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
    exact
      (zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
        N f).symm
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (𝓝 0))
    hpoint
    hofReal

/-- Source residue-ledger cancellation for the finite oriented real-shadow windows. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) := by
  have hledger :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ ι in ZetaPrimePowerIndex.box N,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
              zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
        Filter.atTop
        (𝓝 0) :=
    zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_tendsto_zero_residueLedger_source
      f
  exact Eq.subst
    (motive := fun u : ℕ → ℂ =>
      Filter.Tendsto u Filter.atTop (𝓝 0))
    (funext
      (fun N =>
        (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
          N f).symm))
    hledger

/-- Source residue-ledger real-shadow cancellation for the oriented face total.

This is the scalar real projection of the infinite oriented-face residue ledger before
it is repackaged as anti-self-conjugacy. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_source
    (f : ZetaAdmissibleFunction) :
    Complex.re
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) = 0 := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_re_eq_zero_residueLedger_core
      f

/-- Source contour-tomography anti-self-conjugacy for the oriented face total.

This is the residue-ledger cancellation at the infinite oriented-face level, before
transporting conjugation to the opposite face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_source
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_core
      f

/-- Source contour-tomography cancellation for the opposite oriented face.

The opposite face has the negative total orientation of the oriented face after the
completed contour ledger is transported to prime-power coordinates. -/
theorem zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_contourTomography_source
    (f : ZetaAdmissibleFunction) :
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
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hu : HasSum u z := by
    unfold z
    exact hu_summable.hasSum
  have hstar : HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) (star z) :=
    hu.star
  have hanti : star z = -z := by
    unfold z
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_source
        f
  have hstar_neg : HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) (-z) :=
    Eq.subst
      (motive := fun w : ℂ =>
        HasSum (fun ι : ZetaPrimePowerIndex => star (u ι)) w)
      hanti
      hstar
  have hpoint :
      (fun ι : ZetaPrimePowerIndex => star (u ι)) = v := by
    funext ι
    unfold u
    unfold v
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
    (f : ZetaAdmissibleFunction) :
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
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hu : HasSum u z := by
    unfold z
    exact hu_summable.hasSum
  have hv : HasSum v (-z) := by
    unfold v
    unfold z
    exact
      zetaCompletedPrimePowerAutocorrelation_opposite_hasSum_neg_oriented_tsum_contourTomography_source
        f
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
    rfl
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
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
            zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      Filter.atTop
      (𝓝 0) := by
  exact
    ZetaPrimePowerIndex.tendsto_sum_box_zero_of_hasSum_complex
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
          zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f)
      (zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_hasSum_zero_contourTomography_source
        f)

/-- Source contour-tomography estimate for the rectangular real-shadow windows.

This is the direct completed vertical-face cancellation statement: the finite
rectangular real shadows tend to zero in the completed boundary limit. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
    (f : ZetaAdmissibleFunction) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑ ι in ZetaPrimePowerIndex.box N,
          ((2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ))
      Filter.atTop
      (𝓝 0) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_realShadowWindow_tendsto_zero_residueLedger_source
      f

/-- Upstream contour-tomography cancellation for the completed oriented
prime-power cross total.

This is the analytic input owned by the completed vertical-face residue ledger:
the two oriented faces pair with opposite orientation, so the completed oriented
cross total is anti-self-conjugate. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.ResidueLedger

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

/-! This owner part contains the contour-tomography cancellation layer. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_tsum_star_eq_neg_residueLedger_source
      f

/-- The paired autocorrelation spectral-sample total is the negative of the
oriented cross total plus its conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_neg_oriented_add_star
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      -((∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) +
        star
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f
  let symm : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex => u ι + star (u ι)
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar :
      (∑' ι : ZetaPrimePowerIndex, star (u ι)) =
        star (∑' ι : ZetaPrimePowerIndex, u ι) :=
    hu.tsum_star.symm
  have hsymm_tsum :
      (∑' ι : ZetaPrimePowerIndex, symm ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) +
          star (∑' ι : ZetaPrimePowerIndex, u ι) := by
    have hsum_add :
        (∑' ι : ZetaPrimePowerIndex, symm ι) =
          (∑' ι : ZetaPrimePowerIndex, u ι) +
            (∑' ι : ZetaPrimePowerIndex, star (u ι)) := by
      unfold symm
      exact (hu.tsum_add hu.star).symm
    exact hsum_add.trans
      (congrArg
        (fun z : ℂ => (∑' ι : ZetaPrimePowerIndex, u ι) + z)
        hstar)
  have hpaired_eq_neg_symm :
      paired = fun ι : ZetaPrimePowerIndex => -symm ι := by
    funext ι
    unfold paired
    unfold symm
    unfold u
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hpaired_tsum :
      (∑' ι : ZetaPrimePowerIndex, paired ι) =
        ∑' ι : ZetaPrimePowerIndex, -symm ι := by
    exact congrArg
      (fun v : ZetaPrimePowerIndex → ℂ =>
        ∑' ι : ZetaPrimePowerIndex, v ι)
      hpaired_eq_neg_symm
  have hsymm_summable : Summable symm :=
    hu.add hu.star
  have hneg_tsum :
      (∑' ι : ZetaPrimePowerIndex, -symm ι) =
        -(∑' ι : ZetaPrimePowerIndex, symm ι) :=
    hsymm_summable.tsum_neg
  calc
    (∑' ι : ZetaPrimePowerIndex, paired ι)
        = ∑' ι : ZetaPrimePowerIndex, -symm ι := hpaired_tsum
    _ = -(∑' ι : ZetaPrimePowerIndex, symm ι) := hneg_tsum
    _ =
        -((∑' ι : ZetaPrimePowerIndex, u ι) +
          star (∑' ι : ZetaPrimePowerIndex, u ι)) := by
          exact congrArg Neg.neg hsymm_tsum

/-- The paired autocorrelation spectral-sample total vanishes from the
anti-self-conjugacy of the oriented cross total. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_zero_of_oriented_tsum_star_eq_neg
    (f : ZetaAdmissibleFunction)
    (horiented :
      star
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
        -∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      0 := by
  let z : ℂ :=
    ∑' ι : ZetaPrimePowerIndex,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  have hpaired :
      (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
        -(z + star z) := by
    unfold z
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_neg_oriented_add_star
        f
  have hsum_zero : z + star z = 0 := by
    calc
      z + star z = z + -z := by
        exact congrArg (fun w : ℂ => z + w) horiented
      _ = 0 := by
        exact add_neg_cancel z
  calc
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
        = -(z + star z) := hpaired
    _ = -0 := by
        exact congrArg Neg.neg hsum_zero
    _ = 0 := by
        exact neg_zero

/-- The autocorrelation spectral-sample total is the paired seed-transform
total. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_tsum_convolutionAutocorrelation_eq_paired_tsum
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      ∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  exact congrArg
    (fun v : ZetaPrimePowerIndex → ℂ =>
      ∑' ι : ZetaPrimePowerIndex, v ι)
    hpoint

/-- Completed autocorrelation prime-power symmetrized cross-coordinate cancellation.

This is the owner contour-tomography form of the vertical-face pairing: the
symmetrized oriented cross series has zero completed sum. -/
theorem zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_eq_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f) = 0 := by
  calc
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
        =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
          exact rfl
    _ =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f := by
          exact
            zetaCompletedPrimePowerSpectralSampleCoordinate_tsum_convolutionAutocorrelation_eq_paired_tsum
              f
    _ = 0 := by
          exact
            zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_tsum_eq_zero_of_oriented_tsum_star_eq_neg
              f
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
                f)

/-- Summability of the autocorrelation prime-power spectral sample follows from
the oriented cross-coordinate majorant and the paired-coordinate normal form. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_summable_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
  let u : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f
  let symm : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f
  let paired : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f
  let spectral : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)
  have hu : Summable u := by
    unfold u
    exact zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_summable f
  have hstar : Summable (fun ι : ZetaPrimePowerIndex => star (u ι)) :=
    hu.star
  have hsymm_raw :
      Summable (fun ι : ZetaPrimePowerIndex => u ι + star (u ι)) :=
    hu.add hstar
  have hsymm_point :
      (fun ι : ZetaPrimePowerIndex => u ι + star (u ι)) = symm := by
    funext ι
    unfold u
    unfold symm
    rfl
  have hsymm : Summable symm :=
    Eq.subst
      (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
      hsymm_point
      hsymm_raw
  have hpaired_neg : Summable (fun ι : ZetaPrimePowerIndex => -symm ι) :=
    hsymm.neg
  have hpaired_point :
      paired = (fun ι : ZetaPrimePowerIndex => -symm ι) := by
    funext ι
    unfold paired
    unfold symm
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hpaired : Summable paired :=
    Eq.subst
      (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
      hpaired_point.symm
      hpaired_neg
  have hspectral_point : spectral = paired := by
    funext ι
    unfold spectral
    unfold paired
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  unfold spectral at hspectral_point
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℂ => Summable v)
    hspectral_point.symm
    hpaired

/-- Completed autocorrelation prime-power spectral-sample cancellation as a
`HasSum` statement. -/
theorem zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))
      0 := by
  have hsummable :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_summable_convolutionAutocorrelation
      f
  have hzero :
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_eq_zero_contourTomography
        f
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        z)
    hzero
    hsummable.hasSum

/-- Completed autocorrelation prime-power paired spectral-sample cancellation.

This transports the contour-tomography spectral-sample cancellation through the
autocorrelation paired-coordinate normal form. -/
theorem zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
      0 := by
  have hspectral :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))
        0 :=
    zetaCompletedPrimePowerSpectralSampleCoordinate_hasSum_zero_contourTomography
      f
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate ι
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleCoordinate_convolutionAutocorrelation_eq_paired
        ι f
  exact Eq.subst
    (motive := fun u : ZetaPrimePowerIndex → ℂ => HasSum u 0)
    hpoint
    hspectral

/-- Completed autocorrelation prime-power symmetrized cross-coordinate cancellation.

This is the algebraic sign transport from the paired spectral-sample coordinate
to the symmetrized oriented cross coordinate. -/
theorem zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate_hasSum_zero_contourTomography
    (f : ZetaAdmissibleFunction) :
    HasSum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
      0 := by
  have hpaired :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f)
        0 :=
    zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_hasSum_zero_contourTomography
      f
  have hpoint :
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate ι f) =
      (fun ι : ZetaPrimePowerIndex =>
        -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f) := by
    funext ι
    exact
      zetaCompletedPrimePowerAutocorrelationPairedSpectralSampleCoordinate_eq_neg_symmetrizedCross
        ι f
  have hneg :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          -zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        0 :=
    Eq.subst
      (motive := fun u : ZetaPrimePowerIndex → ℂ => HasSum u 0)
      hpoint
      hpaired
  have hsymNeg :
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        (-0) :=
    hneg.neg
  exact Eq.subst
    (motive := fun z : ℂ =>
      HasSum
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimePowerAutocorrelationSymmetrizedCrossCoordinate ι f)
        z)
    neg_zero
    hsymNeg

/-- The completed oriented cross-coordinate total is anti-self-conjugate.

This is the upstream contour-tomography cancellation: after the completed
residue ledger pairs the two oriented vertical faces, the oriented prime-power
cross total equals the negative of its conjugate. -/
theorem zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography
    (f : ZetaAdmissibleFunction) :
    star
      (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) =
      -∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f := by
  exact
    zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_tsum_star_eq_neg_contourTomography_source
      f

/-- Rectangular real-shadow windows are twice the real part of the rectangular
oriented-cross window. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f) : ℂ) := by
  exact
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
      N f

/-- The completed contour-tail real shadow of the oriented prime-power face vanishes.

This is the contour-tomography estimate: the analytic core owns the finite oriented
cross-coordinate algebra, while the vanishing limit must be supplied by the downstream
contour/residue ledger normalization. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography
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
    zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_tendsto_zero_contourTomography_source
      f


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

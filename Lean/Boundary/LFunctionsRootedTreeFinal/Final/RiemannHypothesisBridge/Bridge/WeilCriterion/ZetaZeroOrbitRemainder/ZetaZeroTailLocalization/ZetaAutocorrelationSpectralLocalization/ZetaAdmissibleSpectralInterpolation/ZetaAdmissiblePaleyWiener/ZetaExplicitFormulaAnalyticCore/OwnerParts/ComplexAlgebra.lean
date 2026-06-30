import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.PrimePowerCoordinates

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

/-! This owner part contains the complex algebra and finite-window real-shadow identities. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A complex number equal to the negative of its conjugate has zero real part. -/
theorem complex_re_eq_zero_of_star_eq_neg
    (z : ℂ) (hz : star z = -z) :
    Complex.re z = 0 := by
  have hcongr :
      Complex.re (star z) = Complex.re (-z) :=
    congrArg Complex.re hz
  have hstar : Complex.re (star z) = Complex.re z := by
    exact Eq.trans
      (congrArg Complex.re (Complex.star_def z))
      (Complex.conj_re z)
  have hneg : Complex.re (-z) = -Complex.re z :=
    Complex.neg_re z
  have hz_neg : Complex.re z = -Complex.re z :=
    hstar.symm.trans (hcongr.trans hneg)
  have hadd : Complex.re z + Complex.re z = 0 :=
    eq_neg_iff_add_eq_zero.mp hz_neg
  have hmul : (2 : ℝ) * Complex.re z = 0 :=
    (two_mul (Complex.re z)).symm.trans hadd
  exact (mul_eq_zero.mp hmul).resolve_left two_ne_zero

/-- A complex number with zero real part is the negative of its conjugate. -/
theorem complex_star_eq_neg_of_re_eq_zero
    (z : ℂ) (hz : Complex.re z = 0) :
    star z = -z := by
  apply Complex.ext
  · calc
      Complex.re (star z) = Complex.re z := by
        exact Eq.trans
          (congrArg Complex.re (Complex.star_def z))
          (Complex.conj_re z)
      _ = 0 := hz
      _ = -0 := by
        exact (neg_zero : -(0 : ℝ) = 0).symm
      _ = -Complex.re z := by
        exact congrArg Neg.neg hz.symm
      _ = Complex.re (-z) := by
        exact (Complex.neg_re z).symm
  · calc
      Complex.im (star z) = -Complex.im z := by
        exact Eq.trans
          (congrArg Complex.im (Complex.star_def z))
          (Complex.conj_im z)
      _ = Complex.im (-z) := by
        exact (Complex.neg_im z).symm

/-- A complex number plus its conjugate is twice its real part. -/
theorem complex_add_star_eq_two_re
    (z : ℂ) :
    z + star z = ((2 : ℝ) * Complex.re z : ℂ) := by
  apply Complex.ext
  · calc
      Complex.re (z + star z) = Complex.re z + Complex.re (star z) := by
        exact Complex.add_re z (star z)
      _ = Complex.re z + Complex.re z := by
        exact congrArg (fun x : ℝ => Complex.re z + x)
          (Eq.trans
            (congrArg Complex.re (Complex.star_def z))
            (Complex.conj_re z))
      _ = (2 : ℝ) * Complex.re z := by
        exact (two_mul (Complex.re z)).symm
      _ = Complex.re (((2 : ℝ) * Complex.re z : ℝ) : ℂ) := by
        exact (Complex.ofReal_re ((2 : ℝ) * Complex.re z)).symm
  · calc
      Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
        exact Complex.add_im z (star z)
      _ = Complex.im z + -Complex.im z := by
        exact congrArg (fun x : ℝ => Complex.im z + x)
          (Eq.trans
            (congrArg Complex.im (Complex.star_def z))
            (Complex.conj_im z))
      _ = 0 := by
        exact add_neg_cancel (Complex.im z)
      _ = Complex.im (((2 : ℝ) * Complex.re z : ℝ) : ℂ) := by
        exact (Complex.ofReal_im ((2 : ℝ) * Complex.re z)).symm

/-- The finite two-face cross sum is the real shadow of the oriented face. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_add_opposite_boxSum_eq_realShadow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f +
        zetaCompletedPrimePowerAutocorrelationOppositeOrientedCrossCoordinate ι f) =
      ∑ ι in ZetaPrimePowerIndex.box N,
        ((2 : ℝ) *
          Complex.re
            (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
  exact Finset.sum_congr
    rfl
    (fun ι _ =>
      (congrArg
        (fun z : ℂ =>
          zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f + z)
        (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate_star_eq_opposite
          ι f).symm).trans
        (complex_add_star_eq_two_re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)))

/-- Rectangular real-shadow windows are twice the real part of the rectangular
oriented-cross window, at the residue-ledger source layer. -/
theorem zetaCompletedPrimePowerAutocorrelation_oriented_boxRealShadow_eq_two_re_boxSum_source
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    (∑ ι in ZetaPrimePowerIndex.box N,
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum N f) : ℂ) := by
  unfold zetaCompletedPrimePowerAutocorrelationOrientedCrossBoxSum
  calc
    (∑ ι in ZetaPrimePowerIndex.box N,
      ((2 : ℝ) *
        Complex.re
          (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ)) =
        ((∑ ι in ZetaPrimePowerIndex.box N,
          (2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℝ) : ℂ) := by
      exact Finset.sum_ofReal
        (ZetaPrimePowerIndex.box N)
        (fun ι : ZetaPrimePowerIndex =>
          (2 : ℝ) *
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
    _ =
        ((2 : ℝ) *
          (∑ ι in ZetaPrimePowerIndex.box N,
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)) : ℝ) := by
      exact congrArg
        (fun r : ℝ => (r : ℂ))
        (Finset.mul_sum
          (ZetaPrimePowerIndex.box N)
          (fun ι : ZetaPrimePowerIndex =>
            Complex.re
              (zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f))
          (2 : ℝ)).symm
    _ =
        ((2 : ℝ) *
          Complex.re
            (∑ ι in ZetaPrimePowerIndex.box N,
              zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f) : ℂ) := by
      exact congrArg
        (fun r : ℝ => ((2 : ℝ) * r : ℝ) : ℂ)
        (Complex.sum_re
          (ZetaPrimePowerIndex.box N)
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimePowerAutocorrelationOrientedCrossCoordinate ι f)).symm


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

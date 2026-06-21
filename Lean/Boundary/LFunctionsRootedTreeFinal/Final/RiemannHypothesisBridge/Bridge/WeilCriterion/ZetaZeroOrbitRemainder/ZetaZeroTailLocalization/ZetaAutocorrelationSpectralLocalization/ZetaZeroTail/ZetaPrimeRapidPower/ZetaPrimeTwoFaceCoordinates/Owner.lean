import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaCompletedPositiveBoundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaPrimeRapidPower.ZetaPrimeTwoFaceCoordinates.ZetaPrimeContourTomography.Owner

/-!
# Prime two-face coordinates

This file owns the completed prime two-face coordinates and the finite time/contour
prime-window convergence statements used by horizontal decay and final tomography.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The real completed two-face/GNS coordinate attached to one prime-power index. -/
noncomputable def completedPrimeTwoFaceGNSRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
    (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
        star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) +
      star
        (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
          star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)))

/-- The real completed two-face boundary coordinate attached to one prime-power index.

This is the real shadow of the completed two-face/GNS boundary coordinate.  It is not the
raw real-lag off-diagonal coordinate; the raw time-side channel reaches this coordinate only
after completed prime tomography/transport. -/
noncomputable def completedPrimeTwoFaceGNSBoundaryRealCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)

/-- The completed two-face boundary real coordinate is the real part of the signed
symmetrized two-face/GNS packet coordinate. -/
theorem completedPrimeTwoFaceGNSBoundaryRealCoordinate_eq_neg_symmetrizedCoordinate_re
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f =
      Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
  rfl

/-- The completed two-face boundary real-coordinate sum reconstructs the completed
two-face boundary coefficient.

This is the owner holographic reconstruction theorem for the completed prime two-face
coordinate layer: the completed real boundary-coordinate sum and the completed
two-face boundary coefficient are the same reconstructed prime boundary scalar. -/
theorem completedPrimeTwoFaceBoundaryRealCoordinate_tsum_eq_coefficient_re_ownerCoordinates
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
      Complex.re (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) := by
  have hcoordinate :
      (∑' ι : ZetaPrimePowerIndex,
          completedPrimeTwoFaceGNSBoundaryRealCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
    exact tsum_congr
      (fun ι : ZetaPrimePowerIndex =>
        completedPrimeTwoFaceGNSBoundaryRealCoordinate_eq_neg_symmetrizedCoordinate_re
          ι f)
  have hre :
      (∑' ι : ZetaPrimePowerIndex,
          Complex.re (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) =
        Complex.re
          (∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
    let u : ZetaPrimePowerIndex → ℂ :=
      fun ι : ZetaPrimePowerIndex =>
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f
    have hzero : ∀ ι : ZetaPrimePowerIndex, Complex.im (u ι) = 0 := by
      intro ι
      calc
        Complex.im (u ι) =
            Complex.im (-zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
          rfl
        _ = -Complex.im (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
          exact Complex.neg_im (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
        _ = -0 := by
          exact congrArg Neg.neg
            (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_im_eq_zero ι f)
        _ = 0 := by
          exact neg_zero
    have hpoint :
        u = fun ι : ZetaPrimePowerIndex => (Complex.re (u ι) : ℂ) :=
      funext
        (fun ι : ZetaPrimePowerIndex =>
          complex_eq_ofReal_re_of_im_eq_zero (u ι) (hzero ι))
    have htsum_u :
        (∑' ι : ZetaPrimePowerIndex, u ι) =
          ∑' ι : ZetaPrimePowerIndex, (Complex.re (u ι) : ℂ) := by
      exact congrArg
        (fun v : ZetaPrimePowerIndex → ℂ =>
          ∑' ι : ZetaPrimePowerIndex, v ι)
        hpoint
    have hofReal_tsum :
        ((∑' ι : ZetaPrimePowerIndex, Complex.re (u ι) : ℝ) : ℂ) =
          ∑' ι : ZetaPrimePowerIndex, (Complex.re (u ι) : ℂ) :=
      Complex.ofReal_tsum
        (fun ι : ZetaPrimePowerIndex => Complex.re (u ι))
    have hre_u :
        (∑' ι : ZetaPrimePowerIndex, Complex.re (u ι)) =
          Complex.re (∑' ι : ZetaPrimePowerIndex, u ι) := by
      calc
        (∑' ι : ZetaPrimePowerIndex, Complex.re (u ι)) =
            Complex.re
              (((∑' ι : ZetaPrimePowerIndex, Complex.re (u ι) : ℝ) : ℂ)) := by
          exact (Complex.ofReal_re
            (∑' ι : ZetaPrimePowerIndex, Complex.re (u ι))).symm
        _ =
            Complex.re
              (∑' ι : ZetaPrimePowerIndex, (Complex.re (u ι) : ℂ)) := by
          exact congrArg Complex.re hofReal_tsum
        _ = Complex.re (∑' ι : ZetaPrimePowerIndex, u ι) := by
          exact congrArg Complex.re htsum_u.symm
    exact hre_u
  have hboundary :
      (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  exact hcoordinate.trans (hre.trans (congrArg Complex.re hboundary))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

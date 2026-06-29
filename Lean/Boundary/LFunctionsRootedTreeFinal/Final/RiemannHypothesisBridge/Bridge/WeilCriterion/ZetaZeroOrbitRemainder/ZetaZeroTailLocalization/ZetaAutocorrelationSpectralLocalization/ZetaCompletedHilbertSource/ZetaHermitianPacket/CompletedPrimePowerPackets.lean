import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeBoundaryPackets

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The completed prime spectral amplitude over the owner prime-power index type. -/
noncomputable def zetaCompletedPrimeSpectralAmplitudeIndex
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.sqrtWeight ι : ℂ) *
    zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f

/-- The completed opposite prime spectral amplitude over the owner prime-power index type. -/
noncomputable def zetaCompletedPrimeOppositeSpectralAmplitudeIndex
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (ZetaPrimePowerIndex.sqrtWeight ι : ℂ) *
    zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f

/-- The completed raw oriented prime two-face/GNS matrix coefficient over all genuine
prime-power indices.  Nongenuine indices have zero weight through `ZetaPrimePowerIndex`. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSOrientedCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeSpectralAmplitudeIndex ι f *
    star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- One oriented completed prime two-face coordinate is the weighted paired seed sample. -/
theorem zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f =
      (ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi f ι.center *
          star (zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ)))) := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let a : ℂ := zetaCompletedExplicitFormulaPhi f ι.center
  let b : ℂ := zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))
  have hstar_r : star (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  have hstar_rb :
      star ((r : ℂ) * b) = (r : ℂ) * star b := by
    calc
      star ((r : ℂ) * b) = star b * star (r : ℂ) := by
        exact star_mul (r : ℂ) b
      _ = star b * (r : ℂ) := by
        exact congrArg (fun z : ℂ => star b * z) hstar_r
      _ = (r : ℂ) * star b := by
        exact mul_comm (star b) (r : ℂ)
  have hsqrt :
      (r : ℂ) * (r : ℂ) = (ι.weight : ℂ) := by
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul r r).symm
      _ = (ι.weight : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ))
          (ZetaPrimePowerIndex.sqrtWeight_mul_self ι)
  calc
    ((r : ℂ) * a) * star ((r : ℂ) * b) =
        ((r : ℂ) * a) * ((r : ℂ) * star b) := by
      exact congrArg (fun z : ℂ => ((r : ℂ) * a) * z) hstar_rb
    _ = ((r : ℂ) * (r : ℂ)) * (a * star b) := by
      calc
        ((r : ℂ) * a) * ((r : ℂ) * star b) =
            (r : ℂ) * (a * ((r : ℂ) * star b)) := by
          exact mul_assoc (r : ℂ) a ((r : ℂ) * star b)
        _ = (r : ℂ) * ((a * (r : ℂ)) * star b) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * z)
            ((mul_assoc a (r : ℂ) (star b)).symm)
        _ = (r : ℂ) * (((r : ℂ) * a) * star b) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * (z * star b))
            (mul_comm a (r : ℂ))
        _ = (r : ℂ) * ((r : ℂ) * (a * star b)) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * z)
            (mul_assoc (r : ℂ) a (star b))
        _ = ((r : ℂ) * (r : ℂ)) * (a * star b) := by
          exact (mul_assoc (r : ℂ) (r : ℂ) (a * star b)).symm
    _ = (ι.weight : ℂ) * (a * star b) := by
      exact congrArg (fun z : ℂ => z * (a * star b)) hsqrt

/-- The completed raw oriented prime two-face/GNS matrix coefficient over all genuine
prime-power indices.  Nongenuine indices have zero weight through `ZetaPrimePowerIndex`. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSOrientedCoefficient
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f

/-- The completed prime two-face/GNS matrix coefficient over the owner prime-power index
type. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSMatrixCoefficient
    (f : ZetaAdmissibleFunction) : ℂ :=
  -zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Completed autocorrelation prime-power spectral-sample cancellation.

This is the spectral-sample sink beneath the completed two-face/GNS matrix cancellation:
the completed prime-power spectral sample has zero real scalar on autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_re_eq_zero_boundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Complex.re
      (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  exact
    zetaCompletedPrimePowerSpectralSampleCoordinateTsum_convolutionAutocorrelation_re_eq_zero_boundaryCancellation
      f

/-- The completed two-face/GNS matrix coefficient has zero real scalar once the
autocorrelation prime-power spectral sample cancels. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_spectralSampleBoundaryCancellation
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  let S : ℂ :=
    zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
  have hS : Complex.re S = 0 := by
    unfold S
    exact
      zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution_convolutionAutocorrelation_re_eq_zero_boundaryCancellation
        f
  unfold zetaCompletedPrimeTwoFaceGNSMatrixCoefficient
  change Complex.re (-S) = 0
  calc
    Complex.re (-S) = -Complex.re S := by
      exact Complex.neg_re S
    _ = -0 := by
      exact congrArg Neg.neg hS
    _ = 0 := by
      exact neg_zero

/-- The completed prime two-face boundary coefficient over the owner prime-power index type.

The GNS matrix coefficient is the positive symmetrized cross term in the defect-square
expansion.  The explicit-formula prime boundary channel is the negative cross term. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The completed prime boundary coefficient is the explicit-formula signed version of the
completed positive two-face/GNS matrix coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
      -zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
  exact (neg_neg
    (zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))).symm

/-- The completed prime diagonal-debt coordinate over the owner prime-power index type. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeSpectralAmplitudeIndex ι f *
      star (zetaCompletedPrimeSpectralAmplitudeIndex ι f) +
    zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f *
      star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The completed positive prime defect-kernel coordinate over the owner prime-power index
type. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedPrimeSpectralAmplitudeIndex ι f -
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) *
    star
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f -
        zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The raw completed prime diagonal-debt coordinate presentation. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f

/-- The completed prime diagonal debt.

This is the lower-weight completion of the defect-square identity, not an independently
owned raw spectral series.  The raw coordinate `tsum` is kept as a presentation surface. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebt
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeDefectKernelDiagonalDebt f -
    zetaPrimeTwoFaceGNSMatrixCoefficient f +
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f

/-- The raw completed positive prime defect-kernel coordinate presentation. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveCoordinateTsum
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑' ι : ZetaPrimePowerIndex,
    zetaCompletedPrimeDefectKernelPositiveCoordinate ι f

/-- The real scalar attached to the raw completed positive prime defect-kernel coordinate
presentation. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f)

/-- The completed positive prime defect kernel.

This is owned by the completed defect-square expansion: positive square equals completed
diagonal debt minus the completed two-face cross term.  The raw coordinate `tsum` is kept as
a presentation surface, not as the owner definition. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeDefectKernelDiagonalDebt f -
    zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f

/-- The completed positive prime defect-kernel channel. -/
noncomputable def completedPrimeDefectKernelPositiveChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f)

/-- The completed positive prime defect kernel over a finite prime-power window. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    zetaCompletedPrimeDefectKernelPositiveCoordinate ι f

/-- The completed two-face prime matrix coefficient over a finite prime-power window. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (∑ ι in ZetaPrimePowerIndex.window N,
    zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) +
    star
      (∑ ι in ZetaPrimePowerIndex.window N,
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)

/-- The completed symmetrized two-face cross coordinate at one prime-power index. -/
noncomputable def zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f +
    star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)

/-- Each completed symmetrized two-face prime coordinate is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_im_eq_zero
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) = 0 := by
  let z : ℂ := zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f
  calc
    Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
      exact Complex.add_im z (star z)
    _ = Complex.im z + -Complex.im z := by
      exact congrArg (fun x : ℝ => Complex.im z + x) (Complex.conj_im z)
    _ = 0 := by
      exact add_neg_cancel (Complex.im z)

/-- The contour-side autocorrelation spectral prime coordinate is the negative completed
two-face boundary coordinate. -/
theorem zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    -((ι.weight : ℂ) *
        (zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
          star
            (zetaCompletedExplicitFormulaPhi
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))) =
      -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
  let A : ℂ := zetaCompletedExplicitFormulaPhi f ι.center
  let B : ℂ := zetaCompletedExplicitFormulaPhi f (-(ι.center : ℂ))
  let W : ℂ := (ι.weight : ℂ)
  let C : ℂ := zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f
  have hconv :
      zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center =
        A * star B := by
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
      f ι.center
  have hC : C = W * (A * star B) := by
    exact zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_eq_weightedSeedPair ι f
  have hstarW : star W = W := by
    exact Complex.conj_ofReal ι.weight
  have hstarC :
      star C = W * star (A * star B) := by
    calc
      star C = star (W * (A * star B)) := by
        exact congrArg star hC
      _ = star (A * star B) * star W := by
        exact star_mul W (A * star B)
      _ = star (A * star B) * W := by
        exact congrArg (fun z : ℂ => star (A * star B) * z) hstarW
      _ = W * star (A * star B) := by
        exact mul_comm (star (A * star B)) W
  exact congrArg Neg.neg
    (calc
      W *
          (zetaCompletedExplicitFormulaPhi
              (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
            star
              (zetaCompletedExplicitFormulaPhi
                (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center)) =
          W * ((A * star B) + star (A * star B)) := by
        exact congrArg
          (fun z : ℂ => W * (z + star z))
          hconv
      _ = W * (A * star B) + W * star (A * star B) := by
        exact mul_add W (A * star B) (star (A * star B))
      _ = C + W * star (A * star B) := by
        exact congrArg
          (fun z : ℂ => z + W * star (A * star B))
          hC.symm
      _ = C + star C := by
        exact congrArg (fun z : ℂ => C + z) hstarC.symm)

/-- The completed prime diagonal debt over a finite prime-power window. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f

/-- The real part of the completed diagonal-debt coordinate presentation over a finite
prime-power window. -/
noncomputable def zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f)

/-- The real part of the completed positive prime defect kernel over a finite prime-power
window. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveRealWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelPositiveWindow N f)

/-- The additive cancellation at the end of one completed prime-power defect-square expansion. -/
private theorem completed_defect_square_cross_cancel
    (x y z w : ℂ) :
    ((x - y) - (z - w)) + (z + y) = x + w :=
  calc
    ((x - y) - (z - w)) + (z + y) =
        ((x - y) + (w - z)) + (z + y) := by
      exact congrArg (fun t : ℂ => t + (z + y))
        (calc
          (x - y) - (z - w) = (x - y) + -(z - w) := by
            exact sub_eq_add_neg (x - y) (z - w)
          _ = (x - y) + (w - z) := by
            exact congrArg (fun t : ℂ => (x - y) + t) (neg_sub z w))
    _ = (x - y) + ((w - z) + (z + y)) := by
      exact add_assoc (x - y) (w - z) (z + y)
    _ = (x - y) + (w + y) := by
      exact congrArg (fun t : ℂ => (x - y) + t)
        (calc
          (w - z) + (z + y) = ((w - z) + z) + y := by
            exact (add_assoc (w - z) z y).symm
          _ = w + y := by
            exact congrArg (fun t : ℂ => t + y) (sub_add_cancel w z))
    _ = (x - y) + (y + w) := by
      exact congrArg (fun t : ℂ => (x - y) + t) (add_comm w y)
    _ = ((x - y) + y) + w := by
      exact (add_assoc (x - y) y w).symm
    _ = x + w := by
      exact congrArg (fun t : ℂ => t + w) (sub_add_cancel x y)

/-- One completed positive prime defect square expands as diagonal debt minus the symmetrized
two-face cross term. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveCoordinate ι f +
        (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
            star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) +
          star
            (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
              star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f))) =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have hstar_cross : star (a * star b) = b * star a := by
    calc
      star (a * star b) = star (star b) * star a := by
        exact star_mul a (star b)
      _ = b * star a := by
        exact congrArg (fun z : ℂ => z * star a) (star_star b)
  calc
    (a - b) * star (a - b) + (a * star b + star (a * star b)) =
        (a - b) * (star a - star b) + (a * star b + star (a * star b)) := by
      exact congrArg
        (fun z : ℂ => (a - b) * z + (a * star b + star (a * star b)))
        (star_sub a b)
    _ =
        ((a - b) * star a - (a - b) * star b) +
          (a * star b + star (a * star b)) := by
      exact congrArg
        (fun z : ℂ => z + (a * star b + star (a * star b)))
        (mul_sub (a - b) (star a) (star b))
    _ =
        ((a * star a - b * star a) - (a * star b - b * star b)) +
          (a * star b + star (a * star b)) := by
      exact congrArg
        (fun z : ℂ => z + (a * star b + star (a * star b)))
        (congrArg₂ Sub.sub
          (sub_mul a b (star a))
          (sub_mul a b (star b)))
    _ =
        ((a * star a - b * star a) - (a * star b - b * star b)) +
          (a * star b + b * star a) := by
      exact congrArg
        (fun z : ℂ =>
          ((a * star a - b * star a) - (a * star b - b * star b)) +
            (a * star b + z))
        hstar_cross
    _ = a * star a + b * star b := by
      exact completed_defect_square_cross_cancel
        (a * star a) (b * star a) (a * star b) (b * star b)

/-- One completed positive prime defect-kernel coordinate has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  exact complex_re_mul_star_self_nonnegative_hermitianPacket (a - b)

/-- One completed diagonal-debt coordinate has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have ha : 0 ≤ Complex.re (a * star a) :=
    complex_re_mul_star_self_nonnegative_hermitianPacket a
  have hb : 0 ≤ Complex.re (b * star b) :=
    complex_re_mul_star_self_nonnegative_hermitianPacket b
  calc
    0 ≤ Complex.re (a * star a) + Complex.re (b * star b) := by
      exact add_nonneg ha hb
    _ = Complex.re (a * star a + b * star b) := by
      exact (Complex.add_re (a * star a) (b * star b)).symm

/-- A completed diagonal-debt coordinate is real-valued. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_im_eq_zero
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) = 0 := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have ha : a * star a = (Complex.normSq a : ℂ) :=
    Complex.mul_conj a
  have hb : b * star b = (Complex.normSq b : ℂ) :=
    Complex.mul_conj b
  calc
    Complex.im (a * star a + b * star b) =
        Complex.im ((Complex.normSq a : ℂ) + b * star b) := by
      exact congrArg
        (fun z : ℂ => Complex.im (z + b * star b))
        ha
    _ = Complex.im ((Complex.normSq a : ℂ) + (Complex.normSq b : ℂ)) := by
      exact congrArg
        (fun z : ℂ => Complex.im ((Complex.normSq a : ℂ) + z))
        hb
    _ =
        Complex.im (((Complex.normSq a + Complex.normSq b : ℝ) : ℂ)) := by
      exact congrArg Complex.im
        (Complex.ofReal_add (Complex.normSq a) (Complex.normSq b)).symm
    _ = 0 := by
      exact Complex.ofReal_im (Complex.normSq a + Complex.normSq b)

/-- The real scalar of one completed diagonal-debt coordinate is the sum of the two face
norm-squares. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) =
      Complex.normSq (zetaCompletedPrimeSpectralAmplitudeIndex ι f) +
        Complex.normSq (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have ha : Complex.re (a * star a) = Complex.normSq a :=
    complex_re_mul_star_self_eq_normSq_hermitianPacket a
  have hb : Complex.re (b * star b) = Complex.normSq b :=
    complex_re_mul_star_self_eq_normSq_hermitianPacket b
  calc
    Complex.re (a * star a + b * star b) =
        Complex.re (a * star a) + Complex.re (b * star b) := by
      exact Complex.add_re (a * star a) (b * star b)
    _ = Complex.normSq a + Complex.re (b * star b) := by
      exact congrArg (fun x : ℝ => x + Complex.re (b * star b)) ha
    _ = Complex.normSq a + Complex.normSq b := by
      exact congrArg (fun x : ℝ => Complex.normSq a + x) hb

/-- A completed diagonal-debt coordinate has zero real scalar when both weighted faces
vanish. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_zero_of_faces_eq_zero
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hpos : zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0)
    (hneg : zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) = 0 := by
  calc
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) =
        Complex.normSq (zetaCompletedPrimeSpectralAmplitudeIndex ι f) +
          Complex.normSq (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) := by
      exact zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
        ι f
    _ = Complex.normSq 0 +
          Complex.normSq (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) := by
      exact congrArg
        (fun z : ℂ =>
          Complex.normSq z +
            Complex.normSq (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f))
        hpos
    _ = Complex.normSq 0 + Complex.normSq 0 := by
      exact congrArg
        (fun z : ℂ => Complex.normSq 0 + Complex.normSq z)
        hneg
    _ = 0 + Complex.normSq 0 := by
      exact congrArg
        (fun x : ℝ => x + Complex.normSq 0)
        Complex.normSq_zero
    _ = 0 + 0 := by
      exact congrArg
        (fun x : ℝ => 0 + x)
        Complex.normSq_zero
    _ = 0 := by
      exact add_zero 0

/-- A completed diagonal-debt coordinate has zero real scalar only when both weighted faces
vanish. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_faces_eq_zero_of_re_eq_zero
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hzero : Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) = 0) :
    zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0 ∧
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0 := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have hre :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) =
        Complex.normSq a + Complex.normSq b :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_normSq_add_normSq
      ι f
  have hsum : Complex.normSq a + Complex.normSq b = 0 :=
    hre.symm.trans hzero
  have hparts :
      Complex.normSq a = 0 ∧ Complex.normSq b = 0 :=
    (add_eq_zero_iff_of_nonneg
      (Complex.normSq_nonneg a)
      (Complex.normSq_nonneg b)).mp
      hsum
  exact
    ⟨Complex.normSq_eq_zero.mp hparts.left,
      Complex.normSq_eq_zero.mp hparts.right⟩

/-- A completed diagonal-debt coordinate has zero real scalar exactly when both weighted
faces vanish. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_zero_iff_faces_eq_zero
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) = 0 ↔
      zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0 ∧
        zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0 := by
  constructor
  · intro hzero
    exact
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_faces_eq_zero_of_re_eq_zero
        ι f hzero
  · intro hfaces
    exact
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_eq_zero_of_faces_eq_zero
        ι f hfaces.left hfaces.right

/-- A finite completed positive prime defect-kernel window has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_re_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeDefectKernelPositiveRealWindow N f := by
  calc
    0 ≤ ∑ ι in ZetaPrimePowerIndex.window N,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
      exact Finset.sum_nonneg
        (fun ι _ =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate_re_nonnegative ι f)
    _ = Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
      exact (Complex.re_sum
        (ZetaPrimePowerIndex.window N)
        (fun ι =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)).symm

/-- A finite completed diagonal-debt coordinate window has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f := by
  calc
    0 ≤ ∑ ι in ZetaPrimePowerIndex.window N,
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) := by
      exact Finset.sum_nonneg
        (fun ι _ =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_nonnegative ι f)
    _ = Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) := by
      exact (Complex.re_sum
        (ZetaPrimePowerIndex.window N)
        (fun ι =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)).symm

/-- Nongenuine prime-power indices have zero completed positive defect coordinate. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimeDefectKernelPositiveCoordinate ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  have hsqrt : ZetaPrimePowerIndex.sqrtWeight ι = 0 := by
    exact (congrArg Real.sqrt hweight).trans Real.sqrt_zero
  have hpos :
      zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0 := by
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f))
  have hneg :
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0 := by
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f))
  calc
    (zetaCompletedPrimeSpectralAmplitudeIndex ι f -
          zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) *
        star
          (zetaCompletedPrimeSpectralAmplitudeIndex ι f -
            zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) =
        (0 - 0) * star (0 - 0 : ℂ) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ Sub.sub hpos hneg)
        (congrArg star (congrArg₂ Sub.sub hpos hneg))
    _ = 0 := by
      exact Eq.trans
        (congrArg
          (fun z : ℂ => z * star (0 - 0 : ℂ))
          (sub_self (0 : ℂ)))
        (zero_mul (star (0 - 0 : ℂ)))

/-- Nongenuine prime-power indices have zero completed diagonal-debt coordinate. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  have hsqrt : ZetaPrimePowerIndex.sqrtWeight ι = 0 := by
    exact (congrArg Real.sqrt hweight).trans Real.sqrt_zero
  have hpos :
      zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0 := by
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f))
  have hneg :
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0 := by
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f))
  calc
    zetaCompletedPrimeSpectralAmplitudeIndex ι f *
          star (zetaCompletedPrimeSpectralAmplitudeIndex ι f) +
        zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f *
          star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f) =
        0 * star (0 : ℂ) + 0 * star (0 : ℂ) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HMul.hMul hpos (congrArg star hpos))
        (congrArg₂ HMul.hMul hneg (congrArg star hneg))
    _ = 0 + 0 * star (0 : ℂ) := by
      exact congrArg
        (fun z : ℂ => z + 0 * star (0 : ℂ))
        (zero_mul (star (0 : ℂ)))
    _ = 0 + 0 := by
      exact congrArg
        (fun z : ℂ => 0 + z)
        (zero_mul (star (0 : ℂ)))
    _ = 0 := by
      exact add_zero 0

/-- The prime spectral majorant for the two real-axis amplitude families.

This is a conditional comparison majorant.  It is useful for estimates after a contour
realization supplies summability, but the code no longer treats independent real-axis
Laplace seed samples as intrinsically square-summable. -/
noncomputable def zetaCompletedPrimeSpectralCoordinateMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 +
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2

/-- The positive weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimePositiveWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2

/-- The opposite weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimeOppositeWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2

/-- Expanding a square-root-weighted real square only uses associativity,
commutativity, and the recorded square-root weight identity. -/
private theorem real_mul_norm_square_from_weight
    (r x w : ℝ) (hweight : r * r = w) :
    (r * x) ^ 2 = w * x ^ 2 :=
  calc
    (r * x) ^ 2 = (r * x) * (r * x) := by
      exact pow_two (r * x)
    _ = r * (x * (r * x)) := by
      exact mul_assoc r x (r * x)
    _ = r * ((x * r) * x) := by
      exact congrArg (fun z : ℝ => r * z) ((mul_assoc x r x).symm)
    _ = r * ((r * x) * x) := by
      exact congrArg (fun z : ℝ => r * (z * x)) (mul_comm x r)
    _ = r * (r * (x * x)) := by
      exact congrArg (fun z : ℝ => r * z) (mul_assoc r x x)
    _ = (r * r) * (x * x) := by
      exact (mul_assoc r r (x * x)).symm
    _ = w * (x * x) := by
      exact congrArg (fun z : ℝ => z * (x * x)) hweight
    _ = w * x ^ 2 := by
      exact congrArg (fun z : ℝ => w * z) (pow_two x).symm

/-- A nonnegative product of two real sizes is bounded by the sum of their squares. -/
private theorem nonnegative_mul_le_sq_add_sq
    (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y ≤ x ^ 2 + y ^ 2 := by
  have hxy_nonnegative : 0 ≤ x * y := by
    exact mul_nonneg hx hy
  have hproduct_le_twice : x * y ≤ 2 * x * y := by
    calc
      x * y = 1 * (x * y) := by
        exact (one_mul (x * y)).symm
      _ ≤ 2 * (x * y) := by
        exact mul_le_mul_of_nonneg_right one_le_two hxy_nonnegative
      _ = 2 * x * y := by
        exact (mul_assoc (2 : ℝ) x y).symm
  exact hproduct_le_twice.trans (two_mul_le_add_sq x y)

/-- The positive square-root-weight amplitude has norm square equal to the positive
weighted prime sample norm square. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      exact real_mul_norm_square_from_weight r ‖A‖ (ZetaPrimePowerIndex.weight ι) hweight

/-- The opposite square-root-weight amplitude has norm square equal to the opposite
weighted prime sample norm square. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimeOppositeWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      exact real_mul_norm_square_from_weight r ‖A‖ (ZetaPrimePowerIndex.weight ι) hweight

/-- The norm of a two-face product is bounded by the sum of the two squared face norms. -/
theorem complex_norm_mul_star_le_sq_add_sq (a b : ℂ) :
    ‖a * star b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hmul : ‖a * star b‖ ≤ ‖a‖ * ‖star b‖ :=
    norm_mul_le a (star b)
  have hstar : ‖star b‖ = ‖b‖ :=
    norm_star b
  have hmul_faces : ‖a * star b‖ ≤ ‖a‖ * ‖b‖ :=
    Eq.subst
      (motive := fun x : ℝ => ‖a * star b‖ ≤ ‖a‖ * x)
      hstar
      hmul
  have hface_arith : ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    exact nonnegative_mul_le_sq_add_sq ‖a‖ ‖b‖ (norm_nonneg a) (norm_nonneg b)
  exact hmul_faces.trans hface_arith

/-- The norm of one defect-square coordinate is bounded by twice the sum of the squared
face norms. -/
theorem complex_norm_defect_square_le_two_sq_add_sq (a b : ℂ) :
    ‖(a - b) * star (a - b)‖ ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hmul : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖star (a - b)‖ :=
    norm_mul_le (a - b) (star (a - b))
  have hstar : ‖star (a - b)‖ = ‖a - b‖ :=
    norm_star (a - b)
  have hmul_self : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖a - b‖ :=
    Eq.subst
      (motive := fun x : ℝ =>
        ‖(a - b) * star (a - b)‖ ≤ ‖a - b‖ * x)
      hstar
      hmul
  have hsub : ‖a - b‖ ≤ ‖a‖ + ‖b‖ :=
    norm_sub_le a b
  have hsub_nonneg : 0 ≤ ‖a - b‖ :=
    norm_nonneg (a - b)
  have hsum_nonneg : 0 ≤ ‖a‖ + ‖b‖ :=
    add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hsquare :
      ‖a - b‖ * ‖a - b‖ ≤
        (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) :=
    mul_le_mul hsub hsub hsub_nonneg hsum_nonneg
  have harith :
      (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) ≤
        2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2))
      (pow_two (‖a‖ + ‖b‖))
      (add_sq_le (a := ‖a‖) (b := ‖b‖))
  exact hmul_self.trans (hsquare.trans harith)

/-- The positive defect-square coordinate is bounded by twice the spectral majorant. -/
theorem norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeDefectKernelPositiveCoordinate ι f‖ ≤
      2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  exact
    complex_norm_defect_square_le_two_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The oriented two-face coordinate is bounded by the spectral majorant. -/
theorem norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  exact
    complex_norm_mul_star_le_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The completed diagonal-debt coordinate is bounded by the spectral majorant. -/
theorem norm_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  have ha :
      ‖a * star a‖ = ‖a‖ ^ 2 := by
    calc
      ‖a * star a‖ = ‖a‖ * ‖star a‖ := by
        exact norm_mul a (star a)
      _ = ‖a‖ * ‖a‖ := by
        exact congrArg (fun x : ℝ => ‖a‖ * x) (norm_star a)
      _ = ‖a‖ ^ 2 := by
        exact (pow_two ‖a‖).symm
  have hb :
      ‖b * star b‖ = ‖b‖ ^ 2 := by
    calc
      ‖b * star b‖ = ‖b‖ * ‖star b‖ := by
        exact norm_mul b (star b)
      _ = ‖b‖ * ‖b‖ := by
        exact congrArg (fun x : ℝ => ‖b‖ * x) (norm_star b)
      _ = ‖b‖ ^ 2 := by
        exact (pow_two ‖b‖).symm
  calc
    ‖a * star a + b * star b‖ ≤
        ‖a * star a‖ + ‖b * star b‖ := by
      exact norm_add_le (a * star a) (b * star b)
    _ = ‖a‖ ^ 2 + ‖b * star b‖ := by
      exact congrArg (fun x : ℝ => x + ‖b * star b‖) ha
    _ = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      exact congrArg (fun x : ℝ => ‖a‖ ^ 2 + x) hb

/-- A complex family bounded by twice the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_two_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  have htwo_majorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :=
    Summable.mul_left 2 hmajorant
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      htwo_majorant
      hbound

/-- A complex family bounded by the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      hmajorant
      hbound

/-- Summability of the spectral majorant implies summability of the positive defect-square
coordinates. -/
theorem summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_two_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the oriented two-face
coordinates. -/
theorem summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the completed diagonal-debt
coordinates. -/
theorem summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the symmetrized two-face
coordinates. -/
theorem summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
  let C : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f
  have hC : Summable C :=
    summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
      f hmajorant
  have hstar : Summable (fun ι : ZetaPrimePowerIndex => star (C ι)) :=
    hC.star
  have hsum : Summable (fun ι : ZetaPrimePowerIndex => C ι + star (C ι)) :=
    hC.add hstar
  exact hsum

/-- Taking real parts commutes with the completed prime-power sum of positive defect
coordinates. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f := by
  exact
    (Complex.re_tsum hsum).symm

/-- Taking real parts commutes with the completed prime-power sum of diagonal-debt
coordinates. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_tsum_eq_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hsum :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)) =
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) := by
  exact
    (Complex.re_tsum hsum).symm

set_option maxHeartbeats 800000

/-- Completed positive prime defect-square windows exhaust the real coordinate presentation,
provided the completed spectral-coordinate majorant is summable.

This is only a Hermitian prime-power window exhaustion theorem.  It does not identify these
spectral windows with a physical time-domain stream. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) := by
  let u : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
  have hsum_complex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f hmajorant
  have hsum_re : Summable u :=
    (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hsum_complex
  have hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι → u ι = 0 := by
    intro ι hι
    exact
      (congrArg Complex.re
        (zetaCompletedPrimeDefectKernelPositiveCoordinate_eq_zero_of_not_isGenuine
          ι f hι)).trans
        Complex.zero_re
  have hwindow :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f) =
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι) := by
    exact funext
      (fun N : ℕ => by
        unfold zetaCompletedPrimeDefectKernelPositiveRealWindow
        unfold zetaCompletedPrimeDefectKernelPositiveWindow
        exact Complex.re_sum
          (ZetaPrimePowerIndex.window N)
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimeDefectKernelPositiveCoordinate ι f))
  have hlimit :
      Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      u hsum_re hzero
  have htarget :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
      f hsum_complex
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
        atTop
        (𝓝 x))
    htarget
    (Eq.subst
      (motive := fun v : ℕ → ℝ =>
        Tendsto v atTop (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)))
      hwindow.symm
      hlimit)

/-- Completed diagonal-debt windows exhaust the real diagonal-debt coordinate presentation,
provided the completed spectral-coordinate majorant is summable. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
      atTop
      (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) := by
  let u : ZetaPrimePowerIndex → ℝ :=
    fun ι : ZetaPrimePowerIndex =>
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f)
  have hsum_complex :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f) :=
    summable_zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_of_spectralMajorant
      f hmajorant
  have hsum_re : Summable u :=
    (RCLike.reCLM : ℂ →L[ℝ] ℝ).summable hsum_complex
  have hzero :
      ∀ ι : ZetaPrimePowerIndex,
        ¬ ZetaPrimePowerIndex.IsGenuine ι → u ι = 0 := by
    intro ι hι
    exact
      (congrArg Complex.re
        (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_not_isGenuine
          ι f hι)).trans
        Complex.zero_re
  have hwindow :
      (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f) =
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι) := by
    exact funext
      (fun N : ℕ => by
        unfold zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow
        unfold zetaCompletedPrimeDefectKernelDiagonalDebtWindow
        exact Complex.re_sum
          (ZetaPrimePowerIndex.window N)
          (fun ι : ZetaPrimePowerIndex =>
            zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f))
  have hlimit :
      Tendsto
        (fun N : ℕ => ∑ ι in ZetaPrimePowerIndex.window N, u ι)
        atTop
        (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    ZetaPrimePowerIndex.tendsto_sum_window_tsum_of_summable
      u hsum_re hzero
  have htarget :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate_re_tsum_eq_coordinateTsum_re
      f hsum_complex
  exact Eq.subst
    (motive := fun x : ℝ =>
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 x))
    htarget
    (Eq.subst
      (motive := fun v : ℕ → ℝ =>
        Tendsto v atTop (𝓝 (∑' ι : ZetaPrimePowerIndex, u ι)))
      hwindow.symm
      hlimit)

/-- Under spectral-majorant summability, convergence of the completed positive prime-power
windows to the owner positive channel is exactly the comparison between the raw positive
coordinate presentation and the completed positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_iff_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) ↔
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  constructor
  · intro hpositive
    have hcoordinate :
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
      zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
        f hmajorant
    exact tendsto_nhds_unique hcoordinate hpositive
  · intro hcoordinate
    have hlimit :
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 (zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f)) :=
      zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
        f hmajorant
    exact Eq.subst
      (motive := fun x : ℝ =>
        Tendsto
          (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
          atTop
          (𝓝 x))
      hcoordinate
      hlimit

/-- The coordinate-presentation comparison turns completed positive prime-power window
convergence into convergence to the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_of_coordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hcoordinate :
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f) :
    Tendsto
      (fun N : ℕ => zetaCompletedPrimeDefectKernelPositiveRealWindow N f)
      atTop
      (𝓝 (completedPrimeDefectKernelPositiveChannel f)) := by
  exact
    (zetaCompletedPrimeDefectKernelPositiveRealWindow_tendsto_positiveChannel_iff_coordinateTsum_re
      f hmajorant).mpr
      hcoordinate

set_option maxHeartbeats 200000

/-- Dagger commutes with the completed oriented prime-power sum. -/
theorem zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_star_tsum
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)) =
      star
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    (tsum_star
      (f := fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)).symm

/-- A complex number with zero imaginary part is its real part embedded in `ℂ`. -/
theorem complex_eq_ofReal_re_of_im_eq_zero
    (z : ℂ) (hz : Complex.im z = 0) :
    z = (Complex.re z : ℂ) := by
  exact Complex.ext
    (Complex.ofReal_re (Complex.re z)).symm
    (hz.trans (Complex.ofReal_im (Complex.re z)).symm)

/-- The imaginary part of a completed complex sum vanishes when every coordinate is
real-valued. -/
theorem complex_im_tsum_eq_zero_of_forall_im_eq_zero
    {ι : Type*} (u : ι → ℂ)
    (hzero : ∀ i : ι, Complex.im (u i) = 0) :
    Complex.im (∑' i : ι, u i) = 0 := by
  have hpoint :
      (fun i : ι => u i) =
        (fun i : ι => (Complex.re (u i) : ℂ)) :=
    funext
      (fun i : ι =>
        complex_eq_ofReal_re_of_im_eq_zero (u i) (hzero i))
  calc
    Complex.im (∑' i : ι, u i) =
        Complex.im (∑' i : ι, (Complex.re (u i) : ℂ)) := by
      exact congrArg
        (fun v : ι → ℂ => Complex.im (∑' i : ι, v i))
        hpoint
    _ =
        Complex.im ((∑' i : ι, Complex.re (u i) : ℝ) : ℂ) := by
      exact congrArg Complex.im
        (Complex.ofReal_tsum
          (fun i : ι => Complex.re (u i))).symm
    _ = 0 := by
      exact Complex.ofReal_im (∑' i : ι, Complex.re (u i))

/-- Finite completed prime defect-square windows expand as diagonal debt minus the
symmetrized two-face window. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let P : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelPositiveCoordinate ι f
  let C : ZetaPrimePowerIndex → ℂ :=
    fun ι =>
      zetaCompletedPrimeSpectralAmplitudeIndex ι f *
        star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)
  let D : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f
  calc
    (∑ ι in s, P ι) + ((∑ ι in s, C ι) + star (∑ ι in s, C ι)) =
        (∑ ι in s, P ι) + ((∑ ι in s, C ι) + (∑ ι in s, star (C ι))) := by
      exact congrArg
        (fun z : ℂ => (∑ ι in s, P ι) + ((∑ ι in s, C ι) + z))
        (star_sum s C)
    _ =
        ((∑ ι in s, P ι) + (∑ ι in s, C ι)) +
          (∑ ι in s, star (C ι)) := by
      exact (add_assoc (∑ ι in s, P ι) (∑ ι in s, C ι) (∑ ι in s, star (C ι))).symm
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => P ι + C ι) +
          Finset.sum s (fun ι : ZetaPrimePowerIndex => star (C ι)) := by
      exact congrArg
        (fun z : ℂ => z + Finset.sum s (fun ι : ZetaPrimePowerIndex => star (C ι)))
        ((Finset.sum_add_distrib (s := s) (f := P) (g := C)).symm)
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => (P ι + C ι) + star (C ι)) := by
      exact
        ((Finset.sum_add_distrib
          (s := s)
          (f := fun ι : ZetaPrimePowerIndex => P ι + C ι)
          (g := fun ι : ZetaPrimePowerIndex => star (C ι))).symm)
    _ =
        Finset.sum s (fun ι : ZetaPrimePowerIndex => P ι + (C ι + star (C ι))) := by
      exact Finset.sum_congr rfl
        (fun (ι : ZetaPrimePowerIndex) (_ : ι ∈ s) =>
          add_assoc (P ι) (C ι) (star (C ι)))
    _ = ∑ ι in s, D ι := by
      exact Finset.sum_congr rfl
        (fun (ι : ZetaPrimePowerIndex) (_ : ι ∈ s) =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
            ι f)

/-- The completed sum of negative symmetrized two-face coordinates is the completed prime
boundary coefficient.

This is now the owner completed-channel comparison: the boundary coefficient is defined from
the completed spectral-sample channel, and the coordinatewise two-face expression is only a
presentation of that channel. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  calc
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          -((ZetaPrimePowerIndex.weight ι : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedExplicitFormulaPhi
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  (ZetaPrimePowerIndex.center ι)))) := by
      exact tsum_congr
        (fun ι : ZetaPrimePowerIndex =>
          (zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
            ι f).symm)

/-- The completed symmetrized two-face cross-coordinate sum is the completed matrix
coefficient.

This is the unsigned form of
`zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient`, transported
through the explicit sign theorem for the completed boundary coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
  have hboundary :
      (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  have hneg :
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
    have htsum :
        (∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) :=
      tsum_neg
        (f := fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
    calc
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (-(∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) := by
        exact congrArg Neg.neg htsum
      _ =
          ∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
        exact neg_neg
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
  have hmatrix :
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
    calc
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
          -(-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact congrArg Neg.neg
          (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
      _ = zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
        exact neg_neg (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  exact hneg.symm.trans
    ((congrArg Neg.neg hboundary).trans hmatrix)

/-- The completed coordinatewise defect expansion may be summed over all prime powers. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFaceCoordinate_tsum_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
  exact tsum_congr
    (fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
        ι f)

/-- The completed coordinatewise defect expansion separates into the positive coordinate
presentation plus the completed two-face matrix coefficient. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
  let P : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate ι f
  let T : ZetaPrimePowerIndex → ℂ :=
    fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f
  have hP : Summable P :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f hmajorant
  have hT : Summable T :=
    summable_zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_of_spectralMajorant
      f hmajorant
  have hsum :
      (∑' ι : ZetaPrimePowerIndex, (P ι + T ι)) =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          (∑' ι : ZetaPrimePowerIndex, T ι) :=
    tsum_add hP hT
  have hdiagonal :
      (∑' ι : ZetaPrimePowerIndex, (P ι + T ι)) =
        zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f :=
    zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFaceCoordinate_tsum_eq_diagonalDebt
      f
  have htwoFace :
      (∑' ι : ZetaPrimePowerIndex, T ι) =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient f
  calc
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
      rfl
    _ =
        (∑' ι : ZetaPrimePowerIndex, P ι) +
          (∑' ι : ZetaPrimePowerIndex, T ι) := by
      exact congrArg
        (fun z : ℂ => (∑' ι : ZetaPrimePowerIndex, P ι) + z)
        htwoFace.symm
    _ = ∑' ι : ZetaPrimePowerIndex, (P ι + T ι) := by
      exact hsum.symm
    _ = zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
      exact hdiagonal

/-- The raw completed positive prime defect-kernel presentation is its coordinate sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_positiveCoordinateTsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      ∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f := by
  rfl

/-- The finite completed prime defect-square expansion passes to the completed prime-power
realization.

This is the completed transport theorem for the three prime channels: positive defect
square, symmetrized two-face coefficient, and diagonal debt.  It is not proved from
real-axis spectral-coordinate summability; the owner proof must pass through the finite
defect-square windows, the prime distribution transport, and the completed contour
realization. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  exact sub_add_cancel (Df - Tf + T) T

/-- If the completed diagonal-debt coordinate presentation transports to the owner completed
diagonal debt, then the raw completed positive coordinate presentation has the owner positive
channel as its real scalar. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  let Pcoord : ℂ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Dcoord : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f
  let Powner : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let Downer : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  have hcoord_complex : Pcoord + T = Dcoord :=
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
      f hmajorant
  have howner_complex : Powner + T = Downer :=
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f
  have hcoord_re :
      Complex.re Pcoord + Complex.re T = Complex.re Dcoord := by
    calc
      Complex.re Pcoord + Complex.re T = Complex.re (Pcoord + T) := by
        exact (Complex.add_re Pcoord T).symm
      _ = Complex.re Dcoord := by
        exact congrArg Complex.re hcoord_complex
  have howner_re :
      completedPrimeDefectKernelPositiveChannel f + Complex.re T =
        Complex.re Downer := by
    calc
      completedPrimeDefectKernelPositiveChannel f + Complex.re T =
          Complex.re Powner + Complex.re T := by
        rfl
      _ = Complex.re (Powner + T) := by
        exact (Complex.add_re Powner T).symm
      _ = Complex.re Downer := by
        exact congrArg Complex.re howner_complex
  have hsame_sum :
      Complex.re Pcoord + Complex.re T =
        completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
    exact hcoord_re.trans (hdiagonal.trans howner_re.symm)
  have hcancel :
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
        (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T := by
    exact congrArg (fun x : ℝ => x + -Complex.re T) hsame_sum
  have hleft :
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
        Complex.re Pcoord := by
    calc
      (Complex.re Pcoord + Complex.re T) + -Complex.re T =
          Complex.re Pcoord + (Complex.re T + -Complex.re T) := by
        exact add_assoc (Complex.re Pcoord) (Complex.re T) (-Complex.re T)
      _ = Complex.re Pcoord + 0 := by
        exact congrArg
          (fun x : ℝ => Complex.re Pcoord + x)
          (add_neg_cancel (Complex.re T))
      _ = Complex.re Pcoord := by
        exact add_zero (Complex.re Pcoord)
  have hright :
      (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T =
        completedPrimeDefectKernelPositiveChannel f := by
    calc
      (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T =
          completedPrimeDefectKernelPositiveChannel f +
            (Complex.re T + -Complex.re T) := by
        exact add_assoc
          (completedPrimeDefectKernelPositiveChannel f)
          (Complex.re T)
          (-Complex.re T)
      _ = completedPrimeDefectKernelPositiveChannel f + 0 := by
        exact congrArg
          (fun x : ℝ => completedPrimeDefectKernelPositiveChannel f + x)
          (add_neg_cancel (Complex.re T))
      _ = completedPrimeDefectKernelPositiveChannel f := by
        exact add_zero (completedPrimeDefectKernelPositiveChannel f)
  calc
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        Complex.re Pcoord := by
      rfl
    _ =
        (Complex.re Pcoord + Complex.re T) + -Complex.re T := by
      exact hleft.symm
    _ =
        (completedPrimeDefectKernelPositiveChannel f + Complex.re T) +
          -Complex.re T := by
      exact hcancel
    _ = completedPrimeDefectKernelPositiveChannel f := by
      exact hright

/-- Under spectral-majorant summability, comparing the raw completed positive coordinate
presentation with the owner positive channel is equivalent to comparing the corresponding
diagonal-debt presentations. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_iff_diagonalDebtCoordinateTsum_re
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
        completedPrimeDefectKernelPositiveChannel f ↔
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
  constructor
  · intro hpositive
    let Pcoord : ℂ := zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f
    let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
    let Dcoord : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f
    let Powner : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
    let Downer : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
    have hcoord_complex : Pcoord + T = Dcoord :=
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_add_twoFace_eq_diagonalDebtCoordinateTsum
        f hmajorant
    have howner_complex : Powner + T = Downer :=
      zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f
    have hcoord_re :
        Complex.re Dcoord =
          zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f + Complex.re T := by
      calc
        Complex.re Dcoord = Complex.re (Pcoord + T) := by
          exact congrArg Complex.re hcoord_complex.symm
        _ = Complex.re Pcoord + Complex.re T := by
          exact Complex.add_re Pcoord T
        _ =
            zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
              Complex.re T := by
          rfl
    have howner_re :
        Complex.re Downer =
          completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
      calc
        Complex.re Downer = Complex.re (Powner + T) := by
          exact congrArg Complex.re howner_complex.symm
        _ = Complex.re Powner + Complex.re T := by
          exact Complex.add_re Powner T
        _ =
            completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
          rfl
    calc
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
          Complex.re Dcoord := by
        rfl
      _ =
          zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f +
            Complex.re T := by
        exact hcoord_re
      _ =
          completedPrimeDefectKernelPositiveChannel f + Complex.re T := by
        exact congrArg (fun x : ℝ => x + Complex.re T) hpositive
      _ = Complex.re Downer := by
        exact howner_re.symm
      _ = Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) := by
        rfl
  · intro hdiagonal
    exact
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
        f hmajorant hdiagonal

/-- Diagonal-debt finite-window convergence to the owner completed diagonal debt identifies
the raw positive coordinate presentation with the owner positive channel. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtRealWindow_tendsto
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hdiagonalOwnerLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f)))) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f =
      completedPrimeDefectKernelPositiveChannel f := by
  have hcoordinateLimit :
      Tendsto
        (fun N : ℕ => zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow N f)
        atTop
        (𝓝 (Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f))) :=
    zetaCompletedPrimeDefectKernelDiagonalDebtRealWindow_tendsto_coordinateTsum_re_of_spectralMajorant
      f hmajorant
  have hdiagonal :
      Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f) =
        Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) :=
    tendsto_nhds_unique hcoordinateLimit hdiagonalOwnerLimit
  exact
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_completedPrimeDefectKernelPositiveChannel_of_diagonalDebtCoordinateTsum_re
      f hmajorant hdiagonal

/-- The owner completed diagonal debt has zero real part once the completed and reconstructed
two-face real coefficients agree. -/
theorem zetaCompletedPrimeDefectKernelDiagonalDebt_re_eq_zero_of_twoFace_re_eq
    (f : ZetaAdmissibleFunction)
    (htwoFace :
      Complex.re (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f)) :
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) = 0 := by
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  have hfinite : Complex.re Df = 0 := by
    unfold Df
    exact zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_completedLowerWeightNormalization
      f
  have hre :
      Complex.re (Df - Tf + Tc) =
        Complex.re Df - Complex.re Tf + Complex.re Tc := by
    calc
      Complex.re (Df - Tf + Tc) =
          Complex.re (Df - Tf) + Complex.re Tc := by
        exact Complex.add_re (Df - Tf) Tc
      _ = (Complex.re Df - Complex.re Tf) + Complex.re Tc := by
        exact congrArg (fun x : ℝ => x + Complex.re Tc)
          (Complex.sub_re Df Tf)
      _ = Complex.re Df - Complex.re Tf + Complex.re Tc := by
        rfl
  calc
    Complex.re (zetaCompletedPrimeDefectKernelDiagonalDebt f) =
        Complex.re (Df - Tf + Tc) := by
      rfl
    _ = Complex.re Df - Complex.re Tf + Complex.re Tc := by
      exact hre
    _ = 0 - Complex.re Tf + Complex.re Tc := by
      exact congrArg
        (fun x : ℝ => x - Complex.re Tf + Complex.re Tc)
        hfinite
    _ = 0 - Complex.re Tf + Complex.re Tf := by
      exact congrArg
        (fun x : ℝ => 0 - Complex.re Tf + x)
        htwoFace
    _ = -Complex.re Tf + Complex.re Tf := by
      exact congrArg
        (fun x : ℝ => x + Complex.re Tf)
        (zero_sub (Complex.re Tf))
    _ = 0 := by
      exact neg_add_cancel (Complex.re Tf)

/-- The completed positive prime defect-kernel channel is the finite positive prime defect
form transported through the completed defect-square expansion. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  let Pc : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  have hfinite :
      zetaPrimeDefectKernelPositiveForm f + Tf = Df :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    Complex.re ((Df - Tf + Tc) - Tc) =
        Complex.re (Df - Tf) := by
      exact congrArg Complex.re (add_sub_cancel_right (Df - Tf) Tc)
    _ = Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
      have hpositive : Df - Tf = zetaPrimeDefectKernelPositiveForm f := by
        calc
          Df - Tf = (zetaPrimeDefectKernelPositiveForm f + Tf) - Tf := by
            exact congrArg (fun z : ℂ => z - Tf) hfinite.symm
          _ = zetaPrimeDefectKernelPositiveForm f := by
            exact add_sub_cancel_right (zetaPrimeDefectKernelPositiveForm f) Tf
      exact congrArg Complex.re hpositive

/-- Under the current finite-display lower-weight normalization, the owner completed positive
prime defect-kernel channel has zero real scalar. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f = 0 := by
  calc
    completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
      exact completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
    _ = 0 := by
      exact zetaPrimeDefectKernelPositiveForm_re_eq_zero_of_completedLowerWeightNormalization
        f

/-- The completed positive prime defect-kernel channel is nonnegative. -/
theorem completedPrimeDefectKernelPositiveChannel_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedPrimeDefectKernelPositiveChannel f := by
  have hchannel :
      completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) :=
    completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hchannel.symm
    (zetaPrimeDefectKernelPositiveForm_re_nonnegative f)

/-- The completed symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.im
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
          f).symm
    _ = 0 := by
      exact complex_im_tsum_eq_zero_of_forall_im_eq_zero
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_im_eq_zero ι f)

/-- The completed prime two-face boundary coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        Complex.im (-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
    _ =
        -Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact Complex.neg_im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    _ = -0 := by
      exact congrArg Neg.neg
        (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)
    _ = 0 := by
      exact neg_zero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

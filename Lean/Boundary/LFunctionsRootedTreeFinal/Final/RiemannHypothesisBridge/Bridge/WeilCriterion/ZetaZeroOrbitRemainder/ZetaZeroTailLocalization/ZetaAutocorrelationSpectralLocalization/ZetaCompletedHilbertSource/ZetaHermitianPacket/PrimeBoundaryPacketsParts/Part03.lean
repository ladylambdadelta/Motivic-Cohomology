import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PrimeBoundaryPacketsParts.Part02

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The one-coordinate positive prime defect square expands as diagonal debt minus the
symmetrized two-face cross term. -/
theorem zetaPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelPositiveCoordinate p n f +
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
            star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f) +
          star
            (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f))) =
      zetaPrimeDefectKernelDiagonalDebtCoordinate p n f := by
  let a : ℂ := zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f
  let b : ℂ := zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f
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
      exact defect_square_cross_cancel
        (a * star a) (b * star a) (a * star b) (b * star b)

/-- The positive prime defect kernel plus its two-face cross term is the prime diagonal debt. -/
theorem zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
      zetaPrimeDefectKernelPositiveForm f +
        zetaPrimeTwoFaceGNSMatrixCoefficient f =
      zetaPrimeDefectKernelDiagonalDebt f := by
  let s : Finset (ℕ × ℕ) := zetaCompletedExplicitFormulaPrimeSupport
  let P : ℕ × ℕ → ℂ :=
    fun ℓ => zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f
  let C : ℕ × ℕ → ℂ :=
    fun ℓ =>
      zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)
  let D : ℕ × ℕ → ℂ :=
    fun ℓ => zetaPrimeDefectKernelDiagonalDebtCoordinate ℓ.1 ℓ.2 f
  calc
    (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + star (∑ ℓ in s, C ℓ)) =
        (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + (∑ ℓ in s, star (C ℓ))) := by
      exact congrArg
        (fun z : ℂ =>
          (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + z))
        (star_sum s C)
    _ =
        ((∑ ℓ in s, P ℓ) + (∑ ℓ in s, C ℓ)) +
          (∑ ℓ in s, star (C ℓ)) := by
      exact (add_assoc (∑ ℓ in s, P ℓ) (∑ ℓ in s, C ℓ) (∑ ℓ in s, star (C ℓ))).symm
    _ =
        Finset.sum s (fun ℓ : ℕ × ℕ => P ℓ + C ℓ) +
          Finset.sum s (fun ℓ : ℕ × ℕ => star (C ℓ)) := by
      exact congrArg
        (fun z : ℂ => z + Finset.sum s (fun ℓ : ℕ × ℕ => star (C ℓ)))
        ((Finset.sum_add_distrib (s := s) (f := P) (g := C)).symm)
    _ =
        Finset.sum s (fun ℓ : ℕ × ℕ => (P ℓ + C ℓ) + star (C ℓ)) := by
      exact
        ((Finset.sum_add_distrib
          (s := s)
          (f := fun ℓ : ℕ × ℕ => P ℓ + C ℓ)
          (g := fun ℓ : ℕ × ℕ => star (C ℓ))).symm)
    _ =
        Finset.sum s (fun ℓ : ℕ × ℕ => P ℓ + (C ℓ + star (C ℓ))) := by
      exact Finset.sum_congr rfl
        (fun (ℓ : ℕ × ℕ) (_ : ℓ ∈ s) =>
          add_assoc (P ℓ) (C ℓ) (star (C ℓ)))
    _ = ∑ ℓ in s, D ℓ := by
      exact Finset.sum_congr rfl
        (fun (ℓ : ℕ × ℕ) (_ : ℓ ∈ s) =>
          zetaPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
            ℓ.1 ℓ.2 f)

/-- Real scalar form of the prime defect-square expansion. -/
theorem zetaPrimeDefectKernelPositiveForm_re_add_twoFace_re_eq_diagonalDebt_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
      Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
  have hcomplex :
      zetaPrimeDefectKernelPositiveForm f +
          zetaPrimeTwoFaceGNSMatrixCoefficient f =
        zetaPrimeDefectKernelDiagonalDebt f :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  calc
    Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.re
          (zetaPrimeDefectKernelPositiveForm f +
            zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact (Complex.add_re
        (zetaPrimeDefectKernelPositiveForm f)
        (zetaPrimeTwoFaceGNSMatrixCoefficient f)).symm
    _ = Complex.re (zetaPrimeDefectKernelDiagonalDebt f) := by
      exact congrArg Complex.re hcomplex

/-- The real part of one complex Hermitian square is its norm-square. -/
theorem complex_re_mul_star_self_eq_normSq_hermitianPacket
    (z : ℂ) :
    Complex.re (z * star z) = Complex.normSq z := by
  have hmul : z * star z = (Complex.normSq z : ℂ) := by
    exact Complex.mul_conj z
  calc
    Complex.re (z * star z) =
        Complex.re (Complex.normSq z : ℂ) := by
      exact congrArg Complex.re hmul
    _ = Complex.normSq z := by
      rfl

/-- The real part of one complex Hermitian square is nonnegative. -/
theorem complex_re_mul_star_self_nonnegative_hermitianPacket
    (z : ℂ) :
    0 ≤ Complex.re (z * star z) := by
  have hnorm :
      Complex.re (z * star z) = Complex.normSq z :=
    complex_re_mul_star_self_eq_normSq_hermitianPacket z
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hnorm.symm
    (Complex.normSq_nonneg z)

/-- One positive prime defect-kernel coordinate has nonnegative real part. -/
theorem zetaPrimeDefectKernelPositiveCoordinate_re_nonnegative
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaPrimeDefectKernelPositiveCoordinate p n f) := by
  let a : ℂ := zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f
  let b : ℂ := zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f
  exact complex_re_mul_star_self_nonnegative_hermitianPacket (a - b)

/-- The positive prime defect-kernel form has nonnegative real part. -/
theorem zetaPrimeDefectKernelPositiveForm_re_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  calc
    0 ≤ ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        Complex.re (zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact Finset.sum_nonneg
        (fun ℓ _ =>
          zetaPrimeDefectKernelPositiveCoordinate_re_nonnegative ℓ.1 ℓ.2 f)
    _ = Complex.re
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact (Complex.re_sum
        zetaCompletedExplicitFormulaPrimeSupport
        (fun ℓ =>
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f)).symm

/-- One finite-display prime defect coordinate has real part equal to the Hermitian
defect-amplitude coordinate Gram. -/
theorem zetaPrimeDefectKernelPositiveCoordinate_re_eq_defectAmplitude_normSq
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveCoordinate p n f) =
      ZetaHermitianPacketEnsemble.coordinateGram
        (zetaPrimeHermitianDefectAmplitude p n f) := by
  exact complex_re_mul_star_self_eq_normSq_hermitianPacket
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
      zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)

/-- The symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  let z : ℂ := zetaPrimeTwoFaceGNSOrientedCoefficient f
  calc
    Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
      exact Complex.add_im z (star z)
    _ = Complex.im z + -Complex.im z := by
      exact congrArg (fun x : ℝ => Complex.im z + x) (Complex.conj_im z)
    _ = 0 := by
      exact add_neg_cancel (Complex.im z)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

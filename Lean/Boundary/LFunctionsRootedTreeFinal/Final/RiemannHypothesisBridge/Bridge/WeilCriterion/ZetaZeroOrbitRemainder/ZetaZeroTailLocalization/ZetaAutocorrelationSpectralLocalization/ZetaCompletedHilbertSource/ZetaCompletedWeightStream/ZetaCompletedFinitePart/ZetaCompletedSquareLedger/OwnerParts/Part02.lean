import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaCompletedWeightStream.ZetaCompletedFinitePart.ZetaCompletedSquareLedger.OwnerParts.Part01

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

open Filter
open ZetaPrimePowerIndex

/-- The non-prime completed channel: archimedean contribution plus centered correction,
evaluated on the convolution autocorrelation probe. -/
def zetaArchimedeanCorrectionAutocorrelationChannel
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re
      (zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)) +
    Complex.re
      (zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- The archimedean autocorrelation square energy at the self-dual basepoint. -/
def zetaArchimedeanAutocorrelationSquareEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  2 * Complex.normSq (zetaCompletedExplicitFormulaPhi f 0)

/-- The correction autocorrelation square energy is the centered-pole Hermitian correction
packet gram. -/
def zetaCorrectionAutocorrelationSquareEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.correctionPacketGram
    (zetaCompletedHermitianBoundaryDefect f)

/-- The honest non-prime completed square energy: archimedean square plus correction square. -/
def zetaArchimedeanCorrectionAutocorrelationSquareEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaArchimedeanAutocorrelationSquareEnergy f +
    zetaCorrectionAutocorrelationSquareEnergy f

/-- Multiplying a complex conjugate square by the real scalar two has real part twice the
complex norm square. -/
theorem complex_two_mul_conjSquare_re
    (z : ℂ) :
    Complex.re ((2 : ℂ) * (z * star z)) =
      2 * Complex.normSq z := by
  have hsq : z * star z = (Complex.normSq z : ℂ) :=
    Complex.mul_conj z
  have hreal :
      (2 : ℂ) * (Complex.normSq z : ℂ) =
        ((2 * Complex.normSq z : ℝ) : ℂ) := by
    exact (Complex.ofReal_mul 2 (Complex.normSq z)).symm
  calc
    Complex.re ((2 : ℂ) * (z * star z)) =
        Complex.re ((2 : ℂ) * (Complex.normSq z : ℂ)) := by
      exact congrArg (fun x : ℂ => Complex.re ((2 : ℂ) * x)) hsq
    _ = Complex.re ((2 * Complex.normSq z : ℝ) : ℂ) := by
      exact congrArg Complex.re hreal
    _ = 2 * Complex.normSq z := by
      exact Complex.ofReal_re (2 * Complex.normSq z)

/-- The autocorrelation transform at the archimedean basepoint is a Hermitian square. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_zero
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
      zetaCompletedExplicitFormulaPhi f 0 *
        star (zetaCompletedExplicitFormulaPhi f 0) := by
  have hpair :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0
  have hzero :
      zetaCompletedExplicitFormulaPhi f (-(0 : ℂ)) =
        zetaCompletedExplicitFormulaPhi f 0 := by
    exact congrArg (zetaCompletedExplicitFormulaPhi f) (neg_zero : -(0 : ℂ) = 0)
  calc
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f (-(0 : ℂ))) := hpair
    _ =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0) := by
      exact congrArg
        (fun x : ℂ => zetaCompletedExplicitFormulaPhi f 0 * star x)
        hzero

/-- The archimedean autocorrelation channel is the archimedean Hermitian square energy. -/
theorem zetaArchimedeanAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      zetaArchimedeanAutocorrelationSquareEnergy f := by
  unfold zetaCompletedExplicitFormulaArchimedeanContribution
  unfold zetaArchimedeanAutocorrelationSquareEnergy
  have hzero :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_zero f
  calc
    Complex.re
        ((2 : ℂ) *
          zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0) =
        Complex.re
          ((2 : ℂ) *
            (zetaCompletedExplicitFormulaPhi f 0 *
              star (zetaCompletedExplicitFormulaPhi f 0))) := by
      exact congrArg (fun x : ℂ => Complex.re ((2 : ℂ) * x)) hzero
    _ = 2 * Complex.normSq (zetaCompletedExplicitFormulaPhi f 0) := by
      exact complex_two_mul_conjSquare_re (zetaCompletedExplicitFormulaPhi f 0)

/-- The correction autocorrelation channel is the correction square energy. -/
theorem zetaCorrectionAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      zetaCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaCorrectionAutocorrelationSquareEnergy
  have howner :
      zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
      f
  calc
    Complex.re
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
        Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      exact congrArg Complex.re howner
    _ =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
      exact zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic f

/-- Archimedean plus correction is exactly the honest non-prime completed square energy. -/
theorem zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy
    (f : ZetaAdmissibleFunction) :
    zetaArchimedeanCorrectionAutocorrelationChannel f =
      zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
  have harch := zetaArchimedeanAutocorrelationChannel_eq_squareEnergy f
  have hcorr := zetaCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold zetaArchimedeanCorrectionAutocorrelationChannel
  unfold zetaArchimedeanCorrectionAutocorrelationSquareEnergy
  exact congrArg₂ HAdd.hAdd harch hcorr

/-- The archimedean autocorrelation square energy is nonnegative. -/
theorem zetaArchimedeanAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaArchimedeanAutocorrelationSquareEnergy f := by
  unfold zetaArchimedeanAutocorrelationSquareEnergy
  exact mul_nonneg
    (by exact zero_le_two)
    (Complex.normSq_nonneg (zetaCompletedExplicitFormulaPhi f 0))

/-- The correction autocorrelation square energy is nonnegative. -/
theorem zetaCorrectionAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaCorrectionAutocorrelationSquareEnergy
  exact
    ZetaHermitianPacketEnsemble.correctionPacketGram_nonnegative
      (zetaCompletedHermitianBoundaryDefect f)

/-- The honest non-prime completed square energy is nonnegative. -/
theorem zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
  unfold zetaArchimedeanCorrectionAutocorrelationSquareEnergy
  exact add_nonneg
    (zetaArchimedeanAutocorrelationSquareEnergy_nonnegative f)
    (zetaCorrectionAutocorrelationSquareEnergy_nonnegative f)

/-- The raw finite completed autocorrelation boundary channel in physical variables. -/
def zetaCompletedPhysicalAutocorrelationBoundaryChannel
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeOffDiagonalChannel N f +
    zetaArchimedeanCorrectionAutocorrelationChannel f

/-- The completed square energy attached to the finite physical boundary channel after adding
the matching prime diagonal debt. -/
def zetaCompletedPhysicalAutocorrelationSquareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaPrimeTranslationDefectEnergy N f +
    zetaArchimedeanCorrectionAutocorrelationSquareEnergy f

/-- The completed physical boundary channel becomes a sum of squares after adding the matching
prime diagonal debt. -/
theorem zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPhysicalAutocorrelationBoundaryChannel N f +
        zetaPrimeDiagonalDebt N f =
      zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
  have hprime :=
    zetaPrimeOffDiagonal_add_diagonalDebt_eq_translationDefectEnergy N f
  have harch :=
    zetaArchimedeanCorrectionAutocorrelationChannel_eq_squareEnergy f
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
  calc
    (zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f) +
        zetaPrimeDiagonalDebt N f =
        (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f) +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      have hassoc₁ :
          (zetaPrimeOffDiagonalChannel N f +
              zetaArchimedeanCorrectionAutocorrelationChannel f) +
              zetaPrimeDiagonalDebt N f =
            zetaPrimeOffDiagonalChannel N f +
              (zetaArchimedeanCorrectionAutocorrelationChannel f +
                zetaPrimeDiagonalDebt N f) := by
        exact add_assoc
          (zetaPrimeOffDiagonalChannel N f)
          (zetaArchimedeanCorrectionAutocorrelationChannel f)
          (zetaPrimeDiagonalDebt N f)
      have hcomm :
          zetaArchimedeanCorrectionAutocorrelationChannel f +
              zetaPrimeDiagonalDebt N f =
            zetaPrimeDiagonalDebt N f +
              zetaArchimedeanCorrectionAutocorrelationChannel f := by
        exact add_comm
          (zetaArchimedeanCorrectionAutocorrelationChannel f)
          (zetaPrimeDiagonalDebt N f)
      have hassoc₂ :
          zetaPrimeOffDiagonalChannel N f +
              (zetaPrimeDiagonalDebt N f +
                zetaArchimedeanCorrectionAutocorrelationChannel f) =
            (zetaPrimeOffDiagonalChannel N f + zetaPrimeDiagonalDebt N f) +
              zetaArchimedeanCorrectionAutocorrelationChannel f := by
        exact (add_assoc
          (zetaPrimeOffDiagonalChannel N f)
          (zetaPrimeDiagonalDebt N f)
          (zetaArchimedeanCorrectionAutocorrelationChannel f)).symm
      exact hassoc₁.trans
        ((congrArg
          (fun x : ℝ => zetaPrimeOffDiagonalChannel N f + x)
          hcomm).trans hassoc₂)
    _ =
        zetaPrimeTranslationDefectEnergy N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      exact congrArg
        (fun x : ℝ => x + zetaArchimedeanCorrectionAutocorrelationChannel f)
        hprime
    _ =
        zetaPrimeTranslationDefectEnergy N f +
          zetaArchimedeanCorrectionAutocorrelationSquareEnergy f := by
      exact congrArg
        (fun x : ℝ => zetaPrimeTranslationDefectEnergy N f + x)
        harch

/-- The debt-corrected completed finite physical autocorrelation boundary channel is
nonnegative. -/
theorem zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPhysicalAutocorrelationBoundaryChannel N f +
        zetaPrimeDiagonalDebt N f := by
  have hsquare :=
    zetaCompletedPhysicalAutocorrelationBoundaryChannel_add_diagonalDebt_eq_squareEnergy N f
  have hprime := zetaPrimeTranslationDefectEnergy_nonnegative N f
  have haux := zetaArchimedeanCorrectionAutocorrelationSquareEnergy_nonnegative f
  have hsum :
      0 ≤ zetaCompletedPhysicalAutocorrelationSquareEnergy N f := by
    unfold zetaCompletedPhysicalAutocorrelationSquareEnergy
    exact add_nonneg hprime haux
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hsquare.symm hsum

/-- The finite completed physical boundary channel attached to the `N`th prime-power window. -/
def completedBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedPhysicalAutocorrelationBoundaryChannel N f

/-- The physical prime off-diagonal boundary window evaluates the convolution autocorrelation
kernel at prime-power centers.  This is distinct from the Laplace-transform spectral window. -/
def primeKernelOffDiagonalBoundaryWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  ∑ ι in ZetaPrimePowerIndex.window N,
    - (2 * ι.weight * Complex.re (convolutionAutocorrelationKernel f ι.center))

/-- The kernel-level prime off-diagonal window is the physical prime off-diagonal channel. -/
theorem primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    primeKernelOffDiagonalBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f := by
  unfold primeKernelOffDiagonalBoundaryWindow
  unfold zetaPrimeOffDiagonalChannel
  exact Finset.sum_congr rfl
    (fun ι hι =>
      (fun hmem : ι ∈ ZetaPrimePowerIndex.window N =>
        by
          unfold zetaPrimeOffDiagonalCoordinate
          have hkernel :
              convolutionAutocorrelationKernel f ι.center =
                zetaSeedInner (zetaTranslate ι.center f) f :=
            convolutionAutocorrelationKernel_eq_translateInner f ι.center
          exact congrArg
            (fun x : ℝ => - (2 * ι.weight * x))
            (congrArg Complex.re hkernel)) hι)

/-- The completed physical boundary window is the kernel off-diagonal window plus the
archimedean/correction square channel. -/
theorem completedBoundaryWindow_eq_primeKernelOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      primeKernelOffDiagonalBoundaryWindow N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  have hprime :=
    primeKernelOffDiagonalBoundaryWindow_eq_physicalPrimeOffDiagonal N f
  unfold completedBoundaryWindow
  unfold zetaCompletedPhysicalAutocorrelationBoundaryChannel
  calc
    zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f =
        zetaPrimeOffDiagonalChannel N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      rfl
    _ =
        primeKernelOffDiagonalBoundaryWindow N f +
          zetaArchimedeanCorrectionAutocorrelationChannel f := by
      exact congrArg
        (fun x : ℝ => x + zetaArchimedeanCorrectionAutocorrelationChannel f)
        hprime.symm

/-- The completed physical boundary window unfolds to the prime off-diagonal window plus the
archimedean/correction channel. -/
theorem completedBoundaryWindow_eq_primeOffDiagonal_add_archimedeanCorrection
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    completedBoundaryWindow N f =
      zetaPrimeOffDiagonalChannel N f +
        zetaArchimedeanCorrectionAutocorrelationChannel f := by
  rfl

/-- The smaller prime-power window embeds into the larger one compatibly with the completed
physical boundary presentation. -/
theorem completedBoundaryWindow_mono_compat
    {N M : ℕ} (hNM : N ≤ M) (f : ZetaAdmissibleFunction) :
    zetaPrimeOffDiagonalChannel N f =
      ∑ ι in (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N),
        zetaPrimeOffDiagonalCoordinate ι f := by
  unfold zetaPrimeOffDiagonalChannel
  have hwindow :
      (ZetaPrimePowerIndex.window M).filter
          (fun ι => ι ∈ ZetaPrimePowerIndex.window N) =
        ZetaPrimePowerIndex.window N := by
    ext ι
    constructor
    · intro hι
      exact (Finset.mem_filter.mp hι).2
    · intro hι
      exact Finset.mem_filter.mpr
        ⟨ZetaPrimePowerIndex.window_mono hNM hι, hι⟩
  exact congrArg
    (fun s : Finset ZetaPrimePowerIndex =>
      ∑ ι in s, zetaPrimeOffDiagonalCoordinate ι f)
    hwindow.symm

/-- The debt-corrected finite completed boundary window.  This is the finite approximant in the
completed normalization; the raw finite physical window alone is not the approximating object. -/
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

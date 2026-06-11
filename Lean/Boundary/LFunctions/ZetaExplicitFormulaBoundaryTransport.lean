import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaPacketComparison
import Boundary.LFunctions.ZetaHermitianPacket

/-!
# Boundary explicit-formula transport

This file owns the proved transport between the explicit-formula boundary
package and the completed packet/boundary-defect package.

It deliberately does not prove the zero-side explicit formula

```lean
zetaCompletedZeroKreinGram f =
  ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f
```

That equality is the analytic contour-shift theorem. The owner theorem for it
belongs to the completed explicit-formula assembly layer, after the residue,
decay, and vertical-decomposition inputs are available.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The completed explicit-formula boundary sum in signed real form. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The completed boundary-defect Krein Gram in signed form. -/
noncomputable def zetaCompletedBoundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The boundary-defect Krein notation is the boundary-defect Gram. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Krein Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectKreinGram f := by
  rfl

/-- The completed explicit-formula boundary sum is the boundary-defect Gram. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedBoundaryDefectGram f := by
  rfl

/-- The boundary-defect Krein Gram is the centered completed packet norm square. -/
theorem zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryDefectKreinGram f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f).trans
      (zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f)

/-- The explicit-formula boundary sum is the centered completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySum f =
      zetaCompletedPacketNormSq f 0 := by
  exact
    (zetaCompletedExplicitFormulaBoundarySum_eq_boundaryDefectKreinGram f).trans
      (zetaCompletedBoundaryDefectKreinGram_eq_completedPacketNormSq f)

/-- The centered completed packet norm square is the explicit-formula boundary sum. -/
theorem zetaCompletedPacketNormSq_eq_explicitFormulaBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPacketNormSq f 0 =
      zetaCompletedExplicitFormulaBoundarySum f := by
  exact (zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f).symm

/-- The explicit-formula boundary sum is nonnegative through the packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundarySum_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaBoundarySum f := by
  have hpacket : 0 ≤ zetaCompletedPacketNormSq f 0 :=
    zetaCompletedPacketNormSq_nonnegative f 0
  have hboundary :
      zetaCompletedExplicitFormulaBoundarySum f =
        zetaCompletedPacketNormSq f 0 :=
    zetaCompletedExplicitFormulaBoundarySum_eq_completedPacketNormSq f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hboundary.symm hpacket

/-- The completed boundary-defect Krein Gram is nonnegative. -/
theorem zetaCompletedBoundaryDefectKreinGram_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedBoundaryDefectKreinGram f := by
  have hboundary : 0 ≤ zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectGram_nonnegative f
  have hkrein :
      zetaCompletedBoundaryDefectKreinGram f =
        zetaCompletedBoundaryDefectGram f :=
    zetaCompletedBoundaryDefectKreinGram_eq_boundaryDefectGram f
  exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hkrein.symm hboundary

/-- The geometry-layer analytic boundary sum is the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      zetaCompletedExplicitFormulaBoundarySumCore f := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq f).trans
      (zetaCompletedExplicitFormulaBoundarySumCore_eq f).symm

/-- The real part of the analytic-core boundary expression. This is the linear explicit-formula
boundary functional before it is compared with the Krein/Gram packet normalization. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaBoundarySumCore f)

/-- The analytic boundary sum has the same real part as the analytic-core boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_analytic
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core f).symm

/-- The real linear boundary sum unfolds to the real parts of the prime, archimedean, and
correction contributions. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_components
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      Complex.re (zetaCompletedExplicitFormulaPrimeContribution f) +
        Complex.re (zetaCompletedExplicitFormulaArchimedeanContribution f) +
        Complex.re (zetaCompletedExplicitFormulaCorrectionContribution f) := by
  exact congrArg Complex.re (zetaCompletedExplicitFormulaBoundarySumCore_eq f)

/-- The Krein/Gram boundary expression attached to the explicit-formula packets. -/
noncomputable def zetaCompletedExplicitFormulaBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedBoundaryDefectGram f

/-- The Krein boundary sum is the signed real boundary sum used downstream. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

/-- The Krein boundary sum is the completed packet norm square. -/
theorem zetaCompletedExplicitFormulaBoundaryKreinSum_eq_completedPacketNormSq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryKreinSum f =
      zetaCompletedPacketNormSq f 0 := by
  exact zetaCompletedBoundaryDefectGram_eq_completedPacketNormSq f

/-- The convolution-autocorrelation boundary Krein sum is the Hermitian seed packet Gram.
This is the target normalization for the holographic positivity argument: the explicit
formula is evaluated on the convolution autocorrelation kernel, while the Hermitian Gram is
formed from the original seed `f`. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedHermitianPacketNormSq f

/-- Historical name for the convolution-autocorrelation boundary Krein sum. -/
abbrev zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum f

/-- The convolution-autocorrelation boundary Krein sum is nonnegative. -/
theorem zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum f := by
  exact zetaCompletedHermitianPacketNormSq_nonnegative f

/-- Historical name for nonnegativity of the convolution-autocorrelation boundary Krein sum. -/
theorem zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaConvolutionAutocorrelationBoundaryKreinSum_nonnegative f

/-- A complex number is a real scalar once its real part is the scalar and its imaginary part
vanishes. -/
theorem complex_eq_of_re_eq_of_im_eq_zero
    (z : ℂ) (r : ℝ)
    (hre : Complex.re z = r)
    (him : Complex.im z = 0) :
    z = (r : ℂ) := by
  exact Complex.ext hre (him.trans (Complex.ofReal_im r).symm)

/-- Prime-channel holography: the prime explicit-formula functional evaluated on the
convolution autocorrelation kernel is the Hermitian prime packet Gram. -/
theorem zetaCompletedExplicitFormulaPrimeChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic f

/-- The prime linear boundary functional on the convolution autocorrelation kernel is its
Hermitian prime packet contribution. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionLinearReal_eq_primePacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaPrimeChannel_holographic f

/-- Historical name for prime convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaPrimeLinearReal_autocorrelation_eq_primePacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionLinearReal_eq_primePacketGram f

/-- Archimedean-channel holography: the archimedean explicit-formula functional evaluated
on the convolution autocorrelation kernel is the Hermitian archimedean packet Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic f

/-- The archimedean linear boundary functional on the convolution autocorrelation kernel is its
Hermitian archimedean packet contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanChannel_holographic f

/-- Historical name for archimedean convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaArchimedeanLinearReal_autocorrelation_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram f

/-- Correction-channel holography: the correction explicit-formula functional evaluated on the
convolution autocorrelation kernel is the Hermitian correction packet Gram. -/
theorem zetaCompletedExplicitFormulaCorrectionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic f

/-- The correction linear boundary functional on the convolution autocorrelation kernel is its
Hermitian correction packet contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionChannel_holographic f

/-- Historical name for correction convolution-channel holography. -/
theorem zetaCompletedExplicitFormulaCorrectionLinearReal_autocorrelation_eq_correctionPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram f

/-- The convolution-autocorrelation boundary functional in real channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)

/-- The convolution-autocorrelation boundary functional in complex channel form. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f

/-- The real part of the convolution boundary sum is the real channel sum. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
      zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f := by
  unfold zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic
  unfold zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum
  calc
    Complex.re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re
            (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
              zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) :=
      Complex.add_re
        (zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)
        (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f)
    _ =
        (Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f)) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      exact congrArg
        (fun x : ℝ =>
          x + Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f))
        (Complex.add_re
          (zetaCompletedExplicitFormulaPrimeConvolutionContribution f)
          (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f))
    _ =
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      rfl

/-- The Hermitian convolution boundary Krein sum. -/
noncomputable def zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f)

/-- The real convolution explicit-formula boundary functional agrees with the Hermitian
seed packet Krein sum. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  have hprime :
      Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
        ZetaHermitianPacketEnsemble.primePacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedExplicitFormulaPrimeConvolutionLinearReal_eq_primePacketGram f
  have harch :
      Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedExplicitFormulaArchimedeanConvolutionLinearReal_eq_archimedeanPacketGram f
  have hcorrection :
      Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) :=
    zetaCompletedExplicitFormulaCorrectionConvolutionLinearReal_eq_correctionPacketGram f
  have hgram :
      ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.primePacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
    exact ZetaHermitianPacketEnsemble.normSq_eq_prime_add_archimedean_add_correction
      (zetaCompletedHermitianBoundaryDefect f)
  calc
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
        Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) +
          Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) := by
      rfl
    _ =
        ZetaHermitianPacketEnsemble.primePacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) +
          ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (congrArg₂ (fun a b : ℝ => a + b) hprime harch)
        hcorrection
    _ = ZetaHermitianPacketEnsemble.normSq
          (zetaCompletedHermitianBoundaryDefect f) := hgram.symm
    _ = zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
      rfl

/-- Historical name for the real convolution boundary assembly theorem. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaConvolutionBoundaryKreinSum f := by
  exact zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum f

/-- The convolution boundary sum is real. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) = 0 := by
  let p : ℂ := zetaCompletedExplicitFormulaPrimeConvolutionContribution f
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f
  let c : ℂ := zetaCompletedExplicitFormulaCorrectionConvolutionContribution f
  have hp : Complex.im p = 0 :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero f
  have ha : Complex.im a = 0 :=
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero f
  have hc : Complex.im c = 0 :=
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution_im_eq_zero f
  calc
    Complex.im (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
        Complex.im (p + a + c) := by
      rfl
    _ = Complex.im (p + a) + Complex.im c := Complex.add_im (p + a) c
    _ = (Complex.im p + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im p a)
    _ = (0 + 0) + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hp ha)
        hc
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The complex convolution boundary sum agrees with the Hermitian seed packet Krein
normalization. -/
theorem zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  have hreal :
      Complex.re (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) =
        zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f := by
    exact
      (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_re f).trans
        (zetaCompletedExplicitFormulaConvolutionBoundaryLinearRealSum_eq_seedKreinSum f)
  have him :
      Complex.im (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f) = 0 :=
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_im_eq_zero f
  exact complex_eq_of_re_eq_of_im_eq_zero
    (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f)
    (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f)
    hreal him

/-- Prime analytic convolution transform bridge before paired-coordinate folding.

This is the owner analytic bridge between the original explicit-formula prime functional
applied to the convolution autocorrelation probe and the paired spectral prime channel
attached to the seed. Its proof is the prime-channel transform identity for
`g_f = f * f†`, with the square-root prime weights absorbed into the two paired spectral
coordinates. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_convolutionAutocorrelation_eq_pairedSpectral
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f := by
  sorry

/-- Prime spectral convolution bridge after paired-coordinate folding. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f := by
  exact
    (zetaCompletedExplicitFormulaPrimeContribution_convolutionAutocorrelation_eq_pairedSpectral
      f).trans
      (zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_hermitian f)

/-- Archimedean analytic convolution transform bridge before self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
        star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) := by
  sorry

/-- Archimedean spectral convolution bridge after self-paired folding. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  exact
    (zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_pairedSpectral
      f).trans
      (zetaCompletedExplicitFormulaArchimedeanConvolutionPaired_eq_hermitian f)

/-- The usual correction contribution of the admissible convolution autocorrelation probe is the
convolution-channel correction contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero.symm

/-- The usual analytic boundary sum of the admissible convolution autocorrelation probe is the
convolution-channel boundary sum. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  have hprime :
      zetaCompletedExplicitFormulaPrimeContribution g =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f :=
    zetaCompletedExplicitFormulaPrimeContribution_convolutionAutocorrelation_eq f
  have harch :
      zetaCompletedExplicitFormulaArchimedeanContribution g =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq f
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionContribution g =
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq f
  calc
    zetaCompletedExplicitFormulaBoundarySumAnalytic g =
        zetaCompletedExplicitFormulaPrimeContribution g +
          zetaCompletedExplicitFormulaArchimedeanContribution g +
          zetaCompletedExplicitFormulaCorrectionContribution g := by
      exact zetaCompletedExplicitFormulaBoundarySumAnalytic_eq g
    _ =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
      exact congrArg₂ (fun a b : ℂ => a + b)
        (congrArg₂ (fun a b : ℂ => a + b) hprime harch)
        hcorrection
    _ = zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f := by
      rfl

/-- The analytic boundary sum of the admissible convolution autocorrelation probe agrees with
the Hermitian seed packet Krein normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_convolutionAutocorrelation_eq f).trans
      (zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_seedKreinSum f)

/-- Raw all-probe boundary normalization. This is stronger than the holographic
convolution-autocorrelation route and is not used by the convolution-autocorrelation positivity
proof. -/
theorem zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_kreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundaryLinearRealSum f =
      zetaCompletedExplicitFormulaBoundaryKreinSum f := by
  sorry

/-- Raw all-probe real-valuedness of the analytic-core boundary expression. This is stronger
than the convolution-autocorrelation real-valuedness needed for positivity. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaBoundarySumCore f) = 0 := by
  sorry

/-- The prime contribution is real on convolution-autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have h :
      zetaCompletedExplicitFormulaPrimeContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f :=
    zetaCompletedExplicitFormulaPrimeContribution_convolutionAutocorrelation_eq f
  exact (congrArg Complex.im h).trans
    (zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero f)

/-- The archimedean contribution is real on convolution-autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have h :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq f
  exact (congrArg Complex.im h).trans
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero f)

/-- The correction contribution is real on convolution-autocorrelation probes. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        zetaCompletionCorrection 0 :=
    Boundary.LFunctions.zetaCompletionCorrection_zero.symm
  exact (congrArg Complex.im hcorrection).trans
    Boundary.LFunctions.zetaCompletionCorrection_zero_im

/-- If the three explicit-formula boundary channels are real, then their analytic-core sum is
real. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components
    (f : ZetaAdmissibleFunction)
    (hprime :
      Complex.im
          (zetaCompletedExplicitFormulaPrimeContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (harch :
      Complex.im
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0)
    (hcorrection :
      Complex.im
          (zetaCompletedExplicitFormulaCorrectionContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  let g : ZetaAdmissibleFunction := ZetaAdmissibleFunction.convolutionAutocorrelation f
  let p : ℂ := zetaCompletedExplicitFormulaPrimeContribution g
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanContribution g
  let c : ℂ := zetaCompletedExplicitFormulaCorrectionContribution g
  have hcore :
      Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) :=
    congrArg Complex.im (zetaCompletedExplicitFormulaBoundarySumCore_eq g)
  have hp : Complex.im p = 0 := hprime
  have ha : Complex.im a = 0 := harch
  have hc : Complex.im c = 0 := hcorrection
  calc
    Complex.im (zetaCompletedExplicitFormulaBoundarySumCore g) =
        Complex.im (p + a + c) := hcore
    _ = Complex.im (p + a) + Complex.im c := Complex.add_im (p + a) c
    _ = (Complex.im p + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im p a)
    _ = (0 + 0) + 0 := by
      exact congrArg₂ (fun x y : ℝ => x + y)
        (congrArg₂ (fun x y : ℝ => x + y) hp ha)
        hc
    _ = 0 + 0 := by
      exact add_zero (0 + 0)
    _ = 0 := by
      exact zero_add 0

/-- The analytic-core boundary expression attached to a convolution-autocorrelation probe has
vanishing imaginary part. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im
        (zetaCompletedExplicitFormulaBoundarySumCore
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) = 0 := by
  exact zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_im_eq_zero_of_components f
    (zetaCompletedExplicitFormulaPrimeContribution_autocorrelation_im_eq_zero f)
    (zetaCompletedExplicitFormulaArchimedeanContribution_autocorrelation_im_eq_zero f)
    (zetaCompletedExplicitFormulaCorrectionContribution_autocorrelation_im_eq_zero f)

/-- Legacy wrapper name for the corrected convolution-boundary normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_seedKreinSum f

/-- Legacy wrapper name for the corrected convolution-boundary analytic normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_autocorrelation_eq_seedKreinSum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic f =
      (zetaCompletedExplicitFormulaAutocorrelationBoundaryKreinSum f : ℂ) := by
  exact zetaCompletedExplicitFormulaConvolutionBoundarySumAnalytic_eq_seedKreinSum f

/-- The analytic-core explicit-formula boundary expression agrees with the signed real
boundary-defect Gram normalization.

This is the substantive normalization comparison: the left side is the prime,
archimedean, and pole-correction expression from the contour formula, while the right side is
the packet/boundary-defect Gram used in the positivity argument, embedded in `ℂ`. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_eq_realBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumCore f =
      (zetaCompletedExplicitFormulaBoundarySum f : ℂ) := by
  have hreal :
      Complex.re (zetaCompletedExplicitFormulaBoundarySumCore f) =
        zetaCompletedExplicitFormulaBoundarySum f := by
    exact
      (zetaCompletedExplicitFormulaBoundaryLinearRealSum_eq_kreinSum f).trans
        (zetaCompletedExplicitFormulaBoundaryKreinSum_eq_realBoundarySum f)
  have him :
      Complex.im (zetaCompletedExplicitFormulaBoundarySumCore f) = 0 :=
    zetaCompletedExplicitFormulaBoundarySumCore_im_eq_zero f
  exact complex_eq_of_re_eq_of_im_eq_zero
    (zetaCompletedExplicitFormulaBoundarySumCore f)
    (zetaCompletedExplicitFormulaBoundarySum f)
    hreal him

/-- The analytic explicit-formula boundary sum agrees with the signed real boundary-defect
Gram normalization. -/
theorem zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_realBoundarySum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumAnalytic f =
      (zetaCompletedExplicitFormulaBoundarySum f : ℂ) := by
  exact
    (zetaCompletedExplicitFormulaBoundarySumAnalytic_eq_core f).trans
      (zetaCompletedExplicitFormulaBoundarySumCore_eq_realBoundarySum f)

/-- The analytic equality still required to complete the explicit formula. -/
def zetaCompletedExplicitFormulaAutocorrelationTarget
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedZeroKreinGram f =
    zetaCompletedExplicitFormulaBoundarySum f

/-- The target proposition unfolds to the zero-side/boundary equality. -/
theorem zetaCompletedExplicitFormulaAutocorrelationTarget_iff
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaAutocorrelationTarget f ↔
      zetaCompletedZeroKreinGram f =
        zetaCompletedExplicitFormulaBoundarySum f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.HermitianBoundaryDefect

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The prime channel produced directly by the convolution transform factorization, before
folding paired spectral coordinates into Hermitian squares. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  Finset.sum zetaCompletedExplicitFormulaPrimeSupport (fun ℓ : ℕ × ℕ =>
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) +
      star
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)))

/-- The archimedean channel produced directly by the convolution transform factorization. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
    star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)

/-- A prime paired spectral coordinate expands to the weighted paired spectral product. -/
theorem zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f) =
      (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
        (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
          star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) := by
  let r : ℝ := zetaCompletedExplicitFormulaPrimeSqrtWeight p n
  let a : ℂ := zetaCompletedPrimeBoundaryRealizedPositiveFace p n f
  let b : ℂ := zetaCompletedPrimeBoundaryRealizedNegativeFace p n f
  have hstar_r : star (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  have hstar_opposite :
      star ((r : ℂ) * b) = (r : ℂ) * star b := by
    calc
      star ((r : ℂ) * b) = star b * star (r : ℂ) := by
        exact star_mul (r : ℂ) b
      _ = star b * (r : ℂ) := by
        exact congrArg (fun z : ℂ => star b * z) hstar_r
      _ = (r : ℂ) * star b := by
        exact mul_comm (star b) (r : ℂ)
  have hsqrt_sq_real :
      r * r = zetaCompletedExplicitFormulaPrimeWeight p n := by
    exact zetaCompletedExplicitFormulaPrimeSqrtWeight_mul_self p n
  have hsqrt_sq_complex :
      (r : ℂ) * (r : ℂ) =
        (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) := by
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul r r).symm
      _ = (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hsqrt_sq_real
  calc
    ((r : ℂ) * a) * star ((r : ℂ) * b) =
        ((r : ℂ) * a) * ((r : ℂ) * star b) := by
      exact congrArg (fun z : ℂ => ((r : ℂ) * a) * z) hstar_opposite
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
    _ = (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) * (a * star b) := by
      exact congrArg (fun z : ℂ => z * (a * star b)) hsqrt_sq_complex

/-- The paired prime spectral packet contribution is the weighted paired-product sum. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_weightedPairedSum_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      Finset.sum zetaCompletedExplicitFormulaPrimeSupport (fun ℓ : ℕ × ℕ =>
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedPrimeBoundaryRealizedPositiveFace ℓ.1 ℓ.2 f *
              star (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f)) +
            star
              (zetaCompletedPrimeBoundaryRealizedPositiveFace ℓ.1 ℓ.2 f *
                star (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f)))) := by
  exact Finset.sum_congr rfl
    (fun ℓ _ => by
      let w : ℝ := zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2
      let x : ℂ :=
        zetaCompletedPrimeBoundaryRealizedPositiveFace ℓ.1 ℓ.2 f *
          star (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f)
      have hraw :
          zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) =
            (w : ℂ) * x :=
        zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite ℓ.1 ℓ.2 f
      have hstar_w : star (w : ℂ) = (w : ℂ) := by
        exact Complex.conj_ofReal w
      have hstar_weighted : star ((w : ℂ) * x) = (w : ℂ) * star x := by
        calc
          star ((w : ℂ) * x) = star x * star (w : ℂ) := by
            exact star_mul (w : ℂ) x
          _ = star x * (w : ℂ) := by
            exact congrArg (fun z : ℂ => star x * z) hstar_w
          _ = (w : ℂ) * star x := by
            exact mul_comm (star x) (w : ℂ)
      calc
        zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) +
            star
              (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) =
            (w : ℂ) * x + star ((w : ℂ) * x) := by
          exact congrArg (fun z : ℂ => z + star z) hraw
        _ = (w : ℂ) * x + (w : ℂ) * star x := by
          exact congrArg (fun z : ℂ => (w : ℂ) * x + z) hstar_weighted
        _ = (w : ℂ) * (x + star x) := by
          exact (mul_add (w : ℂ) x (star x)).symm)

/-- The paired archimedean spectral packet contribution is the weighted paired product. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f =
      (2 : ℂ) *
        (zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0)) := by
  let r : ℝ := Real.sqrt 2
  let a : ℂ := zetaCompletedExplicitFormulaPhi f 0
  have hstar_r : star (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  have hstar_amp : star ((r : ℂ) * a) = (r : ℂ) * star a := by
    calc
      star ((r : ℂ) * a) = star a * star (r : ℂ) := by
        exact star_mul (r : ℂ) a
      _ = star a * (r : ℂ) := by
        exact congrArg (fun z : ℂ => star a * z) hstar_r
      _ = (r : ℂ) * star a := by
        exact mul_comm (star a) (r : ℂ)
  have htwo_nonnegative : (0 : ℝ) ≤ 2 := by
    exact zero_le_two
  have hsqrt_sq_real : r * r = 2 := by
    exact (pow_two (Real.sqrt 2)).symm.trans (Real.sq_sqrt htwo_nonnegative)
  have hsqrt_sq_complex : (r : ℂ) * (r : ℂ) = (2 : ℂ) := by
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul r r).symm
      _ = (2 : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hsqrt_sq_real
  calc
    ((r : ℂ) * a) * star ((r : ℂ) * a) =
        ((r : ℂ) * a) * ((r : ℂ) * star a) := by
      exact congrArg (fun z : ℂ => ((r : ℂ) * a) * z) hstar_amp
    _ = ((r : ℂ) * (r : ℂ)) * (a * star a) := by
      calc
        ((r : ℂ) * a) * ((r : ℂ) * star a) =
            (r : ℂ) * (a * ((r : ℂ) * star a)) := by
          exact mul_assoc (r : ℂ) a ((r : ℂ) * star a)
        _ = (r : ℂ) * ((a * (r : ℂ)) * star a) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * z)
            ((mul_assoc a (r : ℂ) (star a)).symm)
        _ = (r : ℂ) * (((r : ℂ) * a) * star a) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * (z * star a))
            (mul_comm a (r : ℂ))
        _ = (r : ℂ) * ((r : ℂ) * (a * star a)) := by
          exact congrArg (fun z : ℂ => (r : ℂ) * z)
            (mul_assoc (r : ℂ) a (star a))
        _ = ((r : ℂ) * (r : ℂ)) * (a * star a) := by
          exact (mul_assoc (r : ℂ) (r : ℂ) (a * star a)).symm
    _ = (2 : ℂ) * (a * star a) := by
      exact congrArg (fun z : ℂ => z * (a * star a)) hsqrt_sq_complex

/-- The prime explicit-formula channel evaluated on the convolution autocorrelation kernel.
This is the finite paired spectral display channel produced by the convolution transform
identity. The completed cone-facing two-face coefficient is
`zetaCompletedPrimeTwoFaceGNSMatrixCoefficient`. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f

/-- The archimedean explicit-formula channel evaluated on the convolution autocorrelation
kernel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f

/-- The correction channel evaluated on autocorrelation is the centered-pole owner
contribution of the autocorrelation probe. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaCorrectionContribution
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The prime paired channel is definitionally the convolution prime contribution. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_paired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
      zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f := by
  rfl

/-- The archimedean paired channel is definitionally the convolution archimedean contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
      zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f := by
  rfl

/-- Archimedean reconstruction into the realized Gram channel is the direct coordinate identity. -/
theorem zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f =
  zetaCompletedArchimedeanBoundaryRealizedGram f := by
  rfl

/-- Correction reconstruction into the realized Gram channel is the correction normalization. -/
theorem zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      zetaCompletedCorrectionBoundaryRealizedGram f := by
  rfl
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

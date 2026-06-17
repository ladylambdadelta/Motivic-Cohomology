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
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) +
      star
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f))

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
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        (zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 : ℂ) *
          ((zetaCompletedPrimeBoundaryRealizedPositiveFace ℓ.1 ℓ.2 f *
              star (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f)) +
            star
              (zetaCompletedPrimeBoundaryRealizedPositiveFace ℓ.1 ℓ.2 f *
                star (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f))) := by
  exact Finset.sum_congr rfl
    (fun ℓ _ =>
      congrArg (fun z : ℂ => z + star z)
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite ℓ.1 ℓ.2 f))

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
This is the paired spectral channel produced by the convolution transform identity. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f

/-- The archimedean explicit-formula channel evaluated on the convolution autocorrelation
kernel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f

/-- The correction channel evaluated on autocorrelation is the centered correction scalar. -/
def zetaCompletedExplicitFormulaCorrectionConvolutionContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletionCorrection 0

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

/-- The realized archimedean Gram channel agrees with the Hermitian archimedean amplitude
packet Gram. -/
theorem zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanBoundaryRealizedGram f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  rfl

/-- The weighted seed-amplitude prime coordinate is the completed autocorrelation face
coordinate. This is the coordinate form of the spectral-factor theorem, not a raw negative-face
identification. -/
theorem zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) +
      star
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) =
      zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f := by
  let raw : ℂ :=
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
      star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)
  calc
    raw + star raw =
        ((zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
          (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
            star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f))) +
        star ((zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
          (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
            star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f))) := by
      exact congrArg (fun z : ℂ => z + star z)
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite p n f)
    _ =
        (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
          ((zetaCompletedPrimeHermitianSeedAmplitude p n f *
              star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f)) +
            star
              (zetaCompletedPrimeHermitianSeedAmplitude p n f *
                star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f))) := by
      -- The weight is real, so conjugating the weighted raw coordinate preserves the weight.
      let w : ℝ := zetaCompletedExplicitFormulaPrimeWeight p n
      let x : ℂ :=
        zetaCompletedPrimeHermitianSeedAmplitude p n f *
          star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f)
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
        (w : ℂ) * x + star ((w : ℂ) * x) =
            (w : ℂ) * x + (w : ℂ) * star x := by
          exact congrArg (fun z : ℂ => (w : ℂ) * x + z) hstar_weighted
        _ = (w : ℂ) * (x + star x) := by
          exact (mul_add (w : ℂ) x (star x)).symm
    _ = zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f := by
      exact (zetaCompletedPrimeBoundaryRealizedCoordinateGram_eq_twoFaceCoefficient
        p n hp hn f).symm

/-- Every prime-label coordinate reconstructs into the realized Gram coordinate. Genuine prime
powers use the spectral-factor theorem; non-prime or zero-exponent labels vanish by the
completed prime weight. -/
theorem zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram_all
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) +
      star
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) =
      zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f := by
  exact
    if hp : Nat.Prime p then
      if hn : n ≠ 0 then
        zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram
          p n hp hn f
      else
        have hweight :
            zetaCompletedExplicitFormulaPrimeWeight p n = 0 :=
          zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_zero_exponent p n hp hn
        have hweighted :
            (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
              (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) =
              0 := by
          calc
            (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
                (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                  star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) =
                (0 : ℂ) *
                  (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                    star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) := by
              exact congrArg
                (fun x : ℝ => (x : ℂ) *
                  (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                    star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)))
                hweight
            _ = 0 := by
              exact zero_mul
        have hrealized :
            zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f = 0 := by
          calc
            (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
                (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f) +
                  star (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f))) =
                (0 : ℂ) *
                  (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f) +
                    star (zetaCompletedAutocorrelationPrimePositiveFace p n
                      (zetaCompletedAutocorrelationProbe f))) := by
              exact congrArg
                (fun x : ℝ => (x : ℂ) *
                  (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f) +
                    star (zetaCompletedAutocorrelationPrimePositiveFace p n
                      (zetaCompletedAutocorrelationProbe f))))
                hweight
            _ = 0 := by
              exact zero_mul
        calc
          (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) +
              star (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) =
              0 + star (0 : ℂ) := by
            exact congrArg (fun z : ℂ => z + star z)
              ((zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite p n f).trans
                hweighted)
          _ = 0 := by
            calc
              0 + star (0 : ℂ) = 0 + (0 : ℂ) := by
                exact congrArg (fun z : ℂ => 0 + z) (star_zero : star (0 : ℂ) = 0)
              _ = 0 := by
                exact add_zero 0
          _ = zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f := hrealized.symm
    else
      have hweight :
        zetaCompletedExplicitFormulaPrimeWeight p n = 0 :=
        zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_not_prime p n hp
      have hweighted :
          (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
            (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
              star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) =
            0 := by
        calc
          (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
              (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) =
              (0 : ℂ) *
                (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                  star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)) := by
            exact congrArg
              (fun x : ℝ => (x : ℂ) *
                (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                  star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f)))
              hweight
          _ = 0 := by
            exact zero_mul
      have hrealized :
          zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f = 0 := by
        calc
          (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
              (zetaCompletedAutocorrelationPrimePositiveFace p n
                (zetaCompletedAutocorrelationProbe f) +
                star (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f))) =
              (0 : ℂ) *
                (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f) +
                  star (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f))) := by
            exact congrArg
              (fun x : ℝ => (x : ℂ) *
                (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f) +
                  star (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f))))
              hweight
          _ = 0 := by
            exact zero_mul
      calc
        (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
            star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) +
            star (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)) =
            0 + star (0 : ℂ) := by
          exact congrArg (fun z : ℂ => z + star z)
            ((zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite p n f).trans
              hweighted)
        _ = 0 := by
          calc
            0 + star (0 : ℂ) = 0 + (0 : ℂ) := by
              exact congrArg (fun z : ℂ => 0 + z) (star_zero : star (0 : ℂ) = 0)
            _ = 0 := by
              exact add_zero 0
        _ = zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f := hrealized.symm

/-- The raw paired archimedean coordinate is definitionally the realized archimedean Gram
coordinate. -/
theorem zetaCompletedArchimedeanBoundaryReconstruction_pairedCoordinate_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
        star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f) =
      zetaCompletedArchimedeanBoundaryRealizedCoordinateGram f := by
  exact (zetaCompletedArchimedeanBoundaryCoordinate_isReconstructed f).symm

/-- Prime reconstruction into the realized Gram channel is the finite-sum form of the completed
autocorrelation spectral-factor theorem. -/
theorem zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      zetaCompletedPrimeBoundaryRealizedGram f := by
  exact Finset.sum_congr rfl
    (fun ℓ _ =>
      zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram_all
        ℓ.1 ℓ.2 f)

/-- The archimedean explicit-formula channel on the convolution-autocorrelation probe descends
to the paired archimedean spectral contribution. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_eq_paired_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f := by
  have hzero :
      zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) 0 =
        zetaCompletedExplicitFormulaPhi f 0 *
          star (zetaCompletedExplicitFormulaPhi f 0) := by
    have hpair :=
      zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair f 0
    have hneg :
        zetaCompletedExplicitFormulaPhi f (-(0 : ℂ)) =
          zetaCompletedExplicitFormulaPhi f 0 := by
      exact congrArg (zetaCompletedExplicitFormulaPhi f) (neg_zero : -(0 : ℂ) = 0)
    exact hpair.trans
      (congrArg
        (fun z : ℂ => zetaCompletedExplicitFormulaPhi f 0 * star z)
        hneg)
  have hleft :
      zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
        (2 : ℂ) *
          (zetaCompletedExplicitFormulaPhi f 0 *
            star (zetaCompletedExplicitFormulaPhi f 0)) := by
    exact congrArg (fun z : ℂ => (2 : ℂ) * z) hzero
  exact hleft.trans
    (zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution_eq_weightedPaired_owner
      f).symm

/-- The correction explicit-formula channel on the convolution-autocorrelation probe is the
correction convolution contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero.symm

/-- The finite paired prime contribution is the finite two-face/GNS matrix coefficient.

This is only finite-support bookkeeping: it says that summing each oriented coordinate
together with its adjoint is the same as taking the finite oriented sum and adding its
adjoint.  It does not identify finite-support data with the completed prime-power `tsum`. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_twoFaceMatrixCoefficient_finite
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  let C : ℕ × ℕ → ℂ :=
    fun ℓ =>
      zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)
  have hsplit :
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ + star (C ℓ)) =
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ) +
          (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, star (C ℓ)) := by
    exact Finset.sum_add_distrib
  have hstar :
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, star (C ℓ)) =
        star (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ) := by
    exact
      (map_sum star zetaCompletedExplicitFormulaPrimeSupport C).symm
  exact hsplit.trans
    (congrArg
      (fun z : ℂ => (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ) + z)
      hstar)

/-- The realized real prime channel agrees with the two-face/GNS prime matrix coefficient.
This is the correct real-side replacement for the false one-face norm-square comparison. -/
theorem zetaCompletedPrimeBoundaryRealizedGram_eq_twoFacePrimeMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeBoundaryRealizedGram f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  exact
    (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram f).symm.trans
      (zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_twoFaceMatrixCoefficient_finite
        f)

/-- Prime completed boundary reconstruction: the paired prime spectral channel is the two-face
GNS matrix coefficient of the reconstructed real prime packet. -/
theorem zetaCompletedPrimeBoundaryReconstruction_pairing_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  exact
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_twoFaceMatrixCoefficient_finite
      f

/-- Archimedean completed boundary reconstruction: the paired archimedean spectral channel is
the Hermitian Gram of the reconstructed archimedean boundary packet. -/
theorem zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_gram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_realizedGram f).trans
    (zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram f)

/-- The prime convolution contribution is the reconstructed two-face/GNS prime matrix
coefficient. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  exact (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_paired f).trans
    (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_twoFaceMatrixCoefficient f)

/-- The explicit prime convolution contribution is the cross term in the positive prime
defect-kernel expansion.  Adding the positive prime defect kernel produces the prime diagonal
debt. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_add_primeDefectKernelPositiveForm_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelPositiveForm f +
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
      zetaPrimeDefectKernelDiagonalDebt f := by
  have hcross :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient f
  calc
    zetaPrimeDefectKernelPositiveForm f +
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
        zetaPrimeDefectKernelPositiveForm f +
          zetaPrimeTwoFaceGNSMatrixCoefficient f := by
      exact congrArg (fun z : ℂ => zetaPrimeDefectKernelPositiveForm f + z) hcross
    _ = zetaPrimeDefectKernelDiagonalDebt f := by
      exact zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f

/-- The archimedean convolution contribution is the reconstructed Hermitian archimedean Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired f).trans
    (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_gram f)

/-- The real part of the prime convolution contribution is the real part of the reconstructed
two-face/GNS matrix coefficient. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact congrArg Complex.re
    (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient f)

/-- The prime convolution contribution is real-valued when the two-face/GNS matrix coefficient
is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero_of_twoFace_real
    (f : ZetaAdmissibleFunction)
    (hreal : Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0) :
    Complex.im (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) = 0 := by
  exact (congrArg Complex.im
    (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_twoFaceMatrixCoefficient f)).trans
    hreal

/-- The reconstructed prime convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) = 0 := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero_of_twoFace_real
    f (zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)

/-- The reconstructed archimedean convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) = 0 := by
  exact (congrArg Complex.im
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram f)).trans
    (Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f)))

/-- The real part of the reconstructed archimedean convolution contribution is the Hermitian
archimedean packet Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact congrArg Complex.re
    (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram f)

/-- The correction convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) = 0 := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero_im

/-- Prime-channel two-face/GNS holography. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic_twoFace
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient f

/-- Archimedean-channel norm-square holography. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram f

/-- Correction-channel holography for the normalized Hermitian correction packet. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  have hleft :
      Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re (zetaCompletionCorrection 0) := by
    rfl
  have hsquare :
      Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate =
        Complex.re (zetaCompletionCorrection 0) :=
    Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate_sq
  have hright :
      ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
    exact zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq f
  calc
    Complex.re (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) =
        Complex.re (zetaCompletionCorrection 0) := hleft
    _ =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := hsquare.symm
    _ =
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := hright.symm

/-- Correction completed boundary reconstruction. -/
theorem zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_gram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  apply Complex.ext
  · exact zetaCompletedExplicitFormulaCorrectionConvolutionChannel_holographic f
  · calc
      Complex.im (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) = 0 := by
        exact zetaCompletedExplicitFormulaCorrectionConvolutionContribution_im_eq_zero f
      _ =
          Complex.im
            (ZetaHermitianPacketEnsemble.correctionPacketGram
              (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
        exact (Complex.ofReal_im
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f))).symm

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

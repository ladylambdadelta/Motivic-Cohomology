import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ConvolutionChannelsParts.Part01_Basic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ArchimedeanCriticalLineIntegrability

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The realized archimedean Gram channel agrees with the Hermitian archimedean amplitude
packet Gram. -/
theorem zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanBoundaryRealizedGram f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  let x : ZetaHermitianPacketEnsemble := zetaCompletedHermitianBoundaryDefect f
  let a : ℂ := zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f
  have hprime :
      zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = 0 :=
    zetaPrimeHermitianPacketAsEnsemble_archimedean_apply f
  have hcorr :
      zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = 0 := by
    exact
      Finsupp.single_eq_of_ne
        (fun h : ZetaPacketLabel.correction = ZetaPacketLabel.archimedean =>
          ZetaPacketLabel.noConfusion h)
  have harch :
      zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = a := by
    exact Finsupp.single_eq_same
  have hx_arch : x ZetaPacketLabel.archimedean = a := by
    calc
      (zetaPrimeHermitianPacketAsEnsemble f +
            zetaArchimedeanHermitianPacketAsEnsemble f +
            zetaCorrectionHermitianPacketAsEnsemble f)
          ZetaPacketLabel.archimedean =
          zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean +
            zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean +
            zetaCorrectionHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean := by
        rfl
      _ =
          0 +
            zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean +
            0 := by
        exact congrArg₂
          (fun u v : ℂ =>
            u +
              zetaArchimedeanHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean +
              v)
          hprime
          hcorr
      _ = 0 + a + 0 := by
        exact congrArg (fun z : ℂ => 0 + z + 0) harch
      _ = a + 0 := by
        exact congrArg (fun z : ℂ => z + 0) (zero_add a)
      _ = a := by
        exact add_zero a
  have hsum :
      ∑ ℓ in x.support,
          (match ℓ with
          | .archimedean => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0) =
        ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.archimedean) := by
    exact Finset.sum_eq_single ZetaPacketLabel.archimedean
      (fun ℓ hℓ hne => by
        cases ℓ with
        | prime p n => rfl
        | archimedean => exact False.elim (hne rfl)
        | correction => rfl)
      (fun hnotmem => by
        have hx_zero : x ZetaPacketLabel.archimedean = 0 :=
          Finsupp.not_mem_support_iff.mp hnotmem
        exact
          (congrArg ZetaHermitianPacketEnsemble.coordinateGram hx_zero).trans
            ZetaHermitianPacketEnsemble.coordinateGram_zero)
  have hgram :
      ZetaHermitianPacketEnsemble.archimedeanPacketGram x =
        ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.archimedean) := by
    exact hsum
  have hcoord :
      (ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.archimedean) : ℂ) =
        a * star a := by
    calc
      (ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.archimedean) : ℂ) =
          (ZetaHermitianPacketEnsemble.coordinateGram a : ℂ) := by
        exact congrArg
          (fun z : ℂ => (ZetaHermitianPacketEnsemble.coordinateGram z : ℂ))
          hx_arch
      _ = a * star a := by
        exact (Complex.mul_conj a).symm
  calc
    zetaCompletedArchimedeanBoundaryRealizedGram f = a * star a := by
      rfl
    _ = (ZetaHermitianPacketEnsemble.coordinateGram
          (x ZetaPacketLabel.archimedean) : ℂ) := hcoord.symm
    _ = (ZetaHermitianPacketEnsemble.archimedeanPacketGram x : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hgram.symm

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
                (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                  star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f))
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
                (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f) +
                  star (zetaCompletedAutocorrelationPrimePositiveFace p n
                    (zetaCompletedAutocorrelationProbe f)))
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
                exact congrArg (fun z : ℂ => 0 + z) (star_zero (R := ℂ))
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
              (zetaCompletedPrimeBoundaryRealizedPositiveFace p n f *
                star (zetaCompletedPrimeBoundaryRealizedNegativeFace p n f))
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
              (zetaCompletedAutocorrelationPrimePositiveFace p n
                (zetaCompletedAutocorrelationProbe f) +
                star (zetaCompletedAutocorrelationPrimePositiveFace p n
                  (zetaCompletedAutocorrelationProbe f)))
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
              exact congrArg (fun z : ℂ => 0 + z) (star_zero (R := ℂ))
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

/-- The archimedean boundary channel on the autocorrelation probe unfolds to
the Hermitian Gamma-factor contribution. This is the valid direct-centered
archimedean transport hook; it does not identify the continuum channel with
the rank-one endpoint packet. -/
theorem archimedeanBoundaryChannel_convolutionAutocorrelation_eq_hermitianContribution_owner
    (f : ZetaAdmissibleFunction) :
    archimedeanBoundaryChannel (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaArchimedeanContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) := by
  exact archimedeanBoundaryChannel_unfold
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The archimedean explicit-formula channel on the convolution-autocorrelation probe is the
signed continuum archimedean form on real parts. -/
theorem zetaCompletedExplicitFormulaArchimedeanContribution_convolutionAutocorrelation_re_eq_signed_owner
    (f : ZetaAdmissibleFunction) :
    Complex.re
        (zetaCompletedExplicitFormulaArchimedeanContribution
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)) =
      Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f) := by
  have howner :
      zetaCompletedArchimedeanSignedQuadraticForm f =
        (Complex.re
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) : ℂ) :=
    zetaCompletedArchimedeanSignedQuadraticForm_eq_archimedeanContribution_re_owner
      f
  have hreal :
      Complex.re (zetaCompletedArchimedeanSignedQuadraticForm f) =
        Complex.re
          ((Complex.re
            (zetaCompletedExplicitFormulaArchimedeanContribution
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))) : ℂ) := by
    exact congrArg Complex.re howner
  have hofReal :
      Complex.re
          ((Complex.re
            (zetaCompletedExplicitFormulaArchimedeanContribution
              (ZetaAdmissibleFunction.convolutionAutocorrelation f))) : ℂ) =
        Complex.re
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)) := by
    exact
      Complex.ofReal_re
        (Complex.re
          (zetaCompletedExplicitFormulaArchimedeanContribution
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)))
  exact hreal.trans hofReal |>.symm

/-- The correction explicit-formula channel on the convolution-autocorrelation probe is the
correction convolution contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionContribution_convolutionAutocorrelation_eq_owner
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionContribution
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  rfl

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
      Finset.sum zetaCompletedExplicitFormulaPrimeSupport
          (fun ℓ : ℕ × ℕ => C ℓ + star (C ℓ)) =
        Finset.sum zetaCompletedExplicitFormulaPrimeSupport C +
          Finset.sum zetaCompletedExplicitFormulaPrimeSupport
            (fun ℓ : ℕ × ℕ => star (C ℓ)) := by
    exact Finset.sum_add_distrib
  have hstar :
      Finset.sum zetaCompletedExplicitFormulaPrimeSupport
          (fun ℓ : ℕ × ℕ => star (C ℓ)) =
        star (Finset.sum zetaCompletedExplicitFormulaPrimeSupport C) := by
    exact
      (star_sum zetaCompletedExplicitFormulaPrimeSupport C).symm
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

/-- Completed prime-power cone equation for the genuine `ZetaPrimePowerIndex` channel.

This is the B3 cone-facing version of the prime defect-square identity.  It deliberately
uses the completed prime-power two-face coefficient rather than the finite display support. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_add_completedPrimeDefectKernelPositiveForm_eq_completedDiagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  exact zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f

/-- The archimedean convolution contribution is the reconstructed Hermitian archimedean Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired f).trans
    (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_gram f)
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

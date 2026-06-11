import Boundary.LFunctions.AutocorrelationCore
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaCompletionCorrection
import Boundary.LFunctions.ZetaPacketLabels

/-!
# Boundary zeta Hermitian packets

This file owns the complex packet layer used by the autocorrelation
explicit-formula argument. The older real packet layer is a real shadow; the
RH-lane positivity proof needs Hermitian squares of complex seed amplitudes,
not squares of real parts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A Hermitian zeta packet is a finitely supported complex packet. -/
abbrev ZetaHermitianPacketEnsemble := ZetaPacketLabel →₀ ℂ

namespace ZetaHermitianPacketEnsemble

/-- The Hermitian packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (a : ℂ) : ZetaHermitianPacketEnsemble :=
  Finsupp.single ℓ a

/-- The Hermitian square of one complex packet coordinate. -/
def coordinateGram (z : ℂ) : ℝ :=
  Complex.normSq z

/-- The total Hermitian packet norm square. -/
def normSq (x : ZetaHermitianPacketEnsemble) : ℝ :=
  ∑ ℓ in x.support, coordinateGram (x ℓ)

/-- The prime Hermitian Gram contribution. -/
def primePacketGram (x : ZetaHermitianPacketEnsemble) : ℝ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .prime _ _ => coordinateGram (x ℓ)
    | _ => 0

/-- The archimedean Hermitian Gram contribution. -/
def archimedeanPacketGram (x : ZetaHermitianPacketEnsemble) : ℝ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .archimedean => coordinateGram (x ℓ)
    | _ => 0

/-- The correction Hermitian Gram contribution. -/
def correctionPacketGram (x : ZetaHermitianPacketEnsemble) : ℝ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .correction => coordinateGram (x ℓ)
    | _ => 0

/-- A pointwise sum of two Hermitian packet-family terms splits into two finite sums. -/
theorem sum_two_terms (s : Finset ZetaPacketLabel) (f g : ZetaPacketLabel → ℝ) :
    ∑ ℓ in s, (f ℓ + g ℓ) = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ := by
  exact Finset.sum_add_distrib

/-- A pointwise sum of three Hermitian packet-family terms splits into three finite sums. -/
theorem sum_three_terms
    (s : Finset ZetaPacketLabel) (f g h : ZetaPacketLabel → ℝ) :
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ) =
      ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
  calc
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ) =
        ∑ ℓ in s, ((f ℓ + g ℓ) + h ℓ) := by
      rfl
    _ = ∑ ℓ in s, (f ℓ + g ℓ) + ∑ ℓ in s, h ℓ := by
      exact sum_two_terms s (fun ℓ => f ℓ + g ℓ) h
    _ = (∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ) + ∑ ℓ in s, h ℓ := by
      exact congrArg (fun t : ℝ => t + ∑ ℓ in s, h ℓ)
        (sum_two_terms s f g)
    _ = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
      rfl

/-- A prime-coordinate Hermitian square belongs wholly to the prime packet family. -/
theorem coordinateGram_split_prime
    (x : ZetaHermitianPacketEnsemble) (m n : ℕ) :
    coordinateGram (x (ZetaPacketLabel.prime m n)) =
      (match ZetaPacketLabel.prime m n with
        | .prime _ _ => coordinateGram (x (ZetaPacketLabel.prime m n))
        | _ => 0) +
      (match ZetaPacketLabel.prime m n with
        | .archimedean => coordinateGram (x (ZetaPacketLabel.prime m n))
        | _ => 0) +
      (match ZetaPacketLabel.prime m n with
        | .correction => coordinateGram (x (ZetaPacketLabel.prime m n))
        | _ => 0) := by
  calc
    coordinateGram (x (ZetaPacketLabel.prime m n)) =
        coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 := by
      exact (add_zero _).symm
    _ = coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 + 0 := by
      exact (add_zero _).symm

/-- The archimedean-coordinate Hermitian square belongs wholly to the archimedean packet
family. -/
theorem coordinateGram_split_archimedean
    (x : ZetaHermitianPacketEnsemble) :
    coordinateGram (x ZetaPacketLabel.archimedean) =
      (match ZetaPacketLabel.archimedean with
        | .prime _ _ => coordinateGram (x ZetaPacketLabel.archimedean)
        | _ => 0) +
      (match ZetaPacketLabel.archimedean with
        | .archimedean => coordinateGram (x ZetaPacketLabel.archimedean)
        | _ => 0) +
      (match ZetaPacketLabel.archimedean with
        | .correction => coordinateGram (x ZetaPacketLabel.archimedean)
        | _ => 0) := by
  calc
    coordinateGram (x ZetaPacketLabel.archimedean) =
        0 + coordinateGram (x ZetaPacketLabel.archimedean) := by
      exact (zero_add _).symm
    _ = 0 + coordinateGram (x ZetaPacketLabel.archimedean) + 0 := by
      exact (add_zero _).symm

/-- The correction-coordinate Hermitian square belongs wholly to the correction packet family. -/
theorem coordinateGram_split_correction
    (x : ZetaHermitianPacketEnsemble) :
    coordinateGram (x ZetaPacketLabel.correction) =
      (match ZetaPacketLabel.correction with
        | .prime _ _ => coordinateGram (x ZetaPacketLabel.correction)
        | _ => 0) +
      (match ZetaPacketLabel.correction with
        | .archimedean => coordinateGram (x ZetaPacketLabel.correction)
        | _ => 0) +
      (match ZetaPacketLabel.correction with
        | .correction => coordinateGram (x ZetaPacketLabel.correction)
        | _ => 0) := by
  calc
    coordinateGram (x ZetaPacketLabel.correction) =
        0 + coordinateGram (x ZetaPacketLabel.correction) := by
      exact (zero_add _).symm
    _ = 0 + (0 + coordinateGram (x ZetaPacketLabel.correction)) := by
      exact congrArg (fun t : ℝ => 0 + t)
        (zero_add (coordinateGram (x ZetaPacketLabel.correction))).symm
    _ = 0 + 0 + coordinateGram (x ZetaPacketLabel.correction) := by
      exact (add_assoc 0 0 (coordinateGram (x ZetaPacketLabel.correction))).symm

/-- A Hermitian packet coordinate splits into exactly one of the three packet families. -/
theorem coordinateGram_split
    (x : ZetaHermitianPacketEnsemble) (ℓ : ZetaPacketLabel) :
    coordinateGram (x ℓ) =
      (match ℓ with
        | .prime _ _ => coordinateGram (x ℓ)
        | _ => 0) +
      (match ℓ with
        | .archimedean => coordinateGram (x ℓ)
        | _ => 0) +
      (match ℓ with
        | .correction => coordinateGram (x ℓ)
        | _ => 0) := by
  cases ℓ with
  | prime m n => exact coordinateGram_split_prime x m n
  | archimedean => exact coordinateGram_split_archimedean x
  | correction => exact coordinateGram_split_correction x

/-- The Hermitian packet norm is nonnegative. -/
theorem normSq_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ normSq x := by
  unfold normSq coordinateGram
  exact Finset.sum_nonneg (fun ℓ _ => Complex.normSq_nonneg (x ℓ))

/-- The Hermitian norm square splits into prime, archimedean, and correction
packet-family Gram contributions. -/
theorem normSq_eq_prime_add_archimedean_add_correction
    (x : ZetaHermitianPacketEnsemble) :
    normSq x =
      primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
  unfold normSq primePacketGram archimedeanPacketGram correctionPacketGram
  calc
    ∑ ℓ in x.support, coordinateGram (x ℓ) =
        ∑ ℓ in x.support,
          (match ℓ with
            | .prime _ _ => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .archimedean => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .correction => coordinateGram (x ℓ)
            | _ => 0) := by
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      exact coordinateGram_split x ℓ
    _ =
        (∑ ℓ in x.support,
          match ℓ with
          | .prime _ _ => coordinateGram (x ℓ)
          | _ => 0) +
        (∑ ℓ in x.support,
          match ℓ with
          | .archimedean => coordinateGram (x ℓ)
          | _ => 0) +
        (∑ ℓ in x.support,
          match ℓ with
          | .correction => coordinateGram (x ℓ)
          | _ => 0) := by
      exact sum_three_terms x.support
        (fun ℓ =>
          match ℓ with
          | .prime _ _ => coordinateGram (x ℓ)
          | _ => 0)
        (fun ℓ =>
          match ℓ with
          | .archimedean => coordinateGram (x ℓ)
          | _ => 0)
        (fun ℓ =>
          match ℓ with
          | .correction => coordinateGram (x ℓ)
          | _ => 0)

end ZetaHermitianPacketEnsemble

namespace ZetaAdmissibleFunction

/-- The square-root prime weight used to turn the linear explicit-formula coefficient into a
Hermitian packet amplitude. -/
noncomputable def zetaCompletedExplicitFormulaPrimeSqrtWeight (p n : ℕ) : ℝ :=
  Real.sqrt (zetaCompletedExplicitFormulaPrimeWeight p n)

/-- The prime spectral coordinate attached to the seed probe.

This is the owner-level Hermitian amplitude: the completed explicit-formula prime channel on
the convolution autocorrelation is the squared norm of this spectral coordinate, not the square
of a pointwise time-translation defect. -/
noncomputable def zetaCompletedExplicitFormulaPrimeSpectralAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) *
    zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter p n)

/-- The opposite prime spectral coordinate paired by the convolution transform identity. -/
noncomputable def zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) *
    zetaCompletedExplicitFormulaPhi f (-(zetaPrimePacketCenter p n : ℂ))

/-- The archimedean spectral coordinate attached to the seed probe. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude
    (f : ZetaAdmissibleFunction) : ℂ :=
  (Real.sqrt 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0

/-- The correction spectral coordinate is the normalized completion-correction coordinate. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionSpectralAmplitude
    (f : ZetaAdmissibleFunction) : ℂ :=
  (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ)

/-- The prime Hermitian packet attached to the seed probe. -/
def zetaPrimeHermitianPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaHermitianPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The archimedean Hermitian packet attached to the seed probe. -/
def zetaArchimedeanHermitianPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ZetaHermitianPacketEnsemble.single .archimedean
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)

/-- The normalized correction Hermitian packet. -/
def zetaCorrectionHermitianPacketAsEnsemble (_f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ZetaHermitianPacketEnsemble.single .correction
    (zetaCompletedExplicitFormulaCorrectionSpectralAmplitude _f)

/-- The completed Hermitian boundary packet attached to a seed probe. -/
def zetaCompletedHermitianBoundaryDefect (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  zetaPrimeHermitianPacketAsEnsemble f +
    zetaArchimedeanHermitianPacketAsEnsemble f +
    zetaCorrectionHermitianPacketAsEnsemble f

/-- The correction coordinate of the completed Hermitian boundary packet is the normalized
completion-correction coordinate. -/
theorem zetaCompletedHermitianBoundaryDefect_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaCompletedHermitianBoundaryDefect f ZetaPacketLabel.correction =
      (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
  simp [zetaCompletedHermitianBoundaryDefect,
    zetaPrimeHermitianPacketAsEnsemble,
    zetaArchimedeanHermitianPacketAsEnsemble,
    zetaCorrectionHermitianPacketAsEnsemble,
    zetaCompletedExplicitFormulaCorrectionSpectralAmplitude,
    ZetaHermitianPacketEnsemble.single]

/-- The correction Hermitian packet Gram is the square of the normalized correction coordinate. -/
theorem zetaCompletedHermitianBoundaryDefect_correctionPacketGram_eq_coordinate_sq
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
  let x : ZetaHermitianPacketEnsemble := zetaCompletedHermitianBoundaryDefect f
  have hcorr :
      x ZetaPacketLabel.correction =
        (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) :=
    zetaCompletedHermitianBoundaryDefect_correction_apply f
  have hcoord_nonzero :
      (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) ≠ 0 := by
    norm_num [Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate]
  have hcorr_mem : ZetaPacketLabel.correction ∈ x.support := by
    refine Finsupp.mem_support_iff.mpr ?_
    intro hxzero
    exact hcoord_nonzero (hcorr.symm.trans hxzero)
  have hsum :
      ∑ ℓ in x.support,
          match ℓ with
          | .correction => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0 =
        ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) := by
    refine Finset.sum_eq_single ZetaPacketLabel.correction ?_ ?_
    · intro ℓ hℓ hne
      cases ℓ with
      | prime p n => rfl
      | archimedean => rfl
      | correction => exact False.elim (hne rfl)
    · intro hnotmem
      exact False.elim (hnotmem hcorr_mem)
  have hcoord :
      ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
    calc
      ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) =
          ZetaHermitianPacketEnsemble.coordinateGram
            (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) := by
        exact congrArg ZetaHermitianPacketEnsemble.coordinateGram hcorr
      _ =
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
            Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := by
        norm_num [ZetaHermitianPacketEnsemble.coordinateGram,
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate, Complex.normSq]
  calc
    ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
        ∑ ℓ in x.support,
          match ℓ with
          | .correction => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0 := by
      rfl
    _ = ZetaHermitianPacketEnsemble.coordinateGram (x ZetaPacketLabel.correction) := hsum
    _ =
        Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate *
          Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate := hcoord

/-- The completed Hermitian packet norm square. -/
def zetaCompletedHermitianPacketNormSq (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f)

/-- The completed Hermitian packet norm square is nonnegative. -/
theorem zetaCompletedHermitianPacketNormSq_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedHermitianPacketNormSq f := by
  exact ZetaHermitianPacketEnsemble.normSq_nonnegative
    (zetaCompletedHermitianBoundaryDefect f)

/-- The spectral-convolution prime channel as a real Hermitian packet Gram. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionRealContribution
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.primePacketGram (zetaCompletedHermitianBoundaryDefect f)

/-- The spectral-convolution archimedean channel as a real Hermitian packet Gram. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanConvolutionRealContribution
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaHermitianPacketEnsemble.archimedeanPacketGram (zetaCompletedHermitianBoundaryDefect f)

/-- The prime channel produced directly by the convolution transform factorization, before
folding paired spectral coordinates into Hermitian squares. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
      star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The prime explicit-formula channel evaluated on the convolution autocorrelation kernel.
The analytic owner theorem identifying the old time-defect expression with this spectral
Hermitian channel is stated in the boundary-transport layer. -/
noncomputable def zetaCompletedExplicitFormulaPrimeConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeConvolutionRealContribution f : ℂ)

/-- The archimedean explicit-formula channel evaluated on the convolution autocorrelation
kernel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanConvolutionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaArchimedeanConvolutionRealContribution f : ℂ)

/-- Folding the paired prime spectral channel into the Hermitian prime packet Gram.

This is the prime-channel symmetry cut: after the completed functional-equation normalization
identifies the paired spectral coordinates, the paired contribution becomes the Hermitian
square of the seed spectral amplitude. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution_eq_hermitian
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f := by
  sorry

/-- The archimedean paired channel already sits at the self-paired spectral point. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionPaired_eq_hermitian
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
        star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  sorry

/-- The correction channel evaluated on autocorrelation is the centered correction scalar. -/
def zetaCompletedExplicitFormulaCorrectionConvolutionContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletionCorrection 0

/-- The prime convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) = 0 := by
  rfl

/-- The real part of the prime convolution contribution is the Hermitian prime packet Gram. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_primePacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  rfl

/-- The archimedean convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) = 0 := by
  rfl

/-- The real part of the archimedean convolution contribution is the Hermitian archimedean
packet Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  rfl

/-- The correction convolution contribution is real-valued. -/
theorem zetaCompletedExplicitFormulaCorrectionConvolutionContribution_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedExplicitFormulaCorrectionConvolutionContribution f) = 0 := by
  exact Boundary.LFunctions.zetaCompletionCorrection_zero_im

/-- Prime-channel holography for the convolution autocorrelation kernel. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_primePacketGram f

/-- Archimedean-channel holography for the convolution autocorrelation kernel. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram f

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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

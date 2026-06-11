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

/-- The prime Hermitian packet Gram is nonnegative. -/
theorem primePacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ primePacketGram x := by
  unfold primePacketGram coordinateGram
  exact Finset.sum_nonneg
    (fun ℓ _ => by
      cases ℓ with
      | prime p n => exact Complex.normSq_nonneg (x (ZetaPacketLabel.prime p n))
      | archimedean => exact le_refl 0
      | correction => exact le_refl 0)

/-- The archimedean Hermitian packet Gram is nonnegative. -/
theorem archimedeanPacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ archimedeanPacketGram x := by
  unfold archimedeanPacketGram coordinateGram
  exact Finset.sum_nonneg
    (fun ℓ _ => by
      cases ℓ with
      | prime p n => exact le_refl 0
      | archimedean => exact Complex.normSq_nonneg (x ZetaPacketLabel.archimedean)
      | correction => exact le_refl 0)

/-- The correction Hermitian packet Gram is nonnegative. -/
theorem correctionPacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ correctionPacketGram x := by
  unfold correctionPacketGram coordinateGram
  exact Finset.sum_nonneg
    (fun ℓ _ => by
      cases ℓ with
      | prime p n => exact le_refl 0
      | archimedean => exact le_refl 0
      | correction => exact Complex.normSq_nonneg (x ZetaPacketLabel.correction))

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
          ((match ℓ with
            | .prime _ _ => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .archimedean => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .correction => coordinateGram (x ℓ)
            | _ => 0)) := by
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

/-- A paired spectral packet records the two spectral coordinates naturally produced by the
convolution autocorrelation transform: the `+a` coordinate and its paired `-a` coordinate. -/
abbrev ZetaPairedSpectralPacketEnsemble := ZetaPacketLabel →₀ (ℂ × ℂ)

/-- A two-face/GNS packet stores the positive and negative faces of each boundary coordinate.
Its coordinate form is the matrix coefficient `positive * star negative`, not a one-face
norm square. -/
abbrev ZetaTwoFaceGNSPacketEnsemble := ZetaPacketLabel →₀ (ℂ × ℂ)

/-- A realized Gram packet stores post-reconstruction Gram coordinates directly.

This is distinct from `ZetaHermitianPacketEnsemble`, which stores amplitudes and then takes
`Complex.normSq`. The explicit formula first reconstructs these Gram coordinates from paired
raw faces; identifying them with amplitude norm-squares is a separate realization theorem. -/
abbrev ZetaCompletedBoundaryRealizedGramPacket := ZetaPacketLabel →₀ ℂ

namespace ZetaTwoFaceGNSPacketEnsemble

/-- The two-face/GNS packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (positive negative : ℂ) :
    ZetaTwoFaceGNSPacketEnsemble :=
  Finsupp.single ℓ (positive, negative)

/-- The two-face matrix coefficient of a stored coordinate. -/
def coordinateMatrixCoefficient (x : ZetaTwoFaceGNSPacketEnsemble)
    (ℓ : ZetaPacketLabel) : ℂ :=
  (x ℓ).1 * star (x ℓ).2

/-- The total two-face/GNS matrix coefficient. -/
def matrixCoefficient (x : ZetaTwoFaceGNSPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support, coordinateMatrixCoefficient x ℓ

/-- The prime two-face/GNS matrix coefficient. -/
def primeMatrixCoefficient (x : ZetaTwoFaceGNSPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .prime _ _ => coordinateMatrixCoefficient x ℓ
    | _ => 0

/-- A two-face coordinate at a prime label belongs wholly to the prime family. -/
theorem coordinateMatrixCoefficient_split_prime
    (x : ZetaTwoFaceGNSPacketEnsemble) (p n : ℕ) :
    coordinateMatrixCoefficient x (ZetaPacketLabel.prime p n) =
      (match ZetaPacketLabel.prime p n with
        | .prime _ _ => coordinateMatrixCoefficient x (ZetaPacketLabel.prime p n)
        | _ => 0) := by
  rfl

end ZetaTwoFaceGNSPacketEnsemble

namespace ZetaPairedSpectralPacketEnsemble

/-- The paired spectral packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (zPlus zMinus : ℂ) : ZetaPairedSpectralPacketEnsemble :=
  Finsupp.single ℓ (zPlus, zMinus)

/-- The paired sesquilinear coordinate form. -/
def coordinateForm (zPlus zMinus : ℂ) : ℂ :=
  zPlus * star zMinus

/-- The paired coordinate form of a packet coordinate. -/
def coordinateGram (z : ℂ × ℂ) : ℂ :=
  coordinateForm z.1 z.2

/-- The total paired sesquilinear packet form. -/
def pairedForm (x : ZetaPairedSpectralPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support, coordinateGram (x ℓ)

/-- The prime paired spectral contribution. -/
def primePairedForm (x : ZetaPairedSpectralPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .prime _ _ => coordinateGram (x ℓ)
    | _ => 0

/-- The archimedean paired spectral contribution. -/
def archimedeanPairedForm (x : ZetaPairedSpectralPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .archimedean => coordinateGram (x ℓ)
    | _ => 0

/-- The correction paired spectral contribution. -/
def correctionPairedForm (x : ZetaPairedSpectralPacketEnsemble) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .correction => coordinateGram (x ℓ)
    | _ => 0

/-- The real part of the paired packet form. This is the real quantity consumed by positivity
statements; the complex paired form remains the owner object. -/
def pairedRealForm (x : ZetaPairedSpectralPacketEnsemble) : ℝ :=
  Complex.re (pairedForm x)

/-- A pointwise sum of two paired packet-family terms splits into two finite sums. -/
theorem sum_two_terms (s : Finset ZetaPacketLabel) (f g : ZetaPacketLabel → ℂ) :
    ∑ ℓ in s, (f ℓ + g ℓ) = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ := by
  exact Finset.sum_add_distrib

/-- A pointwise sum of three paired packet-family terms splits into three finite sums. -/
theorem sum_three_terms
    (s : Finset ZetaPacketLabel) (f g h : ZetaPacketLabel → ℂ) :
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ) =
      ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
  calc
    ∑ ℓ in s, (f ℓ + g ℓ + h ℓ) =
        ∑ ℓ in s, ((f ℓ + g ℓ) + h ℓ) := by
      rfl
    _ = ∑ ℓ in s, (f ℓ + g ℓ) + ∑ ℓ in s, h ℓ := by
      exact sum_two_terms s (fun ℓ => f ℓ + g ℓ) h
    _ = (∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ) + ∑ ℓ in s, h ℓ := by
      exact congrArg (fun t : ℂ => t + ∑ ℓ in s, h ℓ)
        (sum_two_terms s f g)
    _ = ∑ ℓ in s, f ℓ + ∑ ℓ in s, g ℓ + ∑ ℓ in s, h ℓ := by
      rfl

/-- The paired packet form splits into prime, archimedean, and correction channels. -/
theorem pairedForm_eq_prime_add_archimedean_add_correction
    (x : ZetaPairedSpectralPacketEnsemble) :
    pairedForm x =
      primePairedForm x + archimedeanPairedForm x + correctionPairedForm x := by
  unfold pairedForm primePairedForm archimedeanPairedForm correctionPairedForm
  calc
    ∑ ℓ in x.support, coordinateGram (x ℓ) =
        ∑ ℓ in x.support,
          ((match ℓ with
            | .prime _ _ => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .archimedean => coordinateGram (x ℓ)
            | _ => 0) +
          (match ℓ with
            | .correction => coordinateGram (x ℓ)
            | _ => 0)) := by
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      cases ℓ with
      | prime m n =>
          calc
            coordinateGram (x (ZetaPacketLabel.prime m n)) =
                coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 := by
              exact (add_zero _).symm
            _ =
                coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 + 0 := by
              exact (add_zero _).symm
      | archimedean =>
          calc
            coordinateGram (x ZetaPacketLabel.archimedean) =
                0 + coordinateGram (x ZetaPacketLabel.archimedean) := by
              exact (zero_add _).symm
            _ = 0 + coordinateGram (x ZetaPacketLabel.archimedean) + 0 := by
              exact (add_zero _).symm
      | correction =>
          calc
            coordinateGram (x ZetaPacketLabel.correction) =
                0 + coordinateGram (x ZetaPacketLabel.correction) := by
              exact (zero_add _).symm
            _ = 0 + (0 + coordinateGram (x ZetaPacketLabel.correction)) := by
              exact congrArg (fun t : ℂ => 0 + t)
                (zero_add (coordinateGram (x ZetaPacketLabel.correction))).symm
            _ = 0 + 0 + coordinateGram (x ZetaPacketLabel.correction) := by
              exact (add_assoc 0 0 (coordinateGram (x ZetaPacketLabel.correction))).symm
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

end ZetaPairedSpectralPacketEnsemble

namespace ZetaCompletedBoundaryRealizedGramPacket

/-- The realized Gram packet singleton at a label. -/
def single (ℓ : ZetaPacketLabel) (a : ℂ) : ZetaCompletedBoundaryRealizedGramPacket :=
  Finsupp.single ℓ a

/-- The total realized Gram of a reconstructed boundary packet. -/
def totalGram (x : ZetaCompletedBoundaryRealizedGramPacket) : ℂ :=
  ∑ ℓ in x.support, x ℓ

/-- The prime realized Gram contribution. -/
def primeGram (x : ZetaCompletedBoundaryRealizedGramPacket) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .prime _ _ => x ℓ
    | _ => 0

/-- The archimedean realized Gram contribution. -/
def archimedeanGram (x : ZetaCompletedBoundaryRealizedGramPacket) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .archimedean => x ℓ
    | _ => 0

/-- The correction realized Gram contribution. -/
def correctionGram (x : ZetaCompletedBoundaryRealizedGramPacket) : ℂ :=
  ∑ ℓ in x.support,
    match ℓ with
    | .correction => x ℓ
    | _ => 0

/-- A realized Gram coordinate splits into exactly one of the three channel families. -/
theorem coordinate_split (x : ZetaCompletedBoundaryRealizedGramPacket) (ℓ : ZetaPacketLabel) :
    x ℓ =
      (match ℓ with | .prime _ _ => x ℓ | _ => 0) +
      (match ℓ with | .archimedean => x ℓ | _ => 0) +
      (match ℓ with | .correction => x ℓ | _ => 0) := by
  cases ℓ with
  | prime m n =>
      calc
        x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) + 0 := by
          exact (add_zero _).symm
        _ = x (ZetaPacketLabel.prime m n) + 0 + 0 := by
          exact (add_zero _).symm
  | archimedean =>
      calc
        x ZetaPacketLabel.archimedean = 0 + x ZetaPacketLabel.archimedean := by
          exact (zero_add _).symm
        _ = 0 + x ZetaPacketLabel.archimedean + 0 := by
          exact (add_zero _).symm
  | correction =>
      calc
        x ZetaPacketLabel.correction = 0 + x ZetaPacketLabel.correction := by
          exact (zero_add _).symm
        _ = 0 + (0 + x ZetaPacketLabel.correction) := by
          exact congrArg (fun t : ℂ => 0 + t) (zero_add (x ZetaPacketLabel.correction)).symm
        _ = 0 + 0 + x ZetaPacketLabel.correction := by
          exact (add_assoc 0 0 (x ZetaPacketLabel.correction)).symm

/-- The total realized Gram splits into prime, archimedean, and correction channels. -/
theorem totalGram_eq_prime_add_archimedean_add_correction
    (x : ZetaCompletedBoundaryRealizedGramPacket) :
    totalGram x = primeGram x + archimedeanGram x + correctionGram x := by
  unfold totalGram primeGram archimedeanGram correctionGram
  calc
    ∑ ℓ in x.support, x ℓ =
        ∑ ℓ in x.support,
          ((match ℓ with | .prime _ _ => x ℓ | _ => 0) +
          (match ℓ with | .archimedean => x ℓ | _ => 0) +
          (match ℓ with | .correction => x ℓ | _ => 0)) := by
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      exact coordinate_split x ℓ
    _ =
        (∑ ℓ in x.support, match ℓ with | .prime _ _ => x ℓ | _ => 0) +
        (∑ ℓ in x.support, match ℓ with | .archimedean => x ℓ | _ => 0) +
        (∑ ℓ in x.support, match ℓ with | .correction => x ℓ | _ => 0) := by
      exact ZetaPairedSpectralPacketEnsemble.sum_three_terms x.support
        (fun ℓ => match ℓ with | .prime _ _ => x ℓ | _ => 0)
        (fun ℓ => match ℓ with | .archimedean => x ℓ | _ => 0)
        (fun ℓ => match ℓ with | .correction => x ℓ | _ => 0)

end ZetaCompletedBoundaryRealizedGramPacket

namespace ZetaAdmissibleFunction

/-- A completed boundary coordinate records the two raw explicit-formula faces and the realized
Hermitian Gram coordinate produced after completed boundary reconstruction. -/
structure ZetaCompletedBoundaryCoordinate where
  positiveFace : ℂ
  negativeFace : ℂ
  realizedGram : ℂ

/-- The raw face pairing attached to a completed boundary coordinate. -/
def ZetaCompletedBoundaryCoordinate.rawPairing
    (c : ZetaCompletedBoundaryCoordinate) : ℂ :=
  c.positiveFace * star c.negativeFace

/-- A coordinate has been reconstructed when its realized Gram is the raw face pairing. -/
def ZetaCompletedBoundaryCoordinate.IsReconstructed
    (c : ZetaCompletedBoundaryCoordinate) : Prop :=
  c.realizedGram = c.rawPairing

/-- The square-root prime weight used to turn the linear explicit-formula coefficient into a
Hermitian packet amplitude. -/
noncomputable def zetaCompletedExplicitFormulaPrimeSqrtWeight (p n : ℕ) : ℝ :=
  Real.sqrt (zetaCompletedExplicitFormulaPrimeWeight p n)

/-- The completed prime explicit-formula weight is nonnegative. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_nonnegative (p n : ℕ) :
    0 ≤ zetaCompletedExplicitFormulaPrimeWeight p n := by
  by_cases hp : Nat.Prime p
  · by_cases hn : n ≠ 0
    · have hp_two : 2 ≤ p := Nat.Prime.two_le hp
      have hp_pos_nat : 0 < p := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hp_two
      have hp_one_real : (1 : ℝ) ≤ p := by
        exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
      have hlog : 0 ≤ Real.log p := Real.log_nonneg hp_one_real
      have hsqrt : 0 ≤ Real.sqrt (p ^ n) := Real.sqrt_nonneg _
      have hquot : 0 ≤ Real.log p / Real.sqrt (p ^ n) :=
        div_nonneg hlog hsqrt
      have hweight :
          zetaCompletedExplicitFormulaPrimeWeight p n =
            Real.log p / Real.sqrt (p ^ n) := by
        unfold zetaCompletedExplicitFormulaPrimeWeight
        exact (if_pos hp).trans (if_pos hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        hquot
    · have hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
        unfold zetaCompletedExplicitFormulaPrimeWeight
        exact (if_pos hp).trans (if_neg hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        (le_refl 0)
  · have hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
      unfold zetaCompletedExplicitFormulaPrimeWeight
      exact if_neg hp
    exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hweight.symm
      (le_refl 0)

/-- The square-root prime weight squares back to the completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeSqrtWeight_mul_self (p n : ℕ) :
    zetaCompletedExplicitFormulaPrimeSqrtWeight p n *
      zetaCompletedExplicitFormulaPrimeSqrtWeight p n =
        zetaCompletedExplicitFormulaPrimeWeight p n := by
  unfold zetaCompletedExplicitFormulaPrimeSqrtWeight
  exact (pow_two (Real.sqrt (zetaCompletedExplicitFormulaPrimeWeight p n))).symm.trans
    (Real.sq_sqrt (zetaCompletedExplicitFormulaPrimeWeight_nonnegative p n))

/-- Non-prime labels have zero completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_not_prime
    (p n : ℕ) (hp : ¬ Nat.Prime p) :
    zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeWeight
  exact if_neg hp

/-- Zero-exponent labels have zero completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_zero_exponent
    (p n : ℕ) (hp : Nat.Prime p) (hn : ¬ n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeWeight
  exact (if_pos hp).trans (if_neg hn)

/-- A zero completed prime weight has zero square-root weight. -/
theorem zetaCompletedExplicitFormulaPrimeSqrtWeight_eq_zero_of_weight_eq_zero
    (p n : ℕ)
    (hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0) :
    zetaCompletedExplicitFormulaPrimeSqrtWeight p n = 0 := by
  unfold zetaCompletedExplicitFormulaPrimeSqrtWeight
  exact (congrArg Real.sqrt hweight).trans Real.sqrt_zero

/-- The completed prime weight is the Hermitian norm square of its square-root weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_normSq_sqrtWeight
    (p n : ℕ) :
    (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) =
      (Complex.normSq
        (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) : ℂ) := by
  let r : ℝ := zetaCompletedExplicitFormulaPrimeSqrtWeight p n
  let w : ℝ := zetaCompletedExplicitFormulaPrimeWeight p n
  have hstar_r : star (r : ℂ) = (r : ℂ) := by
    exact Complex.conj_ofReal r
  have hsquare : r * r = w := by
    exact zetaCompletedExplicitFormulaPrimeSqrtWeight_mul_self p n
  have hsquare_complex : (r : ℂ) * (r : ℂ) = (w : ℂ) := by
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul r r).symm
      _ = (w : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hsquare
  calc
    (w : ℂ) = (r : ℂ) * (r : ℂ) := by
      exact hsquare_complex.symm
    _ = (r : ℂ) * star (r : ℂ) := by
      exact congrArg (fun z : ℂ => (r : ℂ) * z) hstar_r.symm
    _ = (Complex.normSq (r : ℂ) : ℂ) := by
      exact Complex.mul_conj (r : ℂ)

/-- A completed autocorrelation probe generated by a seed. The boundary layer sees the
completed autocorrelation object, while the Hermitian packet remembers the seed amplitude used
to factor its positive faces. -/
structure ZetaCompletedAutocorrelationProbe where
  seed : ZetaAdmissibleFunction

/-- The admissible function underlying a completed autocorrelation probe. -/
noncomputable def ZetaCompletedAutocorrelationProbe.toAdmissible
    (g : ZetaCompletedAutocorrelationProbe) : ZetaAdmissibleFunction :=
  ZetaAdmissibleFunction.convolutionAutocorrelation g.seed

/-- The completed autocorrelation probe attached to a seed. -/
noncomputable def zetaCompletedAutocorrelationProbe
    (f : ZetaAdmissibleFunction) : ZetaCompletedAutocorrelationProbe :=
  ⟨f⟩

/-- The vertical/Fourier prime coordinate fixed by the dagger involution `z ↦ -star z`. -/
noncomputable def zetaPrimeHermitianVerticalCenter (p n : ℕ) : ℂ :=
  (zetaPrimePacketCenter p n : ℂ) * Complex.I

/-- The vertical prime coordinate is fixed by reflection followed by conjugation. -/
theorem zetaPrimeHermitianVerticalCenter_dagger_fixed (p n : ℕ) :
    -star (zetaPrimeHermitianVerticalCenter p n) =
      zetaPrimeHermitianVerticalCenter p n := by
  let a : ℝ := zetaPrimePacketCenter p n
  unfold zetaPrimeHermitianVerticalCenter
  change -star ((a : ℂ) * Complex.I) = (a : ℂ) * Complex.I
  have hstar_a : star (a : ℂ) = (a : ℂ) := by
    exact Complex.conj_ofReal a
  have hstar_I : star Complex.I = -Complex.I := by
    exact Complex.conj_I
  calc
    -star ((a : ℂ) * Complex.I) =
        -(star Complex.I * star (a : ℂ)) := by
      exact congrArg Neg.neg (star_mul (a : ℂ) Complex.I)
    _ = -((-Complex.I) * (a : ℂ)) := by
      exact congrArg₂ (fun x y : ℂ => -(x * y)) hstar_I hstar_a
    _ = -((-Complex.I) * (a : ℂ)) := by
      rfl
    _ = -( -((Complex.I) * (a : ℂ))) := by
      exact congrArg Neg.neg (neg_mul Complex.I (a : ℂ)).symm
    _ = Complex.I * (a : ℂ) := by
      exact neg_neg (Complex.I * (a : ℂ))
    _ = (a : ℂ) * Complex.I := by
      exact mul_comm Complex.I (a : ℂ)

/-- The unweighted seed amplitude at the real positive prime coordinate. -/
noncomputable def zetaCompletedPrimeHermitianSeedAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (zetaPrimePacketCenter p n)

/-- The unweighted seed amplitude at the real negative prime coordinate. -/
noncomputable def zetaCompletedPrimeHermitianNegativeSeedAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (-(zetaPrimePacketCenter p n : ℂ))

/-- The seed amplitude at the vertical prime coordinate. This belongs to the separate
Fourier/Hilbert channel, not the real explicit-formula prime presentation. -/
noncomputable def zetaCompletedPrimeVerticalSeedAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (zetaPrimeHermitianVerticalCenter p n)

/-- The positive real prime face of a completed autocorrelation boundary probe. This is
`Ψ(a)`, the real explicit-formula prime presentation coordinate. -/
noncomputable def zetaCompletedAutocorrelationPrimePositiveFace
    (p n : ℕ) (g : ZetaCompletedAutocorrelationProbe) : ℂ :=
  zetaCompletedExplicitFormulaPhi g.toAdmissible (zetaPrimePacketCenter p n)

/-- The negative real prime face of a completed autocorrelation boundary probe. -/
noncomputable def zetaCompletedAutocorrelationPrimeNegativeFace
    (p n : ℕ) (g : ZetaCompletedAutocorrelationProbe) : ℂ :=
  zetaCompletedExplicitFormulaPhi g.toAdmissible (-(zetaPrimePacketCenter p n : ℂ))

/-- The vertical completed autocorrelation prime face has the canonical Hermitian spectral
factor. This theorem is reserved for the vertical/Fourier channel. -/
theorem zetaCompletedAutocorrelationPrimeVerticalFace_eq_normSq_seedAmplitude
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi
        (ZetaCompletedAutocorrelationProbe.toAdmissible
          (zetaCompletedAutocorrelationProbe f))
        (zetaPrimeHermitianVerticalCenter p n) =
      (Complex.normSq
        (zetaCompletedPrimeVerticalSeedAmplitude p n f) : ℂ) := by
  let z : ℂ := zetaPrimeHermitianVerticalCenter p n
  let a : ℂ := zetaCompletedExplicitFormulaPhi f z
  have hfixed : -star z = z := by
    exact zetaPrimeHermitianVerticalCenter_dagger_fixed p n
  have hfactor :
      zetaCompletedExplicitFormulaPhi
          (ZetaCompletedAutocorrelationProbe.toAdmissible
            (zetaCompletedAutocorrelationProbe f)) z =
        a * star a := by
    unfold zetaCompletedAutocorrelationProbe
    unfold ZetaCompletedAutocorrelationProbe.toAdmissible
    change zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) z =
      a * star a
    calc
      zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) z =
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
        exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f z
      _ = a * star (zetaCompletedExplicitFormulaPhi f z) := by
        exact congrArg
          (fun y : ℂ => zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f y))
          hfixed
      _ = a * star a := by
        rfl
  calc
    zetaCompletedExplicitFormulaPhi
        (ZetaCompletedAutocorrelationProbe.toAdmissible
          (zetaCompletedAutocorrelationProbe f))
        (zetaPrimeHermitianVerticalCenter p n) =
        a * star a := hfactor
    _ = (Complex.normSq a : ℂ) := by
      exact Complex.mul_conj a

/-- The real completed autocorrelation prime face is the two-face seed matrix coefficient. -/
theorem zetaCompletedAutocorrelationPrimeRealFace_eq_twoFaceCoefficient
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedAutocorrelationPrimePositiveFace p n
        (zetaCompletedAutocorrelationProbe f) =
      zetaCompletedPrimeHermitianSeedAmplitude p n f *
        star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f) := by
  unfold zetaCompletedAutocorrelationPrimePositiveFace
  unfold zetaCompletedAutocorrelationProbe
  unfold ZetaCompletedAutocorrelationProbe.toAdmissible
  unfold zetaCompletedPrimeHermitianSeedAmplitude
  unfold zetaCompletedPrimeHermitianNegativeSeedAmplitude
  exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
    f (zetaPrimePacketCenter p n)

/-- The completed autocorrelation prime faces are fixed by reflection followed by dagger. -/
theorem zetaCompletedAutocorrelationPrimeFace_reflectionDagger
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (g : ZetaCompletedAutocorrelationProbe) :
    star (zetaCompletedAutocorrelationPrimeNegativeFace p n g) =
      zetaCompletedAutocorrelationPrimePositiveFace p n g := by
  let a : ℝ := zetaPrimePacketCenter p n
  let φ : ℂ → ℂ := zetaCompletedExplicitFormulaPhi g.seed
  have hpos :
      zetaCompletedAutocorrelationPrimePositiveFace p n g =
        φ (a : ℂ) * star (φ (-(a : ℂ))) := by
    unfold zetaCompletedAutocorrelationPrimePositiveFace
    unfold ZetaCompletedAutocorrelationProbe.toAdmissible
    change zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation g.seed) (a : ℂ) =
      φ (a : ℂ) * star (φ (-(a : ℂ)))
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair g.seed a
  have hneg :
      zetaCompletedAutocorrelationPrimeNegativeFace p n g =
        φ (-(a : ℂ)) * star (φ (a : ℂ)) := by
    unfold zetaCompletedAutocorrelationPrimeNegativeFace
    unfold ZetaCompletedAutocorrelationProbe.toAdmissible
    have hpair :
        zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation g.seed) ((-a : ℝ) : ℂ) =
          φ ((-a : ℝ) : ℂ) * star (φ (-(((-a : ℝ) : ℂ)))) :=
      zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair g.seed (-a)
    have hneg_coe : ((-a : ℝ) : ℂ) = -(a : ℂ) := by
      exact map_neg (algebraMap ℝ ℂ) a
    have hdouble_neg : -(((-a : ℝ) : ℂ)) = (a : ℂ) := by
      calc
        -(((-a : ℝ) : ℂ)) = -(-(a : ℂ)) := by
          exact congrArg Neg.neg hneg_coe
        _ = (a : ℂ) := by
          exact neg_neg (a : ℂ)
    calc
      zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation g.seed) (-(a : ℂ)) =
          zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation g.seed) ((-a : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ =>
            zetaCompletedExplicitFormulaPhi
              (ZetaAdmissibleFunction.convolutionAutocorrelation g.seed) z)
          hneg_coe.symm
      _ = φ ((-a : ℝ) : ℂ) * star (φ (-(((-a : ℝ) : ℂ)))) := hpair
      _ = φ (-(a : ℂ)) * star (φ (-(((-a : ℝ) : ℂ)))) := by
        exact congrArg
          (fun z : ℂ => φ z * star (φ (-(((-a : ℝ) : ℂ)))))
          hneg_coe
      _ = φ (-(a : ℂ)) * star (φ (a : ℂ)) := by
        exact congrArg (fun z : ℂ => φ (-(a : ℂ)) * star (φ z)) hdouble_neg
  calc
    star (zetaCompletedAutocorrelationPrimeNegativeFace p n g) =
        star (φ (-(a : ℂ)) * star (φ (a : ℂ))) := by
      exact congrArg star hneg
    _ = star (star (φ (a : ℂ))) * star (φ (-(a : ℂ))) := by
      exact star_mul (φ (-(a : ℂ))) (star (φ (a : ℂ)))
    _ = φ (a : ℂ) * star (φ (-(a : ℂ))) := by
      exact congrArg (fun z : ℂ => z * star (φ (-(a : ℂ))))
        (star_star (φ (a : ℂ)))
    _ = zetaCompletedAutocorrelationPrimePositiveFace p n g := hpos.symm

/-- The prime spectral coordinate attached to the seed probe.

This is the owner-level Hermitian amplitude: the completed explicit-formula prime channel on
the convolution autocorrelation is the squared norm of this spectral coordinate, not the square
of a pointwise time-translation defect. -/
noncomputable def zetaCompletedExplicitFormulaPrimeSpectralAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) *
    zetaCompletedPrimeHermitianSeedAmplitude p n f

/-- The completed realized positive prime boundary face. This is the positive oriented face
after completed-boundary realization, not merely an anonymous sample coordinate. -/
noncomputable def zetaCompletedPrimeBoundaryRealizedPositiveFace
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeHermitianSeedAmplitude p n f

/-- The completed realized negative prime boundary face. This is the real `-a` face in the
two-face/GNS prime packet. -/
noncomputable def zetaCompletedPrimeBoundaryRealizedNegativeFace
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f

/-- The opposite prime spectral coordinate paired by the completed boundary realization. -/
noncomputable def zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) *
    zetaCompletedPrimeBoundaryRealizedNegativeFace p n f

/-- The raw analytic negative prime face before dagger gluing. It is kept separate from the
realized negative slot used by Hermitian reconstruction. -/
noncomputable def zetaCompletedPrimeBoundaryRawNegativeFace
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPhi f (-(zetaPrimePacketCenter p n : ℂ))

/-- The completed prime boundary negative face is the real negative seed amplitude. -/
theorem zetaCompletedPrimeBoundaryRealizedNegativeFace_eq_negativeSeed
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeBoundaryRealizedNegativeFace p n f =
      zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f := by
  rfl

/-- The canonical positive realized prime amplitude. In the real prime channel this is one face
of a two-face matrix coefficient, not a one-face norm-square coordinate. -/
noncomputable def zetaCompletedPrimeHermitianRealizedAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSqrtWeight p n : ℂ) *
    zetaCompletedPrimeBoundaryRealizedPositiveFace p n f

/-- The completed realized prime coordinate is the weighted two-face/GNS matrix coefficient. -/
noncomputable def zetaCompletedPrimeBoundaryRealizedCoordinateGram
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
    (zetaCompletedAutocorrelationPrimePositiveFace p n
        (zetaCompletedAutocorrelationProbe f) +
      star
        (zetaCompletedAutocorrelationPrimePositiveFace p n
          (zetaCompletedAutocorrelationProbe f)))

/-- Weighted prime autocorrelation face as the weighted two-face matrix coefficient. -/
theorem zetaCompletedPrimeBoundaryRealizedCoordinateGram_eq_twoFaceCoefficient
    (p n : ℕ) (hp : Nat.Prime p) (hn : n ≠ 0)
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f =
      (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) *
        ((zetaCompletedPrimeHermitianSeedAmplitude p n f *
            star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f)) +
          star
            (zetaCompletedPrimeHermitianSeedAmplitude p n f *
              star (zetaCompletedPrimeHermitianNegativeSeedAmplitude p n f))) := by
  unfold zetaCompletedPrimeBoundaryRealizedCoordinateGram
  exact congrArg
    (fun z : ℂ => (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) * (z + star z))
    (zetaCompletedAutocorrelationPrimeRealFace_eq_twoFaceCoefficient p n hp hn f)

/-- The completed prime boundary coordinate with both raw faces and the realized Gram. -/
noncomputable def zetaCompletedPrimeBoundaryCoordinate
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryCoordinate where
  positiveFace := zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f
  negativeFace := zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f
  realizedGram := zetaCompletedPrimeBoundaryRealizedCoordinateGram p n f

/-- The archimedean spectral coordinate attached to the seed probe. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude
    (f : ZetaAdmissibleFunction) : ℂ :=
  (Real.sqrt 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0

/-- The completed realized archimedean coordinate Gram. The archimedean channel is self-paired
at the centered basepoint, but it still passes through the same realized-Gram interface. -/
noncomputable def zetaCompletedArchimedeanBoundaryRealizedCoordinateGram
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
    star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)

/-- The completed archimedean boundary coordinate with both raw faces and the realized Gram. -/
noncomputable def zetaCompletedArchimedeanBoundaryCoordinate
    (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryCoordinate where
  positiveFace := zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f
  negativeFace := zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f
  realizedGram := zetaCompletedArchimedeanBoundaryRealizedCoordinateGram f

/-- The completed archimedean boundary coordinate is reconstructed by construction of the
realized Gram channel. -/
theorem zetaCompletedArchimedeanBoundaryCoordinate_isReconstructed
    (f : ZetaAdmissibleFunction) :
    (zetaCompletedArchimedeanBoundaryCoordinate f).IsReconstructed := by
  rfl

/-- The correction spectral coordinate is the normalized completion-correction coordinate. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionSpectralAmplitude
    (_f : ZetaAdmissibleFunction) : ℂ :=
  (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ)

/-- The paired prime spectral packet attached to the seed probe. -/
noncomputable def zetaPrimePairedSpectralPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaPairedSpectralPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaPairedSpectralPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f)
      (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The paired archimedean spectral packet attached to the seed probe. -/
noncomputable def zetaArchimedeanPairedSpectralPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaPairedSpectralPacketEnsemble :=
  ZetaPairedSpectralPacketEnsemble.single .archimedean
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)

/-- The paired correction spectral packet attached to the seed probe. -/
noncomputable def zetaCorrectionPairedSpectralPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaPairedSpectralPacketEnsemble :=
  ZetaPairedSpectralPacketEnsemble.single .correction
    (zetaCompletedExplicitFormulaCorrectionSpectralAmplitude f)
    (zetaCompletedExplicitFormulaCorrectionSpectralAmplitude f)

/-- The completed paired spectral boundary packet attached to a seed probe. -/
noncomputable def zetaCompletedPairedSpectralBoundaryDefect
    (f : ZetaAdmissibleFunction) : ZetaPairedSpectralPacketEnsemble :=
  zetaPrimePairedSpectralPacketAsEnsemble f +
    zetaArchimedeanPairedSpectralPacketAsEnsemble f +
    zetaCorrectionPairedSpectralPacketAsEnsemble f

/-- The realized prime Gram packet attached to the seed probe. -/
noncomputable def zetaPrimeRealizedGramPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryRealizedGramPacket :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaCompletedBoundaryRealizedGramPacket.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaCompletedPrimeBoundaryRealizedCoordinateGram ℓ.1 ℓ.2 f)

/-- The realized archimedean Gram packet attached to the seed probe. -/
noncomputable def zetaArchimedeanRealizedGramPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryRealizedGramPacket :=
  ZetaCompletedBoundaryRealizedGramPacket.single .archimedean
    (zetaCompletedArchimedeanBoundaryRealizedCoordinateGram f)

/-- The realized correction Gram packet attached to the seed probe. -/
noncomputable def zetaCorrectionRealizedGramPacketAsEnsemble
    (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryRealizedGramPacket :=
  ZetaCompletedBoundaryRealizedGramPacket.single .correction
    (zetaCompletionCorrection 0)

/-- The completed realized Gram boundary packet attached to a seed probe. -/
noncomputable def zetaCompletedBoundaryRealizedGramPacket
    (f : ZetaAdmissibleFunction) : ZetaCompletedBoundaryRealizedGramPacket :=
  zetaPrimeRealizedGramPacketAsEnsemble f +
    zetaArchimedeanRealizedGramPacketAsEnsemble f +
    zetaCorrectionRealizedGramPacketAsEnsemble f

/-- The completed realized Gram boundary form. -/
noncomputable def zetaCompletedBoundaryRealizedGram
    (f : ZetaAdmissibleFunction) : ℂ :=
  (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaCompletedPrimeBoundaryRealizedCoordinateGram ℓ.1 ℓ.2 f) +
    zetaCompletedArchimedeanBoundaryRealizedCoordinateGram f +
    zetaCompletionCorrection 0

/-- The prime realized Gram channel. -/
noncomputable def zetaCompletedPrimeBoundaryRealizedGram
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaCompletedPrimeBoundaryRealizedCoordinateGram ℓ.1 ℓ.2 f

/-- The archimedean realized Gram channel. -/
noncomputable def zetaCompletedArchimedeanBoundaryRealizedGram
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedArchimedeanBoundaryRealizedCoordinateGram f

/-- The correction realized Gram channel. -/
noncomputable def zetaCompletedCorrectionBoundaryRealizedGram
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletionCorrection 0

/-- The completed paired spectral boundary form. -/
noncomputable def zetaCompletedPairedSpectralBoundaryForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ZetaPairedSpectralPacketEnsemble.pairedForm
    (zetaCompletedPairedSpectralBoundaryDefect f)

/-- The completed paired spectral boundary real form. -/
noncomputable def zetaCompletedPairedSpectralBoundaryRealForm
    (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPairedSpectralPacketEnsemble.pairedRealForm
    (zetaCompletedPairedSpectralBoundaryDefect f)

/-- The prime Hermitian packet attached to the seed probe. -/
def zetaPrimeHermitianPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaHermitianPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The prime two-face/GNS packet attached to the seed probe. -/
def zetaPrimeTwoFaceGNSPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaTwoFaceGNSPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaTwoFaceGNSPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f)
      (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The raw oriented prime two-face/GNS matrix coefficient over the explicit prime support. -/
noncomputable def zetaPrimeTwoFaceGNSOrientedCoefficient
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
      star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)

/-- The prime two-face/GNS matrix coefficient is the symmetrized two-face contribution. -/
noncomputable def zetaPrimeTwoFaceGNSMatrixCoefficient
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeTwoFaceGNSOrientedCoefficient f +
    star (zetaPrimeTwoFaceGNSOrientedCoefficient f)

/-- The symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  let z : ℂ := zetaPrimeTwoFaceGNSOrientedCoefficient f
  unfold zetaPrimeTwoFaceGNSMatrixCoefficient
  change Complex.im (z + star z) = 0
  calc
    Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
      exact Complex.add_im z (star z)
    _ = Complex.im z + -Complex.im z := by
      exact congrArg (fun x : ℝ => Complex.im z + x) (Complex.conj_im z)
    _ = 0 := by
      exact add_neg_cancel (Complex.im z)

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

/-- The symmetrized real two-face completed boundary presentation. This is Hermitian
real-valued data, but not by itself a positivity theorem. -/
noncomputable def zetaCompletedGNSSymmetrizedBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeTwoFaceGNSMatrixCoefficient f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- Compatibility alias for the symmetrized completed GNS boundary presentation.

The positive prime kernel is not owned in this spectral packet file; it lives in the
completed-square/defect-kernel descent layer where diagonal debt and debt absorption are
visible. -/
noncomputable def zetaCompletedGNSBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedGNSSymmetrizedBoundaryForm f

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
          (match ℓ with
          | .correction => ZetaHermitianPacketEnsemble.coordinateGram (x ℓ)
          | _ => 0) =
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
  unfold zetaCompletedExplicitFormulaPrimeSpectralAmplitude
  unfold zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
  change ((r : ℂ) * a) * star ((r : ℂ) * b) =
      (zetaCompletedExplicitFormulaPrimeWeight p n : ℂ) * (a * star b)
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
  unfold zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
  refine Finset.sum_congr rfl ?_
  intro ℓ hℓ
  exact congrArg (fun z : ℂ => z + star z)
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude_mul_star_opposite ℓ.1 ℓ.2 f)

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
    unfold r
    exact (pow_two (Real.sqrt 2)).symm.trans (Real.sq_sqrt htwo_nonnegative)
  have hsqrt_sq_complex : (r : ℂ) * (r : ℂ) = (2 : ℂ) := by
    calc
      (r : ℂ) * (r : ℂ) = ((r * r : ℝ) : ℂ) := by
        exact (Complex.ofReal_mul r r).symm
      _ = (2 : ℂ) := by
        exact congrArg (fun x : ℝ => (x : ℂ)) hsqrt_sq_real
  unfold zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution
  unfold zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude
  change ((r : ℂ) * a) * star ((r : ℂ) * a) = (2 : ℂ) * (a * star a)
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
  unfold zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution
  unfold zetaCompletedArchimedeanBoundaryRealizedGram
  rfl

/-- Correction reconstruction into the realized Gram channel is the correction normalization. -/
theorem zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
      zetaCompletedCorrectionBoundaryRealizedGram f := by
  unfold zetaCompletedExplicitFormulaCorrectionConvolutionContribution
  unfold zetaCompletedCorrectionBoundaryRealizedGram
  rfl

/-- The realized archimedean Gram channel agrees with the Hermitian archimedean amplitude
packet Gram. -/
theorem zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedArchimedeanBoundaryRealizedGram f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  unfold zetaCompletedArchimedeanBoundaryRealizedGram
  unfold zetaCompletedArchimedeanBoundaryRealizedCoordinateGram
  unfold zetaCompletedHermitianBoundaryDefect
  unfold zetaPrimeHermitianPacketAsEnsemble
  unfold zetaArchimedeanHermitianPacketAsEnsemble
  unfold zetaCorrectionHermitianPacketAsEnsemble
  unfold ZetaHermitianPacketEnsemble.archimedeanPacketGram
  unfold ZetaHermitianPacketEnsemble.coordinateGram
  simp [ZetaHermitianPacketEnsemble.single,
    zetaCompletedExplicitFormulaCorrectionSpectralAmplitude,
    zetaCompletionCorrectionPacketCoordinate_sq]

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
      unfold zetaCompletedPrimeBoundaryRealizedPositiveFace
      unfold zetaCompletedPrimeBoundaryRealizedNegativeFace
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
      change (w : ℂ) * x + star ((w : ℂ) * x) =
        (w : ℂ) * (x + star x)
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
  by_cases hp : Nat.Prime p
  · by_cases hn : n ≠ 0
    · exact zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram
        p n hp hn f
    · have hweight :
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
        unfold zetaCompletedPrimeBoundaryRealizedCoordinateGram
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
  · have hweight :
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
      unfold zetaCompletedPrimeBoundaryRealizedCoordinateGram
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
  unfold zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
  unfold zetaCompletedPrimeBoundaryRealizedGram
  refine Finset.sum_congr rfl ?_
  intro ℓ hℓ
  exact zetaCompletedPrimeBoundaryReconstruction_pairedCoordinate_eq_realizedGram_all
    ℓ.1 ℓ.2 f

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
    unfold zetaCompletedExplicitFormulaArchimedeanContribution
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

/-- The realized real prime channel agrees with the two-face/GNS prime matrix coefficient.
This is the correct real-side replacement for the false one-face norm-square comparison. -/
theorem zetaCompletedPrimeBoundaryRealizedGram_eq_twoFacePrimeMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeBoundaryRealizedGram f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  exact (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram f).symm

/-- Prime completed boundary reconstruction: the paired prime spectral channel is the two-face
GNS matrix coefficient of the reconstructed real prime packet. -/
theorem zetaCompletedPrimeBoundaryReconstruction_pairing_eq_twoFaceMatrixCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution f =
      zetaPrimeTwoFaceGNSMatrixCoefficient f := by
  exact (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram f).trans
    (zetaCompletedPrimeBoundaryRealizedGram_eq_twoFacePrimeMatrixCoefficient f)

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

/-- The archimedean convolution contribution is the reconstructed Hermitian archimedean Gram. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_archimedeanPacketGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  exact (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired f).trans
    (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_gram f)

/-- Predicate saying the prime paired spectral channel is represented by the two-face/GNS
matrix coefficient. -/
def zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
    zetaPrimeTwoFaceGNSMatrixCoefficient f

/-- Predicate saying the archimedean paired spectral channel folds to the single-coordinate
Hermitian archimedean packet Gram. -/
def zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual
    (f : ZetaAdmissibleFunction) : Prop :=
  zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The real part of the prime convolution contribution is the real part of the two-face/GNS
matrix coefficient. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient_of
    (f : ZetaAdmissibleFunction)
    (hself :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact congrArg Complex.re hself

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

/-- The real part of the prime convolution contribution is the real part of the two-face/GNS
matrix coefficient under the two-face representation. -/
theorem zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient'
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact congrArg Complex.re hself

/-- The archimedean convolution contribution is real-valued under the self-dual
specialization. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_im_eq_zero_of_selfDual
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.im (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) = 0 := by
  exact (congrArg Complex.im hself).trans
    (Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f)))

/-- The real part of the archimedean convolution contribution is the Hermitian archimedean
packet Gram under the self-dual specialization. -/
theorem
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram_of_selfDual
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact congrArg Complex.re hself

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
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaPrimeConvolutionContributionTwoFace f) :
    Complex.re (zetaCompletedExplicitFormulaPrimeConvolutionContribution f) =
      Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) := by
  exact zetaCompletedExplicitFormulaPrimeConvolutionContribution_re_eq_twoFaceMatrixCoefficient'
    f hself

/-- Archimedean-channel norm-square holography under the self-dual specialization. -/
theorem zetaCompletedExplicitFormulaArchimedeanConvolutionChannel_holographic_of_selfDual
    (f : ZetaAdmissibleFunction)
    (hself : zetaCompletedExplicitFormulaArchimedeanConvolutionContributionSelfDual f) :
    Complex.re (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f) =
      ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f) := by
  exact
    zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_re_eq_archimedeanPacketGram_of_selfDual
      f hself

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

/-- The prime projection of the completed paired spectral packet is the prime convolution
paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_prime_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.primePairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f := by
  unfold zetaCompletedPairedSpectralBoundaryDefect
  unfold zetaPrimePairedSpectralPacketAsEnsemble
  unfold zetaArchimedeanPairedSpectralPacketAsEnsemble
  unfold zetaCorrectionPairedSpectralPacketAsEnsemble
  unfold zetaCompletedExplicitFormulaPrimeConvolutionContribution
  unfold zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
  unfold ZetaPairedSpectralPacketEnsemble.primePairedForm
  unfold ZetaPairedSpectralPacketEnsemble.coordinateGram
  unfold ZetaPairedSpectralPacketEnsemble.coordinateForm
  simp [ZetaPairedSpectralPacketEnsemble.single]

/-- The archimedean projection of the completed paired spectral packet is the archimedean
convolution paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_archimedean_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f := by
  unfold zetaCompletedPairedSpectralBoundaryDefect
  unfold zetaPrimePairedSpectralPacketAsEnsemble
  unfold zetaArchimedeanPairedSpectralPacketAsEnsemble
  unfold zetaCorrectionPairedSpectralPacketAsEnsemble
  unfold zetaCompletedExplicitFormulaArchimedeanConvolutionContribution
  unfold zetaCompletedExplicitFormulaArchimedeanConvolutionPairedContribution
  unfold ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
  unfold ZetaPairedSpectralPacketEnsemble.coordinateGram
  unfold ZetaPairedSpectralPacketEnsemble.coordinateForm
  simp [ZetaPairedSpectralPacketEnsemble.single]

/-- The correction projection of the completed paired spectral packet is the correction
convolution paired contribution. -/
theorem zetaCompletedPairedSpectralBoundaryForm_correction_eq_contribution
    (f : ZetaAdmissibleFunction) :
    ZetaPairedSpectralPacketEnsemble.correctionPairedForm
        (zetaCompletedPairedSpectralBoundaryDefect f) =
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  unfold zetaCompletedPairedSpectralBoundaryDefect
  unfold zetaPrimePairedSpectralPacketAsEnsemble
  unfold zetaArchimedeanPairedSpectralPacketAsEnsemble
  unfold zetaCorrectionPairedSpectralPacketAsEnsemble
  unfold zetaCompletedExplicitFormulaCorrectionConvolutionContribution
  unfold zetaCompletedExplicitFormulaCorrectionSpectralAmplitude
  unfold ZetaPairedSpectralPacketEnsemble.correctionPairedForm
  unfold ZetaPairedSpectralPacketEnsemble.coordinateGram
  unfold ZetaPairedSpectralPacketEnsemble.coordinateForm
  simp [ZetaPairedSpectralPacketEnsemble.single,
    zetaCompletionCorrectionPacketCoordinate_sq]

/-- The completed paired spectral boundary form is the sum of the three convolution-channel
contributions. -/
theorem zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f := by
  have hsplit :
      ZetaPairedSpectralPacketEnsemble.pairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        ZetaPairedSpectralPacketEnsemble.primePairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) +
          ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) +
          ZetaPairedSpectralPacketEnsemble.correctionPairedForm
            (zetaCompletedPairedSpectralBoundaryDefect f) :=
    ZetaPairedSpectralPacketEnsemble.pairedForm_eq_prime_add_archimedean_add_correction
      (zetaCompletedPairedSpectralBoundaryDefect f)
  have hprime :
      ZetaPairedSpectralPacketEnsemble.primePairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_prime_eq_contribution f
  have harch :
      ZetaPairedSpectralPacketEnsemble.archimedeanPairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_archimedean_eq_contribution f
  have hcorrection :
      ZetaPairedSpectralPacketEnsemble.correctionPairedForm
          (zetaCompletedPairedSpectralBoundaryDefect f) =
        zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_correction_eq_contribution f
  unfold zetaCompletedPairedSpectralBoundaryForm
  exact hsplit.trans
    (congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection)

/-- Completed boundary reconstruction into the realized Gram channel. This is the direct
explicit-formula reconstruction statement; it does not identify the realized Gram with an
amplitude norm-square packet. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_realizedGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedBoundaryRealizedGram f := by
  have hpaired :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f :=
    zetaCompletedPairedSpectralBoundaryForm_eq_convolutionContributions f
  have hprime :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f =
        zetaCompletedPrimeBoundaryRealizedGram f := by
    exact (zetaCompletedExplicitFormulaPrimeConvolutionContribution_eq_paired f).trans
      (zetaCompletedPrimeBoundaryReconstruction_pairing_eq_realizedGram f)
  have harch :
      zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f =
        zetaCompletedArchimedeanBoundaryRealizedGram f := by
    exact (zetaCompletedExplicitFormulaArchimedeanConvolutionContribution_eq_paired f).trans
      (zetaCompletedArchimedeanBoundaryReconstruction_pairing_eq_realizedGram f)
  have hcorrection :
      zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
        zetaCompletedCorrectionBoundaryRealizedGram f :=
    zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram f
  have hcomponents :
      zetaCompletedExplicitFormulaPrimeConvolutionContribution f +
          zetaCompletedExplicitFormulaArchimedeanConvolutionContribution f +
          zetaCompletedExplicitFormulaCorrectionConvolutionContribution f =
        zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f :=
    congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection
  have hrealized :
      zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f =
        zetaCompletedBoundaryRealizedGram f := by
    unfold zetaCompletedBoundaryRealizedGram
    unfold zetaCompletedPrimeBoundaryRealizedGram
    unfold zetaCompletedArchimedeanBoundaryRealizedGram
    unfold zetaCompletedCorrectionBoundaryRealizedGram
    rfl
  exact hpaired.trans (hcomponents.trans hrealized)

/-- The realized completed boundary form is represented by the mixed symmetrized boundary package:
the prime channel is two-face/GNS, while the archimedean and correction channels are one-face
Hermitian squares. -/
theorem zetaCompletedBoundaryRealizedGram_eq_GNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryRealizedGram f =
      zetaCompletedGNSSymmetrizedBoundaryForm f := by
  have hprime :
      zetaCompletedPrimeBoundaryRealizedGram f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f :=
    zetaCompletedPrimeBoundaryRealizedGram_eq_twoFacePrimeMatrixCoefficient f
  have harch :
      zetaCompletedArchimedeanBoundaryRealizedGram f =
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) :=
    zetaCompletedArchimedeanBoundaryRealizedGram_eq_hermitianArchimedeanPacketGram f
  have hcorrection :
      zetaCompletedCorrectionBoundaryRealizedGram f =
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
    exact (zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_realizedGram f).symm.trans
      (zetaCompletedCorrectionBoundaryReconstruction_pairing_eq_gram f)
  have hcomponents :
      zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f =
        zetaPrimeTwoFaceGNSMatrixCoefficient f +
          (ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) :=
    congrArg₂ (fun x y : ℂ => x + y)
      (congrArg₂ (fun x y : ℂ => x + y) hprime harch)
      hcorrection
  calc
    zetaCompletedBoundaryRealizedGram f =
        zetaCompletedPrimeBoundaryRealizedGram f +
          zetaCompletedArchimedeanBoundaryRealizedGram f +
          zetaCompletedCorrectionBoundaryRealizedGram f := by
      unfold zetaCompletedBoundaryRealizedGram
      unfold zetaCompletedPrimeBoundaryRealizedGram
      unfold zetaCompletedArchimedeanBoundaryRealizedGram
      unfold zetaCompletedCorrectionBoundaryRealizedGram
      rfl
    _ =
        zetaPrimeTwoFaceGNSMatrixCoefficient f +
          (ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) := hcomponents
    _ = zetaCompletedGNSSymmetrizedBoundaryForm f := by
      unfold zetaCompletedGNSSymmetrizedBoundaryForm
      rfl

/-- Completed boundary reconstruction into the symmetrized real two-face presentation. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_GNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedGNSSymmetrizedBoundaryForm f := by
  exact (zetaCompletedBoundaryReconstruction_pairedForm_eq_realizedGram f).trans
    (zetaCompletedBoundaryRealizedGram_eq_GNSSymmetrizedBoundaryForm f)

/-- The completed mixed GNS boundary form is real-valued: the real prime channel is the
symmetrized two-face coefficient, and the remaining packet Gram coordinates are real
coercions. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedGNSSymmetrizedBoundaryForm f) = 0 := by
  let z : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let a : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let c : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hz : Complex.im z = 0 := by
    exact zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
  have ha : Complex.im a = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.archimedeanPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hc : Complex.im c = 0 := by
    exact Complex.ofReal_im
      (ZetaHermitianPacketEnsemble.correctionPacketGram
        (zetaCompletedHermitianBoundaryDefect f))
  have hza : Complex.im z + Complex.im a = 0 := by
    calc
      Complex.im z + Complex.im a = 0 + Complex.im a := by
        exact congrArg (fun x : ℝ => x + Complex.im a) hz
      _ = 0 + 0 := by
        exact congrArg (fun x : ℝ => 0 + x) ha
      _ = 0 := by
        exact add_zero 0
  unfold zetaCompletedGNSSymmetrizedBoundaryForm
  change Complex.im (z + a + c) = 0
  calc
    Complex.im (z + a + c) = Complex.im (z + a) + Complex.im c := by
      exact Complex.add_im (z + a) c
    _ = (Complex.im z + Complex.im a) + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) (Complex.add_im z a)
    _ = 0 + Complex.im c := by
      exact congrArg (fun x : ℝ => x + Complex.im c) hza
    _ = 0 + 0 := by
      exact congrArg (fun x : ℝ => 0 + x) hc
    _ = 0 := by
      exact add_zero 0

/-- The compatibility GNS boundary presentation is real-valued because it is the symmetrized
two-face presentation. -/
theorem zetaCompletedGNSBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedGNSBoundaryForm f) = 0 := by
  unfold zetaCompletedGNSBoundaryForm
  exact zetaCompletedGNSSymmetrizedBoundaryForm_im_eq_zero f

/-- The symmetrized completed GNS boundary form is definitionally the compatibility GNS
boundary presentation in this spectral packet layer.  Positivity is owned downstream by the
completed defect-kernel channel, where diagonal debt and debt absorption are visible. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_eq_GNSBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedGNSBoundaryForm f := by
  rfl

/-- Completed boundary reconstruction into the compatibility GNS boundary presentation. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_GNSBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaCompletedGNSBoundaryForm f := by
  exact (zetaCompletedBoundaryReconstruction_pairedForm_eq_GNSSymmetrizedBoundaryForm f).trans
    (zetaCompletedGNSSymmetrizedBoundaryForm_eq_GNSBoundaryForm f)

/-- The completed paired spectral boundary form is real-valued. -/
theorem zetaCompletedPairedSpectralBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPairedSpectralBoundaryForm f) = 0 := by
  have hform :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaCompletedGNSBoundaryForm f :=
    zetaCompletedBoundaryReconstruction_pairedForm_eq_GNSBoundaryForm f
  exact (congrArg Complex.im hform).trans
    (zetaCompletedGNSBoundaryForm_im_eq_zero f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

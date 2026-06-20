import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPacketLabels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner

/-!
# Boundary zeta Hermitian packets

This file owns the complex packet layer used by the autocorrelation
explicit-formula argument. The older real packet layer is a real shadow; the
RH-lane sign proof needs Hermitian squares of complex seed amplitudes,
not squares of real parts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

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
        | _ => 0) :=
  match ℓ with
  | .prime m n => coordinateGram_split_prime x m n
  | .archimedean => coordinateGram_split_archimedean x
  | .correction => coordinateGram_split_correction x

/-- The Hermitian packet norm is nonnegative. -/
theorem normSq_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ normSq x := by
  exact Finset.sum_nonneg (fun ℓ _ => Complex.normSq_nonneg (x ℓ))

/-- The prime Hermitian packet Gram is nonnegative. -/
theorem primePacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ primePacketGram x := by
  exact Finset.sum_nonneg
    (fun ℓ _ =>
      match ℓ with
      | .prime p n => Complex.normSq_nonneg (x (ZetaPacketLabel.prime p n))
      | .archimedean => le_refl 0
      | .correction => le_refl 0)

/-- The Hermitian coordinate Gram of a zero coordinate is zero. -/
theorem coordinateGram_zero :
    coordinateGram (0 : ℂ) = 0 := by
  exact Complex.normSq_zero

/-- The prime Hermitian Gram may be computed over any finite set containing the packet
support. -/
theorem primePacketGram_eq_sum_of_support_subset
    (x : ZetaHermitianPacketEnsemble) (s : Finset ZetaPacketLabel)
    (hs : x.support ⊆ s) :
    primePacketGram x =
      ∑ ℓ in s,
        match ℓ with
        | .prime _ _ => coordinateGram (x ℓ)
        | _ => 0 := by
  exact Finset.sum_subset hs
    (fun ℓ _ hnotmem =>
      match ℓ with
      | .prime p n =>
          have hcoord_zero :
              x (ZetaPacketLabel.prime p n) = 0 :=
            Finsupp.not_mem_support_iff.mp hnotmem
          calc
            coordinateGram (x (ZetaPacketLabel.prime p n)) =
                coordinateGram (0 : ℂ) := by
              exact congrArg coordinateGram hcoord_zero
            _ = 0 := coordinateGram_zero
      | .archimedean => rfl
      | .correction => rfl)

/-- The prime Hermitian Gram is determined by the prime coordinates. -/
theorem primePacketGram_eq_of_prime_coordinates
    {x y : ZetaHermitianPacketEnsemble}
    (hprime : ∀ p n : ℕ,
      x (ZetaPacketLabel.prime p n) = y (ZetaPacketLabel.prime p n)) :
    primePacketGram x = primePacketGram y := by
  let s : Finset ZetaPacketLabel := x.support ∪ y.support
  have hxsubset : x.support ⊆ s := by
    exact Finset.subset_union_left
  have hysubset : y.support ⊆ s := by
    exact Finset.subset_union_right
  have hxsum :
      primePacketGram x =
        ∑ ℓ in s,
          match ℓ with
          | .prime _ _ => coordinateGram (x ℓ)
          | _ => 0 :=
    primePacketGram_eq_sum_of_support_subset x s hxsubset
  have hysum :
      primePacketGram y =
        ∑ ℓ in s,
          match ℓ with
          | .prime _ _ => coordinateGram (y ℓ)
          | _ => 0 :=
    primePacketGram_eq_sum_of_support_subset y s hysubset
  have hsum :
      (∑ ℓ in s,
          match ℓ with
          | .prime _ _ => coordinateGram (x ℓ)
          | _ => 0) =
        ∑ ℓ in s,
          match ℓ with
          | .prime _ _ => coordinateGram (y ℓ)
          | _ => 0 := by
    exact Finset.sum_congr rfl
      (fun ℓ _ =>
        match ℓ with
        | .prime p n =>
            congrArg coordinateGram (hprime p n)
        | .archimedean => rfl
        | .correction => rfl)
  exact hxsum.trans (hsum.trans hysum.symm)

/-- The archimedean Hermitian packet Gram is nonnegative. -/
theorem archimedeanPacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ archimedeanPacketGram x := by
  exact Finset.sum_nonneg
    (fun ℓ _ =>
      match ℓ with
      | .prime _p _n => le_refl 0
      | .archimedean => Complex.normSq_nonneg (x ZetaPacketLabel.archimedean)
      | .correction => le_refl 0)

/-- The correction Hermitian packet Gram is nonnegative. -/
theorem correctionPacketGram_nonnegative (x : ZetaHermitianPacketEnsemble) :
    0 ≤ correctionPacketGram x := by
  exact Finset.sum_nonneg
    (fun ℓ _ =>
      match ℓ with
      | .prime _p _n => le_refl 0
      | .archimedean => le_refl 0
      | .correction => Complex.normSq_nonneg (x ZetaPacketLabel.correction))

/-- The Hermitian norm square splits into prime, archimedean, and correction
packet-family Gram contributions. -/
theorem normSq_eq_prime_add_archimedean_add_correction
    (x : ZetaHermitianPacketEnsemble) :
    normSq x =
      primePacketGram x + archimedeanPacketGram x + correctionPacketGram x := by
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
      exact Finset.sum_congr rfl
        (fun ℓ _ => coordinateGram_split x ℓ)
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

/-- The real part of the paired packet form. This is the real quantity consumed by sign
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
      exact Finset.sum_congr rfl
        (fun ℓ _ =>
          match ℓ with
          | .prime m n =>
              calc
                coordinateGram (x (ZetaPacketLabel.prime m n)) =
                    coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 := by
                  exact (add_zero _).symm
                _ =
                    coordinateGram (x (ZetaPacketLabel.prime m n)) + 0 + 0 := by
                  exact (add_zero _).symm
          | .archimedean =>
              calc
                coordinateGram (x ZetaPacketLabel.archimedean) =
                    0 + coordinateGram (x ZetaPacketLabel.archimedean) := by
                  exact (zero_add _).symm
                _ = 0 + coordinateGram (x ZetaPacketLabel.archimedean) + 0 := by
                  exact (add_zero _).symm
          | .correction =>
              calc
                coordinateGram (x ZetaPacketLabel.correction) =
                    0 + coordinateGram (x ZetaPacketLabel.correction) := by
                  exact (zero_add _).symm
                _ = 0 + (0 + coordinateGram (x ZetaPacketLabel.correction)) := by
                  exact congrArg (fun t : ℂ => 0 + t)
                    (zero_add (coordinateGram (x ZetaPacketLabel.correction))).symm
                _ = 0 + 0 + coordinateGram (x ZetaPacketLabel.correction) := by
                  exact (add_assoc 0 0 (coordinateGram (x ZetaPacketLabel.correction))).symm)
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
      (match ℓ with | .correction => x ℓ | _ => 0) :=
  match ℓ with
  | .prime m n =>
      calc
        x (ZetaPacketLabel.prime m n) = x (ZetaPacketLabel.prime m n) + 0 := by
          exact (add_zero _).symm
        _ = x (ZetaPacketLabel.prime m n) + 0 + 0 := by
          exact (add_zero _).symm
  | .archimedean =>
      calc
        x ZetaPacketLabel.archimedean = 0 + x ZetaPacketLabel.archimedean := by
          exact (zero_add _).symm
        _ = 0 + x ZetaPacketLabel.archimedean + 0 := by
          exact (add_zero _).symm
  | .correction =>
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
  calc
    ∑ ℓ in x.support, x ℓ =
        ∑ ℓ in x.support,
          ((match ℓ with | .prime _ _ => x ℓ | _ => 0) +
          (match ℓ with | .archimedean => x ℓ | _ => 0) +
          (match ℓ with | .correction => x ℓ | _ => 0)) := by
      exact Finset.sum_congr rfl
        (fun ℓ _ => coordinate_split x ℓ)
    _ =
        (∑ ℓ in x.support, match ℓ with | .prime _ _ => x ℓ | _ => 0) +
        (∑ ℓ in x.support, match ℓ with | .archimedean => x ℓ | _ => 0) +
        (∑ ℓ in x.support, match ℓ with | .correction => x ℓ | _ => 0) := by
      exact ZetaPairedSpectralPacketEnsemble.sum_three_terms x.support
        (fun ℓ => match ℓ with | .prime _ _ => x ℓ | _ => 0)
        (fun ℓ => match ℓ with | .archimedean => x ℓ | _ => 0)
        (fun ℓ => match ℓ with | .correction => x ℓ | _ => 0)

end ZetaCompletedBoundaryRealizedGramPacket

end
end LFunctions
end Boundary

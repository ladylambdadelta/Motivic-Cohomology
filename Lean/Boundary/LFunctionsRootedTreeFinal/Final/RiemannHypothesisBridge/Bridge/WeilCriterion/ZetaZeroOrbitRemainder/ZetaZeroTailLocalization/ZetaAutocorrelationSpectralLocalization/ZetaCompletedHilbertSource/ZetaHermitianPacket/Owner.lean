import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPacketLabels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner

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

/-- The Hermitian coordinate Gram of a zero coordinate is zero. -/
theorem coordinateGram_zero :
    coordinateGram (0 : ℂ) = 0 := by
  unfold coordinateGram
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
  unfold primePacketGram
  exact Finset.sum_subset hs
    (fun ℓ _ hnotmem => by
      cases ℓ with
      | prime p n =>
          have hcoord_zero :
              x (ZetaPacketLabel.prime p n) = 0 :=
            Finsupp.not_mem_support_iff.mp hnotmem
          calc
            coordinateGram (x (ZetaPacketLabel.prime p n)) =
                coordinateGram (0 : ℂ) := by
              exact congrArg coordinateGram hcoord_zero
            _ = 0 := coordinateGram_zero
      | archimedean => rfl
      | correction => rfl)

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
      (fun ℓ _ => by
        cases ℓ with
        | prime p n =>
            exact congrArg coordinateGram (hprime p n)
        | archimedean => rfl
        | correction => rfl)
  exact hxsum.trans (hsum.trans hysum.symm)

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

/-- The finite-display prime defect amplitude, equal to positive face minus opposite face. -/
noncomputable def zetaPrimeHermitianDefectAmplitude
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
    zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f

/-- The prime Hermitian packet attached to the seed probe. -/
noncomputable def zetaPrimeHermitianPacketAsEnsemble (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    ZetaHermitianPacketEnsemble.single
      (ZetaPacketLabel.prime ℓ.1 ℓ.2)
      (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f)

/-- The prime Hermitian finite-display packet has the displayed amplitude at every label in
the explicit finite prime support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_mem
    (f : ZetaAdmissibleFunction) (ℓ : ℕ × ℕ)
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaPrimeHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime ℓ.1 ℓ.2) =
      zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f := by
  unfold zetaPrimeHermitianPacketAsEnsemble
  calc
    (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.single
          (ZetaPacketLabel.prime m.1 m.2)
          (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        (ZetaPacketLabel.prime ℓ.1 ℓ.2) =
        ∑ m in zetaCompletedExplicitFormulaPrimeSupport,
          (ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
              (ZetaPacketLabel.prime ℓ.1 ℓ.2) := by
      exact Finsupp.finset_sum_apply
        zetaCompletedExplicitFormulaPrimeSupport
        (fun m =>
          ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        (ZetaPacketLabel.prime ℓ.1 ℓ.2)
    _ = zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f := by
      have hsum :
          (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
            (ZetaHermitianPacketEnsemble.single
              (ZetaPacketLabel.prime m.1 m.2)
              (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
                (ZetaPacketLabel.prime ℓ.1 ℓ.2)) =
            (ZetaHermitianPacketEnsemble.single
              (ZetaPacketLabel.prime ℓ.1 ℓ.2)
              (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f))
                (ZetaPacketLabel.prime ℓ.1 ℓ.2) := by
        refine Finset.sum_eq_single ℓ ?_ ?_
        · intro m _ hm_ne
          unfold ZetaHermitianPacketEnsemble.single
          exact Finsupp.single_eq_of_ne
            (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                ZetaPacketLabel.prime ℓ.1 ℓ.2 => by
              rcases m with ⟨p, n⟩
              rcases ℓ with ⟨q, r⟩
              cases hlabel
              exact hm_ne rfl)
        · intro hnotmem
          exact False.elim (hnotmem hℓ)
      calc
        (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
          (ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
              (ZetaPacketLabel.prime ℓ.1 ℓ.2)) =
            (ZetaHermitianPacketEnsemble.single
              (ZetaPacketLabel.prime ℓ.1 ℓ.2)
              (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f))
                (ZetaPacketLabel.prime ℓ.1 ℓ.2) := hsum
        _ = zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f := by
          unfold ZetaHermitianPacketEnsemble.single
          exact Finsupp.single_eq_same

/-- The prime Hermitian finite-display packet is zero at explicit prime labels outside the
finite support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_not_mem
    (f : ZetaAdmissibleFunction) (ℓ : ℕ × ℕ)
    (hℓ : ℓ ∉ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaPrimeHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime ℓ.1 ℓ.2) = 0 := by
  unfold zetaPrimeHermitianPacketAsEnsemble
  calc
    (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.single
          (ZetaPacketLabel.prime m.1 m.2)
          (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        (ZetaPacketLabel.prime ℓ.1 ℓ.2) =
        ∑ m in zetaCompletedExplicitFormulaPrimeSupport,
          (ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
              (ZetaPacketLabel.prime ℓ.1 ℓ.2) := by
      exact Finsupp.finset_sum_apply
        zetaCompletedExplicitFormulaPrimeSupport
        (fun m =>
          ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        (ZetaPacketLabel.prime ℓ.1 ℓ.2)
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun m hm =>
          by
            unfold ZetaHermitianPacketEnsemble.single
            exact Finsupp.single_eq_of_ne
              (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                  ZetaPacketLabel.prime ℓ.1 ℓ.2 => by
                rcases m with ⟨p, n⟩
                rcases ℓ with ⟨q, r⟩
                cases hlabel
                exact hℓ hm))

/-- The finite prime Hermitian packet has zero archimedean coordinate. -/
theorem zetaPrimeHermitianPacketAsEnsemble_archimedean_apply
    (f : ZetaAdmissibleFunction) :
    zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = 0 := by
  unfold zetaPrimeHermitianPacketAsEnsemble
  calc
    (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.single
          (ZetaPacketLabel.prime m.1 m.2)
          (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        ZetaPacketLabel.archimedean =
        ∑ m in zetaCompletedExplicitFormulaPrimeSupport,
          (ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
              ZetaPacketLabel.archimedean := by
      exact Finsupp.finset_sum_apply
        zetaCompletedExplicitFormulaPrimeSupport
        (fun m =>
          ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        ZetaPacketLabel.archimedean
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun m _ => by
          unfold ZetaHermitianPacketEnsemble.single
          exact Finsupp.single_eq_of_ne
            (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                ZetaPacketLabel.archimedean =>
              ZetaPacketLabel.noConfusion hlabel))

/-- The finite prime Hermitian packet has zero correction coordinate. -/
theorem zetaPrimeHermitianPacketAsEnsemble_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction = 0 := by
  unfold zetaPrimeHermitianPacketAsEnsemble
  calc
    (∑ m in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.single
          (ZetaPacketLabel.prime m.1 m.2)
          (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        ZetaPacketLabel.correction =
        ∑ m in zetaCompletedExplicitFormulaPrimeSupport,
          (ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
              ZetaPacketLabel.correction := by
      exact Finsupp.finset_sum_apply
        zetaCompletedExplicitFormulaPrimeSupport
        (fun m =>
          ZetaHermitianPacketEnsemble.single
            (ZetaPacketLabel.prime m.1 m.2)
            (zetaPrimeHermitianDefectAmplitude m.1 m.2 f))
        ZetaPacketLabel.correction
    _ = 0 := by
      exact Finset.sum_eq_zero
        (fun m _ => by
          unfold ZetaHermitianPacketEnsemble.single
          exact Finsupp.single_eq_of_ne
            (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                ZetaPacketLabel.correction =>
              ZetaPacketLabel.noConfusion hlabel))

/-- The finite prime Hermitian packet support is contained in the image of the explicit
finite prime-label support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_support_subset_prime_image
    (f : ZetaAdmissibleFunction) :
    (zetaPrimeHermitianPacketAsEnsemble f).support ⊆
      zetaCompletedExplicitFormulaPrimeSupport.image
        (fun ℓ : ℕ × ℕ => ZetaPacketLabel.prime ℓ.1 ℓ.2) := by
  intro label hlabel
  cases label with
  | prime p n =>
      by_cases hpair : (p, n) ∈ zetaCompletedExplicitFormulaPrimeSupport
      · exact Finset.mem_image.mpr ⟨(p, n), hpair, rfl⟩
      · have hzero :
            zetaPrimeHermitianPacketAsEnsemble f
              (ZetaPacketLabel.prime p n) = 0 :=
          zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_not_mem
            f (p, n) hpair
        have hnonzero :
            zetaPrimeHermitianPacketAsEnsemble f
              (ZetaPacketLabel.prime p n) ≠ 0 :=
          Finsupp.mem_support_iff.mp hlabel
        exact False.elim (hnonzero hzero)
  | archimedean =>
      have hzero :
          zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = 0 :=
        zetaPrimeHermitianPacketAsEnsemble_archimedean_apply f
      have hnonzero :
          zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean ≠ 0 :=
        Finsupp.mem_support_iff.mp hlabel
      exact False.elim (hnonzero hzero)
  | correction =>
      have hzero :
          zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction = 0 :=
        zetaPrimeHermitianPacketAsEnsemble_correction_apply f
      have hnonzero :
          zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction ≠ 0 :=
        Finsupp.mem_support_iff.mp hlabel
      exact False.elim (hnonzero hzero)

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

/-- The weighted prime diagonal-debt coordinate attached to one prime-power label. -/
noncomputable def zetaPrimeDefectKernelDiagonalDebtCoordinate
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f *
      star (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f) +
    zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f *
      star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)

/-- The weighted positive prime defect-kernel coordinate attached to one prime-power label. -/
noncomputable def zetaPrimeDefectKernelPositiveCoordinate
    (p n : ℕ) (f : ZetaAdmissibleFunction) : ℂ :=
  (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
      zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f) *
    star
      (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
        zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)

/-- The prime diagonal debt over the explicit prime support. -/
noncomputable def zetaPrimeDefectKernelDiagonalDebt
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaPrimeDefectKernelDiagonalDebtCoordinate ℓ.1 ℓ.2 f

/-- The positive prime defect kernel over the explicit prime support. -/
noncomputable def zetaPrimeDefectKernelPositiveForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f

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
  unfold zetaPrimeDefectKernelPositiveCoordinate
  unfold zetaPrimeDefectKernelDiagonalDebtCoordinate
  change (a - b) * star (a - b) + (a * star b + star (a * star b)) =
    a * star a + b * star b
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
      ring

/-- The positive prime defect kernel plus its two-face cross term is the prime diagonal debt. -/
theorem zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelPositiveForm f +
        zetaPrimeTwoFaceGNSMatrixCoefficient f =
      zetaPrimeDefectKernelDiagonalDebt f := by
  unfold zetaPrimeDefectKernelPositiveForm
  unfold zetaPrimeTwoFaceGNSMatrixCoefficient
  unfold zetaPrimeTwoFaceGNSOrientedCoefficient
  unfold zetaPrimeDefectKernelDiagonalDebt
  calc
    (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) +
        ((∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
            zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) +
          star
            (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
              zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f))) =
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) +
        ((∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
            zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) +
          ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
            star
              (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f))) := by
      exact congrArg
        (fun z : ℂ =>
          (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
            zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) +
            ((∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
              zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) + z))
        (map_sum star zetaCompletedExplicitFormulaPrimeSupport
          (fun ℓ =>
            zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)))
    _ =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          (zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f +
            (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) +
              star
                (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
                  star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)))) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      abel
    _ =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelDiagonalDebtCoordinate ℓ.1 ℓ.2 f := by
      refine Finset.sum_congr rfl ?_
      intro ℓ hℓ
      exact zetaPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
        ℓ.1 ℓ.2 f

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
  unfold zetaPrimeDefectKernelPositiveCoordinate
  change 0 ≤ Complex.re ((a - b) * star (a - b))
  exact complex_re_mul_star_self_nonnegative_hermitianPacket (a - b)

/-- The positive prime defect-kernel form has nonnegative real part. -/
theorem zetaPrimeDefectKernelPositiveForm_re_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  unfold zetaPrimeDefectKernelPositiveForm
  calc
    0 ≤ ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        Complex.re (zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact Finset.sum_nonneg
        (fun ℓ _ =>
          zetaPrimeDefectKernelPositiveCoordinate_re_nonnegative ℓ.1 ℓ.2 f)
    _ = Complex.re
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact (Complex.sum_re
        (fun ℓ =>
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f)
        zetaCompletedExplicitFormulaPrimeSupport).symm

/-- One finite-display prime defect coordinate has real part equal to the Hermitian
defect-amplitude coordinate Gram. -/
theorem zetaPrimeDefectKernelPositiveCoordinate_re_eq_defectAmplitude_normSq
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveCoordinate p n f) =
      ZetaHermitianPacketEnsemble.coordinateGram
        (zetaPrimeHermitianDefectAmplitude p n f) := by
  unfold zetaPrimeDefectKernelPositiveCoordinate
  unfold zetaPrimeHermitianDefectAmplitude
  unfold ZetaHermitianPacketEnsemble.coordinateGram
  exact complex_re_mul_star_self_eq_normSq_hermitianPacket
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
      zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)

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
  unfold zetaCompletedPrimeTwoFaceGNSOrientedCoordinate
  unfold zetaCompletedPrimeSpectralAmplitudeIndex
  unfold zetaCompletedPrimeOppositeSpectralAmplitudeIndex
  change ((r : ℂ) * a) * star ((r : ℂ) * b) =
    (ι.weight : ℂ) * (a * star b)
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
  unfold zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
  unfold zetaCompletedPrimeTwoFaceGNSMatrixCoefficient
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
  unfold zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate
  change Complex.im (z + star z) = 0
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
  unfold zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate
  change -(W *
      (zetaCompletedExplicitFormulaPhi
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center +
        star
          (zetaCompletedExplicitFormulaPhi
            (ZetaAdmissibleFunction.convolutionAutocorrelation f) ι.center))) =
    -(C + star C)
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

/-- The real part of the completed positive prime defect kernel over a finite prime-power
window. -/
noncomputable def zetaCompletedPrimeDefectKernelPositiveRealWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelPositiveWindow N f)

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
  unfold zetaCompletedPrimeDefectKernelPositiveCoordinate
  unfold zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate
  change (a - b) * star (a - b) + (a * star b + star (a * star b)) =
    a * star a + b * star b
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
      ring

/-- One completed positive prime defect-kernel coordinate has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_nonnegative
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  let a : ℂ := zetaCompletedPrimeSpectralAmplitudeIndex ι f
  let b : ℂ := zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f
  unfold zetaCompletedPrimeDefectKernelPositiveCoordinate
  change 0 ≤ Complex.re ((a - b) * star (a - b))
  exact complex_re_mul_star_self_nonnegative_hermitianPacket (a - b)

/-- A finite completed positive prime defect-kernel window has nonnegative real part. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_re_nonnegative
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeDefectKernelPositiveRealWindow N f := by
  unfold zetaCompletedPrimeDefectKernelPositiveRealWindow
  unfold zetaCompletedPrimeDefectKernelPositiveWindow
  calc
    0 ≤ ∑ ι in ZetaPrimePowerIndex.window N,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
      exact Finset.sum_nonneg
        (fun ι _ =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate_re_nonnegative ι f)
    _ = Complex.re
        (∑ ι in ZetaPrimePowerIndex.window N,
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
      exact (Complex.sum_re
        (fun ι =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
        (ZetaPrimePowerIndex.window N)).symm

/-- Nongenuine prime-power indices have zero completed positive defect coordinate. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction)
    (hι : ¬ ZetaPrimePowerIndex.IsGenuine ι) :
    zetaCompletedPrimeDefectKernelPositiveCoordinate ι f = 0 := by
  have hweight : ZetaPrimePowerIndex.weight ι = 0 :=
    ZetaPrimePowerIndex.weight_eq_zero_of_not_isGenuine ι hι
  have hsqrt : ZetaPrimePowerIndex.sqrtWeight ι = 0 := by
    unfold ZetaPrimePowerIndex.sqrtWeight
    exact (congrArg Real.sqrt hweight).trans Real.sqrt_zero
  have hpos :
      zetaCompletedPrimeSpectralAmplitudeIndex ι f = 0 := by
    unfold zetaCompletedPrimeSpectralAmplitudeIndex
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f))
  have hneg :
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f = 0 := by
    unfold zetaCompletedPrimeOppositeSpectralAmplitudeIndex
    exact Eq.trans
      (congrArg
        (fun x : ℝ =>
          (x : ℂ) * zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f)
        hsqrt)
      (zero_mul (zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f))
  unfold zetaCompletedPrimeDefectKernelPositiveCoordinate
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
      exact zero_mul (star (0 - 0 : ℂ))

/-- The prime spectral majorant for the two real-axis amplitude families.

This is a conditional comparison majorant.  It is useful for estimates after a contour
realization supplies summability, but the code no longer treats independent real-axis
Laplace seed samples as intrinsically square-summable. -/
noncomputable def zetaCompletedPrimeSpectralCoordinateMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 +
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2

/-- The positive weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimePositiveWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f‖ ^ 2

/-- The opposite weighted prime sample norm square before the square-root-weight
amplitude packaging. -/
noncomputable def zetaCompletedPrimeOppositeWeightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  ZetaPrimePowerIndex.weight ι *
    ‖zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f‖ ^ 2

/-- The positive square-root-weight amplitude has norm square equal to the positive
weighted prime sample norm square. -/
theorem zetaCompletedPrimeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimePositiveWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    unfold r
    unfold ZetaPrimePowerIndex.sqrtWeight
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    unfold r
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  unfold zetaCompletedPrimeSpectralAmplitudeIndex
  unfold zetaCompletedPrimePositiveWeightedSampleNormSq
  change ‖(r : ℂ) * A‖ ^ 2 =
    ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      nlinarith [hweight]

/-- The opposite square-root-weight amplitude has norm square equal to the opposite
weighted prime sample norm square. -/
theorem zetaCompletedPrimeOppositeSpectralAmplitudeIndex_norm_sq_eq_weightedSampleNormSq
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f‖ ^ 2 =
      zetaCompletedPrimeOppositeWeightedSampleNormSq ι f := by
  let r : ℝ := ZetaPrimePowerIndex.sqrtWeight ι
  let A : ℂ := zetaCompletedPrimeHermitianNegativeSeedAmplitude ι.p ι.n f
  have hr_nonneg : 0 ≤ r := by
    unfold r
    unfold ZetaPrimePowerIndex.sqrtWeight
    exact Real.sqrt_nonneg _
  have hnorm_r : ‖(r : ℂ)‖ = r := by
    calc
      ‖(r : ℂ)‖ = |r| := by
        exact RCLike.norm_ofReal r
      _ = r := by
        exact abs_of_nonneg hr_nonneg
  have hnorm :
      ‖(r : ℂ) * A‖ = r * ‖A‖ := by
    calc
      ‖(r : ℂ) * A‖ = ‖(r : ℂ)‖ * ‖A‖ := by
        exact norm_mul (r : ℂ) A
      _ = r * ‖A‖ := by
        exact congrArg (fun x : ℝ => x * ‖A‖) hnorm_r
  have hweight : r * r = ZetaPrimePowerIndex.weight ι := by
    unfold r
    exact ZetaPrimePowerIndex.sqrtWeight_mul_self ι
  unfold zetaCompletedPrimeOppositeSpectralAmplitudeIndex
  unfold zetaCompletedPrimeOppositeWeightedSampleNormSq
  change ‖(r : ℂ) * A‖ ^ 2 =
    ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2
  calc
    ‖(r : ℂ) * A‖ ^ 2 = (r * ‖A‖) ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) hnorm
    _ = ZetaPrimePowerIndex.weight ι * ‖A‖ ^ 2 := by
      nlinarith [hweight]

/-- The norm of a two-face product is bounded by the sum of the two squared face norms. -/
theorem complex_norm_mul_star_le_sq_add_sq (a b : ℂ) :
    ‖a * star b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hmul : ‖a * star b‖ ≤ ‖a‖ * ‖star b‖ :=
    norm_mul_le a (star b)
  have hstar : ‖star b‖ = ‖b‖ :=
    norm_star b
  have hmul_faces : ‖a * star b‖ ≤ ‖a‖ * ‖b‖ :=
    Eq.subst
      (motive := fun x : ℝ => ‖a * star b‖ ≤ ‖a‖ * x)
      hstar
      hmul
  have hface_arith : ‖a‖ * ‖b‖ ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact hmul_faces.trans hface_arith

/-- The norm of one defect-square coordinate is bounded by twice the sum of the squared
face norms. -/
theorem complex_norm_defect_square_le_two_sq_add_sq (a b : ℂ) :
    ‖(a - b) * star (a - b)‖ ≤
      2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have hmul : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖star (a - b)‖ :=
    norm_mul_le (a - b) (star (a - b))
  have hstar : ‖star (a - b)‖ = ‖a - b‖ :=
    norm_star (a - b)
  have hmul_self : ‖(a - b) * star (a - b)‖ ≤
      ‖a - b‖ * ‖a - b‖ :=
    Eq.subst
      (motive := fun x : ℝ =>
        ‖(a - b) * star (a - b)‖ ≤ ‖a - b‖ * x)
      hstar
      hmul
  have hsub : ‖a - b‖ ≤ ‖a‖ + ‖b‖ :=
    norm_sub_le a b
  have hsub_nonneg : 0 ≤ ‖a - b‖ :=
    norm_nonneg (a - b)
  have hsum_nonneg : 0 ≤ ‖a‖ + ‖b‖ :=
    add_nonneg (norm_nonneg a) (norm_nonneg b)
  have hsquare :
      ‖a - b‖ * ‖a - b‖ ≤
        (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) :=
    mul_le_mul hsub hsub hsub_nonneg hsum_nonneg
  have harith :
      (‖a‖ + ‖b‖) * (‖a‖ + ‖b‖) ≤
        2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  exact hmul_self.trans (hsquare.trans harith)

/-- The positive defect-square coordinate is bounded by twice the spectral majorant. -/
theorem norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeDefectKernelPositiveCoordinate ι f‖ ≤
      2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  unfold zetaCompletedPrimeDefectKernelPositiveCoordinate
  unfold zetaCompletedPrimeSpectralCoordinateMajorant
  exact
    complex_norm_defect_square_le_two_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- The oriented two-face coordinate is bounded by the spectral majorant. -/
theorem norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
    (ι : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f‖ ≤
      zetaCompletedPrimeSpectralCoordinateMajorant ι f := by
  unfold zetaCompletedPrimeTwoFaceGNSOrientedCoordinate
  unfold zetaCompletedPrimeSpectralCoordinateMajorant
  exact
    complex_norm_mul_star_le_sq_add_sq
      (zetaCompletedPrimeSpectralAmplitudeIndex ι f)
      (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)

/-- A complex family bounded by twice the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_two_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ 2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  have htwo_majorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f) :=
    Summable.mul_left 2 hmajorant
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        2 * zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      htwo_majorant
      hbound

/-- A complex family bounded by the completed spectral majorant is summable. -/
theorem summable_complex_family_of_norm_le_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℂ)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f))
    (hbound :
      ∀ ι : ZetaPrimePowerIndex,
        ‖u ι‖ ≤ zetaCompletedPrimeSpectralCoordinateMajorant ι f) :
    Summable u := by
  exact
    Summable.of_norm_bounded
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeSpectralCoordinateMajorant ι f)
      hmajorant
      hbound

/-- Summability of the spectral majorant implies summability of the positive defect-square
coordinates. -/
theorem summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_two_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeDefectKernelPositiveCoordinate_le_spectralMajorant
          ι f)

/-- Summability of the spectral majorant implies summability of the oriented two-face
coordinates. -/
theorem summable_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (hmajorant :
      Summable
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant ι f)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    summable_complex_family_of_norm_le_spectralMajorant
      f
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)
      hmajorant
      (fun ι : ZetaPrimePowerIndex =>
        norm_zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_le_spectralMajorant
          ι f)

/-- Taking real parts commutes with the completed prime-power sum of positive defect
coordinates. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)) =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f) := by
  unfold zetaCompletedPrimeDefectKernelPositiveCoordinateTsum
  exact
    (Complex.tsum_re
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f)).symm

/-- Dagger commutes with the completed oriented prime-power sum. -/
theorem zetaCompletedPrimeTwoFaceGNSOrientedCoordinate_star_tsum
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        star (zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)) =
      star
        (∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f) := by
  exact
    (star_tsum
      (fun ι : ZetaPrimePowerIndex =>
        zetaCompletedPrimeTwoFaceGNSOrientedCoordinate ι f)).symm

/-- Finite completed prime defect-square windows expand as diagonal debt minus the
symmetrized two-face window. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_add_twoFaceWindow_eq_diagonalDebtWindow
    (N : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveWindow N f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow N f =
      zetaCompletedPrimeDefectKernelDiagonalDebtWindow N f := by
  unfold zetaCompletedPrimeDefectKernelPositiveWindow
  unfold zetaCompletedPrimeTwoFaceGNSMatrixCoefficientWindow
  unfold zetaCompletedPrimeDefectKernelDiagonalDebtWindow
  let s : Finset ZetaPrimePowerIndex := ZetaPrimePowerIndex.window N
  let P : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelPositiveCoordinate ι f
  let C : ZetaPrimePowerIndex → ℂ :=
    fun ι =>
      zetaCompletedPrimeSpectralAmplitudeIndex ι f *
        star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)
  let D : ZetaPrimePowerIndex → ℂ :=
    fun ι => zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f
  change (∑ ι in s, P ι) + ((∑ ι in s, C ι) + star (∑ ι in s, C ι)) =
    ∑ ι in s, D ι
  calc
    (∑ ι in s, P ι) + ((∑ ι in s, C ι) + star (∑ ι in s, C ι)) =
        (∑ ι in s, P ι) + ((∑ ι in s, C ι) + (∑ ι in s, star (C ι))) := by
      exact congrArg
        (fun z : ℂ => (∑ ι in s, P ι) + ((∑ ι in s, C ι) + z))
        (map_sum star C s)
    _ =
        ((∑ ι in s, P ι) + (∑ ι in s, C ι)) +
          (∑ ι in s, star (C ι)) := by
      exact add_assoc (∑ ι in s, P ι) (∑ ι in s, C ι) (∑ ι in s, star (C ι))
    _ =
        (∑ ι in s, P ι + C ι) + (∑ ι in s, star (C ι)) := by
      exact congrArg
        (fun z : ℂ => z + (∑ ι in s, star (C ι)))
        (Finset.sum_add_distrib.symm)
    _ =
        ∑ ι in s, (P ι + C ι) + star (C ι) := by
      exact Finset.sum_add_distrib.symm
    _ = ∑ ι in s, D ι := by
      exact Finset.sum_congr rfl
        (fun ι _ => by
          change
            zetaCompletedPrimeDefectKernelPositiveCoordinate ι f +
                (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
                  star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)) +
                star
                  (zetaCompletedPrimeSpectralAmplitudeIndex ι f *
                    star (zetaCompletedPrimeOppositeSpectralAmplitudeIndex ι f)) =
              zetaCompletedPrimeDefectKernelDiagonalDebtCoordinate ι f
          exact
            (zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
              ι f))

/-- The completed sum of negative symmetrized two-face coordinates is the completed prime
boundary coefficient.

This is now the owner completed-channel comparison: the boundary coefficient is defined from
the completed spectral-sample channel, and the coordinatewise two-face expression is only a
presentation of that channel. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  unfold zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient
  unfold zetaCompletedExplicitFormulaPrimePowerSpectralSampleContribution
  calc
    (∑' ι : ZetaPrimePowerIndex,
        -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          -((ZetaPrimePowerIndex.weight ι : ℂ) *
            (zetaCompletedExplicitFormulaPhi
                (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                (ZetaPrimePowerIndex.center ι) +
              star
                (zetaCompletedExplicitFormulaPhi
                  (ZetaAdmissibleFunction.convolutionAutocorrelation f)
                  (ZetaPrimePowerIndex.center ι)))) := by
      exact tsum_congr
        (fun ι : ZetaPrimePowerIndex =>
          (zetaCompletedPrimeSpectralSampleCoordinate_eq_neg_twoFaceBoundaryCoordinate
            ι f).symm)

/-- The completed symmetrized two-face cross-coordinate sum is the completed matrix
coefficient.

This is the unsigned form of
`zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient`, transported
through the explicit sign theorem for the completed boundary coefficient. -/
theorem zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
  have hboundary :
      (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f :=
    zetaCompletedPrimeTwoFaceGNSBoundaryCoordinate_tsum_eq_boundaryCoefficient f
  have hneg :
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
        ∑' ι : ZetaPrimePowerIndex,
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
    have htsum :
        (∑' ι : ZetaPrimePowerIndex,
            -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) :=
      tsum_neg
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
    calc
      - (∑' ι : ZetaPrimePowerIndex,
          -zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
          - (-(∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)) := by
        exact congrArg Neg.neg htsum
      _ =
          ∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f := by
        exact neg_neg
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
  have hmatrix :
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
    calc
      -zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f =
          -(-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
        exact congrArg Neg.neg
          (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
      _ = zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f := by
        exact neg_neg (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
  exact hneg.symm.trans
    ((congrArg Neg.neg hboundary).trans hmatrix)

/-- The completed coordinatewise defect expansion may be summed over all prime powers. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFaceCoordinate_tsum_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    (∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f +
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) =
      zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum f := by
  unfold zetaCompletedPrimeDefectKernelDiagonalDebtCoordinateTsum
  exact tsum_congr
    (fun ι : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
        ι f)

/-- The raw completed positive prime defect-kernel presentation is its coordinate sum. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsum_eq_positiveCoordinateTsum
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsum f =
      ∑' ι : ZetaPrimePowerIndex,
        zetaCompletedPrimeDefectKernelPositiveCoordinate ι f := by
  rfl

/-- The finite completed prime defect-square expansion passes to the completed prime-power
realization.

This is the completed transport theorem for the three prime channels: positive defect
square, symmetrized two-face coefficient, and diagonal debt.  It is not proved from
real-axis spectral-coordinate summability; the owner proof must pass through the finite
defect-square windows, the prime distribution transport, and the completed contour
realization. -/
theorem zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  unfold zetaCompletedPrimeDefectKernelPositiveForm
  unfold zetaCompletedPrimeDefectKernelDiagonalDebt
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  change (Df - Tf + T) - T + T = Df - Tf + T
  exact sub_add_cancel (Df - Tf + T) T

/-- The completed positive prime defect-kernel channel is the finite positive prime defect
form transported through the completed defect-square expansion. -/
theorem completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re
    (f : ZetaAdmissibleFunction) :
    completedPrimeDefectKernelPositiveChannel f =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  let Pc : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let Df : ℂ := zetaPrimeDefectKernelDiagonalDebt f
  let Tf : ℂ := zetaPrimeTwoFaceGNSMatrixCoefficient f
  let Tc : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  have hfinite :
      zetaPrimeDefectKernelPositiveForm f + Tf = Df :=
    zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  unfold completedPrimeDefectKernelPositiveChannel
  unfold zetaCompletedPrimeDefectKernelPositiveForm
  unfold zetaCompletedPrimeDefectKernelDiagonalDebt
  change Complex.re ((Df - Tf + Tc) - Tc) =
    Complex.re (zetaPrimeDefectKernelPositiveForm f)
  calc
    Complex.re ((Df - Tf + Tc) - Tc) =
        Complex.re (Df - Tf) := by
      exact congrArg Complex.re (add_sub_cancel_right (Df - Tf) Tc)
    _ = Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
      have hpositive : Df - Tf = zetaPrimeDefectKernelPositiveForm f := by
        calc
          Df - Tf = (zetaPrimeDefectKernelPositiveForm f + Tf) - Tf := by
            exact congrArg (fun z : ℂ => z - Tf) hfinite.symm
          _ = zetaPrimeDefectKernelPositiveForm f := by
            exact add_sub_cancel_right (zetaPrimeDefectKernelPositiveForm f) Tf
      exact congrArg Complex.re hpositive

/-- The completed positive prime defect-kernel channel is nonnegative. -/
theorem completedPrimeDefectKernelPositiveChannel_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ completedPrimeDefectKernelPositiveChannel f := by
  have hchannel :
      completedPrimeDefectKernelPositiveChannel f =
        Complex.re (zetaPrimeDefectKernelPositiveForm f) :=
    completedPrimeDefectKernelPositiveChannel_eq_finitePositiveForm_re f
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    hchannel.symm
    (zetaPrimeDefectKernelPositiveForm_re_nonnegative f)

/-- The completed symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) =
        Complex.im
          (∑' ι : ZetaPrimePowerIndex,
            zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_tsum_eq_matrixCoefficient
          f).symm
    _ =
        ∑' ι : ZetaPrimePowerIndex,
          Complex.im (zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f) := by
      exact Complex.tsum_im
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate ι f)
    _ = ∑' _ι : ZetaPrimePowerIndex, (0 : ℝ) := by
      exact tsum_congr
        (fun ι : ZetaPrimePowerIndex =>
          zetaCompletedPrimeTwoFaceGNSSymmetrizedCoordinate_im_eq_zero ι f)
    _ = 0 := by
      exact tsum_zero

/-- The completed prime two-face boundary coefficient is real-valued. -/
theorem zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) = 0 := by
  calc
    Complex.im (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f) =
        Complex.im (-zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact congrArg Complex.im
        (zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f)
    _ =
        -Complex.im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f) := by
      exact Complex.neg_im (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f)
    _ = -0 := by
      exact congrArg Neg.neg
        (zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f)
    _ = 0 := by
      exact neg_zero

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

/-- The archimedean Hermitian packet has zero prime coordinates. -/
theorem zetaArchimedeanHermitianPacketAsEnsemble_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaArchimedeanHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 := by
  unfold zetaArchimedeanHermitianPacketAsEnsemble
  unfold ZetaHermitianPacketEnsemble.single
  exact
    Finsupp.single_eq_of_ne
      (fun h : ZetaPacketLabel.archimedean = ZetaPacketLabel.prime p n =>
        ZetaPacketLabel.noConfusion h)

/-- The correction Hermitian packet has zero prime coordinates. -/
theorem zetaCorrectionHermitianPacketAsEnsemble_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCorrectionHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 := by
  unfold zetaCorrectionHermitianPacketAsEnsemble
  unfold ZetaHermitianPacketEnsemble.single
  exact
    Finsupp.single_eq_of_ne
      (fun h : ZetaPacketLabel.correction = ZetaPacketLabel.prime p n =>
        ZetaPacketLabel.noConfusion h)

/-- The completed Hermitian boundary defect has the same prime coordinates as its
prime packet component. -/
theorem zetaCompletedHermitianBoundaryDefect_prime_apply
    (p n : ℕ) (f : ZetaAdmissibleFunction) :
    zetaCompletedHermitianBoundaryDefect f (ZetaPacketLabel.prime p n) =
      zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) := by
  unfold zetaCompletedHermitianBoundaryDefect
  have harch :
      zetaArchimedeanHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 :=
    zetaArchimedeanHermitianPacketAsEnsemble_prime_apply p n f
  have hcorr :
      zetaCorrectionHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime p n) = 0 :=
    zetaCorrectionHermitianPacketAsEnsemble_prime_apply p n f
  calc
    (zetaPrimeHermitianPacketAsEnsemble f +
          zetaArchimedeanHermitianPacketAsEnsemble f +
          zetaCorrectionHermitianPacketAsEnsemble f)
        (ZetaPacketLabel.prime p n) =
        zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
          zetaArchimedeanHermitianPacketAsEnsemble f
            (ZetaPacketLabel.prime p n) +
          zetaCorrectionHermitianPacketAsEnsemble f
            (ZetaPacketLabel.prime p n) := by
      rfl
    _ =
        zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
          0 + 0 := by
      exact congrArg₂
        (fun a b : ℂ =>
          zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) +
            a + b)
        harch hcorr
    _ = zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) + 0 := by
      exact add_zero
        (zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) + 0)
    _ = zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n) := by
      exact add_zero
        (zetaPrimeHermitianPacketAsEnsemble f (ZetaPacketLabel.prime p n))

/-- The completed Hermitian boundary defect and its prime component have the same prime
Hermitian Gram. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_primeComponent
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      ZetaHermitianPacketEnsemble.primePacketGram
        (zetaPrimeHermitianPacketAsEnsemble f) := by
  exact
    ZetaHermitianPacketEnsemble.primePacketGram_eq_of_prime_coordinates
      (fun p n =>
        zetaCompletedHermitianBoundaryDefect_prime_apply p n f)

/-- The symmetrized real two-face completed boundary presentation. This is the unsigned
GNS matrix cross term.  The signed explicit-formula prime boundary channel is
`zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient`, related to this prime coordinate by the
explicit boundary-sign theorem. -/
noncomputable def zetaCompletedGNSSymmetrizedBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The positive completed GNS boundary presentation form.

This is a complex spectral presentation: its prime channel is the defect-square kernel and
the symmetrized two-face prime channel is only the expansion cross term.  The ordered-heart
scalar is owned separately by `completedBoundaryGNSNormSq`. -/
noncomputable def zetaCompletedGNSPositiveBoundaryPresentationForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeDefectKernelPositiveForm f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The real scalar attached to the positive completed GNS boundary presentation form. -/
noncomputable def zetaCompletedGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedGNSPositiveBoundaryPresentationForm f)

/-- The finite display-level positive GNS boundary presentation form.

This is the packet/GNS positive square presentation over the explicit finite prime support.
It is separate from the completed prime-power presentation, whose prime channel is a
completed `tsum`. -/
noncomputable def zetaFiniteGNSPositiveBoundaryPresentationForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeDefectKernelPositiveForm f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The real scalar attached to the finite positive GNS boundary presentation form. -/
noncomputable def zetaFiniteGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaFiniteGNSPositiveBoundaryPresentationForm f)

/-- The completed GNS diagonal-debt boundary face associated with the prime defect-square
expansion. -/
noncomputable def zetaCompletedGNSDiagonalDebtBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedPrimeDefectKernelDiagonalDebt f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- Compatibility alias for the symmetrized completed GNS boundary presentation.  This is the
completed cross-term surface, not the positive defect-kernel surface. -/
noncomputable def zetaCompletedGNSBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedGNSSymmetrizedBoundaryForm f

/-- The finite display-level symmetrized boundary presentation reconstructed by the finite
packet surface.  This is intentionally separate from the completed prime-power GNS form:
finite packet reconstruction does not by itself identify the finite display channel with the
completed prime-power `tsum`. -/
noncomputable def zetaFiniteGNSSymmetrizedBoundaryForm (f : ZetaAdmissibleFunction) : ℂ :=
  zetaPrimeTwoFaceGNSMatrixCoefficient f +
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)

/-- The positive completed GNS boundary presentation form unfolds to the positive prime defect
kernel plus the archimedean and correction Gram channels. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f =
      zetaCompletedPrimeDefectKernelPositiveForm f +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  rfl

/-- Scalar normal form for the positive completed GNS boundary presentation. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationScalar f =
      Complex.re (zetaCompletedPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  unfold zetaCompletedGNSPositiveBoundaryPresentationScalar
  unfold zetaCompletedGNSPositiveBoundaryPresentationForm
  change Complex.re (P + (A : ℂ) + (C : ℂ)) = Complex.re P + A + C
  calc
    Complex.re (P + (A : ℂ) + (C : ℂ)) =
        Complex.re (P + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (P + (A : ℂ)) (C : ℂ)
    _ = (Complex.re P + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re P (A : ℂ))
    _ = (Complex.re P + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re P + A + C := by
      rfl

/-- Scalar normal form for the finite positive GNS boundary presentation. -/
theorem zetaFiniteGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaFiniteGNSPositiveBoundaryPresentationScalar f =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) +
        ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) +
        ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) := by
  let P : ℂ := zetaPrimeDefectKernelPositiveForm f
  let A : ℝ :=
    ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  let C : ℝ :=
    ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f)
  unfold zetaFiniteGNSPositiveBoundaryPresentationScalar
  unfold zetaFiniteGNSPositiveBoundaryPresentationForm
  change Complex.re (P + (A : ℂ) + (C : ℂ)) = Complex.re P + A + C
  calc
    Complex.re (P + (A : ℂ) + (C : ℂ)) =
        Complex.re (P + (A : ℂ)) + Complex.re (C : ℂ) := by
      exact Complex.add_re (P + (A : ℂ)) (C : ℂ)
    _ = (Complex.re P + Complex.re (A : ℂ)) + Complex.re (C : ℂ) := by
      exact congrArg
        (fun x : ℝ => x + Complex.re (C : ℂ))
        (Complex.add_re P (A : ℂ))
    _ = (Complex.re P + A) + C := by
      exact congrArg₂ HAdd.hAdd
        (congrArg₂ HAdd.hAdd rfl (Complex.ofReal_re A))
        (Complex.ofReal_re C)
    _ = Complex.re P + A + C := by
      rfl

/-- The symmetrized completed GNS boundary form unfolds to the unsigned two-face prime cross
term plus the archimedean and correction Gram channels. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_eq_primeTwoFace_add_archimedean_add_correction
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f +
        (ZetaHermitianPacketEnsemble.archimedeanPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
        (ZetaHermitianPacketEnsemble.correctionPacketGram
          (zetaCompletedHermitianBoundaryDefect f) : ℂ) := by
  rfl

/-- The completed positive prime defect kernel plus its completed two-face cross term is the
completed prime diagonal debt. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f := by
  exact
    zetaCompletedPrimeDefectKernelPositiveWindow_expansion_passes_to_completedForms f

/-- Boundary-sign form of the completed prime defect expansion.

The explicit-formula boundary coefficient is the negative cross term, so the positive defect
kernel is obtained by adding diagonal debt to the boundary coefficient. -/
theorem zetaCompletedPrimeDefectKernelPositiveForm_eq_diagonalDebt_add_boundaryCoefficient
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectKernelPositiveForm f =
      zetaCompletedPrimeDefectKernelDiagonalDebt f +
        zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  have hcross : P + T = D :=
    zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  have hboundary :
      zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f = -T := by
    exact zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient_eq_neg_matrixCoefficient f
  change P =
    D + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f
  calc
    P = P + T + -T := by
      exact (add_neg_cancel_right P T).symm
    _ = P + T + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
      exact congrArg (fun z : ℂ => P + T + z) hboundary.symm
    _ = D + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f := by
      exact congrArg
        (fun z : ℂ => z + zetaCompletedPrimeTwoFaceGNSBoundaryCoefficient f)
        hcross

/-- Boundary-level prime defect expansion: the positive GNS presentation form plus the prime
two-face cross term equals the diagonal-debt boundary form. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_add_primeTwoFace_eq_diagonalDebtBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f +
        zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f =
      zetaCompletedGNSDiagonalDebtBoundaryForm f := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let C : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hprime : P + T = D := by
    exact zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  unfold zetaCompletedGNSPositiveBoundaryPresentationForm
  unfold zetaCompletedGNSDiagonalDebtBoundaryForm
  change (P + A + C) + T = D + A + C
  calc
    (P + A + C) + T = (P + T) + A + C := by
      ring
    _ = D + A + C := by
      exact congrArg (fun z : ℂ => z + A + C) hprime

/-- Full boundary-form expansion: adding the completed symmetrized boundary form to the positive
GNS presentation form replaces the prime cross term by diagonal debt and leaves a second copy
of the archimedean/correction square channels. -/
theorem zetaCompletedGNSPositiveBoundaryPresentationForm_add_symmetrized_eq_diagonalDebt_add_archCorrection
    (f : ZetaAdmissibleFunction) :
    zetaCompletedGNSPositiveBoundaryPresentationForm f +
        zetaCompletedGNSSymmetrizedBoundaryForm f =
      zetaCompletedGNSDiagonalDebtBoundaryForm f +
        ((ZetaHermitianPacketEnsemble.archimedeanPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ) +
          (ZetaHermitianPacketEnsemble.correctionPacketGram
            (zetaCompletedHermitianBoundaryDefect f) : ℂ)) := by
  let P : ℂ := zetaCompletedPrimeDefectKernelPositiveForm f
  let T : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let D : ℂ := zetaCompletedPrimeDefectKernelDiagonalDebt f
  let A : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let C : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hprime : P + T = D := by
    exact zetaCompletedPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt f
  unfold zetaCompletedGNSPositiveBoundaryPresentationForm
  unfold zetaCompletedGNSSymmetrizedBoundaryForm
  unfold zetaCompletedGNSDiagonalDebtBoundaryForm
  change (P + A + C) + (T + A + C) = (D + A + C) + (A + C)
  calc
    (P + A + C) + (T + A + C) =
        (P + T) + A + C + (A + C) := by
      ring
    _ = D + A + C + (A + C) := by
      exact congrArg (fun z : ℂ => z + A + C + (A + C)) hprime
    _ = (D + A + C) + (A + C) := by
      rfl

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

/-- The finite prime Hermitian packet Gram is the displayed sum of defect-amplitude
coordinate Grams over the explicit prime support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_primePacketGram_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaPrimeHermitianPacketAsEnsemble f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  let x : ZetaHermitianPacketEnsemble := zetaPrimeHermitianPacketAsEnsemble f
  let label : ℕ × ℕ → ZetaPacketLabel :=
    fun ℓ => ZetaPacketLabel.prime ℓ.1 ℓ.2
  have hsupport :
      x.support ⊆ zetaCompletedExplicitFormulaPrimeSupport.image label :=
    zetaPrimeHermitianPacketAsEnsemble_support_subset_prime_image f
  have hgram :
      ZetaHermitianPacketEnsemble.primePacketGram x =
        ∑ τ in zetaCompletedExplicitFormulaPrimeSupport.image label,
          match τ with
          | .prime _ _ => ZetaHermitianPacketEnsemble.coordinateGram (x τ)
          | _ => 0 :=
    ZetaHermitianPacketEnsemble.primePacketGram_eq_sum_of_support_subset
      x
      (zetaCompletedExplicitFormulaPrimeSupport.image label)
      hsupport
  have hinj :
      ∀ a ∈ zetaCompletedExplicitFormulaPrimeSupport,
        ∀ b ∈ zetaCompletedExplicitFormulaPrimeSupport,
          label a = label b → a = b := by
    intro a _ b _ hab
    rcases a with ⟨p, n⟩
    rcases b with ⟨q, r⟩
    unfold label at hab
    cases hab
    rfl
  have himage :
      (∑ τ in zetaCompletedExplicitFormulaPrimeSupport.image label,
          match τ with
          | .prime _ _ => ZetaHermitianPacketEnsemble.coordinateGram (x τ)
          | _ => 0) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram (x (label ℓ)) := by
    exact Finset.sum_image hinj
  have hcoords :
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram (x (label ℓ))) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram
            (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
    exact Finset.sum_congr rfl
      (fun ℓ hℓ => by
        exact congrArg ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_mem f ℓ hℓ))
  exact hgram.trans (himage.trans hcoords)

/-- The prime Hermitian packet Gram is the real positive prime defect-kernel form. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  exact
    (zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_primeComponent
      f).trans
      (zetaPrimeHermitianPacketAsEnsemble_primePacketGram_eq_finiteDefectAmplitudeSum
        f)

/-- The finite positive prime defect form has real part equal to the finite defect-amplitude
Gram sum. -/
theorem zetaPrimeDefectKernelPositiveForm_re_eq_finiteDefectAmplitudeSum
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelPositiveForm f) =
      ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
        ZetaHermitianPacketEnsemble.coordinateGram
          (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
  unfold zetaPrimeDefectKernelPositiveForm
  calc
    Complex.re
        (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          Complex.re (zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f) := by
      exact Complex.sum_re
        (fun ℓ : ℕ × ℕ =>
          zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f)
        zetaCompletedExplicitFormulaPrimeSupport
    _ =
        ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
          ZetaHermitianPacketEnsemble.coordinateGram
            (zetaPrimeHermitianDefectAmplitude ℓ.1 ℓ.2 f) := by
      exact Finset.sum_congr rfl
        (fun ℓ _ =>
          zetaPrimeDefectKernelPositiveCoordinate_re_eq_defectAmplitude_normSq
            ℓ.1 ℓ.2 f)

/-- The prime Hermitian packet Gram is the real positive prime defect-kernel form. -/
theorem zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finitePrimeDefectKernelPositiveForm_re
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.primePacketGram
        (zetaCompletedHermitianBoundaryDefect f) =
      Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
  exact
    (zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finiteDefectAmplitudeSum
      f).trans
      (zetaPrimeDefectKernelPositiveForm_re_eq_finiteDefectAmplitudeSum f).symm

/-- The Hermitian completed boundary-defect norm square is the finite positive GNS
presentation scalar. -/
theorem zetaCompletedHermitianBoundaryDefect_normSq_eq_finiteGNSPositiveBoundaryPresentationScalar
    (f : ZetaAdmissibleFunction) :
    ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f) =
      zetaFiniteGNSPositiveBoundaryPresentationScalar f := by
  let H : ZetaHermitianPacketEnsemble := zetaCompletedHermitianBoundaryDefect f
  let P : ℝ := Complex.re (zetaPrimeDefectKernelPositiveForm f)
  let A : ℝ := ZetaHermitianPacketEnsemble.archimedeanPacketGram H
  let C : ℝ := ZetaHermitianPacketEnsemble.correctionPacketGram H
  have hsplit :
      ZetaHermitianPacketEnsemble.normSq H =
        ZetaHermitianPacketEnsemble.primePacketGram H +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram H +
          ZetaHermitianPacketEnsemble.correctionPacketGram H :=
    ZetaHermitianPacketEnsemble.normSq_eq_prime_add_archimedean_add_correction H
  have hprime :
      ZetaHermitianPacketEnsemble.primePacketGram H = P :=
    zetaCompletedHermitianBoundaryDefect_primePacketGram_eq_finitePrimeDefectKernelPositiveForm_re
      f
  have hfinite :
      zetaFiniteGNSPositiveBoundaryPresentationScalar f = P + A + C :=
    zetaFiniteGNSPositiveBoundaryPresentationScalar_eq_primeDefect_add_archimedean_add_correction
      f
  calc
    ZetaHermitianPacketEnsemble.normSq (zetaCompletedHermitianBoundaryDefect f) =
        ZetaHermitianPacketEnsemble.normSq H := by
      rfl
    _ =
        ZetaHermitianPacketEnsemble.primePacketGram H +
          ZetaHermitianPacketEnsemble.archimedeanPacketGram H +
          ZetaHermitianPacketEnsemble.correctionPacketGram H := by
      exact hsplit
    _ = P + A + C := by
      exact congrArg
        (fun x : ℝ => x + A + C)
        hprime
    _ = zetaFiniteGNSPositiveBoundaryPresentationScalar f := by
      exact hfinite.symm

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
  unfold zetaCompletedExplicitFormulaPrimeConvolutionPairedContribution
  unfold zetaPrimeTwoFaceGNSMatrixCoefficient
  unfold zetaPrimeTwoFaceGNSOrientedCoefficient
  change
    (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ + star (C ℓ)) =
      (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ) +
        star (∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport, C ℓ)
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

/-- The finite realized boundary form is represented by the finite mixed symmetrized boundary
package: the prime channel is the finite two-face/GNS matrix coefficient, while the
archimedean and correction channels are one-face Hermitian squares. -/
theorem zetaCompletedBoundaryRealizedGram_eq_finiteGNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedBoundaryRealizedGram f =
      zetaFiniteGNSSymmetrizedBoundaryForm f := by
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
    _ = zetaFiniteGNSSymmetrizedBoundaryForm f := by
      unfold zetaFiniteGNSSymmetrizedBoundaryForm
      rfl

/-- Finite boundary reconstruction into the finite symmetrized real two-face presentation. -/
theorem zetaCompletedBoundaryReconstruction_pairedForm_eq_finiteGNSSymmetrizedBoundaryForm
    (f : ZetaAdmissibleFunction) :
    zetaCompletedPairedSpectralBoundaryForm f =
      zetaFiniteGNSSymmetrizedBoundaryForm f := by
  exact (zetaCompletedBoundaryReconstruction_pairedForm_eq_realizedGram f).trans
    (zetaCompletedBoundaryRealizedGram_eq_finiteGNSSymmetrizedBoundaryForm f)

/-- The completed mixed GNS boundary form is real-valued: the real prime channel is the
symmetrized two-face coefficient, and the remaining packet Gram coordinates are real
coercions. -/
theorem zetaCompletedGNSSymmetrizedBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedGNSSymmetrizedBoundaryForm f) = 0 := by
  let z : ℂ := zetaCompletedPrimeTwoFaceGNSMatrixCoefficient f
  let a : ℂ :=
    (ZetaHermitianPacketEnsemble.archimedeanPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  let c : ℂ :=
    (ZetaHermitianPacketEnsemble.correctionPacketGram
      (zetaCompletedHermitianBoundaryDefect f) : ℂ)
  have hz : Complex.im z = 0 := by
    exact zetaCompletedPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero f
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

/-- The finite display-level symmetrized boundary form is real-valued. -/
theorem zetaFiniteGNSSymmetrizedBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaFiniteGNSSymmetrizedBoundaryForm f) = 0 := by
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
  unfold zetaFiniteGNSSymmetrizedBoundaryForm
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

/-- The completed paired spectral boundary form is real-valued. -/
theorem zetaCompletedPairedSpectralBoundaryForm_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaCompletedPairedSpectralBoundaryForm f) = 0 := by
  have hform :
      zetaCompletedPairedSpectralBoundaryForm f =
        zetaFiniteGNSSymmetrizedBoundaryForm f :=
    zetaCompletedBoundaryReconstruction_pairedForm_eq_finiteGNSSymmetrizedBoundaryForm f
  exact (congrArg Complex.im hform).trans
    (zetaFiniteGNSSymmetrizedBoundaryForm_im_eq_zero f)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Data.Complex.BigOperators
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.AdmissiblePackets
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletionCorrection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.BoundaryChannels

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

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
    (zetaCompletedExplicitFormulaCorrectionContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))

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
    zetaCompletedExplicitFormulaCorrectionContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)

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
  zetaCompletedExplicitFormulaCorrectionContribution
    (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- The completed paired spectral boundary form. -/
noncomputable def zetaCompletedPairedSpectralBoundaryForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  (Finset.sum zetaCompletedExplicitFormulaPrimeSupport (fun ℓ : ℕ × ℕ =>
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)) +
        star
          (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
            star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)))) +
    (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f *
      star (zetaCompletedExplicitFormulaArchimedeanSpectralAmplitude f)) +
    zetaCompletedExplicitFormulaCorrectionContribution
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)

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
        exact Finset.sum_eq_single ℓ
          (fun m _ hm_ne => by
            exact Finsupp.single_eq_of_ne
              (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                  ZetaPacketLabel.prime ℓ.1 ℓ.2 => by
                match m, ℓ with
                | ⟨p, n⟩, ⟨q, r⟩ =>
                    cases hlabel
                    exact hm_ne rfl))
          (fun hnotmem => False.elim (hnotmem hℓ))
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
          exact Finsupp.single_eq_same

/-- The prime Hermitian finite-display packet is zero at explicit prime labels outside the
finite support. -/
theorem zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_not_mem
    (f : ZetaAdmissibleFunction) (ℓ : ℕ × ℕ)
    (hℓ : ℓ ∉ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaPrimeHermitianPacketAsEnsemble f
        (ZetaPacketLabel.prime ℓ.1 ℓ.2) = 0 := by
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
            exact Finsupp.single_eq_of_ne
              (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                  ZetaPacketLabel.prime ℓ.1 ℓ.2 => by
                match m, ℓ with
                | ⟨p, n⟩, ⟨q, r⟩ =>
                    cases hlabel
                    exact hℓ hm))

/-- The finite prime Hermitian packet has zero archimedean coordinate. -/
theorem zetaPrimeHermitianPacketAsEnsemble_archimedean_apply
    (f : ZetaAdmissibleFunction) :
    zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.archimedean = 0 := by
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
          exact Finsupp.single_eq_of_ne
            (fun hlabel : ZetaPacketLabel.prime m.1 m.2 =
                ZetaPacketLabel.archimedean =>
              ZetaPacketLabel.noConfusion hlabel))

/-- The finite prime Hermitian packet has zero correction coordinate. -/
theorem zetaPrimeHermitianPacketAsEnsemble_correction_apply
    (f : ZetaAdmissibleFunction) :
    zetaPrimeHermitianPacketAsEnsemble f ZetaPacketLabel.correction = 0 := by
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
      exact
        if hpair : (p, n) ∈ zetaCompletedExplicitFormulaPrimeSupport then
          Finset.mem_image.mpr ⟨(p, n), hpair, rfl⟩
        else
          have hzero :
              zetaPrimeHermitianPacketAsEnsemble f
                (ZetaPacketLabel.prime p n) = 0 :=
            zetaPrimeHermitianPacketAsEnsemble_prime_apply_of_not_mem
              f (p, n) hpair
          have hnonzero :
              zetaPrimeHermitianPacketAsEnsemble f
                (ZetaPacketLabel.prime p n) ≠ 0 :=
            Finsupp.mem_support_iff.mp hlabel
          False.elim (hnonzero hzero)
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

/-- Every label in the current finite explicit prime support has first coordinate below `2`. -/
theorem zetaCompletedExplicitFormulaPrimeSupport_fst_lt_two
    {ℓ : ℕ × ℕ}
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    ℓ.1 < 2 := by
  have hexp : Real.exp 0 = 1 := by
    exact Real.exp_zero
  have hceil : Nat.ceil (Real.exp 0) = 1 := by
    exact (congrArg Nat.ceil hexp).trans Nat.ceil_one
  have hrange :
      Finset.range (Nat.ceil (Real.exp 0) + 1) = Finset.range 2 := by
    exact congrArg
      (fun m : ℕ => Finset.range (m + 1))
      hceil
  have hproduct :
      ℓ.1 ∈ Finset.range (Nat.ceil (Real.exp 0) + 1) ∧
        ℓ.2 ∈ Finset.range (Nat.ceil (Real.exp 0) + 1) := by
    exact Finset.mem_product.mp hℓ
  have hmem_two : ℓ.1 ∈ Finset.range 2 := by
    exact Eq.subst
      (motive := fun s : Finset ℕ => ℓ.1 ∈ s)
      hrange
      hproduct.1
  exact Finset.mem_range.mp hmem_two

/-- Labels in the current finite explicit prime support are nongenuine prime labels. -/
theorem zetaCompletedExplicitFormulaPrimeSupport_not_prime_fst
    {ℓ : ℕ × ℕ}
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    ¬ Nat.Prime ℓ.1 := by
  intro hp
  have hlt : ℓ.1 < 2 :=
    zetaCompletedExplicitFormulaPrimeSupport_fst_lt_two hℓ
  have hle : 2 ≤ ℓ.1 :=
    Nat.Prime.two_le hp
  exact (not_lt_of_ge hle) hlt

/-- The explicit-support prime spectral amplitude vanishes on the current finite support. -/
theorem zetaCompletedExplicitFormulaPrimeSpectralAmplitude_eq_zero_of_mem_support
    {ℓ : ℕ × ℕ} (f : ZetaAdmissibleFunction)
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f = 0 := by
  have hnot_prime :
      ¬ Nat.Prime ℓ.1 :=
    zetaCompletedExplicitFormulaPrimeSupport_not_prime_fst hℓ
  have hweight :
      zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 = 0 :=
    zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_not_prime
      ℓ.1 ℓ.2 hnot_prime
  have hsqrt :
      zetaCompletedExplicitFormulaPrimeSqrtWeight ℓ.1 ℓ.2 = 0 :=
    zetaCompletedExplicitFormulaPrimeSqrtWeight_eq_zero_of_weight_eq_zero
      ℓ.1 ℓ.2 hweight
  unfold zetaCompletedExplicitFormulaPrimeSpectralAmplitude
  exact Eq.trans
    (congrArg
      (fun r : ℝ =>
        (r : ℂ) * zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f)
      hsqrt)
    (zero_mul (zetaCompletedPrimeHermitianSeedAmplitude ℓ.1 ℓ.2 f))

/-- The explicit-support opposite prime spectral amplitude vanishes on the current finite
support. -/
theorem zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude_eq_zero_of_mem_support
    {ℓ : ℕ × ℕ} (f : ZetaAdmissibleFunction)
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f = 0 := by
  have hnot_prime :
      ¬ Nat.Prime ℓ.1 :=
    zetaCompletedExplicitFormulaPrimeSupport_not_prime_fst hℓ
  have hweight :
      zetaCompletedExplicitFormulaPrimeWeight ℓ.1 ℓ.2 = 0 :=
    zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_not_prime
      ℓ.1 ℓ.2 hnot_prime
  have hsqrt :
      zetaCompletedExplicitFormulaPrimeSqrtWeight ℓ.1 ℓ.2 = 0 :=
    zetaCompletedExplicitFormulaPrimeSqrtWeight_eq_zero_of_weight_eq_zero
      ℓ.1 ℓ.2 hweight
  unfold zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
  exact Eq.trans
    (congrArg
      (fun r : ℝ =>
        (r : ℂ) * zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f)
      hsqrt)
    (zero_mul (zetaCompletedPrimeBoundaryRealizedNegativeFace ℓ.1 ℓ.2 f))

/-- The explicit-support diagonal-debt coordinate vanishes after completed lower-weight
normalization. -/
theorem zetaPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_mem_support
    {ℓ : ℕ × ℕ} (f : ZetaAdmissibleFunction)
    (hℓ : ℓ ∈ zetaCompletedExplicitFormulaPrimeSupport) :
    zetaPrimeDefectKernelDiagonalDebtCoordinate ℓ.1 ℓ.2 f = 0 := by
  have hpos :
      zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f = 0 :=
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude_eq_zero_of_mem_support f hℓ
  have hneg :
      zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f = 0 :=
    zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude_eq_zero_of_mem_support f hℓ
  unfold zetaPrimeDefectKernelDiagonalDebtCoordinate
  calc
    zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f) +
        zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f *
          star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) =
        0 * star 0 + 0 * star 0 := by
      exact congrArg₂ Add.add
        (congrArg₂ Mul.mul hpos (congrArg star hpos))
        (congrArg₂ Mul.mul hneg (congrArg star hneg))
    _ = 0 + 0 * star 0 := by
      exact congrArg (fun z : ℂ => z + 0 * star 0) (zero_mul (star 0 : ℂ))
    _ = 0 + 0 := by
      exact congrArg (fun z : ℂ => 0 + z) (zero_mul (star 0 : ℂ))
    _ = 0 := by
      exact add_zero 0

/-- The displayed prime diagonal debt vanishes after the completed lower-weight
normalization. -/
theorem zetaPrimeDefectKernelDiagonalDebt_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    zetaPrimeDefectKernelDiagonalDebt f = 0 := by
  unfold zetaPrimeDefectKernelDiagonalDebt
  exact Finset.sum_eq_zero
    (fun ℓ hℓ =>
      zetaPrimeDefectKernelDiagonalDebtCoordinate_eq_zero_of_mem_support f hℓ)

/-- Real form of the completed lower-weight normalization for the displayed prime diagonal
debt. -/
theorem zetaPrimeDefectKernelDiagonalDebt_re_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeDefectKernelDiagonalDebt f) = 0 := by
  exact Eq.trans
    (congrArg Complex.re
      (zetaPrimeDefectKernelDiagonalDebt_eq_zero_of_completedLowerWeightNormalization f))
    Complex.zero_re

/-- The displayed finite-support oriented two-face coefficient vanishes under the current
completed lower-weight normalization. -/
theorem zetaPrimeTwoFaceGNSOrientedCoefficient_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    zetaPrimeTwoFaceGNSOrientedCoefficient f = 0 := by
  unfold zetaPrimeTwoFaceGNSOrientedCoefficient
  exact Finset.sum_eq_zero
    (fun ℓ hℓ => by
      have hpos :
          zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f = 0 :=
        zetaCompletedExplicitFormulaPrimeSpectralAmplitude_eq_zero_of_mem_support
          f hℓ
      calc
        zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
            star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) =
            0 *
              star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f) := by
          exact congrArg
            (fun z : ℂ =>
              z *
                star
                  (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
                    ℓ.1 ℓ.2 f))
            hpos
        _ = 0 := by
          exact zero_mul
            (star
              (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude
                ℓ.1 ℓ.2 f)))

/-- The displayed finite-support two-face/GNS matrix coefficient vanishes under the current
completed lower-weight normalization. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    zetaPrimeTwoFaceGNSMatrixCoefficient f = 0 := by
  have horiented :
      zetaPrimeTwoFaceGNSOrientedCoefficient f = 0 :=
    zetaPrimeTwoFaceGNSOrientedCoefficient_eq_zero_of_completedLowerWeightNormalization
      f
  unfold zetaPrimeTwoFaceGNSMatrixCoefficient
  calc
    zetaPrimeTwoFaceGNSOrientedCoefficient f +
        star (zetaPrimeTwoFaceGNSOrientedCoefficient f) =
        0 + star 0 := by
      exact congrArg₂ HAdd.hAdd horiented (congrArg star horiented)
    _ = 0 + 0 := by
      exact congrArg (fun z : ℂ => 0 + z) (star_zero ℂ)
    _ = 0 := by
      exact add_zero 0

/-- Real form of the completed lower-weight normalization for the displayed finite-support
two-face/GNS matrix coefficient. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_re_eq_zero_of_completedLowerWeightNormalization
    (f : ZetaAdmissibleFunction) :
    Complex.re (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  exact Eq.trans
    (congrArg Complex.re
      (zetaPrimeTwoFaceGNSMatrixCoefficient_eq_zero_of_completedLowerWeightNormalization f))
    Complex.zero_re

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

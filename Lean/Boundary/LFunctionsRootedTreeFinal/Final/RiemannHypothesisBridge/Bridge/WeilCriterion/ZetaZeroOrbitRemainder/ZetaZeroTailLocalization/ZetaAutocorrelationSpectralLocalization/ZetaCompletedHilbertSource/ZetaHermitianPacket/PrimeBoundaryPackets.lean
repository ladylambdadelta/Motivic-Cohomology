import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.AdmissiblePackets

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

/-- The positive prime defect kernel over the explicit prime support. -/
noncomputable def zetaPrimeDefectKernelPositiveForm
    (f : ZetaAdmissibleFunction) : ℂ :=
  ∑ ℓ in zetaCompletedExplicitFormulaPrimeSupport,
    zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f

/-- The additive cancellation at the end of the one-coordinate defect-square expansion. -/
private theorem defect_square_cross_cancel
    (x y z w : ℂ) :
    ((x - y) - (z - w)) + (z + y) = x + w :=
  calc
    ((x - y) - (z - w)) + (z + y) =
        ((x - y) + (w - z)) + (z + y) := by
      exact congrArg (fun t : ℂ => t + (z + y))
        (calc
          (x - y) - (z - w) = (x - y) + -(z - w) := by
            exact sub_eq_add_neg (x - y) (z - w)
          _ = (x - y) + (w - z) := by
            exact congrArg (fun t : ℂ => (x - y) + t) (neg_sub z w))
    _ = (x - y) + ((w - z) + (z + y)) := by
      exact add_assoc (x - y) (w - z) (z + y)
    _ = (x - y) + (w + y) := by
      exact congrArg (fun t : ℂ => (x - y) + t)
        (calc
          (w - z) + (z + y) = ((w - z) + z) + y := by
            exact (add_assoc (w - z) z y).symm
          _ = w + y := by
            exact congrArg (fun t : ℂ => t + y) (sub_add_cancel w z))
    _ = (x - y) + (y + w) := by
      exact congrArg (fun t : ℂ => (x - y) + t) (add_comm w y)
    _ = ((x - y) + y) + w := by
      exact (add_assoc (x - y) y w).symm
    _ = x + w := by
      exact congrArg (fun t : ℂ => t + w) (sub_add_cancel x y)

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
      exact defect_square_cross_cancel
        (a * star a) (b * star a) (a * star b) (b * star b)

/-- The positive prime defect kernel plus its two-face cross term is the prime diagonal debt. -/
theorem zetaPrimeDefectKernelPositiveForm_add_twoFace_eq_diagonalDebt
    (f : ZetaAdmissibleFunction) :
      zetaPrimeDefectKernelPositiveForm f +
        zetaPrimeTwoFaceGNSMatrixCoefficient f =
      zetaPrimeDefectKernelDiagonalDebt f := by
  let s : Finset (ℕ × ℕ) := zetaCompletedExplicitFormulaPrimeSupport
  let P : ℕ × ℕ → ℂ :=
    fun ℓ => zetaPrimeDefectKernelPositiveCoordinate ℓ.1 ℓ.2 f
  let C : ℕ × ℕ → ℂ :=
    fun ℓ =>
      zetaCompletedExplicitFormulaPrimeSpectralAmplitude ℓ.1 ℓ.2 f *
        star (zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude ℓ.1 ℓ.2 f)
  let D : ℕ × ℕ → ℂ :=
    fun ℓ => zetaPrimeDefectKernelDiagonalDebtCoordinate ℓ.1 ℓ.2 f
  calc
    (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + star (∑ ℓ in s, C ℓ)) =
        (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + (∑ ℓ in s, star (C ℓ))) := by
      exact congrArg
        (fun z : ℂ =>
          (∑ ℓ in s, P ℓ) + ((∑ ℓ in s, C ℓ) + z))
        (map_sum star s C)
    _ =
        ((∑ ℓ in s, P ℓ) + (∑ ℓ in s, C ℓ)) +
          (∑ ℓ in s, star (C ℓ)) := by
      exact add_assoc (∑ ℓ in s, P ℓ) (∑ ℓ in s, C ℓ) (∑ ℓ in s, star (C ℓ))
    _ =
        (∑ ℓ in s, P ℓ + C ℓ) + (∑ ℓ in s, star (C ℓ)) := by
      exact congrArg
        (fun z : ℂ => z + (∑ ℓ in s, star (C ℓ)))
        (Finset.sum_add_distrib.symm)
    _ =
        ∑ ℓ in s, (P ℓ + C ℓ) + star (C ℓ) := by
      exact Finset.sum_add_distrib.symm
    _ = ∑ ℓ in s, D ℓ := by
      exact Finset.sum_congr rfl
        (fun ℓ _ =>
          zetaPrimeDefectKernelPositiveCoordinate_add_twoFace_eq_diagonalDebtCoordinate
            ℓ.1 ℓ.2 f)

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
  exact complex_re_mul_star_self_nonnegative_hermitianPacket (a - b)

/-- The positive prime defect-kernel form has nonnegative real part. -/
theorem zetaPrimeDefectKernelPositiveForm_re_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ Complex.re (zetaPrimeDefectKernelPositiveForm f) := by
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
  exact complex_re_mul_star_self_eq_normSq_hermitianPacket
    (zetaCompletedExplicitFormulaPrimeSpectralAmplitude p n f -
      zetaCompletedExplicitFormulaPrimeOppositeSpectralAmplitude p n f)

/-- The symmetrized prime two-face/GNS matrix coefficient is real-valued. -/
theorem zetaPrimeTwoFaceGNSMatrixCoefficient_im_eq_zero
    (f : ZetaAdmissibleFunction) :
    Complex.im (zetaPrimeTwoFaceGNSMatrixCoefficient f) = 0 := by
  let z : ℂ := zetaPrimeTwoFaceGNSOrientedCoefficient f
  calc
    Complex.im (z + star z) = Complex.im z + Complex.im (star z) := by
      exact Complex.add_im z (star z)
    _ = Complex.im z + -Complex.im z := by
      exact congrArg (fun x : ℝ => Complex.im z + x) (Complex.conj_im z)
    _ = 0 := by
      exact add_neg_cancel (Complex.im z)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

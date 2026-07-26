import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.Base
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.PacketBasics
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.OwnerParts.PrimePowerCoordinates

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

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
  exact
    if hp : Nat.Prime p then
      if hn : n ≠ 0 then
        have hp_two : 2 ≤ p := Nat.Prime.two_le hp
        have htwo_pos_nat : (0 : ℕ) < 2 :=
          Nat.zero_lt_succ 1
        have hp_pos_nat : 0 < p := lt_of_lt_of_le htwo_pos_nat hp_two
        have hp_one_real : (1 : ℝ) ≤ p := by
          have hp_one_cast :
              ((1 : ℕ) : ℝ) ≤ (p : ℝ) :=
            Nat.cast_le (α := ℝ).mpr (Nat.succ_le_of_lt hp_pos_nat)
          have hone_cast : ((1 : ℕ) : ℝ) = (1 : ℝ) :=
            Nat.cast_one
          exact Eq.subst
            (motive := fun x : ℝ => x ≤ (p : ℝ))
            hone_cast
            hp_one_cast
        have hlog : 0 ≤ Real.log p := Real.log_nonneg hp_one_real
        have hsqrt : 0 ≤ Real.sqrt (p ^ n) := Real.sqrt_nonneg _
        have hquot : 0 ≤ Real.log p / Real.sqrt (p ^ n) :=
          div_nonneg hlog hsqrt
        have hweight :
            zetaCompletedExplicitFormulaPrimeWeight p n =
              Real.log p / Real.sqrt (p ^ n) := by
          exact (if_pos hp).trans (if_pos hn)
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          hweight.symm
          hquot
      else
        have hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
          exact (if_pos hp).trans (if_neg hn)
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          hweight.symm
          (le_refl 0)
    else
      have hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
        exact if_neg hp
      Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        (le_refl 0)

/-- The square-root prime weight squares back to the completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeSqrtWeight_mul_self (p n : ℕ) :
    zetaCompletedExplicitFormulaPrimeSqrtWeight p n *
      zetaCompletedExplicitFormulaPrimeSqrtWeight p n =
        zetaCompletedExplicitFormulaPrimeWeight p n := by
  exact (pow_two (Real.sqrt (zetaCompletedExplicitFormulaPrimeWeight p n))).symm.trans
    (Real.sq_sqrt (zetaCompletedExplicitFormulaPrimeWeight_nonnegative p n))

/-- Non-prime labels have zero completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_not_prime
    (p n : ℕ) (hp : ¬ Nat.Prime p) :
    zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
  exact if_neg hp

/-- Zero-exponent labels have zero completed prime weight. -/
theorem zetaCompletedExplicitFormulaPrimeWeight_eq_zero_of_zero_exponent
    (p n : ℕ) (hp : Nat.Prime p) (hn : ¬ n ≠ 0) :
    zetaCompletedExplicitFormulaPrimeWeight p n = 0 := by
  exact (if_pos hp).trans (if_neg hn)

/-- A zero completed prime weight has zero square-root weight. -/
theorem zetaCompletedExplicitFormulaPrimeSqrtWeight_eq_zero_of_weight_eq_zero
    (p n : ℕ)
    (hweight : zetaCompletedExplicitFormulaPrimeWeight p n = 0) :
    zetaCompletedExplicitFormulaPrimeSqrtWeight p n = 0 := by
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
      exact congrArg Neg.neg (neg_mul Complex.I (a : ℂ))
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
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair g.seed a
  have hneg :
      zetaCompletedAutocorrelationPrimeNegativeFace p n g =
        φ (-(a : ℂ)) * star (φ (a : ℂ)) := by
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

/-- The correction spectral coordinate is the centered pole amplitude evaluated on the
seed transform. Its Hermitian Gram is the centered-pole correction evaluated on the
autocorrelation probe. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionSpectralAmplitude
    (f : ZetaAdmissibleFunction) : ℂ :=
  (Boundary.LFunctions.zetaCompletionCorrectionPacketCoordinate : ℂ) *
    zetaCompletedExplicitFormulaPhi f 0

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

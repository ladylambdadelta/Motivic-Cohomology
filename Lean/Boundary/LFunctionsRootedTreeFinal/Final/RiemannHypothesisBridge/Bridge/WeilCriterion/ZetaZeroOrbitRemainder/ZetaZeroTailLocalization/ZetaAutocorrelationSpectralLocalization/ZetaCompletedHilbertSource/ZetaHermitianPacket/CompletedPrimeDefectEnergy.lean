import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimePowerPackets

/-!
# Genuine completed prime defect energy

The completed prime defect energy is owned by the genuine prime-power index.
The finite display packet is not used in this definition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The real square coordinate at one genuine completed prime-power index. -/
noncomputable def zetaCompletedPrimeDefectEnergyCoordinate
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaCompletedPrimeDefectKernelPositiveCoordinate index f)

/-- One real completed prime defect coordinate is the norm-square of the
difference of its two weighted faces. -/
theorem zetaCompletedPrimeDefectEnergyCoordinate_eq_normSq
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    zetaCompletedPrimeDefectEnergyCoordinate index f =
      Complex.normSq
        (zetaCompletedPrimeSpectralAmplitudeIndex index f -
          zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f) :=
  let difference : ℂ :=
    zetaCompletedPrimeSpectralAmplitudeIndex index f -
      zetaCompletedPrimeOppositeSpectralAmplitudeIndex index f
  complex_re_mul_star_self_eq_normSq_hermitianPacket difference

/-- Every genuine completed prime defect coordinate is nonnegative. -/
theorem zetaCompletedPrimeDefectEnergyCoordinate_nonnegative
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeDefectEnergyCoordinate index f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinate_re_nonnegative index f

/-- The genuine completed prime defect energy. -/
noncomputable def zetaCompletedPrimeDefectEnergy
    (f : ZetaAdmissibleFunction) : ℝ :=
  ∑' index : ZetaPrimePowerIndex,
    zetaCompletedPrimeDefectEnergyCoordinate index f

/-- The genuine completed prime defect energy is nonnegative. -/
theorem zetaCompletedPrimeDefectEnergy_nonnegative
    (f : ZetaAdmissibleFunction) :
    0 ≤ zetaCompletedPrimeDefectEnergy f :=
  tsum_nonneg
    (fun index : ZetaPrimePowerIndex =>
      zetaCompletedPrimeDefectEnergyCoordinate_nonnegative index f)

/-- Summability allows the real genuine energy to be read as the real part of
the complex completed defect-square series. -/
theorem zetaCompletedPrimeDefectEnergy_eq_coordinateTsumRe_of_summable
    (f : ZetaAdmissibleFunction)
    (coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f)) :
    zetaCompletedPrimeDefectEnergy f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  zetaCompletedPrimeDefectKernelPositiveCoordinate_re_tsum_eq_coordinateTsum_re
    f coordinateSummable

/-- Spectral-majorant summability identifies the genuine energy with the real
part of the complex completed defect-square series. -/
theorem zetaCompletedPrimeDefectEnergy_eq_coordinateTsumRe_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (majorantSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    zetaCompletedPrimeDefectEnergy f =
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
  have coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f) :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f majorantSummable
  zetaCompletedPrimeDefectEnergy_eq_coordinateTsumRe_of_summable
    f coordinateSummable

/-- Vanishing of the genuine completed prime defect energy annihilates the raw
completed positive coordinate real presentation. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_defectEnergy_zero
    (f : ZetaAdmissibleFunction)
    (coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f))
    (henergy :
      zetaCompletedPrimeDefectEnergy f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let henergyCoordinate :
      zetaCompletedPrimeDefectEnergy f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    zetaCompletedPrimeDefectEnergy_eq_coordinateTsumRe_of_summable
      f coordinateSummable
  henergyCoordinate.symm.trans henergy

/-- Spectral-majorant summability transports genuine completed prime defect
energy vanishing to the raw completed positive coordinate real presentation. -/
theorem zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_spectralMajorant_and_defectEnergy_zero
    (f : ZetaAdmissibleFunction)
    (majorantSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f))
    (henergy :
      zetaCompletedPrimeDefectEnergy f = 0) :
    zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f) :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f majorantSummable
  zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe_eq_zero_of_defectEnergy_zero
    f coordinateSummable henergy

/-- Under summability, genuine completed prime defect-energy vanishing is
equivalent to raw completed positive-coordinate annihilation. -/
theorem zetaCompletedPrimeDefectEnergy_eq_zero_iff_positiveCoordinateTsumRe_eq_zero_of_summable
    (f : ZetaAdmissibleFunction)
    (coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f)) :
    zetaCompletedPrimeDefectEnergy f = 0 ↔
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let henergyCoordinate :
      zetaCompletedPrimeDefectEnergy f =
        zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f :=
    zetaCompletedPrimeDefectEnergy_eq_coordinateTsumRe_of_summable
      f coordinateSummable
  Iff.intro
    (fun henergy =>
      henergyCoordinate.symm.trans henergy)
    (fun hpositive =>
      henergyCoordinate.trans hpositive)

/-- Spectral-majorant summability identifies genuine completed prime
defect-energy vanishing with raw completed positive-coordinate annihilation. -/
theorem zetaCompletedPrimeDefectEnergy_eq_zero_iff_positiveCoordinateTsumRe_eq_zero_of_spectralMajorant
    (f : ZetaAdmissibleFunction)
    (majorantSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeSpectralCoordinateMajorant index f)) :
    zetaCompletedPrimeDefectEnergy f = 0 ↔
      zetaCompletedPrimeDefectKernelPositiveCoordinateTsumRe f = 0 :=
  let coordinateSummable :
      Summable
        (fun index : ZetaPrimePowerIndex =>
          zetaCompletedPrimeDefectKernelPositiveCoordinate index f) :=
    summable_zetaCompletedPrimeDefectKernelPositiveCoordinate_of_spectralMajorant
      f majorantSummable
  zetaCompletedPrimeDefectEnergy_eq_zero_iff_positiveCoordinateTsumRe_eq_zero_of_summable
    f coordinateSummable

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

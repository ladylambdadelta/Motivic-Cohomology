import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.CompletedPrimeDiagonalDebtWindowOwnerParts.PrimeAmplitudeBesselSourceParts.WeightedNormMajorant

/-!
# Completed prime weighted norm-summability source

This file owns the Hilbert-frame norm-summability input for the completed
weighted prime-center sampling stream.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Completed weighted prime-center sampling coordinates are equal to their
real norms. -/
theorem completedWeightedPrimeSampling_norm_eq_self_hilbertFrame
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f‖ =
      completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f :=
  Real.norm_of_nonneg
    (completedAutocorrelationSpectralTransform_weightedPrimeSampling_nonnegative
      index f)

/-- The second real norm around a nonnegative weighted sample does not change
the norm value. -/
theorem completedWeightedPrimeSampling_norm_norm_eq_norm_hilbertFrame
    (index : ZetaPrimePowerIndex) (f : ZetaAdmissibleFunction) :
    ‖‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f‖‖ =
      ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f‖ :=
  Real.norm_of_nonneg
    (norm_nonneg
      (completedAutocorrelationSpectralTransform_weightedPrimeSampling
        index f))

/-- The Hilbert-frame majorant bounds the real norm stream. -/
theorem completedWeightedPrimeSampling_norm_le_majorant_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℝ)
    (hu :
      Summable u ∧
        (∀ index : ZetaPrimePowerIndex,
          0 ≤ u index) ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f‖ ≤ u index)
    (index : ZetaPrimePowerIndex) :
    ‖‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
      index f‖‖ ≤ u index :=
  Eq.subst
    (motive := fun value : ℝ => value ≤ u index)
    (completedWeightedPrimeSampling_norm_norm_eq_norm_hilbertFrame
      index f).symm
    (hu.right.right index)

/-- A completed weighted prime-sampling majorant gives norm summability. -/
theorem completedWeightedPrimeSampling_norm_summable_of_majorant_hilbertFrame
    (f : ZetaAdmissibleFunction)
    (u : ZetaPrimePowerIndex → ℝ)
    (hu :
      Summable u ∧
        (∀ index : ZetaPrimePowerIndex,
          0 ≤ u index) ∧
        ∀ index : ZetaPrimePowerIndex,
          ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
            index f‖ ≤ u index) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f‖) :=
  Summable.of_norm_bounded
    u
    hu.left
    (completedWeightedPrimeSampling_norm_le_majorant_hilbertFrame
      f u hu)

/-- Hilbert-frame source norm-summability for completed weighted prime-center
sampling. -/
theorem completedWeightedPrimeSampling_norm_summable_hilbertFrame_source
    (f : ZetaAdmissibleFunction) :
    Summable
      (fun index : ZetaPrimePowerIndex =>
        ‖completedAutocorrelationSpectralTransform_weightedPrimeSampling
          index f‖) :=
  match completedWeightedPrimeSamplingNormMajorant_source f with
  | ⟨u, hu⟩ =>
      completedWeightedPrimeSampling_norm_summable_of_majorant_hilbertFrame
        f u hu

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

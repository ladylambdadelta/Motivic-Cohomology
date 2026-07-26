import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.CarrierTransport.OwnerParts.Part03_MultiplicityTransport

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The image of carrier zeros in a closed disk lies in the completed-zero disk. -/
theorem carrierZeroToCompletedZero_image_closedDisk_subset
    (R : ℝ) :
    carrierZeroToCompletedZero ''
        centeredCompletedZetaZeroCarrierZerosInClosedDisk R ⊆
      completedZerosInCenteredClosedDisk R := by
  intro ρ hρ
  exact
    match hρ with
    | ⟨z, hzmem, hzρ⟩ =>
        Eq.subst
          (motive := fun y : {ρ : ℂ // ZetaCompletedZero ρ} =>
            y ∈ completedZerosInCenteredClosedDisk R)
          hzρ
          (carrierZeroToCompletedZero_mem_closedDisk R z hzmem)

/-- The image of carrier zeros in a closed disk is finite. -/
theorem finite_carrierZeroToCompletedZero_image_closedDisk
    (R : ℝ) :
    (carrierZeroToCompletedZero ''
      centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite := by
  exact Set.Finite.subset
    (finite_completedZerosInCenteredClosedDisk R)
    (carrierZeroToCompletedZero_image_closedDisk_subset R)

/-- The centered entire zero-carrier has only finitely many zeros in every
ordinary closed disk. This is the local-finiteness part of the finite-order
Jensen package for the cleared entire divisor. -/
theorem finite_centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) :
    (centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite := by
  exact Set.Finite.of_finite_image
    (finite_carrierZeroToCompletedZero_image_closedDisk R)
    (fun z hz w hw hzw => carrierZeroToCompletedZero_injective hzw)

/-- Finite carrier closed disks make the carrier multiplicity summand summable. -/
theorem summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_of_finite_closedDisk
    (R : ℝ) :
    Summable
      (fun z : CenteredCompletedZetaZeroCarrierZero =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z) := by
  exact summable_of_finite_support_real
    (fun z : CenteredCompletedZetaZeroCarrierZero =>
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)
    (centeredCompletedZetaZeroCarrierZerosInClosedDisk R)
    (finite_centeredCompletedZetaZeroCarrierZerosInClosedDisk R)
    (centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_zero_of_not_mem R)

/-- Carrier closed-disk multiplicity summands are summable. -/
theorem summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand
    (R : ℝ) :
    Summable
      (fun z : CenteredCompletedZetaZeroCarrierZero =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z) := by
  exact
    summable_centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_of_finite_closedDisk R

/-- Completed-zero closed-disk counting is dominated by the carrier count once the carrier
summand is known to be summable. -/
theorem completedZeroMultiplicityClosedDisk_tsum_eq_carrierPullback_tsum
    (R : ℝ) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        completedZeroMultiplicityClosedDiskSummand R ρ) =
      ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
          (completedZeroToCarrierZero ρ) := by
  exact tsum_congr
    (fun ρ =>
      completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback R ρ)

/-- The carrier summand is pointwise nonnegative with explicit decidability. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_all
    (R : ℝ) :
    ∀ z : CenteredCompletedZetaZeroCarrierZero,
      0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z :=
  fun z =>
    @centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative
      R z inferInstance

/-- The injective completed-zero pullback sum is bounded by the carrier sum. -/
theorem carrierPullback_tsum_le_carrier_tsum
    (R : ℝ)
    (hcarrier :
      Summable
        (fun z : CenteredCompletedZetaZeroCarrierZero =>
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)) :
    (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
          (completedZeroToCarrierZero ρ)) ≤
      ∑' z : CenteredCompletedZetaZeroCarrierZero,
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  exact tsum_comp_le_tsum_of_inj
    hcarrier
    (centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_all R)
    completedZeroToCarrierZero_injective

theorem completedZeroMultiplicityCounting_closedDisk_le_carrierCounting_of_summable
    (R : ℝ)
    (hcarrier :
      Summable
        (fun z : CenteredCompletedZetaZeroCarrierZero =>
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)) :
    completedZeroMultiplicityCountingInCenteredClosedDisk R ≤
      centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' z : CenteredCompletedZetaZeroCarrierZero,
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)
    (completedZeroMultiplicityClosedDisk_tsum_eq_carrierPullback_tsum R).symm
    (carrierPullback_tsum_le_carrier_tsum R hcarrier)


end

end LFunctions
end Boundary

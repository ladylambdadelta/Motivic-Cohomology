import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.CarrierTransport.OwnerParts.Part02_InverseCarrierTransport

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The denominator clearing factor is nonzero at a completed zero. -/
theorem completedZero_denominatorClearingFactor_ne_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ((1 / 2 : ℂ) + (ρ : ℂ)) *
        (1 - ((1 / 2 : ℂ) + (ρ : ℂ))) ≠ 0 := by
  exact centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles
    (zetaCompletedZero_ne_negHalf ρ)
    (zetaCompletedZero_ne_posHalf ρ)

/-- Near a completed zero, the cleared zero-carrier is the denominator unit times the
centered completed zeta normalization. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaZeroCarrier =ᶠ[𝓝 (ρ : ℂ)]
      (fun w : ℂ =>
        ((1 / 2 : ℂ) + w) *
          (1 - ((1 / 2 : ℂ) + w)) *
            centeredCompletedRiemannZeta w) := by
  have hleft_ne :
      ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 := by
    exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ)
  have hright_ne :
      1 - ((1 / 2 : ℂ) + (ρ : ℂ)) ≠ 0 := by
    exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ)
  have hleft_eventually :
      ∀ᶠ w in 𝓝 (ρ : ℂ), (1 / 2 : ℂ) + w ≠ 0 :=
    ((continuous_const.add continuous_id).continuousAt).eventually_ne hleft_ne
  have hright_eventually :
      ∀ᶠ w in 𝓝 (ρ : ℂ), 1 - ((1 / 2 : ℂ) + w) ≠ 0 :=
    ((continuous_const.sub (continuous_const.add continuous_id)).continuousAt).eventually_ne
      hright_ne
  exact
    (hleft_eventually.and hright_eventually).mono
      (fun w hw =>
        centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hw.1 hw.2)

/-- Completed-zero multiplicity is the cleared-carrier multiplicity at the same point. -/
theorem zetaZeroMultiplicity_eq_carrierMultiplicity
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    zetaZeroMultiplicity (ρ : ℂ) =
      centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) := by
  exact Eq.refl (zetaZeroMultiplicity (ρ : ℂ))

/-- Inside the disk, the completed summand equals the carrier pullback summand. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback_of_mem
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ‖(ρ : ℂ)‖ ≤ R) :
    completedZeroMultiplicityClosedDiskSummand R ρ =
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
        (completedZeroToCarrierZero ρ) := by
  have hleft :
      completedZeroMultiplicityClosedDiskSummand R ρ =
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    if_pos hρ
  have hright :
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
          (completedZeroToCarrierZero ρ) =
        (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) :=
    if_pos hρ
  have hmultiplicity :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) =
        (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ))
      (zetaZeroMultiplicity_eq_carrierMultiplicity ρ)
  exact Eq.trans hleft (Eq.trans hmultiplicity hright.symm)

/-- Outside the disk, both completed and carrier pullback summands vanish. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback_of_not_mem
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ¬ ‖(ρ : ℂ)‖ ≤ R) :
    completedZeroMultiplicityClosedDiskSummand R ρ =
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
        (completedZeroToCarrierZero ρ) := by
  have hleft :
      completedZeroMultiplicityClosedDiskSummand R ρ = 0 :=
    if_neg hρ
  have hright :
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
          (completedZeroToCarrierZero ρ) = 0 :=
    if_neg hρ
  exact Eq.trans hleft hright.symm

/-- Closed-disk completed-zero summands are the pullback of carrier-zero summands. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (‖(ρ : ℂ)‖ ≤ R)] :
    completedZeroMultiplicityClosedDiskSummand R ρ =
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
        (completedZeroToCarrierZero ρ) := by
  exact
    match (inferInstance : Decidable (‖(ρ : ℂ)‖ ≤ R)) with
    | Decidable.isTrue hρ =>
        completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback_of_mem R ρ hρ
    | Decidable.isFalse hρ =>
        completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback_of_not_mem R ρ hρ


end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.CarrierTransport.OwnerParts.Part01_CarrierMapsAndPoleFaces

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- The clearing denominator is nonzero at every carrier zero. -/
theorem centeredCompletedZetaZeroCarrierZero_denominator_ne_zero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    ((1 / 2 : ℂ) + (z : ℂ)) *
        (1 - ((1 / 2 : ℂ) + (z : ℂ))) ≠ 0 := by
  exact centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles
    (centeredCompletedZetaZeroCarrierZero_ne_negHalf z)
    (centeredCompletedZetaZeroCarrierZero_ne_posHalf z)

/-- The centered completed function vanishes at every carrier zero. -/
theorem centeredCompletedRiemannZeta_zero_of_carrierZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    centeredCompletedRiemannZeta (z : ℂ) = 0 := by
  have hneg : (z : ℂ) ≠ -(1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_negHalf z
  have hpos : (z : ℂ) ≠ (1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_posHalf z
  have hleft :
      (1 / 2 : ℂ) + (z : ℂ) ≠ 0 :=
    centeredShift_leftDenominator_ne_zero_of_ne_negHalf hneg
  have hright :
      1 - ((1 / 2 : ℂ) + (z : ℂ)) ≠ 0 :=
    centeredShift_rightDenominator_ne_zero_of_ne_posHalf hpos
  have hcarrier :
      centeredCompletedRiemannZetaZeroCarrier (z : ℂ) =
        ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) :=
    centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hleft hright
  have hproduct :
      ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    Eq.trans hcarrier.symm z.2
  exact
    match mul_eq_zero.mp hproduct with
    | Or.inl hdenominator =>
        False.elim
          ((centeredCompletedZetaZeroCarrierZero_denominator_ne_zero z) hdenominator)
    | Or.inr hzero => hzero

/-- A zero of the cleared entire carrier is a completed zero after excluding the shifted
pole faces. -/
theorem zetaCompletedZero_of_centeredCompletedZetaZeroCarrierZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    ZetaCompletedZero (z : ℂ) := by
  have hneg : (z : ℂ) ≠ -(1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_negHalf z
  have hpos : (z : ℂ) ≠ (1 / 2 : ℂ) :=
    centeredCompletedZetaZeroCarrierZero_ne_posHalf z
  have hcompleted_zero :
      centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    centeredCompletedRiemannZeta_zero_of_carrierZero z
  exact zetaCompletedZero_mk hneg hpos
    ((centeredCompletedRiemannZetaFunction_eq (z : ℂ)).trans hcompleted_zero)

/-- A carrier zero maps canonically back to the completed-zero divisor. -/
def carrierZeroToCompletedZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    {ρ : ℂ // ZetaCompletedZero ρ} :=
  ⟨(z : ℂ), zetaCompletedZero_of_centeredCompletedZetaZeroCarrierZero z⟩

/-- The carrier-zero to completed-zero map is injective. -/
theorem carrierZeroToCompletedZero_injective :
    Function.Injective carrierZeroToCompletedZero := by
  intro z w hzw
  exact Subtype.ext
    (congrArg
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (ρ : ℂ))
      hzw)

/-- Carrier zeros in a closed disk map into completed zeros in the same closed disk. -/
theorem carrierZeroToCompletedZero_mem_closedDisk
    (R : ℝ)
    (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : z ∈ centeredCompletedZetaZeroCarrierZerosInClosedDisk R) :
    carrierZeroToCompletedZero z ∈ completedZerosInCenteredClosedDisk R := by
  exact hz

/-- A carrier multiplicity summand is nonnegative inside its closed disk. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_of_mem
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : ‖(z : ℂ)‖ ≤ R) :
    0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (if_pos hz).symm
    (Nat.cast_nonneg (centeredCompletedZetaZeroCarrierMultiplicity (z : ℂ)))

/-- A carrier multiplicity summand is nonnegative outside its closed disk. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_of_not_mem
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : ¬ ‖(z : ℂ)‖ ≤ R) :
    0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  exact Eq.subst
    (motive := fun x : ℝ => 0 ≤ x)
    (if_neg hz).symm
    (le_refl (0 : ℝ))

/-- Carrier closed-disk multiplicity summands are nonnegative. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    [Decidable (‖(z : ℂ)‖ ≤ R)] :
    0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  exact
    match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
    | Decidable.isTrue hz =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_of_mem
          R z hz
    | Decidable.isFalse hz =>
        centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative_of_not_mem
          R z hz

/-- Carrier closed-disk multiplicity summands vanish outside the carrier closed disk. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : z ∉ centeredCompletedZetaZeroCarrierZerosInClosedDisk R) :
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z = 0 := by
  exact if_neg hz


end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ClosedDisk.Owner

/-!
# Carrier transport for completed zeros

This owner layer transports completed-zero data through the centered zero-carrier divisor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- A completed zero is a zero of the centered entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_zero_of_completedZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    centeredCompletedRiemannZetaZeroCarrier (ρ : ℂ) = 0 := by
  exact centeredCompletedRiemannZetaZeroCarrier_eq_zero_of_completed_zero
    (centeredShift_leftDenominator_ne_zero_of_ne_negHalf
      (zetaCompletedZero_ne_negHalf ρ))
    (centeredShift_rightDenominator_ne_zero_of_ne_posHalf
      (zetaCompletedZero_ne_posHalf ρ))
    ((centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm.trans
      (zetaCompletedZero_zero ρ))

/-- A completed zero maps canonically to a zero of the centered entire zero-carrier. -/
def completedZeroToCarrierZero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    CenteredCompletedZetaZeroCarrierZero :=
  ⟨(ρ : ℂ), centeredCompletedRiemannZetaZeroCarrier_zero_of_completedZero ρ⟩

/-- The completed-zero to carrier-zero map is injective. -/
theorem completedZeroToCarrierZero_injective :
    Function.Injective completedZeroToCarrierZero := by
  intro ρ η hρη
  exact Subtype.ext
    (congrArg
      (fun z : CenteredCompletedZetaZeroCarrierZero => (z : ℂ))
      hρη)

/-- The cleared zero-carrier is nonzero at the negative shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf :
    centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) ≠ 0 := by
  have hleft : (1 / 2 : ℂ) + -(1 / 2 : ℂ) = 0 :=
    add_neg_cancel (1 / 2 : ℂ)
  have hvalue :
      centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) = -1 := by
    calc
      ((1 / 2 : ℂ) + -(1 / 2 : ℂ)) *
            (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
            centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) -
          1 =
          0 *
            (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
            centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) -
          1 := by
        exact congrArg
          (fun w : ℂ =>
            w * (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
                centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) -
              1)
          hleft
      _ =
          0 * centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) - 1 := by
        exact congrArg (fun w : ℂ => w * centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) - 1)
          (zero_mul (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))))
      _ = 0 - 1 := by
        exact congrArg (fun w : ℂ => w - 1)
          (zero_mul (centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ))))
      _ = -1 := by
        exact zero_sub 1
  intro hzero
  exact (neg_ne_zero.mpr one_ne_zero) (hvalue.symm.trans hzero)

/-- The cleared zero-carrier is nonzero at the positive shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_posHalf :
    centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) ≠ 0 := by
  have hright : 1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ)) = 0 := by
    have htwo_ne : (2 : ℂ) ≠ 0 :=
      two_ne_zero
    have hhalf_add_half : (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by
      calc
        (1 / 2 : ℂ) + (1 / 2 : ℂ) =
            (1 + 1 : ℂ) / 2 := by
          exact (add_div (1 : ℂ) 1 2).symm
        _ = (2 : ℂ) / 2 := by
          exact congrArg (fun w : ℂ => w / 2) (one_add_one_eq_two)
        _ = 1 := by
          exact div_self htwo_ne
    calc
      1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ)) =
          1 - 1 := by
        exact congrArg (fun w : ℂ => 1 - w) hhalf_add_half
      _ = 0 := by
        exact sub_self 1
  have hvalue :
      centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) = -1 := by
    calc
      ((1 / 2 : ℂ) + (1 / 2 : ℂ)) *
            (1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ))) *
            centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) -
          1 =
          ((1 / 2 : ℂ) + (1 / 2 : ℂ)) *
            0 *
            centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) -
          1 := by
        exact congrArg
          (fun w : ℂ =>
            ((1 / 2 : ℂ) + (1 / 2 : ℂ)) * w *
                centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) -
              1)
          hright
      _ =
          0 * centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) - 1 := by
        exact congrArg (fun w : ℂ => w * centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) - 1)
          (mul_zero ((1 / 2 : ℂ) + (1 / 2 : ℂ)))
      _ = 0 - 1 := by
        exact congrArg (fun w : ℂ => w - 1)
          (zero_mul (centeredCompletedRiemannZeta₀ (1 / 2 : ℂ)))
      _ = -1 := by
        exact zero_sub 1
  intro hzero
  exact (neg_ne_zero.mpr one_ne_zero) (hvalue.symm.trans hzero)

/-- The cleared zero-carrier is not the zero entire function. -/
theorem centeredCompletedRiemannZetaZeroCarrier_nontrivial :
    ∃ z : ℂ, centeredCompletedRiemannZetaZeroCarrier z ≠ 0 := by
  exact ⟨-(1 / 2 : ℂ), centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf⟩

/-- A carrier zero cannot be the negative shifted pole face. -/
theorem centeredCompletedZetaZeroCarrierZero_ne_negHalf
    (z : CenteredCompletedZetaZeroCarrierZero) :
    (z : ℂ) ≠ -(1 / 2 : ℂ) := by
  intro hz
  have hcarrier_at_pole :
      centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) = 0 := by
    exact Eq.subst
      (motive := fun w : ℂ => centeredCompletedRiemannZetaZeroCarrier w = 0)
      hz
      z.2
  exact centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf hcarrier_at_pole

/-- A carrier zero cannot be the positive shifted pole face. -/
theorem centeredCompletedZetaZeroCarrierZero_ne_posHalf
    (z : CenteredCompletedZetaZeroCarrierZero) :
    (z : ℂ) ≠ (1 / 2 : ℂ) := by
  intro hz
  have hcarrier_at_pole :
      centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) = 0 := by
    exact Eq.subst
      (motive := fun w : ℂ => centeredCompletedRiemannZetaZeroCarrier w = 0)
      hz
      z.2
  exact centeredCompletedRiemannZetaZeroCarrier_ne_zero_posHalf hcarrier_at_pole

/-- A zero of the cleared entire carrier is a completed zero after excluding the shifted
pole faces. -/
theorem zetaCompletedZero_of_centeredCompletedZetaZeroCarrierZero
    (z : CenteredCompletedZetaZeroCarrierZero) :
    ZetaCompletedZero (z : ℂ) := by
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
  have hdenom :
      ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) ≠ 0 :=
    centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles hneg hpos
  have hcarrier_eq_product :
      centeredCompletedRiemannZetaZeroCarrier (z : ℂ) =
        ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) :=
    centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hleft hright
  have hproduct_zero :
      ((1 / 2 : ℂ) + (z : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (z : ℂ))) *
            centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    hcarrier_eq_product.symm.trans z.2
  have hcompleted_zero :
      centeredCompletedRiemannZeta (z : ℂ) = 0 :=
    match mul_eq_zero.mp hproduct_zero with
    | Or.inl hdenom_zero => False.elim (hdenom hdenom_zero)
    | Or.inr hzero => hzero
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

/-- Carrier closed-disk multiplicity summands are nonnegative. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    [Decidable (‖(z : ℂ)‖ ≤ R)] :
    0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z := by
  exact
    match (inferInstance : Decidable (‖(z : ℂ)‖ ≤ R)) with
    | Or.inl hz =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_pos hz).symm
          (Nat.cast_nonneg (centeredCompletedZetaZeroCarrierMultiplicity (z : ℂ)))
    | Or.inr hz =>
        Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_neg hz).symm
          (le_refl (0 : ℝ))

/-- Carrier closed-disk multiplicity summands vanish outside the carrier closed disk. -/
theorem centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_eq_zero_of_not_mem
    (R : ℝ) (z : CenteredCompletedZetaZeroCarrierZero)
    (hz : z ∉ centeredCompletedZetaZeroCarrierZerosInClosedDisk R) :
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z = 0 := by
  exact if_neg hz

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
  rfl

/-- Closed-disk completed-zero summands are the pullback of carrier-zero summands. -/
theorem completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback
    (R : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    [Decidable (‖(ρ : ℂ)‖ ≤ R)] :
    completedZeroMultiplicityClosedDiskSummand R ρ =
      centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
        (completedZeroToCarrierZero ρ) := by
  exact
    match (inferInstance : Decidable (‖(ρ : ℂ)‖ ≤ R)) with
    | Or.inl hρ =>
        have hleft :
            completedZeroMultiplicityClosedDiskSummand R ρ =
              (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
          if_pos hρ
        have hright :
            centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
                (completedZeroToCarrierZero ρ) =
              (centeredCompletedZetaZeroCarrierMultiplicity (ρ : ℂ) : ℝ) :=
          if_pos hρ
        hleft.trans
          ((congrArg (fun n : ℕ => (n : ℝ))
            (zetaZeroMultiplicity_eq_carrierMultiplicity ρ)).trans hright.symm)
    | Or.inr hρ =>
        have hleft :
            completedZeroMultiplicityClosedDiskSummand R ρ = 0 :=
          if_neg hρ
        have hright :
            centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
                (completedZeroToCarrierZero ρ) = 0 :=
          if_neg hρ
        hleft.trans hright.symm

/-- The centered entire zero-carrier has only finitely many zeros in every
ordinary closed disk. This is the local-finiteness part of the finite-order
Jensen package for the cleared entire divisor. -/
theorem finite_centeredCompletedZetaZeroCarrierZerosInClosedDisk
    (R : ℝ) :
    (centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite := by
  have himage_subset :
      carrierZeroToCompletedZero ''
          centeredCompletedZetaZeroCarrierZerosInClosedDisk R ⊆
        completedZerosInCenteredClosedDisk R := by
    intro ρ hρ
    match hρ with
    | ⟨z, hzmem, hzρ⟩ =>
        exact Eq.subst
          (motive := fun y : {ρ : ℂ // ZetaCompletedZero ρ} =>
            y ∈ completedZerosInCenteredClosedDisk R)
          hzρ
          (carrierZeroToCompletedZero_mem_closedDisk R z hzmem)
  have himage_finite :
      (carrierZeroToCompletedZero ''
          centeredCompletedZetaZeroCarrierZerosInClosedDisk R).Finite :=
    Set.Finite.subset
      (finite_completedZerosInCenteredClosedDisk R)
      himage_subset
  exact Set.Finite.of_finite_image
    himage_finite
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
theorem completedZeroMultiplicityCounting_closedDisk_le_carrierCounting_of_summable
    (R : ℝ)
    (hcarrier :
      Summable
        (fun z : CenteredCompletedZetaZeroCarrierZero =>
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)) :
    completedZeroMultiplicityCountingInCenteredClosedDisk R ≤
      centeredCompletedZetaZeroCarrierMultiplicityCountingInClosedDisk R := by
  have hcompleted_as_pullback :
      (∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityClosedDiskSummand R ρ) =
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R
            (completedZeroToCarrierZero ρ) :=
    tsum_congr
      (fun ρ =>
        completedZeroMultiplicityClosedDiskSummand_eq_carrierPullback R ρ)
  have hnonnegative :
      ∀ z : CenteredCompletedZetaZeroCarrierZero,
        0 ≤ centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z :=
    centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand_nonnegative R
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' z : CenteredCompletedZetaZeroCarrierZero,
          centeredCompletedZetaZeroCarrierMultiplicityClosedDiskSummand R z)
    hcompleted_as_pullback.symm
    (tsum_comp_le_tsum_of_inj
      hcarrier
      hnonnegative
      completedZeroToCarrierZero_injective)

end

end LFunctions
end Boundary

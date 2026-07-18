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

/-- The cleared product vanishes at the negative shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_negHalf_product_eq_zero :
    ((1 / 2 : ℂ) + -(1 / 2 : ℂ)) *
        (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
        centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) = 0 := by
  have hleft : (1 / 2 : ℂ) + -(1 / 2 : ℂ) = 0 :=
    add_neg_cancel (1 / 2 : ℂ)
  have hreplace :
      ((1 / 2 : ℂ) + -(1 / 2 : ℂ)) *
          (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
          centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) =
        0 * (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
          centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) :=
    congrArg
      (fun w : ℂ => w * (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
        centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)))
      hleft
  have hzero :
      0 * (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ))) *
          centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)) = 0 :=
    Eq.trans
      (congrArg
        (fun w : ℂ => w * centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ)))
        (zero_mul (1 - ((1 / 2 : ℂ) + -(1 / 2 : ℂ)))))
      (zero_mul (centeredCompletedRiemannZeta₀ (-(1 / 2 : ℂ))))
  exact Eq.trans hreplace hzero

/-- The cleared zero-carrier has value negative one at the negative shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_negHalf_eq_neg_one :
    centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) = -1 := by
  have hsubtract :
      centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) = 0 - 1 :=
    congrArg (fun w : ℂ => w - 1)
      centeredCompletedRiemannZetaZeroCarrier_negHalf_product_eq_zero
  exact Eq.trans hsubtract (zero_sub 1)
 
/-- The cleared zero-carrier is nonzero at the negative shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_negHalf :
    centeredCompletedRiemannZetaZeroCarrier (-(1 / 2 : ℂ)) ≠ 0 := by
  intro hzero
  exact (neg_ne_zero.mpr one_ne_zero)
    (centeredCompletedRiemannZetaZeroCarrier_negHalf_eq_neg_one.symm.trans hzero)

/-- The sum of the two complex half units is one. -/
theorem complex_half_add_half_eq_one :
    (1 / 2 : ℂ) + (1 / 2 : ℂ) = 1 := by
  have htwo_ne : (2 : ℂ) ≠ 0 :=
    two_ne_zero
  have hadd :
      (1 / 2 : ℂ) + (1 / 2 : ℂ) = (1 + 1 : ℂ) / 2 :=
    (add_div (1 : ℂ) 1 2).symm
  have honeTwo :
      (1 + 1 : ℂ) / 2 = (2 : ℂ) / 2 :=
    congrArg (fun w : ℂ => w / 2) (one_add_one_eq_two)
  have hdivide :
      (2 : ℂ) / 2 = 1 :=
    div_self htwo_ne
  exact Eq.trans hadd (Eq.trans honeTwo hdivide)

/-- The right clearing factor vanishes at the positive shifted pole face. -/
theorem complex_posHalf_rightClearingFactor_eq_zero :
    1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ)) = 0 := by
  have hreplace :
      1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ)) = 1 - 1 :=
    congrArg (fun w : ℂ => 1 - w) complex_half_add_half_eq_one
  exact Eq.trans hreplace (sub_self 1)

/-- The cleared zero-carrier has value negative one at the positive shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_posHalf_eq_neg_one :
    centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) = -1 := by
  have hproduct :
      ((1 / 2 : ℂ) + (1 / 2 : ℂ)) *
          (1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ))) *
          centeredCompletedRiemannZeta₀ (1 / 2 : ℂ) = 0 := by
    have hreplace :
        ((1 / 2 : ℂ) + (1 / 2 : ℂ)) *
            (1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ))) =
          ((1 / 2 : ℂ) + (1 / 2 : ℂ)) * 0 :=
      congrArg
        (fun w : ℂ => ((1 / 2 : ℂ) + (1 / 2 : ℂ)) * w)
        complex_posHalf_rightClearingFactor_eq_zero
    have hzero :
        ((1 / 2 : ℂ) + (1 / 2 : ℂ)) * 0 = 0 :=
      mul_zero ((1 / 2 : ℂ) + (1 / 2 : ℂ))
    have hfactor :
        ((1 / 2 : ℂ) + (1 / 2 : ℂ)) *
            (1 - ((1 / 2 : ℂ) + (1 / 2 : ℂ))) = 0 :=
      Eq.trans hreplace hzero
    exact Eq.trans
      (congrArg
        (fun w : ℂ => w * centeredCompletedRiemannZeta₀ (1 / 2 : ℂ))
        hfactor)
      (zero_mul (centeredCompletedRiemannZeta₀ (1 / 2 : ℂ)))
  have hsubtract :
      centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) = 0 - 1 :=
    congrArg (fun w : ℂ => w - 1) hproduct
  exact Eq.trans hsubtract (zero_sub 1)

/-- The cleared zero-carrier is nonzero at the positive shifted pole face. -/
theorem centeredCompletedRiemannZetaZeroCarrier_ne_zero_posHalf :
    centeredCompletedRiemannZetaZeroCarrier (1 / 2 : ℂ) ≠ 0 := by
  intro hzero
  exact (neg_ne_zero.mpr one_ne_zero)
    (centeredCompletedRiemannZetaZeroCarrier_posHalf_eq_neg_one.symm.trans hzero)

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


end

end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.FiniteSpectralZeroOperator
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.Coordinate

/-!
# Finite spectral-zero carrier separation

This file owns the finite algebra behind carrier separation.  A finite
spectral-zero differential multiplier is nonzero on any completed-zero carrier
disjoint from the forced sample set, and the reciprocal multipliers have an
explicit finite constant bound.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- The finite spectral-zero differential multiplier. -/
noncomputable def finiteSpectralZeroMultiplier
    (P : Finset ℂ)
    (z : ℂ) : ℂ :=
  (P.toList.map (fun sample : ℂ => sample - z)).prod

/-- The finite multiplier is nonzero away from its forced sample set. -/
theorem finiteSpectralZeroMultiplier_ne_zero_of_not_mem
    (P : Finset ℂ)
    (z : ℂ)
    (hz : z ∉ P) :
    finiteSpectralZeroMultiplier P z ≠ 0 := by
  unfold finiteSpectralZeroMultiplier
  exact List.prod_ne_zero
    (fun hzeroMember =>
      match List.mem_map.mp hzeroMember with
      | ⟨sample, hsampleList, hsampleDifference⟩ =>
          have hsampleEqual : sample = z :=
            sub_eq_zero.mp hsampleDifference
          hz
            (Eq.mp
              (congrArg (fun value : ℂ => value ∈ P) hsampleEqual)
              (Finset.mem_toList.mp hsampleList)))

/-- The finite multiplier is the coordinate multiplier of the finite
spectral-zero differential operator. -/
theorem finiteSpectralZeroMultiplier_eq_operatorMultiplier
    (P : Finset ℂ)
    (f : ZetaAdmissibleFunction)
    (z : ℂ) :
    zetaZeroSideContribution z (finiteSpectralZeroOperator P f) =
      finiteSpectralZeroMultiplier P z * zetaZeroSideContribution z f := by
  exact zetaZeroSideContribution_finiteSpectralZeroOperator P f z

/-- The explicit reciprocal-multiplier bound on a finite completed-zero
carrier. -/
noncomputable def finiteSpectralZeroMultiplierCarrierInverseNormBound
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate) : ℝ :=
  ∑ rho in carrier,
    ‖(finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹‖

/-- The finite reciprocal-multiplier bound is nonnegative. -/
theorem finiteSpectralZeroMultiplierCarrierInverseNormBound_nonnegative
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate) :
    0 ≤ finiteSpectralZeroMultiplierCarrierInverseNormBound P carrier := by
  unfold finiteSpectralZeroMultiplierCarrierInverseNormBound
  exact Finset.sum_nonneg
    (fun rho hrho =>
      norm_nonneg ((finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹))

/-- Every reciprocal multiplier on the finite carrier is bounded by the
explicit carrier constant. -/
theorem finiteSpectralZeroMultiplier_inverseNorm_le_carrierBound
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate)
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : rho ∈ carrier) :
    ‖(finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹‖ ≤
      finiteSpectralZeroMultiplierCarrierInverseNormBound P carrier := by
  unfold finiteSpectralZeroMultiplierCarrierInverseNormBound
  exact Finset.single_le_sum
    (s := carrier)
    (f := fun eta : ZetaCompletedZeroCoordinate =>
      ‖(finiteSpectralZeroMultiplier P (eta : ℂ))⁻¹‖)
    (a := rho)
    (fun eta heta =>
      norm_nonneg ((finiteSpectralZeroMultiplier P (eta : ℂ))⁻¹))
    hrho

/-- A completed-zero carrier disjoint from the forced finite samples has no
vanishing spectral-zero multiplier on that carrier. -/
theorem finiteSpectralZeroMultiplier_ne_zero_of_mem_disjointCarrier
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate)
    (hdisjoint :
      ∀ rho : ZetaCompletedZeroCoordinate,
        rho ∈ carrier → (rho : ℂ) ∉ P)
    (rho : ZetaCompletedZeroCoordinate)
    (hrho : rho ∈ carrier) :
    finiteSpectralZeroMultiplier P (rho : ℂ) ≠ 0 :=
  finiteSpectralZeroMultiplier_ne_zero_of_not_mem
    P (rho : ℂ) (hdisjoint rho hrho)

/-- Quantitative finite-carrier separation for the spectral-zero multiplier:
the carrier is separated from the forced samples exactly by nonvanishing of the
multiplier, and its reciprocal is controlled by the explicit finite constant. -/
theorem finiteSpectralZeroMultiplier_quantitativeCarrierSeparation
    (P : Finset ℂ)
    (carrier : Finset ZetaCompletedZeroCoordinate)
    (hdisjoint :
      ∀ rho : ZetaCompletedZeroCoordinate,
        rho ∈ carrier → (rho : ℂ) ∉ P) :
    0 ≤ finiteSpectralZeroMultiplierCarrierInverseNormBound P carrier ∧
      ∀ rho : ZetaCompletedZeroCoordinate,
        rho ∈ carrier →
          finiteSpectralZeroMultiplier P (rho : ℂ) ≠ 0 ∧
            ‖(finiteSpectralZeroMultiplier P (rho : ℂ))⁻¹‖ ≤
              finiteSpectralZeroMultiplierCarrierInverseNormBound P carrier :=
  And.intro
    (finiteSpectralZeroMultiplierCarrierInverseNormBound_nonnegative
      P carrier)
    (fun rho hrho =>
      And.intro
        (finiteSpectralZeroMultiplier_ne_zero_of_mem_disjointCarrier
          P carrier hdisjoint rho hrho)
        (finiteSpectralZeroMultiplier_inverseNorm_le_carrierBound
          P carrier rho hrho))

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

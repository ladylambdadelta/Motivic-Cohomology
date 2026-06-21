import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.FiniteZeroProduct.InsertionGluing.SupportValue.Owner

/-!
# Normalized factor insertion and removable gluing

This owner layer was split from `FiniteZeroProduct.InsertionGluing.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Maximal-multiplicity zero-freeness for the quotient after finite removable
gluing.

This owner lemma is the local multiplicity sink: after the support product has
removed exactly the analytic order of `F` at every support zero, the glued
quotient has order zero throughout the closed disk. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_from_maximalMultiplicity_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
            Q w *
              entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
                F hF hF0 ρ w) :
    ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  intro w hwρ
  exact
    if hw :
        w ∈
          (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisor
            F hF hF0 ρ).image
            (fun z : EntireFunctionZero F => (z : ℂ)) then
      match Finset.mem_image.1 hw with
      | Exists.intro z hz_data =>
          match hz_data with
          | And.intro hz hzw =>
              Eq.subst (motive := fun x : ℂ => Q x ≠ 0) hzw
                (entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_at_support_from_maximalMultiplicity_ownerRoot
                  F Q hF hF0 ρ hQ_an hfactor z hz)
    else
      entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_nonzero_of_not_mem_support
        F Q hF hF0 ρ hfactor hwρ hw

/-- Maximal-multiplicity zero-freeness for the removable quotient.

If the quotient vanished at a point of the closed disk, then the product
factorization would force `F` to vanish there to order strictly larger than the
exponent extracted in the finite product.  At a support point this contradicts
the local maximality of the multiplicity factor; away from the support it
contradicts the matched zero set. -/
theorem entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_ownerRoot
    (F Q : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0)
    (ρ : ℝ)
    (hQ_an : ∀ w : ℂ, ‖w‖ ≤ ρ → AnalyticAt ℂ Q w)
    (hfactor :
      ∀ w : ℂ,
        ‖w‖ ≤ ρ →
        F w =
          Q w *
            entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteZeroDivisorProduct
              F hF hF0 ρ w) :
    ∀ w : ℂ, ‖w‖ ≤ ρ → Q w ≠ 0 := by
  exact
    entireFunction_standardJensenFormula_nonzeroAtOrigin_closedDiskSupportFiniteRemovableQuotient_zeroFree_from_maximalMultiplicity_ownerRoot
      F Q hF hF0 ρ hQ_an hfactor

end
end LFunctions
end Boundary

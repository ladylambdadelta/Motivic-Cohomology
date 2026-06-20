import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This owner layer was split from `OriginTaylorTransport.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hF0 : F 0 ≠ 0) :
    ∃ C : ℝ,
      (∀ R : ℝ,
        1 ≤ R →
        Summable
          (fun z : EntireFunctionZero F =>
            entireFunctionNonzeroZeroMultiplicityClosedDiskSummand F hF R z)) ∧
      (∀ ρ : ℝ,
          1 ≤ ρ →
          Summable
            (fun z : EntireFunctionZero F =>
              entireFunctionJensenRadialGapSummand F hF ρ z) ∧
          entireFunctionJensenRadialGapSum F hF ρ +
              entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
              C =
            entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_nonzeroAtOrigin_radialGapSum_eq_boundaryLogAverage
        F hF hF0)
      (fun C hC =>
        Exists.intro C
          (And.intro hC.1
            (fun ρ hρ =>
              match hC.2 ρ hρ with
              | ⟨hsum, hradial⟩ =>
                  let horigin :
                      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ = 0 :=
                    entireFunctionOriginMultiplicityLogRadiusContribution_eq_zero_of_ne_zero
                      F hF hF0 ρ
                  let hzero_insert :
                      entireFunctionJensenRadialGapSum F hF ρ +
                          entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ + C =
                        entireFunctionJensenRadialGapSum F hF ρ + 0 + C :=
                    congrArg
                      (fun x : ℝ =>
                        entireFunctionJensenRadialGapSum F hF ρ + x + C)
                      horigin
                  let hzero_drop :
                      entireFunctionJensenRadialGapSum F hF ρ + 0 + C =
                        entireFunctionJensenRadialGapSum F hF ρ + C :=
                    congrArg
                      (fun x : ℝ => x + C)
                      (add_zero (entireFunctionJensenRadialGapSum F hF ρ))
                  And.intro hsum
                    (Eq.trans hzero_insert (Eq.trans hzero_drop hradial)))))


end
end LFunctions
end Boundary

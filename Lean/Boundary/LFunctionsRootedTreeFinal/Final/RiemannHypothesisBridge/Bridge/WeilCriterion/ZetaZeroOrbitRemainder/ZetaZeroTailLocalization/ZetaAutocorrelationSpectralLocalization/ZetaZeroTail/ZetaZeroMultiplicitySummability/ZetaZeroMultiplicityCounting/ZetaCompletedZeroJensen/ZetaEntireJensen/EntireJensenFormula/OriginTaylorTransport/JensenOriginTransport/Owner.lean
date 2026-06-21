import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.OriginTaylorTransport.BoundaryAverageTransport.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This owner layer was split from `OriginTaylorTransport.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Origin Taylor-factor transport in the genuine origin-zero case.

This is the remaining transport step after the nonzero-origin case is removed:
factor the origin zero by `AnalyticAt.order_eq_nat_iff`, apply the nonzero
Jensen formula to the analytic unit, and compare nonzero zero multisets and
boundary averages. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (_hF0 : F 0 = 0)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
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
      (entireFunction_originTaylorFactor_entireQuotient F hF hnontrivial)
      (fun G hG_data =>
        match hG_data with
        | ⟨hG_entire, hG_tail⟩ =>
            match hG_tail with
            | ⟨hG_ne, hfactor⟩ =>
                entireFunction_classicalJensenFormula_originTaylorFactor_transport_from_entireQuotient
                  F hF hnontrivial G hG_entire hG_ne hfactor)

/-- Transport of the nonzero-at-origin Jensen identity through the origin
Taylor factor.

If `F(z) = z^m G(z)` near the origin and `G 0 ≠ 0`, the boundary average gains
the explicit term `m log ρ`, while the nonzero radial-gap and closed-disk
summability data are transported unchanged from the normalized factor.  This is
the exact owner theorem that separates the algebraic origin factor from the
classical Jensen identity for a function nonzero at the origin. -/
theorem entireFunction_classicalJensenFormula_originTaylorFactor_transport
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
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
  -- Factor `F` by its origin order and apply the nonzero-at-origin Jensen
  -- identity to the analytic unit.  The origin power contributes exactly
  -- `m * log ρ` to the boundary average.
  exact
    match eq_or_ne (F 0) 0 with
    | Or.inl hF0 =>
        entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_zeroAtOrigin
          F hF hF0 hnontrivial
    | Or.inr hF0 =>
        entireFunction_classicalJensenFormula_originTaylorFactor_transport_of_nonzeroAtOrigin
          F hF hF0

/-- Origin-factored classical Jensen formula as an exact radial-gap identity.

This is the genuinely analytic theorem: for a nontrivial entire function,
after separating the origin Taylor factor, Jensen's formula identifies the
boundary logarithmic average with the non-origin multiplicity-weighted radial
gap sum plus the origin radius term and one fixed normalization constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
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
    entireFunction_classicalJensenFormula_originTaylorFactor_transport
      F hF hnontrivial

/-- Origin-factored classical Jensen formula in radial-gap bound form.

For large radii, the origin radius term is nonnegative, so the exact Jensen
identity implies a radial-gap upper bound with one absolute-value constant. -/
theorem entireFunction_classicalJensenFormula_originFactoredRadialGapSum_le_boundaryLogAverage
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∃ J : ℝ,
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
          entireFunctionJensenRadialGapSum F hF ρ ≤
            J + entireFunctionJensenBoundaryLogAverage F ρ) := by
  exact
    Exists.elim
      (entireFunction_classicalJensenFormula_originFactoredRadialGapSum_eq_boundaryLogAverage
        F hF hnontrivial)
      (fun C hC =>
        match hC with
        | ⟨hclosed, hidentity⟩ =>
            Exists.intro |C|
              (And.intro hclosed
                (fun ρ hρ =>
                  match hidentity ρ hρ with
                  | ⟨hgap, hJensen⟩ =>
                      have horigin_nonneg :
                          0 ≤ entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := by
                        calc
                          0 ≤
                              (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log ρ :=
                            mul_nonneg
                              (Nat.cast_nonneg (entireFunctionZeroMultiplicity F hF 0))
                              (Real.log_nonneg hρ)
                          _ = entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ := rfl
                      have hC_nonneg : 0 ≤ |C| + C := by
                        have hneg : -C ≤ |C| := neg_le_abs C
                        have hsub : 0 ≤ |C| - (-C) := sub_nonneg.mpr hneg
                        have hsub_eq : |C| - (-C) = |C| + C := by
                          calc
                            |C| - (-C) = |C| + -(-C) :=
                              sub_eq_add_neg |C| (-C)
                            _ = |C| + C := by
                              exact congrArg (fun x : ℝ => |C| + x) (neg_neg C)
                        exact Eq.subst (motive := fun x : ℝ => 0 ≤ x) hsub_eq hsub
                      have htail_nonneg :
                          0 ≤
                            entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                              (|C| + C) :=
                        add_nonneg horigin_nonneg hC_nonneg
                      have hle_add :
                          entireFunctionJensenRadialGapSum F hF ρ ≤
                            entireFunctionJensenRadialGapSum F hF ρ +
                              (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                (|C| + C)) :=
                        le_add_of_nonneg_right htail_nonneg
                      have htarget :
                          entireFunctionJensenRadialGapSum F hF ρ +
                              (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                (|C| + C)) =
                            |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
                        calc
                          entireFunctionJensenRadialGapSum F hF ρ +
                              (entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                (|C| + C)) =
                              |C| +
                                (entireFunctionJensenRadialGapSum F hF ρ +
                                  entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                  C) := by
                            let A : ℝ := entireFunctionJensenRadialGapSum F hF ρ
                            let B : ℝ := entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ
                            let D : ℝ := |C|
                            calc
                              A + (B + (D + C)) = A + ((B + D) + C) := by
                                exact congrArg (fun x : ℝ => A + x) (add_assoc B D C).symm
                              _ = (A + (B + D)) + C := by
                                exact (add_assoc A (B + D) C).symm
                              _ = ((B + D) + A) + C := by
                                exact congrArg (fun x : ℝ => x + C) (add_comm A (B + D))
                              _ = ((D + B) + A) + C := by
                                exact congrArg
                                  (fun x : ℝ => (x + A) + C)
                                  (add_comm B D)
                              _ = (D + (B + A)) + C := by
                                exact congrArg (fun x : ℝ => x + C) (add_assoc D B A)
                              _ = (D + (A + B)) + C := by
                                exact congrArg
                                  (fun x : ℝ => (D + x) + C)
                                  (add_comm B A)
                              _ = D + ((A + B) + C) := by
                                exact add_assoc D (A + B) C
                              _ =
                                  |C| +
                                    (entireFunctionJensenRadialGapSum F hF ρ +
                                      entireFunctionOriginMultiplicityLogRadiusContribution F hF ρ +
                                      C) := rfl
                          _ = |C| + entireFunctionJensenBoundaryLogAverage F ρ := by
                            exact congrArg (fun x : ℝ => |C| + x) hJensen
                      And.intro hgap
                        (Eq.subst
                          (motive := fun x : ℝ =>
                            entireFunctionJensenRadialGapSum F hF ρ ≤ x)
                          htarget
                          hle_add))))


end
end LFunctions
end Boundary

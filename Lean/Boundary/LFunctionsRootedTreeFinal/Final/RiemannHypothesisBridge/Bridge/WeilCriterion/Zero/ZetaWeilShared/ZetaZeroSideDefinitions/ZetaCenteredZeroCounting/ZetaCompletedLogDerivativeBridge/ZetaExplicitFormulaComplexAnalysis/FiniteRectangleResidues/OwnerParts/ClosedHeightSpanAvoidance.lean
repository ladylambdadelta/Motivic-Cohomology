import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareHoleHorizontalIntegrability

/-!
# Closed height-span singular avoidance
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A regular vertical level avoids singularities throughout the closed scheduled height
span.  Interior points are controlled by the raw singular carrier; the two endpoints are
controlled by scheduled boundary avoidance. -/
theorem explicitFormulaRectangle_verticalLine_avoidsSingularSet_on_closedHeightSpan
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x y : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hy : y ∈ Set.Icc (-(h.height_schedule.height u)) (h.height_schedule.height u))
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          x ≠ b.re) :
    (x : ℂ) + (y : ℂ) * Complex.I ∉ completedZetaContourIntegrandSingularSet := by
  let T : ℝ := h.height_schedule.height u
  have hlowerCases : -T < y ∨ -T = y := lt_or_eq_of_le hy.1
  have hupperCases : y < T ∨ y = T := lt_or_eq_of_le hy.2
  match hlowerCases with
  | Or.inr hlowerEq =>
      have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = -T := by
        exact Eq.trans (ofReal_add_mul_I_im x y) hlowerEq.symm
      have hboundary :
          (x : ℂ) + (y : ℂ) * Complex.I ∈
            explicitFormulaContourFamilyBoundary F T :=
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom F T hx him
      exact
        completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
          f F h u hboundary
  | Or.inl hlower =>
      match hupperCases with
      | Or.inr hupperEq =>
          have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = T := by
            exact Eq.trans (ofReal_add_mul_I_im x y) hupperEq
          have hboundary :
              (x : ℂ) + (y : ℂ) * Complex.I ∈
                explicitFormulaContourFamilyBoundary F T :=
            explicitFormulaContourFamilyBoundary_mem_of_im_eq_top F T hx him
          exact
            completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
              f F h u hboundary
      | Or.inl hupper =>
          have habs : |y| < T := abs_lt.mpr (And.intro hlower hupper)
          exact
            explicitFormulaRectangle_verticalLine_avoidsSingularSet
              T x y habs hlevel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

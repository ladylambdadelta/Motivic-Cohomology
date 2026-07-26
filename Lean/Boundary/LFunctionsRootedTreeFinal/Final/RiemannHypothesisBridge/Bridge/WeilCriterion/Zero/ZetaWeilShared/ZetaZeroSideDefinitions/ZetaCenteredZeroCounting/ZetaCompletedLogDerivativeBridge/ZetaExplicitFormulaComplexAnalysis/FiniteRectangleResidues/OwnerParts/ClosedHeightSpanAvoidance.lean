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
theorem explicitFormulaRectangle_verticalLine_avoidsSingularSet_on_closedHeightSpan_of_boundaryAvoidance
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T x y : ℝ)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hy : y ∈ Set.Icc (-T) T)
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          x ≠ b.re) :
    (x : ℂ) + (y : ℂ) * Complex.I ∉ completedZetaContourIntegrandSingularSet := by
  have hlowerCases : -T < y ∨ -T = y := lt_or_eq_of_le hy.1
  have hupperCases : y < T ∨ y = T := lt_or_eq_of_le hy.2
  match hlowerCases with
  | Or.inr hlowerEq =>
      have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x :=
        ofReal_add_mul_I_re x y
      have hxPoint :
          ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.uIcc F.c (1 - F.c) :=
        Eq.subst
          (motive := fun value : ℝ => value ∈ Set.uIcc F.c (1 - F.c))
          hre.symm
          hx
      have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = -T := by
        exact Eq.trans (ofReal_add_mul_I_im x y) hlowerEq.symm
      have hboundary :
          (x : ℂ) + (y : ℂ) * Complex.I ∈
            explicitFormulaContourFamilyBoundary F T :=
        explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom F T hxPoint him
      exact hboundaryAvoidance ((x : ℂ) + (y : ℂ) * Complex.I) hboundary
  | Or.inl hlower =>
      match hupperCases with
      | Or.inr hupperEq =>
          have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x :=
            ofReal_add_mul_I_re x y
          have hxPoint :
              ((x : ℂ) + (y : ℂ) * Complex.I).re ∈ Set.uIcc F.c (1 - F.c) :=
            Eq.subst
              (motive := fun value : ℝ => value ∈ Set.uIcc F.c (1 - F.c))
              hre.symm
              hx
          have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = T := by
            exact Eq.trans (ofReal_add_mul_I_im x y) hupperEq
          have hboundary :
              (x : ℂ) + (y : ℂ) * Complex.I ∈
                explicitFormulaContourFamilyBoundary F T :=
            explicitFormulaContourFamilyBoundary_mem_of_im_eq_top F T hxPoint him
          exact hboundaryAvoidance ((x : ℂ) + (y : ℂ) * Complex.I) hboundary
      | Or.inl hupper =>
          have habs : |y| < T := abs_lt.mpr (And.intro hlower hupper)
          exact
            explicitFormulaRectangle_verticalLine_avoidsSingularSet
              T x hlevel y habs

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
    (x : ℂ) + (y : ℂ) * Complex.I ∉ completedZetaContourIntegrandSingularSet :=
  explicitFormulaRectangle_verticalLine_avoidsSingularSet_on_closedHeightSpan_of_boundaryAvoidance
    f F (h.height_schedule.height u) x y
    (fun z hz =>
      completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
        f F h u hz)
    hx hy hlevel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

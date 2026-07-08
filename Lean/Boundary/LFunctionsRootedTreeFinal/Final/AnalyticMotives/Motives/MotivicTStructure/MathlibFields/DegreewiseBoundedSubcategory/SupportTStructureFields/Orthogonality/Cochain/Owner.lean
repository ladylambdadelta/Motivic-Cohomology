import Mathlib.Tactic.Omega
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Owner

/-!
# Cech-level support orthogonality for the support t-structure

This file proves the concrete cochain-level core of the support orthogonality
field: a map from a complex supported on the lower tail at `0` to a complex
supported on the upper tail at `1` is degreewise zero, hence zero as a cochain
map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Every integer degree is outside the lower tail at `0` or outside the upper
tail at `1`. -/
theorem degree_not_in_lower_zero_or_not_in_upper_one
    (degree : ℤ) :
    (∀ lowerIndex : ℕ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).f
            lowerIndex ≠ degree) ∨
      (∀ upperIndex : ℕ,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            upperIndex ≠ degree) := by
  by_cases nonpositive : degree ≤ 0
  · exact
      Or.inr
        (fun upperIndex upperEq =>
          have upperPositive :
              0 < (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
                upperIndex := by
            omega
          have degreePositive : 0 < degree :=
            Eq.subst upperEq upperPositive
          (not_lt_of_ge nonpositive) degreePositive)
  · exact
      Or.inl
        (fun lowerIndex lowerEq =>
          have degreePositive : 0 < degree :=
            Int.lt_of_not_ge nonpositive
          have lowerNonpositive :
              (TraceAnalyticMotivicTStructure.truncLEEmbedding 0).f
                lowerIndex ≤ 0 := by
            omega
          have degreeNonpositive : degree ≤ 0 :=
            Eq.subst (Eq.symm lowerEq) lowerNonpositive
          (not_lt_of_ge degreeNonpositive) degreePositive)

/-- A component of a cochain map from lower-supported to upper-supported
complexes is zero in every degree. -/
theorem cochainMap_component_zero_of_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom : source ⟶ target)
    (degree : ℤ) :
    hom.f degree = 0 :=
  Or.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .degree_not_in_lower_zero_or_not_in_upper_one degree)
    (fun lowerComplement =>
      (sourceSupport.isZero degree lowerComplement).eq_of_src
        (hom.f degree)
        0)
    (fun upperComplement =>
      (targetSupport.isZero degree upperComplement).eq_of_tgt
        (hom.f degree)
        0)

/-- A cochain map from lower-supported to upper-supported complexes is zero. -/
theorem cochainMap_zero_of_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom : source ⟶ target) :
    hom = 0 :=
  HomologicalComplex.hom_ext
    hom
    0
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cochainMap_component_zero_of_strictSupportLE_zero_strictSupportGE_one
        sourceSupport
        targetSupport
        hom)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

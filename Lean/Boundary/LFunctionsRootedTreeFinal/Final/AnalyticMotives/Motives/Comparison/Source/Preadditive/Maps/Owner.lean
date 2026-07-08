import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Preadditive.Maps.Owner

/-!
# Additive formulas for represented comparison-source morphisms

The comparison source is the stable analytic Verdier quotient.  This file
re-exposes the represented zero, additive, and integer-scalar formulas under
comparison-source names for use by comparison and recognition theorems.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The represented comparison-source morphism of a zero additive-homotopy
morphism is zero. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_zero
    (source target : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonSource.mapOf
        (0 : source ⟶ target) =
      (0 :
        TraceAnalyticDMgmComparisonSource.objectOf source ⟶
          TraceAnalyticDMgmComparisonSource.objectOf target) :=
  TraceAnalyticStableMotiveCategory.mapOf_zero source target

/-- The represented comparison-source morphism of a sum is the sum of the
represented comparison-source morphisms. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_add
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (left right : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf (left + right) =
      TraceAnalyticDMgmComparisonSource.mapOf left +
        TraceAnalyticDMgmComparisonSource.mapOf right :=
  TraceAnalyticStableMotiveCategory.mapOf_add left right

/-- The represented comparison-source morphism of a negation is the negation
of the represented comparison-source morphism. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_neg
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf (-hom) =
      -TraceAnalyticDMgmComparisonSource.mapOf hom :=
  TraceAnalyticStableMotiveCategory.mapOf_neg hom

/-- The represented comparison-source morphism of a difference is the
difference of the represented comparison-source morphisms. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_sub
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (left right : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf (left - right) =
      TraceAnalyticDMgmComparisonSource.mapOf left -
        TraceAnalyticDMgmComparisonSource.mapOf right :=
  TraceAnalyticStableMotiveCategory.mapOf_sub left right

/-- The represented comparison-source morphism of a natural-number multiple is
the same natural-number multiple of the represented comparison-source
morphism. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_nsmul
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (multiplicity : ℕ)
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf (multiplicity • hom) =
      multiplicity • TraceAnalyticDMgmComparisonSource.mapOf hom :=
  TraceAnalyticStableMotiveCategory.mapOf_nsmul multiplicity hom

/-- The represented comparison-source morphism of an integer multiple is the
same integer multiple of the represented comparison-source morphism. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_zsmul
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (weight : ℤ)
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf (weight • hom) =
      weight • TraceAnalyticDMgmComparisonSource.mapOf hom :=
  TraceAnalyticStableMotiveCategory.mapOf_zsmul weight hom

end AnalyticMotives
end LFunctions
end Boundary

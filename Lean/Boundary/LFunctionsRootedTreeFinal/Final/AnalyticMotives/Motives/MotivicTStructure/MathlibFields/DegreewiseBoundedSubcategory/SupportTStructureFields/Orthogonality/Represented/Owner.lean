import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preadditive.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Cochain.Owner

/-!
# Represented support orthogonality

This file descends concrete cochain-level support orthogonality through the
homotopy quotient and the stable analytic Verdier quotient for represented
cochain maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The homotopy image of a cochain map from lower support at `0` to upper
support at `1` is the zero additive-homotopy morphism. -/
theorem additiveHomotopyMap_zero_of_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom : source ⟶ target) :
    TraceAnalyticAdditiveHomotopyCategory.mapOf hom =
      (0 :
        TraceAnalyticAdditiveHomotopyCategory.objectOf source ⟶
          TraceAnalyticAdditiveHomotopyCategory.objectOf target) :=
  congrArg
    TraceAnalyticAdditiveHomotopyCategory.mapOf
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .cochainMap_zero_of_strictSupportLE_zero_strictSupportGE_one
        sourceSupport
        targetSupport
        hom)

/-- The stable comparison-source image of a represented cochain map from lower
support at `0` to upper support at `1` is zero. -/
theorem representedStableMap_zero_of_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf hom) =
      (0 :
        TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf source) ⟶
          TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf target)) :=
  Eq.trans
    (congrArg
      TraceAnalyticDMgmComparisonSource.mapOf
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .additiveHomotopyMap_zero_of_strictSupportLE_zero_strictSupportGE_one
          sourceSupport
          targetSupport
          hom))
    (TraceAnalyticDMgmComparisonSource.mapOf_zero
      (TraceAnalyticAdditiveHomotopyCategory.objectOf source)
      (TraceAnalyticAdditiveHomotopyCategory.objectOf target))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

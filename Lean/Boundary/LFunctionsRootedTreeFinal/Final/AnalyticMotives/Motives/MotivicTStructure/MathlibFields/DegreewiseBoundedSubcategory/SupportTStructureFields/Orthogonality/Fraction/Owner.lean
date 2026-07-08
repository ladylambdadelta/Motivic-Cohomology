import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Homotopy.Owner

/-!
# Fraction-level represented support orthogonality

This file applies represented support orthogonality to Verdier left fractions
whose numerator is represented by an actual cochain map between disjoint
support presentations.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- If a left-fraction numerator is represented by a cochain map from lower
support at `0` to upper support at `1`, then the associated stable roof map is
zero. -/
theorem leftFraction_map_zero_of_supported_represented_numerator
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom : source ⟶ target)
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        (TraceAnalyticAdditiveHomotopyCategory.objectOf source)
        (TraceAnalyticAdditiveHomotopyCategory.objectOf target))
    (numerator_eq :
      fraction.f =
        TraceAnalyticAdditiveHomotopyCategory.mapOf hom) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_zero
      fraction
      (Eq.trans
        (congrArg
          TraceAnalyticDMgmComparisonSource.mapOf
          numerator_eq)
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .representedStableMap_zero_of_strictSupportLE_zero_strictSupportGE_one
            sourceSupport
            targetSupport
            hom))

/-- If a left-fraction numerator lands in a concrete upper-supported cochain
representative, then the associated stable roof map is zero.  No represented
numerator hypothesis is needed: the homotopy quotient is full, so the arbitrary
homotopy numerator has a cochain-map preimage. -/
theorem leftFraction_map_zero_of_supported_concrete_numerator_target
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        (TraceAnalyticAdditiveHomotopyCategory.objectOf source)
        (TraceAnalyticAdditiveHomotopyCategory.objectOf target)) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      0 :=
  TraceAnalyticDMgmComparisonSource
    .leftFraction_map_eq_zero_of_numerator_zero
      fraction
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .stableMap_zero_of_additiveHomotopyHom_strictSupportLE_zero_strictSupportGE_one
          sourceSupport
          targetSupport
          fraction.f)

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

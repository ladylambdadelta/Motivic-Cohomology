import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.SupportTStructureFields.Orthogonality.Represented.Owner

/-!
# Homotopy-level support orthogonality

The homotopy quotient functor is full, so every additive-homotopy morphism
between concrete cochain representatives has a cochain-map preimage.  This
file lifts cochain-level disjoint-support vanishing to arbitrary morphisms in
the additive homotopy category between those representatives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- Every additive-homotopy morphism between concrete cochain representatives
has a concrete cochain-map preimage. -/
theorem exists_cochainMap_preimage_of_additiveHomotopyMap
    {source target : TraceAnalyticAdditiveCochainComplex}
  (hom :
      TraceAnalyticAdditiveHomotopyCategory.objectOf source ⟶
        TraceAnalyticAdditiveHomotopyCategory.objectOf target) :
    ∃ cochainMap : source ⟶ target,
      TraceAnalyticAdditiveHomotopyCategory.mapOf cochainMap = hom :=
  TraceAnalyticAdditiveHomotopyCategory.quotientFunctor
    .map_surjective hom

/-- Any additive-homotopy morphism from lower support at `0` to upper support
at `1` is zero. -/
theorem additiveHomotopyHom_zero_of_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom :
      TraceAnalyticAdditiveHomotopyCategory.objectOf source ⟶
        TraceAnalyticAdditiveHomotopyCategory.objectOf target) :
    hom = 0 :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_cochainMap_preimage_of_additiveHomotopyMap hom)
    (fun cochainMap cochainMap_eq =>
      Eq.trans
        (Eq.symm cochainMap_eq)
        (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
          .additiveHomotopyMap_zero_of_strictSupportLE_zero_strictSupportGE_one
            sourceSupport
            targetSupport
            cochainMap))

/-- The stable comparison-source image of any additive-homotopy morphism from
lower support at `0` to upper support at `1` is zero. -/
theorem stableMap_zero_of_additiveHomotopyHom_strictSupportLE_zero_strictSupportGE_one
    {source target : TraceAnalyticAdditiveCochainComplex}
    (sourceSupport :
      source.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncLEEmbedding 0))
    (targetSupport :
      target.IsStrictlySupported
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1))
    (hom :
      TraceAnalyticAdditiveHomotopyCategory.objectOf source ⟶
        TraceAnalyticAdditiveHomotopyCategory.objectOf target) :
    TraceAnalyticDMgmComparisonSource.mapOf hom =
      (0 :
        TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf source) ⟶
          TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf target)) :=
  Eq.trans
    (congrArg
      TraceAnalyticDMgmComparisonSource.mapOf
      (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
        .additiveHomotopyHom_zero_of_strictSupportLE_zero_strictSupportGE_one
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

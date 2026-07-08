import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.YonedaDetection.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Certificate.Owner

/-!
# Represented truncation composite orthogonality

This file connects the represented truncation certificate to the concrete
Yoneda-detection orthogonality bridge.  For each represented truncation object,
the composite from its chosen lower vertex to its chosen upper vertex is zero;
therefore every probe postcomposes into that composite as zero, and faithful
preadditive Yoneda detects the same zero morphism.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- Postcomposition into the chosen represented truncation composite is zero
for every probe. -/
theorem firstMap_secondMap_postcomp_zero
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (hom : probe.unop ⟶ object.representative.lowerObject) :
    hom ≫ (object.firstMap ≫ object.secondMap) = 0 :=
  Eq.trans
    (congrArg
      (fun map => hom ≫ map)
      object.firstMap_comp_secondMap)
    (comp_zero hom)

/-- Faithful preadditive Yoneda detects that the represented truncation
composite is zero from its probe-wise postcomposition vanishing. -/
theorem firstMap_secondMap_eq_zero_by_yoneda_detection
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.firstMap ≫ object.secondMap = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .morphism_eq_zero_of_postcomp_eq_zero
      (object.firstMap ≫ object.secondMap)
      (fun probe hom =>
        object.firstMap_secondMap_postcomp_zero probe hom)

/-- The chosen lower vertex of a represented truncation object is in the
normalized `≤ 0` aisle. -/
theorem firstMap_source_mem_zero
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0
      object.representative.lowerObject :=
  Eq.subst
    object.lowerAisleObjectZero_object
    (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.membership
      object.lowerAisleObjectZero)

/-- The chosen upper vertex of a represented truncation object is in the
normalized `≥ 1` coaisle. -/
theorem secondMap_target_mem_one
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1
      object.representative.upperObject :=
  Eq.subst
    object.upperCoaisleObjectOne_object
    (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.membership
      object.upperCoaisleObjectOne)

/-- The represented truncation composite has the exact source/target
membership shape of the Mathlib `TStructure.zero'` field. -/
theorem firstMap_secondMap_eq_zero_tStructure_field
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.firstMap ≫ object.secondMap = 0 :=
  TraceAnalyticDerivedMotiveCategory
    .tStructure_zero_field_of_postcomp_eq_zero
      (object.firstMap ≫ object.secondMap)
      object.firstMap_source_mem_zero
      object.secondMap_target_mem_one
      (fun probe hom =>
        object.firstMap_secondMap_postcomp_zero probe hom)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

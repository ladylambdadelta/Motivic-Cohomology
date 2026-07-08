import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Owner

/-!
# Subcategory-valued Yoneda representative truncation existence

This file repackages the object-level Yoneda representative truncation
existence theorem with the lower and upper vertices living explicitly in the
homological aisle and coaisle full subcategories.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Objects carrying a concrete Yoneda truncation representative have a
distinguished truncation triangle whose lower and upper vertices are exposed as
objects of the homological aisle and coaisle. -/
theorem hasYonedaTruncationRepresentative_exists_subcategory_truncation_triangle
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut object) :
    ∃ (lower :
        TraceAnalyticDerivedMotiveCategory.HomologicalAisle
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut))
      (upper : TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle cut),
      ∃ (firstMap :
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).obj
              lower ⟶
            object)
        (secondMap :
          object ⟶
            (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
              cut).obj upper)
        (connectingMap :
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
              cut).obj upper ⟶
            ((TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
              (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).obj
                lower)⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory :=
  Exists.elim
    (TraceAnalyticMotivicTStructure
      .hasYonedaTruncationRepresentative_exists_object_truncation_triangle
        cut
        object
        representativeExists)
    (fun lower lowerResult =>
      Exists.elim lowerResult
        (fun upper triangleData =>
          And.elim triangleData
            (fun lowerMembership upperAndTriangle =>
              And.elim upperAndTriangle
                (fun upperMembership triangleExists =>
                  Exists.elim triangleExists
                    (fun firstMap secondAndConnecting =>
                      Exists.elim secondAndConnecting
                        (fun secondMap connectingAndDistinguished =>
                          Exists.elim connectingAndDistinguished
                            (fun connectingMap distinguished =>
                              Exists.intro
                                (⟨lower, lowerMembership⟩ :
                                  TraceAnalyticDerivedMotiveCategory
                                    .HomologicalAisle
                                      (TraceAnalyticMotivicTStructure
                                        .decompositionLowerCut cut))
                                (Exists.intro
                                  (⟨upper, upperMembership⟩ :
                                    TraceAnalyticDerivedMotiveCategory
                                      .HomologicalCoaisle cut)
                                  (Exists.intro
                                    firstMap
                                    (Exists.intro
                                      secondMap
                                      (Exists.intro
                                        connectingMap
                                        distinguished)))))))))))

/-- Adjacent subcategory-valued truncation existence in the normalized
`≤ 0`, `≥ 1` case. -/
theorem hasYonedaTruncationRepresentative_exists_subcategory_triangle_zero_one
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower : TraceAnalyticDerivedMotiveCategory.HomologicalAisle 0)
      (upper : TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle 1),
      ∃ (firstMap :
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            0).obj lower ⟶
            object)
        (secondMap :
          object ⟶
            (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
              1).obj upper)
        (connectingMap :
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
              1).obj upper ⟶
            ((TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
              0).obj lower)⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_subcategory_truncation_triangle
      1
      object
      representativeExists

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Owner

/-!
# Mathlib field-order Yoneda representative truncation existence

This file rewrites the Yoneda representative truncation existence theorem in
the exact binder order used by Mathlib's `TStructure.exists_triangle_zero_one`
field.  The theorem is scoped to objects equipped with concrete Yoneda
representative data.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Field-order truncation existence for an object carrying a concrete Yoneda
truncation representative. -/
theorem hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
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
                                lower
                                (Exists.intro
                                  upper
                                  (Exists.intro
                                    lowerMembership
                                    (Exists.intro
                                      upperMembership
                                      (Exists.intro
                                        firstMap
                                        (Exists.intro
                                          secondMap
                                          (Exists.intro
                                            connectingMap
                                            distinguished)))))))))))))

/-- Adjacent field-order truncation existence for an object carrying a
concrete Yoneda truncation representative at cut `1`. -/
theorem hasYonedaTruncationRepresentative_exists_triangle_zero_one_fieldShape
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
      1
      object
      representativeExists

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

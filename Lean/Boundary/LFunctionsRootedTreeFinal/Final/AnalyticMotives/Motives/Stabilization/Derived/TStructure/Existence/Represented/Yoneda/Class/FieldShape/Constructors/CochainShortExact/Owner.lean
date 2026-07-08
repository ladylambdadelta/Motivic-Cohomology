import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.CochainShortExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Owner

/-!
# Cochain short-exact constructor for field-order truncation existence

This file composes the cochain short-exact constructor for
`HasYonedaTruncationRepresentative` with the field-order truncation theorem.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Cochain-level short exactness at cut `1` gives the exact field-order
truncation triangle for the represented derived object. -/
theorem cochainShortExact_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (cochainShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap :
        lower ⟶
          TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex))
      (secondMap :
        TraceAnalyticDerivedMotiveCategory.objectOf
            (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex) ⟶
          upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_triangle_zero_one_fieldShape
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex))
      (TraceAnalyticMotivicTStructure
        .hasYonedaTruncationRepresentativeOneOfCochainShortExact
          complex
          hasHomology
          cochainShortExact)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

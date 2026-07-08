import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Heart.MathlibTransport.Owner

/-!
# Mathlib-facing heart representatives

This file transports exact-degree shifted bounded analytic heart
representatives through the concrete equivalence from the iso-closed analytic
heart to the Mathlib-facing reindexed heart.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace HeartMathlibReindexed

/-- A shifted bounded representative as a Mathlib-facing reindexed heart
object at its own degree. -/
def ofShiftedBoundedSelf
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed degree :=
  (TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence degree).functor.obj
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.ofShiftedBoundedSelf complex degree)

/-- A translated shifted bounded representative as a Mathlib-facing reindexed
heart object. -/
def ofShiftedBoundedSelfAddRight
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed
      (degree + shift) :=
  (TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence
      (degree + shift)).functor.obj
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.ofShiftedBoundedSelf complex (degree + shift))

/-- The Mathlib-facing exact-degree representative is the transport of the
iso-closed exact-degree representative through the concrete heart
equivalence. -/
theorem ofShiftedBoundedSelf_eq_equivalence_functor_obj
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed.ofShiftedBoundedSelf
        complex
        degree =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence degree).functor.obj
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofShiftedBoundedSelf complex degree) :=
  rfl

/-- The Mathlib-facing exact-degree representative has the expected ambient
stable comparison-source object. -/
theorem ofShiftedBoundedSelf_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- Including the Mathlib-facing exact-degree representative into the ambient
comparison source gives the expected shifted bounded stable object. -/
theorem ofShiftedBoundedSelf_inclusion_obj
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion
        degree).obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- The Mathlib-facing translated exact-degree representative is the transport
of the iso-closed representative at `degree + shift` through the concrete
heart equivalence. -/
theorem ofShiftedBoundedSelfAddRight_eq_equivalence_functor_obj
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotivicTStructure.HeartMathlibReindexed
        .ofShiftedBoundedSelfAddRight shift complex degree =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence
          (degree + shift)).functor.obj
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofShiftedBoundedSelf complex (degree + shift)) :=
  rfl

/-- The Mathlib-facing translated exact-degree representative has the expected
ambient stable comparison-source object. -/
theorem ofShiftedBoundedSelfAddRight_object
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
        shift
        complex
        degree).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- Including the Mathlib-facing translated exact-degree representative into
the ambient comparison source gives the expected translated shifted bounded
stable object. -/
theorem ofShiftedBoundedSelfAddRight_inclusion_obj
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion
        (degree + shift)).obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end HeartMathlibReindexed

namespace HeartIsoClosed

/-- Applying the concrete heart equivalence to an exact-degree iso-closed
representative gives the Mathlib-facing exact-degree representative. -/
theorem ofShiftedBoundedSelf_equivalence_functor_obj
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).functor.obj
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofShiftedBoundedSelf complex degree) =
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed
        .ofShiftedBoundedSelf complex degree :=
  rfl

/-- Including the equivalence-functor image of an exact-degree iso-closed
representative gives the expected shifted bounded stable object. -/
theorem ofShiftedBoundedSelf_equivalence_functor_inclusion_obj
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion
        degree).obj
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence degree).functor.obj
          (TraceAnalyticMotivicTStructure
            .HeartIsoClosed.ofShiftedBoundedSelf complex degree)) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- Applying the concrete heart equivalence to a translated exact-degree
iso-closed representative gives the Mathlib-facing translated representative. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_functor_obj
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).functor.obj
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofShiftedBoundedSelf complex (degree + shift)) =
      TraceAnalyticMotivicTStructure.HeartMathlibReindexed
        .ofShiftedBoundedSelfAddRight shift complex degree :=
  rfl

/-- Including the equivalence-functor image of a translated exact-degree
iso-closed representative gives the expected translated shifted bounded stable
object. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_functor_inclusion_obj
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.HeartMathlibReindexed.inclusion
        (degree + shift)).obj
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence
            (degree + shift)).functor.obj
          (TraceAnalyticMotivicTStructure
            .HeartIsoClosed.ofShiftedBoundedSelf
              complex
              (degree + shift))) =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

end HeartIsoClosed

namespace HeartMathlibReindexed

/-- Transporting the Mathlib-facing exact-degree representative back through
the inverse heart equivalence recovers the iso-closed exact-degree
representative. -/
theorem ofShiftedBoundedSelf_equivalence_inverse_obj
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
        complex
        degree :=
  rfl

/-- The recovered iso-closed representative has the expected ambient stable
comparison-source object. -/
theorem ofShiftedBoundedSelf_equivalence_inverse_obj_object
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree :=
  rfl

/-- The counit component of the concrete heart equivalence at a Mathlib-facing
exact-degree representative is the component of the defining `eqToIso`
round-trip. -/
theorem ofShiftedBoundedSelf_equivalence_counit_hom_app
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).counitIso.hom.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed
            degree)).hom.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) :=
  rfl

/-- The inverse counit component of the concrete heart equivalence at a
Mathlib-facing exact-degree representative is the inverse component of the
defining `eqToIso` round-trip. -/
theorem ofShiftedBoundedSelf_equivalence_counit_inv_app
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).counitIso.inv.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed
            degree)).inv.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree) :=
  rfl

/-- The unit component at the inverse image of a Mathlib-facing exact-degree
representative is determined by the inverse image of the representative
counit inverse component. -/
theorem ofShiftedBoundedSelf_equivalence_unit_hom_app_inverse
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).unitIso.hom.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.obj
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence degree).counitIso.inv.app
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)) :=
  TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence_unit_hom_app_inverse
      (TraceAnalyticMotivicTStructure
        .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)

/-- The inverse unit component at the inverse image of a Mathlib-facing
exact-degree representative is determined by the inverse image of the
representative counit component. -/
theorem ofShiftedBoundedSelf_equivalence_unit_inv_app_inverse
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence degree).unitIso.inv.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.obj
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence degree).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence degree).counitIso.hom.app
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)) :=
  TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence_unit_inv_app_inverse
      (TraceAnalyticMotivicTStructure
        .HeartMathlibReindexed.ofShiftedBoundedSelf complex degree)

/-- Transporting the Mathlib-facing translated exact-degree representative
back through the inverse heart equivalence recovers the iso-closed
representative at `degree + shift`. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_inverse_obj
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).inverse.obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) =
      TraceAnalyticMotivicTStructure.HeartIsoClosed.ofShiftedBoundedSelf
        complex
        (degree + shift) :=
  rfl

/-- The recovered iso-closed translated representative has the expected
ambient stable comparison-source object. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_inverse_obj_object
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    ((TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).inverse.obj
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree)).object =
      TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) :=
  rfl

/-- The counit component of the concrete heart equivalence at a Mathlib-facing
translated exact-degree representative is the component of the defining
`eqToIso` round-trip. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_counit_hom_app
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).counitIso.hom.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed
            (degree + shift))).hom.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) :=
  rfl

/-- The inverse counit component of the concrete heart equivalence at a
Mathlib-facing translated exact-degree representative is the inverse component
of the defining `eqToIso` round-trip. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_counit_inv_app
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).counitIso.inv.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) =
      (eqToIso
        (TraceAnalyticMotivicTStructure
          .HeartIsoClosed.ofMathlibReindexed_comp_toMathlibReindexed
            (degree + shift))).inv.app
        (TraceAnalyticMotivicTStructure
          .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
            shift
            complex
            degree) :=
  rfl

/-- The unit component at the inverse image of a Mathlib-facing translated
exact-degree representative is determined by the inverse image of the
representative counit inverse component. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_unit_hom_app_inverse
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).unitIso.hom.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence
            (degree + shift)).inverse.obj
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree)) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence
          (degree + shift)).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence
            (degree + shift)).counitIso.inv.app
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree)) :=
  TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence_unit_hom_app_inverse
      (TraceAnalyticMotivicTStructure
        .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree)

/-- The inverse unit component at the inverse image of a Mathlib-facing
translated exact-degree representative is determined by the inverse image of
the representative counit component. -/
theorem ofShiftedBoundedSelfAddRight_equivalence_unit_inv_app_inverse
    (shift : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .HeartIsoClosed.mathlibReindexedEquivalence
        (degree + shift)).unitIso.inv.app
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence
            (degree + shift)).inverse.obj
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree)) =
      (TraceAnalyticMotivicTStructure
        .HeartIsoClosed.mathlibReindexedEquivalence
          (degree + shift)).inverse.map
        ((TraceAnalyticMotivicTStructure
          .HeartIsoClosed.mathlibReindexedEquivalence
            (degree + shift)).counitIso.hom.app
          (TraceAnalyticMotivicTStructure
            .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
              shift
              complex
              degree)) :=
  TraceAnalyticMotivicTStructure
    .HeartIsoClosed.mathlibReindexedEquivalence_unit_inv_app_inverse
      (TraceAnalyticMotivicTStructure
        .HeartMathlibReindexed.ofShiftedBoundedSelfAddRight
          shift
          complex
          degree)

end HeartMathlibReindexed
end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

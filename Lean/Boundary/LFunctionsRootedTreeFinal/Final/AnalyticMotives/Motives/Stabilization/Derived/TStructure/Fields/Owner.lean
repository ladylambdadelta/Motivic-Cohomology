import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Monotonicity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Subcategories.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Constructors.CochainShortExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Constructors.Degreewise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Constructors.ProbeDegreeCasewise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.AbelianEnvelope.Surface.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Constructors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Preimage.Owner

/-!
# Proved field surface for the represented derived analytic t-structure

This file gathers the concrete homological predicate, monotonicity, shift, and
represented truncation-existence fields already proved for the derived analytic
motive category.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The derived analytic `≤ cut` predicate field. -/
abbrev tStructureLE
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory → Prop :=
  TraceAnalyticDerivedMotiveCategory.HomologicalLE cut

/-- The derived analytic `≥ cut` predicate field. -/
abbrev tStructureGE
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory → Prop :=
  TraceAnalyticDerivedMotiveCategory.HomologicalGE cut

/-- The adjacent monotonicity field for the derived analytic `≤` predicate. -/
theorem tStructureLE_zero_le :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 :=
  fun object membership =>
    TraceAnalyticDerivedMotiveCategory.homologicalLE_mono
      (show (0 : ℤ) ≤ 1 from Int.zero_le_one)
      object
      membership

/-- The adjacent monotonicity field for the derived analytic `≥` predicate. -/
theorem tStructureGE_one_le :
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  fun object membership =>
    TraceAnalyticDerivedMotiveCategory.homologicalGE_antitone
      (show (0 : ℤ) ≤ 1 from Int.zero_le_one)
      object
      membership

/-- The closed-under-isomorphisms field for the derived analytic `≤`
predicate. -/
def tStructureLE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDerivedMotiveCategory.tStructureLE cut) :=
  TraceAnalyticDerivedMotiveCategory
    .homologicalLE_closedUnderIsomorphisms cut

/-- The closed-under-isomorphisms field for the derived analytic `≥`
predicate. -/
def tStructureGE_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticDerivedMotiveCategory.tStructureGE cut) :=
  TraceAnalyticDerivedMotiveCategory
    .homologicalGE_closedUnderIsomorphisms cut

/-- Concrete shift transport for the derived analytic `≤` predicate. -/
theorem tStructureLE_shift_cutSub
    (cut shift : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE
      (cut - shift)
      (object⟦shift⟧) :=
  TraceAnalyticDerivedMotiveCategory.homologicalLE_shift
    cut
    shift
    object
    membership

/-- Concrete shift transport for the derived analytic `≥` predicate. -/
theorem tStructureGE_shift_cutSub
    (cut shift : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE cut object) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE
      (cut - shift)
      (object⟦shift⟧) :=
  TraceAnalyticDerivedMotiveCategory.homologicalGE_shift
    cut
    shift
    object
    membership

end TraceAnalyticDerivedMotiveCategory

namespace TraceAnalyticMotivicTStructure

/-- The represented-Yoneda truncation existence field at an arbitrary upper
cut. -/
theorem derivedTStructure_representedYoneda_exists_truncation_triangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.tStructureLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE cut upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex))
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .yonedaRepresentedDerived_exists_truncation_triangle_of_degreewise
      cut
      complex
      hdegree

/-- The represented-Yoneda adjacent truncation existence field in the
`≤ 0`, `≥ 1` normalization. -/
theorem derivedTStructure_representedYoneda_exists_triangle_zero_one
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex))
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .yonedaRepresentedDerived_exists_triangle_zero_one_of_degreewise
      complex
      hdegree

/-- Truncation existence field for any object carrying a concrete Yoneda
truncation representative. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_truncation_triangle
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.tStructureLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_object_truncation_triangle
      cut
      object
      representativeExists

/-- Adjacent truncation existence field for any object carrying a concrete
Yoneda truncation representative at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_triangle_zero_one
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_triangle_zero_one
      object
      representativeExists

/-- Subcategory-valued truncation existence field for any object carrying a
concrete Yoneda truncation representative. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_subcategory_truncation_triangle
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
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_subcategory_truncation_triangle
      cut
      object
      representativeExists

/-- Adjacent subcategory-valued truncation existence field for any object
carrying a concrete Yoneda truncation representative at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_subcategory_triangle_zero_one
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
    .hasYonedaTruncationRepresentative_exists_subcategory_triangle_zero_one
      object
      representativeExists

/-- Field-order truncation existence for any object carrying a concrete Yoneda
truncation representative. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_truncation_triangle_fieldShape
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.tStructureLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE cut upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
      cut
      object
      representativeExists

/-- Adjacent field-order truncation existence for any object carrying a
concrete Yoneda truncation representative at cut `1`. -/
theorem derivedTStructure_hasYonedaTruncationRepresentative_exists_triangle_zero_one_fieldShape
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_triangle_zero_one_fieldShape
      object
      representativeExists

/-- Degreewise short exactness at cut `1` gives the adjacent field-order
truncation triangle for the represented derived object. -/
theorem derivedTStructure_degreewise_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (degreewiseShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
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
    .degreewise_exists_triangle_zero_one_fieldShape
      complex
      hasHomology
      degreewiseShortExact

/-- Cochain-level short exactness at cut `1` gives the adjacent field-order
truncation triangle for the represented derived object. -/
theorem derivedTStructure_cochainShortExact_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (cochainShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex 1 complex)) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
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
    .cochainShortExact_exists_triangle_zero_one_fieldShape
      complex
      hasHomology
      cochainShortExact

/-- Probe-degree analytic data at an arbitrary cut gives the field-order
truncation triangle for the represented derived object. -/
theorem derivedTStructure_probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.tStructureLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE cut upper)
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
    .probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
      cut
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Probe-degree analytic data at cut `1` gives the adjacent field-order
truncation triangle for the represented derived object. -/
theorem derivedTStructure_probeDegreeCasewise_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              (1 - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                (1 - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
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
    .probeDegreeCasewise_exists_triangle_zero_one_fieldShape
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Intrinsic probe-degree analytic data on the canonical cochain preimage at
an arbitrary cut gives the field-order truncation triangle for an arbitrary
derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_probeDegreeCasewise_exists_truncation_triangle_fieldShape
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ :
        TraceAnalyticDerivedMotiveCategory.tStructureLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE cut upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .cochainPreimage_exists_truncation_triangle_fieldShape_of_probeDegree_casewise
      cut
      object
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Intrinsic probe-degree analytic data on the canonical cochain preimage at
cut `1` gives the adjacent field-order truncation triangle for an arbitrary
derived analytic motive. -/
theorem derivedTStructure_cochainPreimage_probeDegreeCasewise_exists_triangle_zero_one_fieldShape
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .derivedTStructure_cochainPreimage_probeDegreeCasewise_exists_truncation_triangle_fieldShape
      1
      object
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

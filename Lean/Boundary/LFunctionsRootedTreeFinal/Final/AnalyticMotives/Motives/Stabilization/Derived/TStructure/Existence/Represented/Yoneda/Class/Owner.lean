import Mathlib.CategoryTheory.ClosedUnderIsomorphisms
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Owner

/-!
# Objects with Yoneda truncation representatives

This file defines the concrete class of derived analytic motives whose
truncation triangle is supplied by a Yoneda abelian-envelope cochain
representative and the degreewise exact analytic truncation sequence.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Concrete representative data for applying the analytic truncation calculus
to a derived analytic motive at `cut`. -/
structure YonedaTruncationRepresentative
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory) where
  complex : TraceAnalyticAdditiveCochainComplex
  hasHomology : ∀ degree : ℤ, complex.HasHomology degree
  degreewiseShortExact :
    letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
    ∀ degree : ℤ,
      ((TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).ShortExact
  iso :
    object ≅
      TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)

/-- The proposition that an object carries concrete Yoneda truncation
representative data at `cut`. -/
def HasYonedaTruncationRepresentative
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory) :
    Prop :=
  Nonempty
    (TraceAnalyticMotivicTStructure
      .YonedaTruncationRepresentative cut object)

/-- The representative complex carried by Yoneda truncation representative
data. -/
def YonedaTruncationRepresentative.representingComplex
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    TraceAnalyticAdditiveCochainComplex :=
  representative.complex

/-- The derived iso carried by Yoneda truncation representative data. -/
def YonedaTruncationRepresentative.representingIso
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    object ≅
      TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope
          .yonedaCochainComplex representative.complex) :=
  representative.iso

/-- The Yoneda-represented object of a complex has the corresponding
representative data whenever the degreewise truncation sequence is short
exact. -/
def yonedaTruncationRepresentativeOfDegreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (degreewiseShortExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticMotivicTStructure.YonedaTruncationRepresentative
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) where
  complex := complex
  hasHomology := hasHomology
  degreewiseShortExact := degreewiseShortExact
  iso := Iso.refl _

/-- A concrete Yoneda representative supplies the analytic truncation triangle
for its represented derived object. -/
theorem YonedaTruncationRepresentative.exists_represented_truncation_triangle
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap :
              lower ⟶
                TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex representative.complex))
            (secondMap :
              TraceAnalyticDerivedMotiveCategory.objectOf
                  (TraceAnalyticAdditiveAbelianEnvelope
                    .yonedaCochainComplex representative.complex) ⟶
                upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .yonedaRepresentedDerived_exists_truncation_triangle_of_degreewise
      cut
      representative.complex
      representative.degreewiseShortExact

/-- A concrete Yoneda representative supplies the analytic truncation triangle
for the derived object it represents up to isomorphism. -/
theorem YonedaTruncationRepresentative.exists_object_truncation_triangle
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  Exists.elim representative.exists_represented_truncation_triangle
    (fun lower representedResult =>
      Exists.elim representedResult
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
                            (fun connectingMap oldDistinguished =>
                              let pulledTriangle :
                                  Triangle
                                    TraceAnalyticDerivedMotiveCategory :=
                                Triangle.mk
                                  (firstMap ≫ representative.iso.inv)
                                  (representative.iso.hom ≫ secondMap)
                                  connectingMap
                              let oldTriangle :
                                  Triangle
                                    TraceAnalyticDerivedMotiveCategory :=
                                Triangle.mk
                                  firstMap
                                  secondMap
                                  connectingMap
                              let triangleIso :
                                  pulledTriangle ≅ oldTriangle :=
                                Triangle.isoMk
                                  pulledTriangle
                                  oldTriangle
                                  (Iso.refl lower)
                                  representative.iso
                                  (Iso.refl upper)
                                  (Eq.trans
                                    (Category.assoc
                                      firstMap
                                      representative.iso.inv
                                      representative.iso.hom)
                                    (Eq.trans
                                      (congrArg
                                        (fun map => firstMap ≫ map)
                                        representative.iso.inv_hom_id)
                                      (Eq.trans
                                        (Category.comp_id firstMap)
                                        (Eq.symm
                                          (Category.id_comp firstMap)))))
                                  (Category.comp_id
                                    (representative.iso.hom ≫ secondMap))
                                  (Eq.trans
                                    (Category.comp_id connectingMap)
                                    (Eq.symm
                                      (Category.id_comp connectingMap)))
                              Exists.intro
                                lower
                                (Exists.intro
                                  upper
                                  (And.intro
                                    lowerMembership
                                    (And.intro
                                      upperMembership
                                      (Exists.intro
                                        (firstMap ≫ representative.iso.inv)
                                        (Exists.intro
                                          (representative.iso.hom ≫ secondMap)
                                          (Exists.intro
                                            connectingMap
                                            (isomorphic_distinguished
                                              oldTriangle
                                              oldDistinguished
                                              pulledTriangle
                                              triangleIso.symm)))))))))))))

/-- Public truncation existence for objects carrying a concrete Yoneda
truncation representative. -/
theorem hasYonedaTruncationRepresentative_exists_object_truncation_triangle
    (cut : ℤ)
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  Nonempty.elim representativeExists
    (fun representative =>
      representative.exists_object_truncation_triangle)

/-- Public adjacent truncation existence in the normalized `≤ 0`, `≥ 1`
case for objects carrying a concrete Yoneda truncation representative at
cut `1`. -/
theorem hasYonedaTruncationRepresentative_exists_triangle_zero_one
    (object : TraceAnalyticDerivedMotiveCategory)
    (representativeExists :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative 1 object) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory),
      TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower ∧
        TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper ∧
          ∃ (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentative_exists_object_truncation_triangle
      1
      object
      representativeExists

/-- The `HasYonedaTruncationRepresentative` predicate is transported along
isomorphisms. -/
theorem hasYonedaTruncationRepresentative_of_iso
    (cut : ℤ)
    {source target : TraceAnalyticDerivedMotiveCategory}
    (iso : source ≅ target)
    (hsource :
      TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut source) :
    TraceAnalyticMotivicTStructure
      .HasYonedaTruncationRepresentative cut target :=
  Nonempty.elim hsource
    (fun representative =>
      Nonempty.intro
        { complex := representative.complex
          hasHomology := representative.hasHomology
          degreewiseShortExact := representative.degreewiseShortExact
          iso := iso.symm ≪≫ representative.iso })

/-- Objects carrying Yoneda truncation representative data are closed under
isomorphisms. -/
def hasYonedaTruncationRepresentative_closedUnderIsomorphisms
    (cut : ℤ) :
    CategoryTheory.ClosedUnderIsomorphisms
      (TraceAnalyticMotivicTStructure
        .HasYonedaTruncationRepresentative cut) where
  of_iso := fun iso hsource =>
    TraceAnalyticMotivicTStructure
      .hasYonedaTruncationRepresentative_of_iso cut iso hsource

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary

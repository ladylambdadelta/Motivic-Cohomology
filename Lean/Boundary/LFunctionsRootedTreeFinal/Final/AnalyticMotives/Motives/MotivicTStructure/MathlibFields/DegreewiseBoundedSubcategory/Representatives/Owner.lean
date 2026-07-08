import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Preimage.Cochain.Owner

/-!
# Concrete representatives of degreewise bounded stable objects

This file exposes the concrete cochain representative carried by the
degreewise iso-closure bounded predicate.  It is the object-level bridge needed
before arbitrary morphisms in the degreewise bounded source can be reduced to
analytic roofs between concrete cochain complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A degreewise bounded stable object has a concrete analytic cochain
representative whose degree objects are bounded up to iso-closure. -/
theorem exists_degreewiseIsoClosureBoundedCochainRepresentative
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (bound : Nat),
      ∃ (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy complex bound ∧
          TraceAnalyticDMgmComparisonSource.objectOf
              (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ≅
            object.object :=
  Exists.elim
    object.membership
    (fun representative representativeData =>
      Exists.elim
        representativeData
        (fun representativeMembership representativeIsoData =>
          Nonempty.elim
            representativeIsoData
            (fun representativeIso =>
              Exists.elim
                representativeMembership
                (fun bound boundData =>
                  Exists.elim
                    boundData
                    (fun complex complexData =>
                      Exists.intro
                        bound
                        (Exists.intro
                          complex
                          (And.intro
                            complexData.left
                            ((eqToIso
                              (Eq.symm complexData.right)) ≪≫
                              representativeIso)))))))))

/-- The concrete representative theorem, restated with the full-subcategory
object coerced directly to its ambient comparison-source object. -/
theorem exists_degreewiseIsoClosureBoundedCochainRepresentative_obj
    (object :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable) :
    ∃ (bound : Nat),
      ∃ (complex : TraceAnalyticAdditiveCochainComplex),
        TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy complex bound ∧
          TraceAnalyticDMgmComparisonSource.objectOf
              (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ≅
            object.obj :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .exists_degreewiseIsoClosureBoundedCochainRepresentative object

/-- A morphism between degreewise bounded stable objects can be conjugated to
a morphism between concrete degreewise-bounded cochain representatives of its
source and target. -/
theorem exists_representativeMorphism
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ representativeMorphism :
                      TraceAnalyticDMgmComparisonSource.objectOf
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            sourceComplex) ⟶
                        TraceAnalyticDMgmComparisonSource.objectOf
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            targetComplex),
                      representativeMorphism ≫ targetIso.hom =
                        sourceIso.hom ≫ morphism :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_degreewiseIsoClosureBoundedCochainRepresentative source)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceRepresentativeData =>
          And.elim
            sourceRepresentativeData
            (fun sourceBounded sourceIso =>
              Exists.elim
                (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
                  .exists_degreewiseIsoClosureBoundedCochainRepresentative
                    target)
                (fun targetBound targetData =>
                  Exists.elim
                    targetData
                    (fun targetComplex targetRepresentativeData =>
                      And.elim
                        targetRepresentativeData
                        (fun targetBounded targetIso =>
                          let representativeMorphism :
                              TraceAnalyticDMgmComparisonSource.objectOf
                                  (TraceAnalyticAdditiveHomotopyCategory
                                    .objectOf sourceComplex) ⟶
                                TraceAnalyticDMgmComparisonSource.objectOf
                                  (TraceAnalyticAdditiveHomotopyCategory
                                    .objectOf targetComplex) :=
                            sourceIso.hom ≫ morphism ≫ targetIso.inv
                          let representativeMorphism_fac :
                              representativeMorphism ≫ targetIso.hom =
                                sourceIso.hom ≫ morphism :=
                            Eq.trans
                              (Category.assoc
                                (sourceIso.hom ≫ morphism)
                                targetIso.inv
                                targetIso.hom)
                              (Eq.trans
                                (congrArg
                                  (fun right =>
                                    (sourceIso.hom ≫ morphism) ≫ right)
                                  targetIso.inv_hom_id)
                                (Category.comp_id
                                  (sourceIso.hom ≫ morphism)))
                          Exists.intro
                            sourceBound
                            (Exists.intro
                              sourceComplex
                              (Exists.intro
                                sourceBounded
                                (Exists.intro
                                  sourceIso
                                  (Exists.intro
                                    targetBound
                                    (Exists.intro
                                      targetComplex
                                      (Exists.intro
                                        targetBounded
                                        (Exists.intro
                                          targetIso
                                          (Exists.intro
                                            representativeMorphism
                                            representativeMorphism_fac))))))))))))))

/-- A morphism between degreewise bounded stable objects can be represented by
a Verdier left fraction between concrete degreewise-bounded cochain
representatives, after conjugating by the representative isomorphisms. -/
theorem exists_representativeLeftFraction
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (fraction :
                      TraceAnalyticStableNullSubcategory
                        .invertedMorphisms.LeftFraction
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            sourceComplex)
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            targetComplex)),
                      fraction.map
                          TraceAnalyticDMgmComparisonSource.quotientFunctor
                          (CategoryTheory.Localization.inverts
                            TraceAnalyticDMgmComparisonSource.quotientFunctor
                            TraceAnalyticStableNullSubcategory
                              .invertedMorphisms) ≫
                          targetIso.hom =
                        sourceIso.hom ≫ morphism :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeMorphism morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceBoundedData =>
          Exists.elim
            sourceBoundedData
            (fun sourceBounded sourceIsoData =>
              Exists.elim
                sourceIsoData
                (fun sourceIso targetBoundData =>
                  Exists.elim
                    targetBoundData
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetBoundedData =>
                          Exists.elim
                            targetBoundedData
                            (fun targetBounded targetIsoData =>
                              Exists.elim
                                targetIsoData
                                (fun targetIso representativeData =>
                                  Exists.elim
                                    representativeData
                                    (fun representativeMorphism
                                      representativeMorphism_fac =>
                                      Exists.elim
                                        (TraceAnalyticDMgmComparisonSource
                                          .exists_leftFraction
                                            representativeMorphism)
                                        (fun fraction fraction_eq =>
                                          let fraction_fac :
                                              fraction.map
                                                  TraceAnalyticDMgmComparisonSource
                                                    .quotientFunctor
                                                  (CategoryTheory.Localization
                                                    .inverts
                                                      TraceAnalyticDMgmComparisonSource
                                                        .quotientFunctor
                                                      TraceAnalyticStableNullSubcategory
                                                        .invertedMorphisms) ≫
                                                  targetIso.hom =
                                                sourceIso.hom ≫ morphism :=
                                            Eq.trans
                                              (congrArg
                                                (fun left =>
                                                  left ≫ targetIso.hom)
                                                (Eq.symm fraction_eq))
                                              representativeMorphism_fac
                                          Exists.intro
                                            sourceBound
                                            (Exists.intro
                                              sourceComplex
                                              (Exists.intro
                                                sourceBounded
                                                (Exists.intro
                                                  sourceIso
                                                  (Exists.intro
                                                    targetBound
                                                    (Exists.intro
                                                      targetComplex
                                                      (Exists.intro
                                                        targetBounded
                                                        (Exists.intro
                                                          targetIso
                                                          (Exists.intro
                                                            fraction
                                                            fraction_fac))))))))))))))))))))

/-- A morphism between degreewise bounded stable objects has a concrete
left-fraction representative whose localized numerator agrees with the
conjugated morphism after postcomposition by the localized denominator. -/
theorem exists_representativeLeftFraction_numerator
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (fraction :
                      TraceAnalyticStableNullSubcategory
                        .invertedMorphisms.LeftFraction
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            sourceComplex)
                          (TraceAnalyticAdditiveHomotopyCategory.objectOf
                            targetComplex)),
                      (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                          (TraceAnalyticDMgmComparisonSource
                            .quotientFunctor.map fraction.s) =
                        TraceAnalyticDMgmComparisonSource
                          .quotientFunctor.map fraction.f :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeMorphism morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceBoundedData =>
          Exists.elim
            sourceBoundedData
            (fun sourceBounded sourceIsoData =>
              Exists.elim
                sourceIsoData
                (fun sourceIso targetBoundData =>
                  Exists.elim
                    targetBoundData
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetBoundedData =>
                          Exists.elim
                            targetBoundedData
                            (fun targetBounded targetIsoData =>
                              Exists.elim
                                targetIsoData
                                (fun targetIso representativeData =>
                                  Exists.elim
                                    representativeData
                                    (fun representativeMorphism
                                      representativeMorphism_fac =>
                                      Exists.elim
                                        (TraceAnalyticDMgmComparisonSource
                                          .exists_leftFraction
                                            representativeMorphism)
                                        (fun fraction fraction_eq =>
                                          let representativeMorphism_eq :
                                              representativeMorphism =
                                                sourceIso.hom ≫
                                                  morphism ≫
                                                    targetIso.inv :=
                                            Eq.trans
                                              (Eq.symm
                                                (Eq.trans
                                                  (Category.assoc
                                                    representativeMorphism
                                                    targetIso.hom
                                                    targetIso.inv)
                                                  (Eq.trans
                                                    (congrArg
                                                      (fun right =>
                                                        representativeMorphism ≫
                                                          right)
                                                      targetIso.hom_inv_id)
                                                    (Category.comp_id
                                                      representativeMorphism))))
                                              (Eq.trans
                                                (congrArg
                                                  (fun left =>
                                                    left ≫ targetIso.inv)
                                                  representativeMorphism_fac)
                                                (Category.assoc
                                                  sourceIso.hom
                                                  morphism
                                                  targetIso.inv))
                                          let fractionMap_eq_conjugate :
                                              fraction.map
                                                  TraceAnalyticDMgmComparisonSource
                                                    .quotientFunctor
                                                  (CategoryTheory.Localization
                                                    .inverts
                                                      TraceAnalyticDMgmComparisonSource
                                                        .quotientFunctor
                                                      TraceAnalyticStableNullSubcategory
                                                        .invertedMorphisms) =
                                                sourceIso.hom ≫
                                                  morphism ≫ targetIso.inv :=
                                            Eq.trans
                                              fraction_eq
                                              representativeMorphism_eq
                                          let conjugate_comp_denominator :
                                              (sourceIso.hom ≫
                                                    morphism ≫ targetIso.inv) ≫
                                                  (TraceAnalyticDMgmComparisonSource
                                                    .quotientFunctor.map
                                                    fraction.s) =
                                                TraceAnalyticDMgmComparisonSource
                                                  .quotientFunctor.map
                                                  fraction.f :=
                                            Eq.trans
                                              (congrArg
                                                (fun left =>
                                                  left ≫
                                                    TraceAnalyticDMgmComparisonSource
                                                      .quotientFunctor.map
                                                      fraction.s)
                                                (Eq.symm
                                                  fractionMap_eq_conjugate))
                                              (TraceAnalyticDMgmComparisonSource
                                                .leftFraction_map_comp_denominator
                                                  fraction)
                                          Exists.intro
                                            sourceBound
                                            (Exists.intro
                                              sourceComplex
                                              (Exists.intro
                                                sourceBounded
                                                (Exists.intro
                                                  sourceIso
                                                  (Exists.intro
                                                    targetBound
                                                    (Exists.intro
                                                      targetComplex
                                                      (Exists.intro
                                                        targetBounded
                                                        (Exists.intro
                                                          targetIso
                                                          (Exists.intro
                                                            fraction
                                                            conjugate_comp_denominator))))))))))))))))))))

/-- A Verdier-inverted denominator whose source is a degreewise bounded
cochain representative transports degreewise boundedness to its roof vertex
after passing to the stable comparison source. -/
theorem roofVertex_degreewiseIsoClosureBoundedStableObject_of_denominator
    {bound : Nat}
    {targetComplex : TraceAnalyticAdditiveCochainComplex}
    (targetBounded :
      TraceAnalyticMotiveComparison
        .sourceComplexDegreewiseIsoClosureBoundedBy
          targetComplex
          bound)
    {roofVertex : TraceAnalyticAdditiveHomotopyCategory}
    (denominator :
      TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex ⟶
        roofVertex)
    (denominatorInverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms denominator) :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticDMgmComparisonSource.objectOf roofVertex) :=
  let targetRepresentative :
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableRepresentative
          (TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf
              targetComplex)) :=
    Exists.intro
      bound
      (Exists.intro
        targetComplex
        (And.intro
          targetBounded
          rfl))
  let targetMembership :
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableObject
          (TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf
              targetComplex)) :=
    CategoryTheory.le_isoClosure
      TraceAnalyticDMgmComparisonSource
        .degreewiseIsoClosureBoundedStableRepresentative
      (TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf targetComplex))
      targetRepresentative
  let denominatorIsIso :
      IsIso
        (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
          denominator) :=
    CategoryTheory.Localization.inverts
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms
      denominatorInverted
  let denominatorStableIso :
      TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf
            targetComplex) ≅
        TraceAnalyticDMgmComparisonSource.objectOf roofVertex :=
    have denominatorMapIsIso :
        IsIso
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            denominator) :=
      denominatorIsIso
    asIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        denominator)
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject)
    denominatorStableIso
    targetMembership

/-- A morphism between degreewise bounded stable objects has explicit
denominator and numerator data after choosing concrete representatives: the
denominator is Verdier-inverted, and postcomposing the conjugated stable
morphism by the localized denominator gives the localized numerator. -/
theorem exists_representativeNumeratorDenominator
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (roofVertex : TraceAnalyticAdditiveHomotopyCategory),
                      ∃ (denominator :
                        TraceAnalyticAdditiveHomotopyCategory.objectOf
                            targetComplex ⟶ roofVertex),
                        ∃ (denominatorInverted :
                          TraceAnalyticStableNullSubcategory
                            .invertedMorphisms denominator),
                          ∃ (numerator :
                            TraceAnalyticAdditiveHomotopyCategory.objectOf
                                sourceComplex ⟶ roofVertex),
                            (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                                (TraceAnalyticDMgmComparisonSource
                                  .quotientFunctor.map denominator) =
                              TraceAnalyticDMgmComparisonSource
                                .quotientFunctor.map numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeLeftFraction_numerator morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceBoundedData =>
          Exists.elim
            sourceBoundedData
            (fun sourceBounded sourceIsoData =>
              Exists.elim
                sourceIsoData
                (fun sourceIso targetBoundData =>
                  Exists.elim
                    targetBoundData
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetBoundedData =>
                          Exists.elim
                            targetBoundedData
                            (fun targetBounded targetIsoData =>
                              Exists.elim
                                targetIsoData
                                (fun targetIso fractionData =>
                                  Exists.elim
                                    fractionData
                                    (fun fraction numeratorEquation =>
                                      Exists.intro
                                        sourceBound
                                        (Exists.intro
                                          sourceComplex
                                          (Exists.intro
                                            sourceBounded
                                            (Exists.intro
                                              sourceIso
                                              (Exists.intro
                                                targetBound
                                                (Exists.intro
                                                  targetComplex
                                                  (Exists.intro
                                                    targetBounded
                                                    (Exists.intro
                                                      targetIso
                                                      (Exists.intro
                                                        fraction.Y'
                                                        (Exists.intro
                                                          fraction.s
                                                          (Exists.intro
                                                            fraction.hs
                                                            (Exists.intro
                                                              fraction.f
                                                              numeratorEquation)))))))))))))))))))

/-- The representative numerator-denominator package can be chosen so that
the stable image of the roof vertex is itself degreewise iso-closure bounded.
The boundedness is transported across the Verdier-inverted denominator. -/
theorem exists_representativeNumeratorDenominator_boundedRoof
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (sourceBounded :
          TraceAnalyticMotiveComparison
            .sourceComplexDegreewiseIsoClosureBoundedBy
              sourceComplex
              sourceBound),
          ∃ (sourceIso :
            TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  sourceComplex) ≅
              source.object),
            ∃ (targetBound : Nat),
              ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
                ∃ (targetBounded :
                  TraceAnalyticMotiveComparison
                    .sourceComplexDegreewiseIsoClosureBoundedBy
                      targetComplex
                      targetBound),
                  ∃ (targetIso :
                    TraceAnalyticDMgmComparisonSource.objectOf
                        (TraceAnalyticAdditiveHomotopyCategory.objectOf
                          targetComplex) ≅
                      target.object),
                    ∃ (roofVertex : TraceAnalyticAdditiveHomotopyCategory),
                      ∃ (roofStableBounded :
                        TraceAnalyticDMgmComparisonSource
                          .degreewiseIsoClosureBoundedStableObject
                            (TraceAnalyticDMgmComparisonSource.objectOf
                              roofVertex)),
                        ∃ (denominator :
                          TraceAnalyticAdditiveHomotopyCategory.objectOf
                              targetComplex ⟶ roofVertex),
                          ∃ (denominatorInverted :
                            TraceAnalyticStableNullSubcategory
                              .invertedMorphisms denominator),
                            ∃ (numerator :
                              TraceAnalyticAdditiveHomotopyCategory.objectOf
                                  sourceComplex ⟶ roofVertex),
                              (sourceIso.hom ≫ morphism ≫ targetIso.inv) ≫
                                  (TraceAnalyticDMgmComparisonSource
                                    .quotientFunctor.map denominator) =
                                TraceAnalyticDMgmComparisonSource
                                  .quotientFunctor.map numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeNumeratorDenominator morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex sourceBoundedData =>
          Exists.elim
            sourceBoundedData
            (fun sourceBounded sourceIsoData =>
              Exists.elim
                sourceIsoData
                (fun sourceIso targetBoundData =>
                  Exists.elim
                    targetBoundData
                    (fun targetBound targetData =>
                      Exists.elim
                        targetData
                        (fun targetComplex targetBoundedData =>
                          Exists.elim
                            targetBoundedData
                            (fun targetBounded targetIsoData =>
                              Exists.elim
                                targetIsoData
                                (fun targetIso roofData =>
                                  Exists.elim
                                    roofData
                                    (fun roofVertex denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun denominator
                                          denominatorInvertedData =>
                                          Exists.elim
                                            denominatorInvertedData
                                            (fun denominatorInverted
                                              numeratorData =>
                                              Exists.elim
                                                numeratorData
                                                (fun numerator
                                                  numeratorEquation =>
                                                  let roofStableBounded :
                                                      TraceAnalyticDMgmComparisonSource
                                                        .degreewiseIsoClosureBoundedStableObject
                                                          (TraceAnalyticDMgmComparisonSource
                                                            .objectOf
                                                            roofVertex) :=
                                                    TraceAnalyticDMgmComparisonSource
                                                      .DegreewiseBoundedStable
                                                      .roofVertex_degreewiseIsoClosureBoundedStableObject_of_denominator
                                                        targetBounded
                                                        denominator
                                                        denominatorInverted
                                                  Exists.intro
                                                    sourceBound
                                                    (Exists.intro
                                                      sourceComplex
                                                      (Exists.intro
                                                        sourceBounded
                                                        (Exists.intro
                                                          sourceIso
                                                          (Exists.intro
                                                            targetBound
                                                            (Exists.intro
                                                              targetComplex
                                                              (Exists.intro
                                                                targetBounded
                                                                (Exists.intro
                                                                  targetIso
                                                                  (Exists.intro
                                                                    roofVertex
                                                                    (Exists.intro
                                                                      roofStableBounded
                                                                      (Exists.intro
                                                                        denominator
                                                                        (Exists.intro
                                                                          denominatorInverted
                                                                          (Exists.intro
                                                                            numerator
                                                                            numeratorEquation)))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

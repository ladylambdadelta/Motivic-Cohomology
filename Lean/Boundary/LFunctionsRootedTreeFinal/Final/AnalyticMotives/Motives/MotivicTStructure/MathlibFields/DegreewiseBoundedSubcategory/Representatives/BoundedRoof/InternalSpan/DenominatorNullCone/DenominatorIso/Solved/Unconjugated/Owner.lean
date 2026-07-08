import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorNullCone.DenominatorIso.Solved.Owner

/-!
# Unconjugated solved null-cone internal bounded roof spans

This file removes the representative-isomorphism conjugation from the solved
null-cone internal bounded roof formula, while retaining the raw analytic
distinguished-triangle certificate for the denominator.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The solved null-cone internal bounded roof formula can be written for the
original bounded-stable morphism itself. -/
theorem
    exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone_solved_unconjugated
    {source target :
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable}
    (morphism : source ⟶ target) :
    ∃ (sourceBound : Nat),
      ∃ (sourceComplex : TraceAnalyticAdditiveCochainComplex),
        ∃ (targetBound : Nat),
          ∃ (targetComplex : TraceAnalyticAdditiveCochainComplex),
            ∃ (sourceRepresentative :
              TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
              ∃ (targetRepresentative :
                TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                ∃ (roof :
                  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable),
                  ∃ (sourceIso :
                    sourceRepresentative.object ≅ source.object),
                    ∃ (targetIso :
                      targetRepresentative.object ≅ target.object),
                      ∃ (denominator :
                        targetRepresentative ⟶ roof),
                        ∃ (_ : IsIso denominator),
                          ∃ (numerator :
                            sourceRepresentative ⟶ roof),
                            ∃ (roofVertex :
                              TraceAnalyticAdditiveHomotopyCategory),
                              ∃ (roof_eq :
                                roof.object =
                                  TraceAnalyticDMgmComparisonSource.objectOf
                                    roofVertex),
                                ∃ (rawDenominator :
                                  TraceAnalyticAdditiveHomotopyCategory.objectOf
                                      targetComplex ⟶ roofVertex),
                                  ∃ (rawNumerator :
                                    TraceAnalyticAdditiveHomotopyCategory
                                        .objectOf sourceComplex ⟶ roofVertex),
                                    ∃ (denominatorCone :
                                      TraceAnalyticAdditiveHomotopyCategory),
                                      ∃ (denominatorCoconeMap :
                                        roofVertex ⟶ denominatorCone),
                                        ∃ (denominatorBoundary :
                                          denominatorCone ⟶
                                            (TraceAnalyticAdditiveHomotopyCategory
                                              .objectOf targetComplex)⟦(1 : ℤ)⟧),
                                          ∃ (_ :
                                            Triangle.mk
                                                rawDenominator
                                                denominatorCoconeMap
                                                denominatorBoundary ∈
                                              TraceAnalyticAdditiveHomotopyCategory
                                                .distinguishedTriangles),
                                            ∃ (_ :
                                              TraceAnalyticStableNullSubcategory.P
                                                denominatorCone),
                                              denominator =
                                                  TraceAnalyticDMgmComparisonSource
                                                    .quotientFunctor.map
                                                    rawDenominator ≫
                                                eqToHom (Eq.symm roof_eq) ∧
                                                numerator =
                                                  TraceAnalyticDMgmComparisonSource
                                                    .quotientFunctor.map
                                                    rawNumerator ≫
                                                eqToHom (Eq.symm roof_eq) ∧
                                                  morphism =
                                                    sourceIso.inv ≫
                                                      numerator ≫
                                                      inv denominator ≫
                                                      targetIso.hom :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone_solved
        morphism)
    (fun sourceBound sourceData =>
      Exists.elim
        sourceData
        (fun sourceComplex targetBoundData =>
          Exists.elim
            targetBoundData
            (fun targetBound targetComplexData =>
              Exists.elim
                targetComplexData
                (fun targetComplex sourceRepresentativeData =>
                  Exists.elim
                    sourceRepresentativeData
                    (fun sourceRepresentative targetRepresentativeData =>
                      Exists.elim
                        targetRepresentativeData
                        (fun targetRepresentative roofData =>
                          Exists.elim
                            roofData
                            (fun roof sourceIsoData =>
                              Exists.elim
                                sourceIsoData
                                (fun sourceIso targetIsoData =>
                                  Exists.elim
                                    targetIsoData
                                    (fun targetIso denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun denominator denominatorIsoData =>
                                          Exists.elim
                                            denominatorIsoData
                                            (fun denominatorIso numeratorData =>
                                              Exists.elim
                                                numeratorData
                                                (fun numerator roofVertexData =>
                                                  Exists.elim
                                                    roofVertexData
                                                    (fun roofVertex roofEqData =>
                                                      Exists.elim
                                                        roofEqData
                                                        (fun roof_eq rawDenominatorData =>
                                                          Exists.elim
                                                            rawDenominatorData
                                                            (fun rawDenominator
                                                              rawNumeratorData =>
                                                              Exists.elim
                                                                rawNumeratorData
                                                                (fun rawNumerator
                                                                  coneData =>
                                                                  Exists.elim
                                                                    coneData
                                                                    (fun denominatorCone
                                                                      coneMapData =>
                                                                      Exists.elim
                                                                        coneMapData
                                                                        (fun denominatorCoconeMap
                                                                          boundaryData =>
                                                                          Exists.elim
                                                                            boundaryData
                                                                            (fun denominatorBoundary
                                                                              distinguishedData =>
                                                                              Exists.elim
                                                                                distinguishedData
                                                                                (fun distinguished
                                                                                  nullData =>
                                                                                  Exists.elim
                                                                                    nullData
                                                                                    (fun null
                                                                                      equationData =>
                                                                                      And.elim
                                                                                        equationData
                                                                                        (fun denominator_eq
                                                                                          equationRest =>
                                                                                          And.elim
                                                                                            equationRest
                                                                                            (fun numerator_eq
                                                                                              solved =>
                                                                                              letI denominatorIsoField :
                                                                                                  IsIso denominator :=
                                                                                                denominatorIso
                                                                                              let solvedAfterSource :
                                                                                                  morphism ≫
                                                                                                      targetIso.inv =
                                                                                                    sourceIso.inv ≫
                                                                                                      (numerator ≫
                                                                                                        inv denominator) :=
                                                                                                (Iso.inv_comp_eq
                                                                                                  sourceIso).mp
                                                                                                  solved
                                                                                              let solvedReverse :
                                                                                                  sourceIso.inv ≫
                                                                                                        (numerator ≫
                                                                                                          inv denominator) ≫
                                                                                                      targetIso.hom =
                                                                                                    morphism :=
                                                                                                (Iso.eq_comp_inv
                                                                                                  targetIso).mp
                                                                                                  (Eq.symm
                                                                                                    solvedAfterSource)
                                                                                              let reassociated :
                                                                                                  sourceIso.inv ≫
                                                                                                        numerator ≫
                                                                                                      inv denominator ≫
                                                                                                    targetIso.hom =
                                                                                                    sourceIso.inv ≫
                                                                                                        (numerator ≫
                                                                                                          inv denominator) ≫
                                                                                                      targetIso.hom :=
                                                                                                Eq.trans
                                                                                                  (Category.assoc
                                                                                                    sourceIso.inv
                                                                                                    numerator
                                                                                                    (inv denominator ≫
                                                                                                      targetIso.hom))
                                                                                                  (congrArg
                                                                                                    (fun arrow =>
                                                                                                      sourceIso.inv ≫
                                                                                                        arrow)
                                                                                                    (Eq.symm
                                                                                                      (Category.assoc
                                                                                                        numerator
                                                                                                        (inv denominator)
                                                                                                        targetIso.hom)))
                                                                                              let unconjugated :
                                                                                                  morphism =
                                                                                                    sourceIso.inv ≫
                                                                                                      numerator ≫
                                                                                                      inv denominator ≫
                                                                                                      targetIso.hom :=
                                                                                                Eq.symm
                                                                                                  (Eq.trans
                                                                                                    reassociated
                                                                                                    solvedReverse)
                                                                                              Exists.intro
                                                                                                sourceBound
                                                                                                (Exists.intro
                                                                                                  sourceComplex
                                                                                                  (Exists.intro
                                                                                                    targetBound
                                                                                                    (Exists.intro
                                                                                                      targetComplex
                                                                                                      (Exists.intro
                                                                                                        sourceRepresentative
                                                                                                        (Exists.intro
                                                                                                          targetRepresentative
                                                                                                          (Exists.intro
                                                                                                            roof
                                                                                                            (Exists.intro
                                                                                                              sourceIso
                                                                                                              (Exists.intro
                                                                                                                targetIso
                                                                                                                (Exists.intro
                                                                                                                  denominator
                                                                                                                  (Exists.intro
                                                                                                                    denominatorIso
                                                                                                                    (Exists.intro
                                                                                                                      numerator
                                                                                                                      (Exists.intro
                                                                                                                        roofVertex
                                                                                                                        (Exists.intro
                                                                                                                          roof_eq
                                                                                                                          (Exists.intro
                                                                                                                            rawDenominator
                                                                                                                            (Exists.intro
                                                                                                                              rawNumerator
                                                                                                                              (Exists.intro
                                                                                                                                denominatorCone
                                                                                                                                (Exists.intro
                                                                                                                                  denominatorCoconeMap
                                                                                                                                  (Exists.intro
                                                                                                                                    denominatorBoundary
                                                                                                                                    (Exists.intro
                                                                                                                                      distinguished
                                                                                                                                      (Exists.intro
                                                                                                                                        null
                                                                                                                                        (And.intro
                                                                                                                                          denominator_eq
                                                                                                                                          (And.intro
                                                                                                                                            numerator_eq
                                                                                                                                            unconjugated))))))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.InternalSpan.DenominatorNullCone.DenominatorIso.Owner

/-!
# Solved null-cone internal bounded roof spans

This file solves the null-cone internal bounded roof span by composing with the
inverse of the internal denominator isomorphism, while keeping the raw
distinguished-triangle and null-cone data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A morphism in the degreewise bounded stable source is represented, after
choosing concrete source and target representatives, by a numerator followed by
the inverse of an internal denominator whose isomorphism comes from a raw
distinguished triangle with null cone. -/
theorem exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone_solved
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
                                                  sourceIso.hom ≫
                                                      morphism ≫
                                                    targetIso.inv =
                                                  numerator ≫
                                                    inv denominator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone_iso
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
                                                                                              spanEquation =>
                                                                                              letI denominatorIsoField :
                                                                                                  IsIso denominator :=
                                                                                                denominatorIso
                                                                                              let conjugated :
                                                                                                  sourceRepresentative
                                                                                                      .object ⟶
                                                                                                    targetRepresentative
                                                                                                      .object :=
                                                                                                sourceIso.hom ≫
                                                                                                  morphism ≫
                                                                                                    targetIso.inv
                                                                                              let solvedReverse :
                                                                                                  numerator ≫
                                                                                                      inv denominator =
                                                                                                    conjugated :=
                                                                                                (Iso.comp_inv_eq
                                                                                                  (asIso
                                                                                                    denominator)).mpr
                                                                                                  spanEquation.symm
                                                                                              let solved :
                                                                                                  conjugated =
                                                                                                    numerator ≫
                                                                                                      inv denominator :=
                                                                                                Eq.symm
                                                                                                  solvedReverse
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
                                                                                                                                            solved))))))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

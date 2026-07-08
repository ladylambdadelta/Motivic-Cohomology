import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Representatives.BoundedRoof.Projections.DenominatorNullCone.Owner

/-!
# Internal bounded roof spans with denominator null-cone data

This file packages the null-cone preserving bounded-roof projection as an
internal span in the degreewise bounded stable source.  The denominator and
numerator become morphisms of the full subcategory, while the raw analytic
distinguished triangle witnessing the denominator remains available.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- A degreewise-bounded morphism factors through an internal bounded roof span,
and the internal denominator is still tied to a raw distinguished triangle with
null cone. -/
theorem exists_internalRepresentativeBoundedRoofSpan_denominatorNullCone
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
                                  TraceAnalyticAdditiveHomotopyCategory.objectOf
                                      sourceComplex ⟶ roofVertex),
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
                                                (sourceIso.hom ≫
                                                      morphism ≫
                                                    targetIso.inv) ≫
                                                  denominator =
                                                numerator :=
  Exists.elim
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .exists_representativeBoundedRoof_stableMaps_denominatorNullCone
        morphism)
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
                                    (fun roof denominatorData =>
                                      Exists.elim
                                        denominatorData
                                        (fun stableDenominator
                                          numeratorData =>
                                          Exists.elim
                                            numeratorData
                                            (fun stableNumerator
                                              roofVertexData =>
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
                                                                                    (fun stableDenominator_eq
                                                                                      equationRest =>
                                                                                      And.elim
                                                                                        equationRest
                                                                                        (fun stableNumerator_eq
                                                                                          stableEquation =>
                                                                                          let sourceRepresentative :
                                                                                              TraceAnalyticDMgmComparisonSource
                                                                                                .DegreewiseBoundedStable where
                                                                                            obj :=
                                                                                              TraceAnalyticDMgmComparisonSource
                                                                                                .objectOf
                                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                                    .objectOf
                                                                                                    sourceComplex)
                                                                                            property :=
                                                                                              CategoryTheory.le_isoClosure
                                                                                                TraceAnalyticDMgmComparisonSource
                                                                                                  .degreewiseIsoClosureBoundedStableRepresentative
                                                                                                (TraceAnalyticDMgmComparisonSource
                                                                                                  .objectOf
                                                                                                    (TraceAnalyticAdditiveHomotopyCategory
                                                                                                      .objectOf
                                                                                                      sourceComplex))
                                                                                                (Exists.intro
                                                                                                  sourceBound
                                                                                                  (Exists.intro
                                                                                                    sourceComplex
                                                                                                    (And.intro
                                                                                                      sourceBounded
                                                                                                      rfl)))
                                                                                          let targetRepresentative :
                                                                                              TraceAnalyticDMgmComparisonSource
                                                                                                .DegreewiseBoundedStable where
                                                                                            obj :=
                                                                                              TraceAnalyticDMgmComparisonSource
                                                                                                .objectOf
                                                                                                  (TraceAnalyticAdditiveHomotopyCategory
                                                                                                    .objectOf
                                                                                                    targetComplex)
                                                                                            property :=
                                                                                              CategoryTheory.le_isoClosure
                                                                                                TraceAnalyticDMgmComparisonSource
                                                                                                  .degreewiseIsoClosureBoundedStableRepresentative
                                                                                                (TraceAnalyticDMgmComparisonSource
                                                                                                  .objectOf
                                                                                                    (TraceAnalyticAdditiveHomotopyCategory
                                                                                                      .objectOf
                                                                                                      targetComplex))
                                                                                                (Exists.intro
                                                                                                  targetBound
                                                                                                  (Exists.intro
                                                                                                    targetComplex
                                                                                                    (And.intro
                                                                                                      targetBounded
                                                                                                      rfl)))
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
                                                                                                              stableDenominator
                                                                                                              (Exists.intro
                                                                                                                stableNumerator
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
                                                                                                                                    stableDenominator_eq
                                                                                                                                    (And.intro
                                                                                                                                      stableNumerator_eq
                                                                                                                                      stableEquation))))))))))))))))))))))))))))))))))))))))

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary

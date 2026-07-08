import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.MappingCone.Complete.Owner

/-!
# Projections from complete mapping-cone recognition packages

This file exposes named projections from the complete mapping-cone
weight-triangular recognition package.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- Vertex object data projected from the complete mapping-cone package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularMappingCone_objectData
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularMappingCone
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).1 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom :=
  rfl

/-- Triangle naturality proof projected from the complete mapping-cone
package. -/
theorem TraceAnalyticMotiveRecognition.completeWeightTriangularMappingCone_triangleNaturality
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (geometricFullyFaithful :
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition) twistData homotopyFunctor inverts).FullyFaithful)
    {bound : Nat}
    {source target :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound}
    (hom :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy.Hom
        source
        target) :
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularMappingCone
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom).2 =
    TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

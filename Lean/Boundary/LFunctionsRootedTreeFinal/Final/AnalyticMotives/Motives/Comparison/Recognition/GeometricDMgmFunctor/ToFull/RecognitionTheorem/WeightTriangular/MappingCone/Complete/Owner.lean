import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.MappingCone.ObjectIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.ToFull.RecognitionTheorem.WeightTriangular.MappingCone.Projections.Owner

/-!
# Complete mapping-cone weight-triangular recognition package

This file pairs the four mapping-cone vertex comparison isomorphisms with the
three mapping-cone naturality equations.
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

/-- Complete mapping-cone recognition package: vertex comparison data together
with first-map, second-map, and connecting-map naturality. -/
def TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_completeWeightTriangularMappingCone
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
    { objectData :
      TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom //
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom) } :=
  Subtype.mk
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeObjectIsos
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom)
    (TraceAnalyticMotiveRecognition.descendedFullDMgmFunctorFromGeometric_fullyFaithful_and_weightTriangular_mappingConeTriangle
      (composition := composition)
      twistData
      homotopyFunctor
      inverts
      geometricFullyFaithful
      hom)

end AnalyticMotives
end LFunctions
end Boundary

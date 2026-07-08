import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Endpoints.Descent.NaturalTransformations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.NaturalTransformations.Summary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.NaturalTransformations.Summary.Owner

/-!
# Represented formulas for endpoint descended natural transformations

This file exposes component and naturality formulas for endpoint descended
natural transformations evaluated on quotient-represented analytic objects and
morphisms.
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

/-- Concrete endpoint component formula at a quotient-represented analytic
object. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_app_objectOf
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        first
        firstInverts
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        second
        secondInverts
        object).inv :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    object

/-- Concrete endpoint naturality formula on a quotient-represented analytic
morphism. -/
theorem TraceAnalyticMotiveComparison.concreteTarget_natTrans_mapOf_naturality
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf source) ≫
      (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
        (composition := composition)
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) =
      (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctor
        (composition := composition)
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticMotiveComparison.concreteTarget_descendInvertingFunctorNatTrans
        (composition := composition)
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf targetObject) :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

/-- Geometric endpoint component formula at a quotient-represented analytic
object. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_app_objectOf
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf object) =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        first
        firstInverts
        object).hom ≫
      transformation.app object ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        second
        secondInverts
        object).inv :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_app_objectOf
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    object

/-- Geometric endpoint naturality formula on a quotient-represented analytic
morphism. -/
theorem TraceAnalyticMotiveComparison.geometricTarget_natTrans_mapOf_naturality
    (twistData :
      TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
        (composition := composition))
    (first second :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (firstInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        first)
    (secondInverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        second)
    (transformation : first ⟶ second)
    {source targetObject : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ targetObject) :
    (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans
      (composition := composition)
      twistData
      first
      second
      firstInverts
      secondInverts
      transformation).app
        (TraceAnalyticStableHomotopyComparisonSource.objectOf source) ≫
      (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
        (composition := composition)
        twistData
        second
        secondInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) =
      (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctor
        (composition := composition)
        twistData
        first
        firstInverts).map
          (TraceAnalyticStableHomotopyComparisonSource.mapOf hom) ≫
      (TraceAnalyticMotiveComparison.geometricTarget_descendInvertingFunctorNatTrans
        (composition := composition)
        twistData
        first
        second
        firstInverts
        secondInverts
        transformation).app
          (TraceAnalyticStableHomotopyComparisonSource.objectOf targetObject) :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorNatTrans_mapOf_naturality
    (composition := composition)
    twistData
    first
    second
    firstInverts
    secondInverts
    transformation
    hom

end AnalyticMotives
end LFunctions
end Boundary

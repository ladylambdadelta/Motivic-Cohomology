import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.StableCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Structures.WeightStructure.Owner

/-!
# Weight-triangular equivalence with `DM_gm(ℚ)_ℚ`

This file owns the final comparison target: a weight-triangular equivalence
between compact geometric analytic motives and `DM_gm(ℚ)_ℚ`, after generator,
correspondence, descent, and Tate compatibility have been established.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Weight-triangular comparison data between compact geometric analytic motives
and the abstract `DM_gm(ℚ)_ℚ` target interface.
-/
structure DMgmQQWeightTriangularEquivalenceData
    {T : DMgmQQTargetInterface}
    (M : DMgmQQMorphismInterface T) where
  analyticStructures : AnalyticMotiveStructures
  tateComparison : DMgmQQTateComparison M
  stableCoherence : DMgmQQStableCoherenceComparison tateComparison
  stablePackage_eq :
    analyticStructures.stablePackage = stableCoherence.stablePackage
  analyticToTarget :
    analyticStructures.stablePackage.infinityInterface.Object → T.Object
  targetWeight :
    Int → T.Object → Type
  weightCompatibility :
    (n : Int) →
      (X : analyticStructures.stablePackage.infinityInterface.Object) →
        analyticStructures.weight.geometric.weightCandidate.lowerWeight n X →
          targetWeight n (analyticToTarget X)

namespace DMgmQQWeightTriangularEquivalenceData

/-- The object map from analytic motives to the target comparison interface. -/
def objectMap {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    E.analyticStructures.stablePackage.infinityInterface.Object → T.Object :=
  E.analyticToTarget

/--
The analytic structures used by the weight-triangular comparison are attached
to the same stable package as the Tate comparison coherence data.
-/
theorem stablePackage_compatibility {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    E.analyticStructures.stablePackage = E.stableCoherence.stablePackage :=
  E.stablePackage_eq

/--
The compact-geometric closed object in the weight-triangular analytic
structures agrees with the analytic Tate stabilization used by the comparison.
-/
theorem compactGeometric_closedObject_compatibility
    {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    E.analyticStructures.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      E.tateComparison.analyticStabilization :=
  Eq.trans
    (congrArg
      (fun P =>
        P.compactLayer.compactGeometric.thickClosure.closedObject)
      E.stablePackage_eq)
    (DMgmQQStableCoherenceComparison.compactGeometric_closedObject_compatibility
      E.stableCoherence)

/-- Transport lower-weight membership along the comparison object map. -/
def lowerWeightMap {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M)
    (n : Int)
    (X : E.analyticStructures.stablePackage.infinityInterface.Object)
    (h :
      E.analyticStructures.weight.geometric.weightCandidate.lowerWeight n X) :
    E.targetWeight n (E.analyticToTarget X) :=
  E.weightCompatibility n X h

/-- The analytic weight data used by a weight-triangular comparison. -/
def analyticWeight {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    AnalyticWeightStructureData :=
  E.analyticStructures.weight

/-- The analytic `t`-structure data used by a weight-triangular comparison. -/
def analyticTStructure {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    AnalyticMotivicTStructureData :=
  E.analyticStructures.tStructure

/-- The target-side weight predicate used by a weight-triangular comparison. -/
def targetWeightAt {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M)
    (n : Int) (Y : T.Object) : Type :=
  E.targetWeight n Y

/-- Lower analytic weight membership maps to target weight membership. -/
theorem lowerWeight_compatibility {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M)
    (n : Int)
    (X : E.analyticStructures.stablePackage.infinityInterface.Object)
    (h :
      E.analyticStructures.weight.geometric.weightCandidate.lowerWeight n X) :
    E.targetWeightAt n (E.objectMap X) :=
  E.weightCompatibility n X h

/-- The Tate comparison used by the weight-triangular comparison. -/
def tate {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    DMgmQQTateComparison M :=
  E.tateComparison

/-- The stable coherence data used by the weight-triangular comparison. -/
def stableCoherenceData {T : DMgmQQTargetInterface}
    {M : DMgmQQMorphismInterface T}
    (E : DMgmQQWeightTriangularEquivalenceData M) :
    DMgmQQStableCoherenceComparison E.tateComparison :=
  E.stableCoherence

end DMgmQQWeightTriangularEquivalenceData

end AnalyticMotives
end LFunctions
end Boundary

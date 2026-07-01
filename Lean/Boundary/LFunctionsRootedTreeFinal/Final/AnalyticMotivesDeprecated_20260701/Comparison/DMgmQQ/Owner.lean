import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Generators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Correspondences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.Tate.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.StableCoherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Comparison.DMgmQQ.WeightTriangularEquivalence.Owner

/-!
# Comparison with `DM_gm(ℚ)_ℚ`

This directory owns the comparison from compact geometric analytic motives to
Voevodsky's geometric motives over `ℚ` with rational coefficients.  The
comparison is downstream from the analytic stable category; it should not be
used to define analytic motives by renaming `DM_gm(ℚ)_ℚ`.

Dependency order: generators, correspondences, descent, Tate, stable-package
coherence, then weight-triangular equivalence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The full downstream comparison package from analytic contour motives to the
abstract `DM_gm(ℚ)_ℚ` target interface.
-/
structure DMgmQQComparisonPackage where
  target : DMgmQQTargetInterface
  morphisms : DMgmQQMorphismInterface target
  generatorComparison : DMgmQQGeneratorComparison target
  tateComparison : DMgmQQTateComparison morphisms
  stableCoherence :
    DMgmQQStableCoherenceComparison tateComparison
  weightTriangular :
    DMgmQQWeightTriangularEquivalenceData morphisms
  weightTriangular_tateComparison_eq :
    weightTriangular.tateComparison = tateComparison
  weightTriangular_stablePackage_eq :
    weightTriangular.analyticStructures.stablePackage =
      stableCoherence.stablePackage

namespace DMgmQQComparisonPackage

/-- The abstract target interface used for comparison with `DM_gm(ℚ)_ℚ`. -/
def targetInterface (C : DMgmQQComparisonPackage) :
    DMgmQQTargetInterface :=
  C.target

/-- The weight-triangular comparison data in the comparison package. -/
def weightTriangularData (C : DMgmQQComparisonPackage) :
    DMgmQQWeightTriangularEquivalenceData C.morphisms :=
  C.weightTriangular

/-- The stable-package coherence data in the comparison package. -/
def stableCoherenceData (C : DMgmQQComparisonPackage) :
    DMgmQQStableCoherenceComparison C.tateComparison :=
  C.stableCoherence

/-- The generator comparison in the comparison package. -/
def generatorData (C : DMgmQQComparisonPackage) :
    DMgmQQGeneratorComparison C.target :=
  C.generatorComparison

/-- The Tate comparison in the comparison package. -/
def tateData (C : DMgmQQComparisonPackage) :
    DMgmQQTateComparison C.morphisms :=
  C.tateComparison

/-- The analytic Tate stabilization used by the comparison package. -/
def analyticStabilization (C : DMgmQQComparisonPackage) :
    TateStabilizedAnalyticPresheaf :=
  C.tateComparison.analyticStabilization

/-- The descent comparison used by the package's Tate comparison. -/
def descentData (C : DMgmQQComparisonPackage) :
    DMgmQQDescentComparison C.morphisms :=
  C.tateComparison.descentComparison

/--
The weight-triangular comparison uses the same Tate comparison as the
comparison package.
-/
theorem weightTriangular_tateComparison_compatibility
    (C : DMgmQQComparisonPackage) :
    C.weightTriangular.tateComparison = C.tateComparison :=
  C.weightTriangular_tateComparison_eq

/--
The analytic structures used by the weight-triangular comparison are attached
to the same stable package as the package's stable-coherence data.
-/
theorem weightTriangular_stablePackage_compatibility
    (C : DMgmQQComparisonPackage) :
    C.weightTriangular.analyticStructures.stablePackage =
      C.stableCoherence.stablePackage :=
  C.weightTriangular_stablePackage_eq

/--
The comparison package's stable package has the same compact-geometric closed
object as the Tate stabilization used by the comparison.
-/
theorem compactGeometric_closedObject_compatibility
    (C : DMgmQQComparisonPackage) :
    C.stableCoherence.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      C.tateComparison.analyticStabilization :=
  DMgmQQStableCoherenceComparison.compactGeometric_closedObject_compatibility
    C.stableCoherence

/--
The compact-geometric closed object in the weight-triangular analytic
structures agrees with the package's Tate stabilization.
-/
theorem weightTriangular_closedObject_compatibility
    (C : DMgmQQComparisonPackage) :
    C.weightTriangular.analyticStructures.stablePackage.compactLayer.compactGeometric.thickClosure.closedObject =
      C.tateComparison.analyticStabilization :=
  Eq.trans
    (congrArg
      (fun P =>
        P.compactLayer.compactGeometric.thickClosure.closedObject)
      C.weightTriangular_stablePackage_eq)
    (compactGeometric_closedObject_compatibility C)

/-- Lower analytic weight membership maps to target weight membership in the package. -/
theorem weightTriangular_lowerWeight_compatibility
    (C : DMgmQQComparisonPackage)
    (n : Int)
    (X :
      C.weightTriangular.analyticStructures.stablePackage.infinityInterface.Object)
    (h :
      C.weightTriangular.analyticStructures.weight.geometric.weightCandidate.lowerWeight
        n X) :
    C.weightTriangular.targetWeight n
      (C.weightTriangular.analyticToTarget X) :=
  DMgmQQWeightTriangularEquivalenceData.lowerWeight_compatibility
    C.weightTriangular n X h

/-- The package's analytic stabilization is the one used by its stable coherence data. -/
theorem stableCoherence_tateStabilization_compatibility
    (C : DMgmQQComparisonPackage) :
    C.analyticStabilization =
      C.stableCoherence.stablePackage.stabilizedLayer.stabilizedPresheaf :=
  DMgmQQStableCoherenceComparison.tateStabilization_compatibility
    C.stableCoherence

end DMgmQQComparisonPackage

/--
Comparison package whose target-side correspondence comparison is attached to
the bulk-generated analytic stable package.
-/
structure DMgmQQBulkGeneratedComparisonPackage where
  generatedStable : BulkGeneratedStableAnalyticMotivePackage
  comparison : DMgmQQComparisonPackage
  correspondenceComparison :
    DMgmQQCorrespondenceCalculusComparison comparison.morphisms
  tateComparison :
    DMgmQQBulkGeneratedTateComparison comparison.morphisms
  correspondence_analyticCalculus_eq :
    correspondenceComparison.analyticCalculus =
      generatedStable.bulk.correspondenceCalculus
  tateComparison_eq :
    tateComparison.tateComparison =
      comparison.tateComparison
  stablePackage_eq :
    comparison.stableCoherence.stablePackage =
      generatedStable.forget

namespace DMgmQQBulkGeneratedComparisonPackage

/-- The bulk-generated stable package used by the comparison. -/
def stable (C : DMgmQQBulkGeneratedComparisonPackage) :
    BulkGeneratedStableAnalyticMotivePackage :=
  C.generatedStable

/-- The downstream comparison package with `DM_gm(ℚ)_ℚ`. -/
def comparisonData (C : DMgmQQBulkGeneratedComparisonPackage) :
    DMgmQQComparisonPackage :=
  C.comparison

/-- The category-level correspondence comparison. -/
def correspondenceData (C : DMgmQQBulkGeneratedComparisonPackage) :
    DMgmQQCorrespondenceCalculusComparison C.comparison.morphisms :=
  C.correspondenceComparison

/-- The bulk-generated Tate comparison. -/
def tateData (C : DMgmQQBulkGeneratedComparisonPackage) :
    DMgmQQBulkGeneratedTateComparison C.comparison.morphisms :=
  C.tateComparison

/-- The bulk construction generating the analytic stable package. -/
def bulk (C : DMgmQQBulkGeneratedComparisonPackage) :
    BulkAnalyticMotiveConstruction :=
  C.generatedStable.bulk

/--
The correspondence comparison uses the contour-correspondence calculus from
the bulk-generated stable package.
-/
theorem correspondence_analyticCalculus_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage) :
    C.correspondenceComparison.analyticCalculus =
      C.generatedStable.bulk.correspondenceCalculus :=
  C.correspondence_analyticCalculus_eq

/-- The package Tate comparison is the bulk-generated Tate comparison. -/
theorem tateComparison_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage) :
    C.tateComparison.tateComparison =
      C.comparison.tateComparison :=
  C.tateComparison_eq

/--
The comparison package's stable-coherence data is attached to the
bulk-generated stable package.
-/
theorem stablePackage_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage) :
    C.comparison.stableCoherence.stablePackage =
      C.generatedStable.forget :=
  C.stablePackage_eq

/-- The analytic Tate object in the comparison is generated by the bulk construction. -/
theorem analyticTate_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage) :
    C.tateComparison.tateComparison.analyticTate =
      C.bulk.presheaves.tate.tateObject :=
  DMgmQQBulkGeneratedTateComparison.analyticTate_compatibility
    C.tateComparison

/-- The analytic Tate stabilization in the comparison is generated by the bulk construction. -/
theorem analyticStabilization_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage) :
    C.tateComparison.tateComparison.analyticStabilization =
      C.bulk.presheaves.tate.forget :=
  DMgmQQBulkGeneratedTateComparison.analyticStabilization_compatibility
    C.tateComparison

/-- The target object assigned to a contour-admissible bulk. -/
def targetObjectAt (C : DMgmQQBulkGeneratedComparisonPackage)
    (X : ContourAdmissibleBulk) : C.comparison.target.Object :=
  C.correspondenceComparison.objectAt X

/-- The target morphism assigned to a contour-compatible correspondence. -/
def targetMorphismAt (C : DMgmQQBulkGeneratedComparisonPackage)
    {X Y : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y) :
    C.comparison.morphisms.Hom (C.targetObjectAt X) (C.targetObjectAt Y) :=
  C.correspondenceComparison.morphismAt F

/-- Identity compatibility for the bulk-generated correspondence comparison. -/
theorem target_identity_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage)
    (X : ContourAdmissibleBulk) :
    C.targetMorphismAt (C.correspondenceComparison.analytic.identityAt X) =
      C.correspondenceComparison.target.identityAt (C.targetObjectAt X) :=
  DMgmQQCorrespondenceCalculusComparison.identity_compatibility
    C.correspondenceComparison X

/-- Composition compatibility for the bulk-generated correspondence comparison. -/
theorem target_composition_compatibility
    (C : DMgmQQBulkGeneratedComparisonPackage)
    {X Y Z : ContourAdmissibleBulk}
    (F : ContourAnalyticCorrespondence X Y)
    (G : ContourAnalyticCorrespondence Y Z) :
    C.targetMorphismAt
        (C.correspondenceComparison.analytic.composeAt F G) =
      C.correspondenceComparison.target.composeAt
        (C.targetMorphismAt F) (C.targetMorphismAt G) :=
  DMgmQQCorrespondenceCalculusComparison.composition_compatibility
    C.correspondenceComparison F G

end DMgmQQBulkGeneratedComparisonPackage

end AnalyticMotives
end LFunctions
end Boundary

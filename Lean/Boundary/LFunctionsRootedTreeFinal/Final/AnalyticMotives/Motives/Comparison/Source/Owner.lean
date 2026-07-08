import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.TriangulatedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.TriangulatedSubcategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Triangles.MappingCone.Vertices.IsoClosure.Owner

/-!
# Source endpoint for analytic comparison

This file records the source side of the `DMgm` comparison as the existing
stable analytic Verdier quotient.  It exposes the quotient functor, localization
universal property, and triangulated structure under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The comparison source quotient functor is the stable analytic Verdier
quotient functor. -/
def TraceAnalyticDMgmComparisonSource.quotientFunctor :
    TraceAnalyticAdditiveHomotopyCategory ⥤
      TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The comparison source quotient functor is definitionally the stable
analytic quotient functor. -/
theorem TraceAnalyticDMgmComparisonSource.quotientFunctor_eq_stable :
    TraceAnalyticDMgmComparisonSource.quotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The morphism property inverted by the comparison source quotient. -/
def TraceAnalyticDMgmComparisonSource.invertedMorphisms :
    MorphismProperty TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticStableMotiveCategory.invertedMorphisms

/-- The comparison source inverted morphisms are the stable analytic inverted
morphisms. -/
theorem TraceAnalyticDMgmComparisonSource.invertedMorphisms_eq_stable :
    TraceAnalyticDMgmComparisonSource.invertedMorphisms =
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  rfl

/-- The comparison source quotient functor is a localization at the stable
analytic inverted morphisms. -/
def TraceAnalyticDMgmComparisonSource.isLocalization :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.IsLocalization
      TraceAnalyticDMgmComparisonSource.invertedMorphisms :=
  TraceAnalyticStableMotiveCategory.isLocalization

/-- The comparison source localization structure is the stable analytic
localization structure. -/
theorem TraceAnalyticDMgmComparisonSource.isLocalization_eq_stable :
    TraceAnalyticDMgmComparisonSource.isLocalization =
      TraceAnalyticStableMotiveCategory.isLocalization :=
  rfl

/-- Additive homotopy objects enter the comparison source through the stable
analytic quotient. -/
def TraceAnalyticDMgmComparisonSource.objectOf
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonSource :=
  TraceAnalyticStableMotiveCategory.objectOf object

/-- The comparison source object map is the stable analytic object map. -/
theorem TraceAnalyticDMgmComparisonSource.objectOf_eq_stable
    (object : TraceAnalyticAdditiveHomotopyCategory) :
    TraceAnalyticDMgmComparisonSource.objectOf object =
      TraceAnalyticStableMotiveCategory.objectOf object :=
  rfl

/-- Additive homotopy morphisms enter the comparison source through the stable
analytic quotient. -/
def TraceAnalyticDMgmComparisonSource.mapOf
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.objectOf source ⟶
      TraceAnalyticDMgmComparisonSource.objectOf target :=
  TraceAnalyticStableMotiveCategory.mapOf hom

/-- The comparison source morphism map is the stable analytic morphism map. -/
theorem TraceAnalyticDMgmComparisonSource.mapOf_eq_stable
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    TraceAnalyticDMgmComparisonSource.mapOf hom =
      TraceAnalyticStableMotiveCategory.mapOf hom :=
  rfl

/-- Functors out of the comparison source are equivalent to additive homotopy
functors that invert the stable analytic null morphisms. -/
def TraceAnalyticDMgmComparisonSource.functorEquivalence
    (target : Type*) [Category target] :
    (TraceAnalyticDMgmComparisonSource ⥤ target) ≌
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.FunctorsInverting target :=
  TraceAnalyticStableMotiveCategory.functorEquivalence target

/-- The comparison-source functor equivalence is the stable analytic functor
equivalence. -/
theorem TraceAnalyticDMgmComparisonSource.functorEquivalence_eq_stable
    (target : Type*) [Category target] :
    TraceAnalyticDMgmComparisonSource.functorEquivalence target =
      TraceAnalyticStableMotiveCategory.functorEquivalence target :=
  rfl

/-- Descend a null-inverting additive homotopy functor to the comparison
source. -/
def TraceAnalyticDMgmComparisonSource.lift
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticDMgmComparisonSource ⥤ target :=
  TraceAnalyticStableMotiveCategory.lift functor inverts

/-- The comparison-source lift is the stable analytic lift. -/
theorem TraceAnalyticDMgmComparisonSource.lift_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticDMgmComparisonSource.lift functor inverts =
      TraceAnalyticStableMotiveCategory.lift functor inverts :=
  rfl

/-- The descended comparison-source functor composed with the quotient recovers
the original additive homotopy functor. -/
def TraceAnalyticDMgmComparisonSource.liftFac
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticDMgmComparisonSource.quotientFunctor ⋙
      TraceAnalyticDMgmComparisonSource.lift functor inverts ≅ functor :=
  TraceAnalyticStableMotiveCategory.liftFac functor inverts

/-- The comparison-source lift factorization is the stable analytic
factorization. -/
theorem TraceAnalyticDMgmComparisonSource.liftFac_eq_stable
    {target : Type*} [Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticDMgmComparisonSource.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticDMgmComparisonSource.liftFac functor inverts =
      TraceAnalyticStableMotiveCategory.liftFac functor inverts :=
  rfl

/-- The comparison source shift structure is the stable analytic shift
structure. -/
theorem TraceAnalyticDMgmComparisonSource.hasShiftStructure_eq_stable :
    TraceAnalyticDMgmComparisonSource.hasShiftStructure =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  rfl

/-- The comparison source pretriangulated structure is the stable analytic
pretriangulated structure. -/
theorem TraceAnalyticDMgmComparisonSource.pretriangulatedStructure_eq_stable :
    TraceAnalyticDMgmComparisonSource.pretriangulatedStructure =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  rfl

/-- The comparison source triangulated structure is the stable analytic
triangulated structure. -/
theorem TraceAnalyticDMgmComparisonSource.triangulatedStructure_eq_stable :
    TraceAnalyticDMgmComparisonSource.triangulatedStructure =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  rfl

/-- The comparison source distinguished triangles are the stable analytic
distinguished triangles. -/
theorem TraceAnalyticDMgmComparisonSource.distinguishedTriangles_eq_stable' :
    TraceAnalyticDMgmComparisonSource.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary

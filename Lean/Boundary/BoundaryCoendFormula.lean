import Boundary.HolographicReconstruction

/-!
# Boundary coend formula

This file owns the presentation data for the boundary reconstruction mechanism.

It packages the diagrammatic input that will later be fed to a normalized
boundary colimit / coend construction. The actual comparison map theorem is
still a separate obligation and is not faked here.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT uD vD uJ vJ

namespace Boundary

/-- A boundary coend presentation packages the data needed to build the
reconstruction object by a normalized colimit. -/
structure BoundaryCoendPresentation
    {T : Type uT} [Category.{vT} T] where
  profileCategory : Type uD
  profileCategoryCat : Category.{vD} profileCategory
  dependencyDiagram : BoundaryDependencyDiagram T
  comparisonCocone : Cocone dependencyDiagram.diagram
  comparisonIsColimit : IsColimit comparisonCocone
  boundaryProfileFunctor : T ⥤ profileCategory
  boundaryProfileFunctorPreservesColimit :
    PreservesColimit dependencyDiagram.diagram boundaryProfileFunctor
  reconstructionFunctor : profileCategory ⥤ T

attribute [instance] BoundaryCoendPresentation.profileCategoryCat

namespace BoundaryCoendPresentation

variable {T : Type uT} [Category.{vT} T]
  (C : BoundaryCoendPresentation (T := T))

/-- The normalized reconstruction object associated to the presentation. -/
noncomputable def reconstructedObject
    [HasColimit C.dependencyDiagram.diagram] : T :=
  BoundaryDependencyDiagram.normalizedBoundaryColimit C.dependencyDiagram

/-- The canonical comparison map from the normalized reconstruction object to
the source object of the boundary presentation. -/
noncomputable def reconstructionComparison
    [HasColimit C.dependencyDiagram.diagram] :
    colimit C.dependencyDiagram.diagram ⟶ C.comparisonCocone.pt :=
  colimit.desc C.dependencyDiagram.diagram C.comparisonCocone

end BoundaryCoendPresentation

end Boundary

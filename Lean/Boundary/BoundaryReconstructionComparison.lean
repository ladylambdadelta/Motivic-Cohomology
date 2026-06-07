import Boundary.BoundaryCoendFormula

/-!
# Boundary reconstruction comparison

This file packages the comparison arrow produced by the reconstruction
mechanism. It is the literal bridge from the reconstructed object back to the
source object.

The probewise comparison theorem lives in the next layer, while the adequacy
upgrade remains separate.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT uD vD

namespace Boundary

/-- The explicit comparison datum produced by reconstruction. This is the
owner-facing place for the canonical comparison morphism from the reconstructed
boundary colimit to the original source object. -/
structure BoundaryReconstructionComparison
    {T : Type uT} [Category.{vT} T] where
  presentation : BoundaryCoendPresentation (T := T)

namespace BoundaryReconstructionComparison

variable {T : Type uT} [Category.{vT} T]
  (C : BoundaryReconstructionComparison (T := T))

/-- The reconstructed object underlying the comparison datum. -/
abbrev reconstructedObject
    [HasColimit C.presentation.dependencyDiagram.diagram] : T :=
  BoundaryCoendPresentation.reconstructedObject (C := C.presentation)

/-- The source object underlying the comparison datum. -/
abbrev sourceObject : T :=
  C.presentation.comparisonCocone.pt

/-- The canonical comparison morphism. -/
noncomputable def reconstructionComparison
    [HasColimit C.presentation.dependencyDiagram.diagram] :
    BoundaryCoendPresentation.reconstructedObject (C := C.presentation) ⟶
      C.sourceObject :=
  BoundaryCoendPresentation.reconstructionComparison (C := C.presentation)

end BoundaryReconstructionComparison

end Boundary

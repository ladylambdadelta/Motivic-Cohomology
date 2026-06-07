import Boundary.BoundaryProbeEvaluation

/-!
# Boundary probe adequacy

This file names the conservativity / adequacy layer for the canonical boundary
probes. It is the point where probewise agreement is upgraded to global
equivalence, but only as an interface package for now.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT uD vD

namespace Boundary

/-- The adequacy package for a boundary probe family. This is the interface
that later reconstruction theorems will use to turn probewise agreement into a
global equivalence. -/
structure BoundaryProbeAdequacy
    {T : Type uT} [Category.{vT} T]
    (profileCategory : Type uD) [Category.{vD} profileCategory]
    (boundaryProfileFunctor : T ⥤ profileCategory) where
  probeDetectsEquivalence :
    ∀ {X Y : T},
      (boundaryProfileFunctor.obj X ≅ boundaryProfileFunctor.obj Y) →
        Nonempty (X ≅ Y)

namespace BoundaryProbeAdequacy

variable {T : Type uT} [Category.{vT} T]
  {profileCategory : Type uD} [Category.{vD} profileCategory]
  {boundaryProfileFunctor : T ⥤ profileCategory}

/-- The adequacy theorem packaged as a boundary-facing name. -/
theorem probeDetectsEquivalence'
    (A : BoundaryProbeAdequacy (T := T) profileCategory boundaryProfileFunctor)
    {X Y : T}
    (h : boundaryProfileFunctor.obj X ≅ boundaryProfileFunctor.obj Y) :
    Nonempty (X ≅ Y) :=
  BoundaryProbeAdequacy.probeDetectsEquivalence A h

/-- The adequacy upgrade for the concrete boundary probe reconstruction. -/
theorem boundaryReconstructionAdequate
    (E : BoundaryProbeEvaluationCompatibility (T := T))
    (A : BoundaryProbeAdequacy (T := T) E.profileCategory E.boundaryProfileFunctor)
    [HasColimit E.comparison.dependencyDiagram.diagram]
    [PreservesColimit E.comparison.dependencyDiagram.diagram
      E.boundaryProfileFunctor]
    (hSourceColimit : IsColimit E.comparison.comparisonCocone) :
    Nonempty (E.comparison.reconstructedObject ≅
      E.comparison.comparisonCocone.pt) := by
  exact BoundaryProbeAdequacy.probeDetectsEquivalence A
    (BoundaryProbeEvaluationCompatibility.boundaryProbeAgreementIso E hSourceColimit)

end BoundaryProbeAdequacy

end Boundary

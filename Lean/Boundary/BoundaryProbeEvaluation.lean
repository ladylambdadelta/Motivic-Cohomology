import Boundary.BoundaryProbeAPI
import Boundary.HolographicReconstruction
import Boundary.BoundaryCoendFormula
import Boundary.BoundaryReconstructionComparison

/-!
# Boundary probe evaluation

This file names the probe-preservation obligations for the reconstruction
mechanism. It does not prove the reconstruction theorem itself; it isolates the
compatibility statement that the later adequacy argument will use.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe vT uT uD vD uJ vJ

namespace Boundary

/-- A reconstruction-to-probe compatibility package. The field
`probeEvaluation_reconstructed` is the theorem we will later prove from the
coend / weighted colimit construction. -/
structure BoundaryProbeEvaluationCompatibility
    {T : Type uT} [Category.{vT} T] where
  profileCategory : Type uD
  profileCategoryCat : Category.{vD} profileCategory
  comparison : BoundaryCoendPresentation (T := T)
  boundaryProfileFunctor : T ⥤ profileCategory

attribute [instance] BoundaryProbeEvaluationCompatibility.profileCategoryCat

namespace BoundaryProbeEvaluationCompatibility

variable {T : Type uT} [Category.{vT} T]
  (C : BoundaryProbeEvaluationCompatibility (T := T))

/-- The boundary profile comparison on the reconstructed object. -/
noncomputable abbrev reconstructedProfile
    [HasColimit C.comparison.dependencyDiagram.diagram] :=
  C.boundaryProfileFunctor.obj C.comparison.reconstructedObject

/-- The boundary profile comparison on the source object. -/
abbrev sourceProfile :=
  C.boundaryProfileFunctor.obj C.comparison.comparisonCocone.pt

/-- The probe-preservation theorem for the reconstructed boundary colimit. -/
noncomputable def boundaryProbeAgreementIso
    (P : BoundaryProbeEvaluationCompatibility (T := T))
    [HasColimit P.comparison.dependencyDiagram.diagram]
    [PreservesColimit P.comparison.dependencyDiagram.diagram
      P.boundaryProfileFunctor]
    (hSourceColimit : IsColimit P.comparison.comparisonCocone) :
    P.boundaryProfileFunctor.obj P.comparison.reconstructedObject ≅
    P.boundaryProfileFunctor.obj P.comparison.comparisonCocone.pt :=
by
  let D := P.comparison.dependencyDiagram.diagram
  let cReconstructed := CategoryTheory.Limits.colimit.cocone D
  have hReconstructed :
      Nonempty (IsColimit (P.boundaryProfileFunctor.mapCocone cReconstructed)) := by
    exact
      (PreservesColimit.preserves
        (K := D)
        (F := P.boundaryProfileFunctor)
        (hc := CategoryTheory.Limits.colimit.isColimit D))
  have hSource :
      Nonempty
        (IsColimit
          (P.boundaryProfileFunctor.mapCocone
          P.comparison.comparisonCocone)) := by
    exact
      (PreservesColimit.preserves
        (K := D)
        (F := P.boundaryProfileFunctor)
        (hc := hSourceColimit))
  letI : IsColimit (P.boundaryProfileFunctor.mapCocone cReconstructed) :=
    Classical.choice hReconstructed
  letI : IsColimit
        (P.boundaryProfileFunctor.mapCocone
          (BoundaryCoendPresentation.comparisonCocone P.comparison)) :=
    Classical.choice hSource
  exact
      IsColimit.coconePointUniqueUpToIso
      (P := Classical.choice hReconstructed)
      (Q := Classical.choice hSource)

/-- The explicit comparison morphism after applying the boundary profile
functor. -/
noncomputable def probeComparison
    (P : BoundaryProbeEvaluationCompatibility (T := T))
    [HasColimit P.comparison.dependencyDiagram.diagram]
    [PreservesColimit P.comparison.dependencyDiagram.diagram
      P.boundaryProfileFunctor]
    (hSourceColimit : IsColimit P.comparison.comparisonCocone) :
    P.boundaryProfileFunctor.obj P.comparison.reconstructedObject ≅
      P.boundaryProfileFunctor.obj P.comparison.comparisonCocone.pt :=
  boundaryProbeAgreementIso (P := P) hSourceColimit

/-- Probe agreement as a theorem-valued package. -/
theorem boundaryProbeAgreement
    (P : BoundaryProbeEvaluationCompatibility (T := T))
    [HasColimit P.comparison.dependencyDiagram.diagram]
    [PreservesColimit P.comparison.dependencyDiagram.diagram
      P.boundaryProfileFunctor]
    (hSourceColimit : IsColimit P.comparison.comparisonCocone) :
    Nonempty (P.boundaryProfileFunctor.obj P.comparison.reconstructedObject ≅
      P.boundaryProfileFunctor.obj P.comparison.comparisonCocone.pt) :=
  ⟨BoundaryProbeEvaluationCompatibility.boundaryProbeAgreementIso (P := P)
      hSourceColimit⟩

end BoundaryProbeEvaluationCompatibility

end Boundary

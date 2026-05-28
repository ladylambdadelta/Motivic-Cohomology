import Boundary.InternalPresentationPackage

/-!
# Geometric Recognition Target Surface

This file records the exact boundary-side theorem surface for recognizing the
internal presentation package inside geometric motives over `Q`, together with
its realization and transport consequences.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

namespace Boundary

noncomputable section

/-- Exact theorem-target package for the recognition stage above an internal
presentation package.  The carrier `DMgmQObj` is intentionally abstract here:
it names the target geometric-motive category without prematurely choosing a
concrete construction. -/
structure GeometricRecognitionPresentationQ
    (category : SmCorQ (k := k))
    (package : InternalPresentationPackageQ category) where
  DMgmQObj : Type (u + 1)
  motiveOf : package.minimal.GeneratorIndex → DMgmQObj
  generatorSoundnessTarget : ∀ idx : package.minimal.GeneratorIndex, Prop
  traceCategoryEquivalentToDMgmQTarget : Prop
  canonicalDMgmEquivalenceTarget : Prop
  realizationComparisonTarget : Prop
  universalRecognitionTarget : Prop
  pureHeartEquivalenceTarget : Prop
  comparisonByDoubleRepresentabilityTarget : Prop
  transportApiTarget : Prop
  recognitionConsequencesTarget : Prop

namespace GeometricRecognitionPresentationQ

def theoremTarget
    {category : SmCorQ (k := k)}
    {package : InternalPresentationPackageQ category}
    (presentation : GeometricRecognitionPresentationQ category package) : Prop :=
  (∀ idx : package.minimal.GeneratorIndex,
      presentation.generatorSoundnessTarget idx) ∧
    presentation.traceCategoryEquivalentToDMgmQTarget ∧
    presentation.canonicalDMgmEquivalenceTarget ∧
    presentation.realizationComparisonTarget ∧
    presentation.universalRecognitionTarget ∧
    presentation.pureHeartEquivalenceTarget ∧
    presentation.comparisonByDoubleRepresentabilityTarget ∧
    presentation.transportApiTarget ∧
    presentation.recognitionConsequencesTarget

end GeometricRecognitionPresentationQ

/-- Certified wrapper for the boundary-side geometric recognition stage. -/
structure CertifiedGeometricRecognitionPresentationQ
    (category : SmCorQ (k := k))
    (package : InternalPresentationPackageQ category) where
  target : GeometricRecognitionPresentationQ category package
  theorem_holds : target.theoremTarget

/-- Final boundary-side bundle through geometric recognition: the internal
presentation package together with the recognition/comparison layer built on
top of it. -/
structure BoundaryMotivicProgramQ (category : SmCorQ (k := k)) where
  internal : InternalPresentationPackageQ category
  recognition : GeometricRecognitionPresentationQ category internal

namespace BoundaryMotivicProgramQ

def theoremTarget
    {category : SmCorQ (k := k)}
    (program : BoundaryMotivicProgramQ category) : Prop :=
  program.internal.theoremTarget ∧ program.recognition.theoremTarget

end BoundaryMotivicProgramQ

/-- Certified wrapper for the full boundary-side motivic program through
recognition. -/
structure CertifiedBoundaryMotivicProgramQ (category : SmCorQ (k := k)) where
  target : BoundaryMotivicProgramQ category
  theorem_holds : target.theoremTarget

end

end Boundary

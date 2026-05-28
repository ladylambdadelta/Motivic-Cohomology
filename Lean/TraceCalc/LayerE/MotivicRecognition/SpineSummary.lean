import TraceCalc.LayerE.MotivicRecognition.TStructureTarget

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

/-- Audit-surface wrapper summarizing the recognition-to-heart dependency chain. -/
structure MotivicRecognitionSpine where
  tracePresentation : TracePresentation.{u, v, w, x, y}
  classicalPresentation : ClassicalMotivicPresentation tracePresentation
  recognition : DMgmRecognitionTarget.{u, v, w, x, y, z}
  structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  tStructurePackage : MotivicTStructurePackage.{u, v, w, x, y, z}
  recognitionAgreesWithTraceTarget : Prop
  recognitionAgreesWithClassicalTarget : Prop
  structuralRecognitionAgreesTarget : Prop
  tStructurePackageAgreesTarget : Prop

namespace MotivicRecognitionSpine

/-- Alias for the recognized motivic category at the spine level. -/
abbrev recognizedCategory
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.recognition.recognizedCategory

/-- Alias for the structural package at the spine level. -/
abbrev structuralPackage
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.structuralRecognition.structuralPackage

/-- Alias for the weight-structure target at the spine level. -/
abbrev weightStructure
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.weightStructure

/-- Alias for the t-structure target at the spine level. -/
abbrev tStructure
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.tStructure

/-- Alias for the Campaign 12B normalization-induced t-structure package at the
spine level. -/
abbrev traceMotivicTStructure
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.traceMotivicTStructure

/-- Alias for the heart candidate at the spine level. -/
abbrev heartCandidate
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.heart

/-- Alias for the abelian-heart target at the spine level. -/
abbrev abelianHeart
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.abelianHeart

/-- Alias for the `MM(Q)`-style heart target at the spine level. -/
abbrev mmqHeart
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z}) :=
  spine.tStructurePackage.mmqHeart

end MotivicRecognitionSpine

/-- Audit-surface theorem-target package recording completion of the full recognition spine.

This does not prove any new mathematics; it only packages the dependency surfaces that later proof
filling will need to discharge.

Current manuscript-spine assembly note: the completion-bridge trio
(`stableCompletion`, `stableCompletionConstruction`,
`completionUniversalProperty`), the classical decomposition wrapper for
`corePresentationEquivalence`, and the direct comparison-faithfulness wrapper
for the proof-relevant period consequence now live as local constructor helpers
in `ManuscriptSpineTargets.lean`. The remaining spine bottlenecks are therefore
the genuinely proof-bearing `C` fields, not these assembly steps. -/
structure MotivicRecognitionSpineCompleteTarget where
  spine : MotivicRecognitionSpine.{u, v, w, x, y, z}
  recognitionReadinessTarget : Prop
  universalPropertyTarget : Prop
  structuralPackageTarget : Prop
  tStructurePackageTarget : Prop
  mmQHeartTarget : Prop

end MotivicRecognition
end TraceCalc

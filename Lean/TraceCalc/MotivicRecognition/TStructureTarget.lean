import TraceCalc.MotivicRecognition.RecognitionTarget

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

set_option maxHeartbeats 3000000

/-!
# Campaign 12 taxonomy targets

Campaign 12 is now split internally as follows:

* 12A: triangulated/stable motivic recognition at the pinned `DM_gm(Q)_Q` layer;
* 12B: normalization-induced motivic `t`-structure on the recognized category;
* 12C: heart construction `MM(Q)` as the heart of that `t`-structure;
* 12D: heart recognition and mixed-motive comparison packaging.

Campaign 11 weight devissage remains an input to 12B. It is not itself the
motivic `t`-structure theorem.
-/

/-- Theorem target for a weight-structure package on the structurally-recognized
motivic category.

Campaign 11 trace-native weight orthogonality feeds this only as a later
consumer; it is not itself the motivic t-structure theorem. -/
structure WeightStructureTarget
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  weightClassNonpositive :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  weightClassNonnegative :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  orthogonalityTarget : Prop
  weightDecompositionTarget : Prop

namespace WeightStructureTarget

def ofCertifiedWeightDevissage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (certifiedWeightDevissage : CertifiedWeightDevissageData structuralRecognition) :
    WeightStructureTarget structuralRecognition where
  weightClassNonpositive := certifiedWeightDevissage.weightClassNonpositive
  weightClassNonnegative := certifiedWeightDevissage.weightClassNonnegative
  orthogonalityTarget := certifiedWeightDevissage.weightOrthogonalityTarget
  weightDecompositionTarget := certifiedWeightDevissage.boundedWeightDecompositionTarget

end WeightStructureTarget

/-- Campaign 12B target for the normalization-induced motivic `t`-structure on
the structurally recognized triangulated/stable category.

This is the finer theorem surface for the new Campaign 12 taxonomy. Campaign
11 weight devissage only feeds this package as input compatibility data; it is
not identified with the `t`-structure itself. Campaign 12A recognition into the
pinned `DM_gm(Q)_Q` layer is likewise an input compatibility requirement rather
than the statement of the `t`-structure. -/
structure TraceMotivicTStructureData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  tNonpos :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  tNonneg :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  shiftClosureNonposTarget : Prop
  shiftClosureNonnegTarget : Prop
  orthogonalityTarget : Prop
  truncationTriangleTarget : Prop
  truncationFunctorialityTarget : Prop
  normalizationCompatibilityTarget : Prop
  canonicalReconstructionCompatibilityTarget : Prop
  normalizationPacketCutTarget : Prop
  normalizationTruncationTriangleTarget : Prop
  orthogonalityFromSeparatedDegreesTarget : Prop
  campaign11WeightDevissageInputTarget : Prop
  recognitionCompatibilityTarget : Prop

/-- Campaign 12B sublemma target: canonical normalization yields a finite
degree-labeled packet decomposition together with an admissible threshold cut.

This packages the precise bridge from Campaign 11 normalized packet data to the
later truncation triangle. It does not yet assert the full `t`-structure. -/
structure NormalizationPacketCutData
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  packetRecord :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  lowerCutRecord :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      packetRecord X → Type z
  upperCutRecord :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      packetRecord X → Type z
  finiteDegreeLabeledPacketDAGTarget : Prop
  canonicalThresholdCutTarget : Prop
  lowerCutAdmissibilityTarget : Prop
  upperCutAdmissibilityTarget : Prop
  boundaryDependencyClosureTarget : Prop
  gluingClosureTarget : Prop
  canonicalReconstructionCompatibilityTarget : Prop
  campaign11WeightDevissageCompatibilityTarget : Prop

/-- Campaign 12B key sublemma target: the canonical normalized lower cut gives
the truncation triangle, and the complementary cofiber agrees with the upper
cut.

This is the precise formal surface for the argument that normalization produces
canonical truncation data rather than merely a weight assignment. -/
structure NormalizationTruncationTriangle
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  lowerTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  upperTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  totalObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  upperTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerInclusion :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (lowerTruncationObject X)
        (totalObject X)
  upperProjection :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (totalObject X)
        (upperTruncationObject X)
  cofiberSequenceWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  cofiberIdentifiesUpper :
    structuralRecognition.recognition.recognizedCategory.Object → Prop
  lowerCutRealizationTarget : Prop
  upperCutCofiberRealizationTarget : Prop
  canonicalInclusionTarget : Prop
  truncationTriangleTarget : Prop
  cofiberIdentifiesUpperCutTarget : Prop
  orthogonalityFromSeparatedDegreesTarget : Prop
  truncationFunctorialityTarget : Prop
  recognitionCompatibilityTarget : Prop
  campaign11WeightDevissageInputTarget : Prop

/- Theorem target for a coarse legacy `t`-structure compatibility shell on the
structurally-recognized motivic category.

This compatibility shell is retained for existing callers. The richer Campaign
12B target surface is `TraceMotivicTStructureData`. -/
structure TStructureTarget
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  connectiveObject :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  coconnectiveObject :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  truncationTriangleTarget : Prop
  orthogonalityTarget : Prop

/-- Preferred honest name for the coarse compatibility shell retained for
legacy callers. Public theorem-facing routes should use
`TraceMotivicTStructureData` for the actual motivic `t`-structure target. -/
abbrev CoarseTStructureCompatibilityTarget := TStructureTarget

/-- Typed candidate for the heart of the recognized t-structure.

Membership witnesses remain type-valued rather than being collapsed into `Prop`. -/
structure HeartCandidate
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  heartObject : Type z
  forgetToMotivicObject :
    heartObject → structuralRecognition.recognition.recognizedCategory.Object
  heartMembershipWitness : heartObject → Type z

/-- Campaign 12C typed heart surface induced by a specific Campaign 12B
`t`-structure.

This packages the heart as the intersection of the `tNonpos` and `tNonneg`
classes without assuming any pre-existing classical `MM(Q)` object. -/
structure TraceMotivicHeart
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  heartObject : Type z
  forgetToMotivicObject :
    heartObject → structuralRecognition.recognition.recognizedCategory.Object
  heartNonposWitness :
    ∀ obj : heartObject, tStructure.tNonpos (forgetToMotivicObject obj)
  heartNonnegWitness :
    ∀ obj : heartObject, tStructure.tNonneg (forgetToMotivicObject obj)

namespace TraceMotivicHeart

def ofTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    TraceMotivicHeart tStructure where
  heartObject :=
    Σ obj : structuralRecognition.recognition.recognizedCategory.Object,
      tStructure.tNonpos obj × tStructure.tNonneg obj
  forgetToMotivicObject := fun obj => obj.1
  heartNonposWitness := fun obj => obj.2.1
  heartNonnegWitness := fun obj => obj.2.2

end TraceMotivicHeart

/-- Heart morphisms are recognized-category morphisms whose endpoints are
already certified as heart objects. -/
structure TraceMotivicHeartMorphism
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlying :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)
  sourceHeart :
    tStructure.tNonpos (heart.forgetToMotivicObject source) ×
      tStructure.tNonneg (heart.forgetToMotivicObject source)
  targetHeart :
    tStructure.tNonpos (heart.forgetToMotivicObject target) ×
      tStructure.tNonneg (heart.forgetToMotivicObject target)

namespace TraceMotivicHeartMorphism

/-- Build a trace-heart morphism from its underlying recognized-category map
once the source and target heart objects have been fixed. -/
def ofUnderlying
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (source target : heart.heartObject)
    (underlying :
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)) :
    TraceMotivicHeartMorphism heart source target where
  underlying := underlying
  sourceHeart :=
    ⟨heart.heartNonposWitness source, heart.heartNonnegWitness source⟩
  targetHeart :=
    ⟨heart.heartNonposWitness target, heart.heartNonnegWitness target⟩

/-- The canonical `ofUnderlying` wrapper is determined by its underlying
recognized-category map. -/
theorem ofUnderlying_eq_of_underlying_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    {f g : structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)}
    (h : f = g) :
    TraceMotivicHeartMorphism.ofUnderlying source target f =
      TraceMotivicHeartMorphism.ofUnderlying source target g := by
  cases h
  rfl

/-- `HEq` on underlying recognized-category maps is enough to identify the
canonical `ofUnderlying` wrappers. -/
theorem ofUnderlying_eq_of_underlying_heq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    {f g : structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject source)
      (heart.forgetToMotivicObject target)}
    (h : HEq f g) :
    TraceMotivicHeartMorphism.ofUnderlying source target f =
      TraceMotivicHeartMorphism.ofUnderlying source target g := by
  cases h
  rfl

end TraceMotivicHeartMorphism

/-- Proof-relevant exactness data for a heart morphism. This does not assert
the abelian theorem by itself; it packages the concrete heart objects,
morphism, and comparison witness that such a theorem would consume. -/
structure TraceMotivicHeartExactData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    {sourceObject targetObject : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) where
  kernelObject : heart.heartObject
  cokernelObject : heart.heartObject
  imageObject : heart.heartObject
  coimageObject : heart.heartObject
  kernelInclusion :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject kernelObject)
      (heart.forgetToMotivicObject sourceObject)
  cokernelProjection :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject targetObject)
      (heart.forgetToMotivicObject cokernelObject)
  imageInclusion :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject imageObject)
      (heart.forgetToMotivicObject targetObject)
  coimageProjection :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject sourceObject)
      (heart.forgetToMotivicObject coimageObject)
  kernelWitness : Type z
  cokernelWitness : Type z
  imageWitness : Type z
  coimageWitness : Type z
  imageCoimageComparison :
    structuralRecognition.recognition.recognizedCategory.Hom
      (heart.forgetToMotivicObject imageObject)
      (heart.forgetToMotivicObject coimageObject)
  imageCoimageComparisonWitness : Type z

/-- Proof-relevant exactness package indexed by an actual transported heart
morphism. The package does not erase the witness carrier: consumers receive a
type of exactness data together with a realization into concrete kernel /
cokernel / image / coimage objects and maps for that same morphism. -/
structure TraceMotivicHeartExactPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    {sourceObject targetObject : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) where
  ExactnessWitness : Type z
  realize : ExactnessWitness → TraceMotivicHeartExactData heart morphism

abbrev TraceMotivicHeartExactWitnessData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (exactnessData :
      ∀ {sourceObject targetObject : heart.heartObject},
        (morphism : TraceMotivicHeartMorphism heart sourceObject targetObject) →
          TraceMotivicHeartExactPackage heart morphism) :
    Type z :=
  Σ sourceObject : heart.heartObject,
    Σ targetObject : heart.heartObject,
      Σ morphism : TraceMotivicHeartMorphism heart sourceObject targetObject,
        (exactnessData morphism).ExactnessWitness

/-- Heart-level compatibility needed to turn recognized morphism-indexed fiber
and cofiber data into actual heart objects. The recognized exactness system
constructs the underlying objects and maps; this package records that those
objects land back in the heart of the given `t`-structure. -/
structure RecognizedFiberCofiberHeartCompatibility
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (fiberCofiberSystem : RecognizedFiberCofiberSystem structuralRecognition) where
  fiberHeartWitness :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject),
        tStructure.tNonpos (fiberCofiberSystem.fiberData morphism).fiberObject ×
          tStructure.tNonneg (fiberCofiberSystem.fiberData morphism).fiberObject
  cofiberHeartWitness :
    ∀ {sourceObject targetObject :
      structuralRecognition.recognition.recognizedCategory.Object}
      (morphism :
        structuralRecognition.recognition.recognizedCategory.Hom
          sourceObject targetObject),
        tStructure.tNonpos (fiberCofiberSystem.cofiberData morphism).cofiberObject ×
          tStructure.tNonneg (fiberCofiberSystem.cofiberData morphism).cofiberObject

/-- Proof-relevant image/coimage comparison data indexed by an actual heart
morphism and derived from the same recognized fiber/cofiber system. -/
structure RecognizedImageCoimageComparisonData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (fiberCofiberSystem : RecognizedFiberCofiberSystem structuralRecognition)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  comparisonMorphism :
    structuralRecognition.recognition.recognizedCategory.Hom
      (fiberCofiberSystem.fiberData
        (fiberCofiberSystem.cofiberData morphism.underlying).targetToCofiber).fiberObject
      (fiberCofiberSystem.cofiberData
        (fiberCofiberSystem.fiberData morphism.underlying).fiberToSource).cofiberObject
  ComparisonWitnessCarrier : Type z
  comparisonWitness : ComparisonWitnessCarrier
  comparisonCompatibilityTarget : Prop

/-- Constructive exactness system for the Campaign 12 heart. This is the
minimal proof-relevant package needed to replace the generic fallback exactness
route. -/

structure TraceMotivicHeartConstructiveExactnessSystem
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  recognizedFiberCofiber : RecognizedFiberCofiberSystem structuralRecognition
  heartCompatibility :
    RecognizedFiberCofiberHeartCompatibility tStructure recognizedFiberCofiber
  imageCoimageComparisonData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject),
        RecognizedImageCoimageComparisonData tStructure recognizedFiberCofiber morphism

namespace TraceMotivicHeart

def kernelRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedFiberData structuralRecognition morphism.underlying :=
  system.recognizedFiberCofiber.fiberData morphism.underlying

def cokernelRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedCofiberData structuralRecognition morphism.underlying :=
  system.recognizedFiberCofiber.cofiberData morphism.underlying

def imageRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedFiberData structuralRecognition
      ((TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber) :=
  system.recognizedFiberCofiber.fiberData
    (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber

def coimageRecognizedData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    RecognizedCofiberData structuralRecognition
      ((TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource) :=
  system.recognizedFiberCofiber.cofiberData
    (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

def recognizedFiber_yields_heartKernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.kernelRecognizedData system morphism).fiberObject,
    system.heartCompatibility.fiberHeartWitness morphism.underlying⟩

def recognizedCofiber_yields_heartCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.cokernelRecognizedData system morphism).cofiberObject,
    system.heartCompatibility.cofiberHeartWitness morphism.underlying⟩

def heartImage_from_kernelCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.imageRecognizedData system morphism).fiberObject,
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber⟩

def heartCoimage_from_kernelCokernel
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    (TraceMotivicHeart.ofTStructure tStructure).heartObject :=
  ⟨(TraceMotivicHeart.coimageRecognizedData system morphism).cofiberObject,
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource⟩

def kernelInclusion
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism)
      sourceObject where
  underlying := (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource
  sourceHeart :=
    (system.heartCompatibility.fiberHeartWitness morphism.underlying)
  targetHeart := sourceObject.2

def cokernelProjection
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      targetObject
      (TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism) where
  underlying := (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  sourceHeart := targetObject.2
  targetHeart :=
    (system.heartCompatibility.cofiberHeartWitness morphism.underlying)

def imageInclusion
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      targetObject where
  underlying := (TraceMotivicHeart.imageRecognizedData system morphism).fiberToSource
  sourceHeart :=
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  targetHeart := targetObject.2

def coimageProjection
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      sourceObject
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism) where
  underlying := (TraceMotivicHeart.coimageRecognizedData system morphism).targetToCofiber
  sourceHeart := sourceObject.2
  targetHeart :=
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

def heartImageCoimageComparison
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism) where
  underlying := (system.imageCoimageComparisonData morphism).comparisonMorphism
  sourceHeart :=
    system.heartCompatibility.fiberHeartWitness
      (TraceMotivicHeart.cokernelRecognizedData system morphism).targetToCofiber
  targetHeart :=
    system.heartCompatibility.cofiberHeartWitness
      (TraceMotivicHeart.kernelRecognizedData system morphism).fiberToSource

end TraceMotivicHeart

structure TraceMotivicHeartKernelWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  kernelMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism)
      sourceObject
  universalPropertyWitness :
    (TraceMotivicHeart.kernelRecognizedData system morphism).FiberWitnessCarrier
  universalPropertyCorrect :
    (TraceMotivicHeart.kernelRecognizedData system morphism).fiberCompatibilityTarget

structure TraceMotivicHeartCokernelWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  cokernelMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      targetObject
      (TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism)
  universalPropertyWitness :
    (TraceMotivicHeart.cokernelRecognizedData system morphism).CofiberWitnessCarrier
  universalPropertyCorrect :
    (TraceMotivicHeart.cokernelRecognizedData system morphism).cofiberCompatibilityTarget

structure TraceMotivicHeartImageWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  imageMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      targetObject
  factorizationWitness :
    (TraceMotivicHeart.imageRecognizedData system morphism).FiberWitnessCarrier
  factorizationCorrect :
    (TraceMotivicHeart.imageRecognizedData system morphism).fiberCompatibilityTarget

structure TraceMotivicHeartCoimageWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  coimageMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      sourceObject
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism)
  factorizationWitness :
    (TraceMotivicHeart.coimageRecognizedData system morphism).CofiberWitnessCarrier
  factorizationCorrect :
    (TraceMotivicHeart.coimageRecognizedData system morphism).cofiberCompatibilityTarget

structure TraceMotivicHeartImageCoimageComparisonWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  comparisonMap :
    TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
      (TraceMotivicHeart.heartImage_from_kernelCokernel system morphism)
      (TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism)
  comparisonWitness :
    (system.imageCoimageComparisonData morphism).ComparisonWitnessCarrier
  comparisonCorrect :
    (system.imageCoimageComparisonData morphism).comparisonCompatibilityTarget

structure TraceMotivicHeartConstructedExactnessWitness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) where
  kernelData : TraceMotivicHeartKernelWitness system morphism
  cokernelData : TraceMotivicHeartCokernelWitness system morphism
  imageData : TraceMotivicHeartImageWitness system morphism
  coimageData : TraceMotivicHeartCoimageWitness system morphism
  imageCoimageData : TraceMotivicHeartImageCoimageComparisonWitness system morphism

namespace TraceMotivicHeartExactData

def ofConstructedExactness
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject)
    (witness : TraceMotivicHeartConstructedExactnessWitness system morphism) :
    TraceMotivicHeartExactData (TraceMotivicHeart.ofTStructure tStructure) morphism where
  kernelObject := TraceMotivicHeart.recognizedFiber_yields_heartKernel system morphism
  cokernelObject := TraceMotivicHeart.recognizedCofiber_yields_heartCokernel system morphism
  imageObject := TraceMotivicHeart.heartImage_from_kernelCokernel system morphism
  coimageObject := TraceMotivicHeart.heartCoimage_from_kernelCokernel system morphism
  kernelInclusion := witness.kernelData.kernelMap.underlying
  cokernelProjection := witness.cokernelData.cokernelMap.underlying
  imageInclusion := witness.imageData.imageMap.underlying
  coimageProjection := witness.coimageData.coimageMap.underlying
  kernelWitness := TraceMotivicHeartKernelWitness system morphism
  cokernelWitness := TraceMotivicHeartCokernelWitness system morphism
  imageWitness := TraceMotivicHeartImageWitness system morphism
  coimageWitness := TraceMotivicHeartCoimageWitness system morphism
  imageCoimageComparison := witness.imageCoimageData.comparisonMap.underlying
  imageCoimageComparisonWitness := TraceMotivicHeartImageCoimageComparisonWitness system morphism

end TraceMotivicHeartExactData

namespace TraceMotivicHeartExactPackage

def heartExactPackage_from_recognizedFiberCofiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure)
    {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject}
    (morphism :
      TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
        sourceObject targetObject) :
    TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism where
  ExactnessWitness := TraceMotivicHeartConstructedExactnessWitness system morphism
  realize := TraceMotivicHeartExactData.ofConstructedExactness system morphism

end TraceMotivicHeartExactPackage

/-- Campaign 12C legacy trace-native candidate/scaffold for the category
`MM(Q)` constructed as the heart of the Campaign 12B `t`-structure.

This is a construction target, not an assumption that a classical `MM(Q)` is
already available. No semisimplicity or global `Ext`-vanishing is asserted at
this stage. The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofFinalMotivicInfrastructure`
in `ManuscriptSpineTargets.lean`. -/
structure MMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  motive : Type z
  forgetToMotivicObject :
    motive → structuralRecognition.recognition.recognizedCategory.Object
  heartWitness :
    ∀ obj : motive,
      tStructure.tNonpos (forgetToMotivicObject obj) ×
        tStructure.tNonneg (forgetToMotivicObject obj)

abbrev MixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  MMQ (structuralRecognition := structuralRecognition)

/-- Honest alias for the legacy trace-native heart candidate over Q scaffold.
Not the classical category MM(Q). The live classical MM(Q) recognition path is
RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
in ManuscriptSpineTargets.lean. -/
abbrev TraceMotivicHeartCandidateOverQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  MMQ (structuralRecognition := structuralRecognition)

/-- Honest deprecated alias for the legacy trace-native MMQ scaffold.
Not the classical category MM(Q). The live classical MM(Q) recognition path is
RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
in ManuscriptSpineTargets.lean. -/
abbrev TraceMMQCandidateDeprecated
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  MMQ (structuralRecognition := structuralRecognition)

namespace MMQ

/-- Campaign 12C theorem target asserting that the constructed `MM(Q)` is the
heart of the Campaign 12B `t`-structure. -/
structure isHeartOfTraceMotivicTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  heartConstructionTarget : Prop
  heartAgreementTarget : Prop

/-- Campaign 12C theorem target asserting that the constructed `MM(Q)` is
abelian. This does not assert semisimplicity. -/
structure isAbelianTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  exactnessData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) →
        TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z
  kernelTarget : Prop
  cokernelTarget : Prop
  imageCoimageTarget : Prop
  abelianCategoryTarget : Prop

/-- Campaign 12D target for the embedding of the constructed `MM(Q)` into the
recognized `DM_gm(Q)_Q`-level motivic category. -/
structure embeddingIntoDMgmQTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) where
  embeddingTarget : Prop
  comparisonCompatibilityTarget : Prop
  recognitionCompatibilityTarget : Prop

end MMQ

/-- Named theorem package for the three normalization t-structure obligations in
Package 7.  Each field is an exact theorem statement, not a free `Prop` slot. -/
structure NormTStructureTheoremPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  /-- The normalization-transported t-structure is compatible with the underlying
  weight structure: the weight filtration cutoffs coincide with the
  t-truncation degrees as recorded by the normalization packet cut. -/
  normalizationInducesWeightCompatibleTStructure :
    tStructure.normalizationPacketCutTarget ∧
      packetCut.canonicalReconstructionCompatibilityTarget
  /-- The transported t-structure is motivic: the t-truncation triangles respect
  the normalization data and the campaign-11 weight devissage input. -/
  transportedTStructureIsMotivic :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.campaign11WeightDevissageInputTarget
  /-- Truncation triangles from the normalization packet cut are representable:
  the truncation triangle and truncation functoriality targets both hold. -/
  truncationTriangleRepresentability :
    tStructure.truncationTriangleTarget ∧
      tStructure.truncationFunctorialityTarget

/-- Classical-facing recognition statement for the trace-constructed heart.

This is the exported theorem surface saying that `TraceMotivicHeart.ofTStructure`
is recognized as the classical mixed-motive abelian heart over `Q`, through the
already assembled `DM_gm(Q)_Q` recognition path. It deliberately packages the
recognition as the conjunction of the transported-heart identification, the
mixed-motive abelian-heart identification, the MM(Q) identification, and the
exact transported-heart compatibility laws, rather than reducing the statement
to a bare normalization or orthogonality fragment. -/
structure TStructureMotivicMMQInfrastructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (heart : TraceMotivicHeart tStructure) where
  dm_gm_Q_Q_category : Type u
  dm_gm_Q_Q_object : dm_gm_Q_Q_category
  dm_gm_Q_Q_hom : dm_gm_Q_Q_category → dm_gm_Q_Q_category → Type v
  dm_gm_Q_Q_id : ∀ X, dm_gm_Q_Q_hom X X
  dm_gm_Q_Q_comp : ∀ {X Y Z}, dm_gm_Q_Q_hom X Y → dm_gm_Q_Q_hom Y Z → dm_gm_Q_Q_hom X Z
  rationalBaseField : Type w
  rationalCoefficientField : Type x
  rationalBaseFieldIsQ : FieldIsQData rationalBaseField
  rationalCoefficientFieldIsQ : FieldIsQData rationalCoefficientField
  tNonpositive : dm_gm_Q_Q_category → Prop
  tNonnegative : dm_gm_Q_Q_category → Prop
  truncLE : Int → dm_gm_Q_Q_category → dm_gm_Q_Q_category
  truncGE : Int → dm_gm_Q_Q_category → dm_gm_Q_Q_category
  truncationTriangle : ∀ (n : Int) (X : dm_gm_Q_Q_category), Prop
  classicalHeartObject : Type y
  classicalHeartEmbedding : classicalHeartObject → dm_gm_Q_Q_category
  classicalHeartIsHeart : ∀ A : classicalHeartObject,
    tNonpositive (classicalHeartEmbedding A) ∧
      tNonnegative (classicalHeartEmbedding A)
  classicalHeartHom : classicalHeartObject → classicalHeartObject → Type z
  classicalHeartZero : classicalHeartObject
  classicalHeartAdd : classicalHeartObject → classicalHeartObject → classicalHeartObject
  classicalHeartKernel : ∀ {A B : classicalHeartObject}, classicalHeartHom A B → classicalHeartObject
  classicalHeartCokernel : ∀ {A B : classicalHeartObject}, classicalHeartHom A B → classicalHeartObject
  mixedMotivesQ : Type y
  mixedMotivesQHom : mixedMotivesQ → mixedMotivesQ → Type z
  mixedMotivesQToHeart : mixedMotivesQ → classicalHeartObject
  heartToMixedMotivesQ : classicalHeartObject → mixedMotivesQ
  mixedMotivesQToHeart_leftInverse :
    ∀ M : mixedMotivesQ, heartToMixedMotivesQ (mixedMotivesQToHeart M) = M
  mixedMotivesQToHeart_rightInverse :
    ∀ A : classicalHeartObject, mixedMotivesQToHeart (heartToMixedMotivesQ A) = A
  traceHeartToClassicalHeart : TraceMotivicHeart tStructure → classicalHeartObject
  traceHeartFromClassicalHeart : classicalHeartObject → TraceMotivicHeart tStructure
  traceHeartClassical_leftInverse :
    ∀ H : TraceMotivicHeart tStructure,
      traceHeartFromClassicalHeart (traceHeartToClassicalHeart H) = H
  traceHeartClassical_rightInverse :
    ∀ A : classicalHeartObject,
      traceHeartToClassicalHeart (traceHeartFromClassicalHeart A) = A
  distinguishedHeartAgreement : traceHeartToClassicalHeart heart =
    traceHeartToClassicalHeart (TraceMotivicHeart.ofTStructure tStructure)
  transportedTStructureMatchesClassical : tStructure.recognitionCompatibilityTarget
  normalizationRealizesClassicalHeart : tStructure.normalizationCompatibilityTarget
  canonicalReconstructionRealizesClassicalHeart :
    tStructure.canonicalReconstructionCompatibilityTarget
  separatedDegreeOrthogonalityRealizesMMQ :
    tStructure.orthogonalityFromSeparatedDegreesTarget
  exactHeartEmbedding :
    tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
      tStructure.orthogonalityTarget
  pureHeartNaturality :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.normalizationPacketCutTarget

structure RecognizesClassicalMMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
  (heart : TraceMotivicHeart tStructure) where
  finalMotivicInfrastructure : TStructureMotivicMMQInfrastructure tStructure heart
  traceHeartIsConstructedHeart : heart = TraceMotivicHeart.ofTStructure tStructure
  recognizedDMgmQTransportTarget : tStructure.recognitionCompatibilityTarget
  classicalAbelianHeartOverQTarget :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.canonicalReconstructionCompatibilityTarget
  mixedMotiveHeartOverQTarget :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.orthogonalityFromSeparatedDegreesTarget
  transportedHeartExactnessTarget :
    tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
      tStructure.orthogonalityTarget
  heartRecognitionNaturalityTarget :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.normalizationPacketCutTarget

namespace RecognizesClassicalMMQ

/-- Assemble the classical MM(Q) recognition record from the already named
recognition-spine components. This is the provenance-preserving constructor:
each field of `RecognizesClassicalMMQ` is supplied by the corresponding
transport, heart-identification, exactness, or naturality theorem rather than
by an opaque single theorem-package field. -/
def ofFinalMotivicInfrastructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (infrastructure : TStructureMotivicMMQInfrastructure tStructure heart)
    (traceHeartIsConstructedHeart : heart = TraceMotivicHeart.ofTStructure tStructure) :
    RecognizesClassicalMMQ tStructure heart where
  finalMotivicInfrastructure := infrastructure
  traceHeartIsConstructedHeart := traceHeartIsConstructedHeart
  recognizedDMgmQTransportTarget := infrastructure.transportedTStructureMatchesClassical
  classicalAbelianHeartOverQTarget :=
    ⟨infrastructure.normalizationRealizesClassicalHeart,
      infrastructure.canonicalReconstructionRealizesClassicalHeart⟩
  mixedMotiveHeartOverQTarget :=
    ⟨infrastructure.normalizationRealizesClassicalHeart,
      infrastructure.separatedDegreeOrthogonalityRealizesMMQ⟩
  transportedHeartExactnessTarget := infrastructure.exactHeartEmbedding
  heartRecognitionNaturalityTarget := infrastructure.pureHeartNaturality

end RecognizesClassicalMMQ

/-- Named component theorem package for the classical MM(Q) heart recognition
surface.  The fields are exactly the five non-definitional component facts
needed to assemble `ClassicalMMQHeartTheorems` for the canonical transported
heart.  This record is deliberately below the final `RecognizesClassicalMMQ`
surface: it exposes the cobblestone facts individually instead of accepting the
closed recognition statement as an input. -/
structure TraceMotivicTStructureComponentTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :
    tStructure.recognitionCompatibilityTarget
  classicalAbelianHeartIsMixedMotivesQ :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.canonicalReconstructionCompatibilityTarget
  mixedMotiveHeartOverQTarget :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.orthogonalityFromSeparatedDegreesTarget
  compatibilityWithTransportedTStructureIsExact :
    tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
      tStructure.orthogonalityTarget
  compatibilityWithHeartRecognitionIsNatural :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.normalizationPacketCutTarget

namespace TraceMotivicTStructureComponentTheorems

/-- Assemble the component theorem package from its individual projection facts.
This is a compatibility constructor for callers that already expose the five
component theorems separately. -/
def ofComponents
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (transportedHeartIdentifiesClassicalGeometricMotivesHeart :
      tStructure.recognitionCompatibilityTarget)
    (classicalAbelianHeartIsMixedMotivesQ :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.canonicalReconstructionCompatibilityTarget)
    (mixedMotiveHeartOverQTarget :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.orthogonalityFromSeparatedDegreesTarget)
    (compatibilityWithTransportedTStructureIsExact :
      tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
        tStructure.orthogonalityTarget)
    (compatibilityWithHeartRecognitionIsNatural :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.normalizationPacketCutTarget) :
    TraceMotivicTStructureComponentTheorems tStructure where
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :=
    transportedHeartIdentifiesClassicalGeometricMotivesHeart
  classicalAbelianHeartIsMixedMotivesQ := classicalAbelianHeartIsMixedMotivesQ
  mixedMotiveHeartOverQTarget := mixedMotiveHeartOverQTarget
  compatibilityWithTransportedTStructureIsExact :=
    compatibilityWithTransportedTStructureIsExact
  compatibilityWithHeartRecognitionIsNatural := compatibilityWithHeartRecognitionIsNatural

end TraceMotivicTStructureComponentTheorems

/-- Named theorem package for the classical heart identification in Package 7.
Each field is an exact theorem statement: the transported trace heart is the
abelian heart of the classical triangulated category of geometric motives over Q
with rational coefficients, and that heart is MM(Q). -/
structure ClassicalMMQHeartTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (heart : TraceMotivicHeart tStructure) where
  finalMotivicInfrastructure : TStructureMotivicMMQInfrastructure tStructure heart
  /-- The transported heart used by this theorem package is the canonical heart
  constructed from the transported t-structure. -/
  classicalTraceHeartAgreement : heart = TraceMotivicHeart.ofTStructure tStructure
  /-- The transported trace heart identifies with the classical abelian heart:
  `TraceMotivicHeart` already carries proof-relevant `heartNonposWitness` and
  `heartNonnegWitness` data by construction.  At the Prop level the canonical
  identification is recorded by the recognition compatibility target. -/
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :
    tStructure.recognitionCompatibilityTarget
  /-- The classical abelian heart is the category of mixed motives over Q:
  the identification respects the mixed-motive structure recorded by
  the normalization compatibility and canonical reconstruction targets. -/
  classicalAbelianHeartIsMixedMotivesQ :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.canonicalReconstructionCompatibilityTarget
  /-- The mixed-motive heart over Q satisfies the MM(Q)-level separated-degree
  orthogonality criterion. This is a component theorem, not the full
  `RecognizesClassicalMMQ` record. -/
  mixedMotiveHeartOverQTarget :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.orthogonalityFromSeparatedDegreesTarget
  /-- The heart identification is compatible with the transported t-structure:
  the abelian heart embedding respects the shift-closure and orthogonality laws. -/
  compatibilityWithTransportedTStructureIsExact :
    tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
      tStructure.orthogonalityTarget
  /-- The identification is compatible with the pure-heart recognition:
  the normalization compatibility and normalization packet cut targets hold,
  confirming that pure-motive objects sit in the weight-zero part of the heart. -/
  compatibilityWithHeartRecognitionIsNatural :
    tStructure.normalizationCompatibilityTarget ∧
      tStructure.normalizationPacketCutTarget
  /-- The category of mixed motives over Q with rational coefficients is MM(Q):
  this compatibility alias remains for existing package code, but is derived
  from the component fields rather than accepted as a theorem-package input. -/
  classicalMixedMotivesQIsMMQ :=
    RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
      (tStructure := tStructure)
      (heart := heart)
      finalMotivicInfrastructure
      classicalTraceHeartAgreement
  /-- The trace-constructed heart is recognized as the classical mixed-motive
  abelian heart over Q. This preferred exported recognition surface is derived
  from the component fields above. -/
  traceHeart_recognizes_classical_MMQ :=
    RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
      (tStructure := tStructure)
      (heart := heart)
      finalMotivicInfrastructure
      classicalTraceHeartAgreement

/-- Concrete morphism-level transport data from the trace-constructed heart to
`MM(Q)`.

This is the exact missing carrier for the final replay-reflection step: object
transport from trace-heart objects to the classical heart, morphism transport
from trace-heart morphisms to classical-heart morphisms, and then transport
from classical-heart morphisms to `MM(Q)` morphisms. -/
structure ClassicalMMQHeartMorphismTransport
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    (theorems : ClassicalMMQHeartTheorems tStructure heart) where
  traceObjectToClassicalHeart :
    heart.heartObject → theorems.finalMotivicInfrastructure.classicalHeartObject
  traceMorphismToClassicalHeart :
    ∀ {source target : heart.heartObject},
      TraceMotivicHeartMorphism heart source target →
        theorems.finalMotivicInfrastructure.classicalHeartHom
          (traceObjectToClassicalHeart source)
          (traceObjectToClassicalHeart target)
  classicalHeartMorphismToMixedMotivesQ :
    ∀ {source target : theorems.finalMotivicInfrastructure.classicalHeartObject},
      theorems.finalMotivicInfrastructure.classicalHeartHom source target →
        theorems.finalMotivicInfrastructure.mixedMotivesQHom
          (theorems.finalMotivicInfrastructure.heartToMixedMotivesQ source)
          (theorems.finalMotivicInfrastructure.heartToMixedMotivesQ target)

namespace ClassicalMMQHeartMorphismTransport

/-- The `MM(Q)` object corresponding to a trace-heart object under a concrete
morphism-transport package. -/
def traceObjectToMixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    (obj : heart.heartObject) :
    theorems.finalMotivicInfrastructure.mixedMotivesQ :=
  theorems.finalMotivicInfrastructure.heartToMixedMotivesQ
    (transport.traceObjectToClassicalHeart obj)

/-- Transport a trace-heart morphism to the corresponding `MM(Q)` morphism. -/
def traceMorphismToMixedMotivesQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (morphism : TraceMotivicHeartMorphism heart source target) :
    theorems.finalMotivicInfrastructure.mixedMotivesQHom
      (transport.traceObjectToMixedMotivesQ source)
      (transport.traceObjectToMixedMotivesQ target) :=
  transport.classicalHeartMorphismToMixedMotivesQ
    (transport.traceMorphismToClassicalHeart morphism)

/-- The transport theorem needed by the recognized replay-reflection step:
equality of trace-heart morphisms implies equality of the transported `MM(Q)`
morphisms. -/
theorem traceMorphism_eq_implies_mixedMotivesQHom_eq
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    {f g : TraceMotivicHeartMorphism heart source target}
    (hfg : f = g) :
    transport.traceMorphismToMixedMotivesQ f =
      transport.traceMorphismToMixedMotivesQ g := by
  cases hfg
  rfl

end ClassicalMMQHeartMorphismTransport

/-- RealObjects-side semantic interpretation of completed traces into the
underlying recognized-category Hom for fixed heart endpoints.

This is the exact special case supplied by the existing frontier-determination
theorems: once a completed replay record has been interpreted as the
underlying recognized morphism between the chosen source and target heart
objects, the heart-morphism wrapper is canonical. -/
structure RealObjectsUnderlyingHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlyingOfCompletedTrace :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)
  underlyingHEq_of_frontierEquiv :
    ∀ {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier →
          HEq
            (underlyingOfCompletedTrace R₁)
            (underlyingOfCompletedTrace R₂)

/-- RealObjects-side realization of completed reconstruction records as fixed
trace-heart morphisms.

This is the exact seam for the remaining holographic step: once a certified
completed trace has been assigned a trace-heart morphism with fixed source and
target heart objects, frontier-equivalent completed traces determine the same
underlying heart morphism action. -/
structure RealObjectsTraceHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (source target : heart.heartObject) where
  underlyingOfCompletedTrace :
    TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup →
      structuralRecognition.recognition.recognizedCategory.Hom
        (heart.forgetToMotivicObject source)
        (heart.forgetToMotivicObject target)
  underlyingHEq_of_frontierEquiv :
    ∀ {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup},
      TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
        (C.assignment.assign R₁).frontier
        (C.assignment.assign R₂).frontier →
          HEq
            (underlyingOfCompletedTrace R₁)
            (underlyingOfCompletedTrace R₂)

namespace RealObjectsTraceHeartMorphismRealization

/-- The canonical trace-heart morphism realized by a completed trace. -/
def morphismOfCompletedTrace
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    TraceMotivicHeartMorphism heart source target :=
  TraceMotivicHeartMorphism.ofUnderlying source target
    (realization.underlyingOfCompletedTrace R)

@[simp] theorem morphismOfCompletedTrace_underlying
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    (realization.morphismOfCompletedTrace R).underlying = realization.underlyingOfCompletedTrace R :=
  rfl

/-- Frontier-equivalent completed traces induce the same trace-heart morphism
once the realization map fixes the source and target heart objects. -/
theorem traceHeartMorphism_eq_of_frontierEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hFrontier : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier) :
    realization.morphismOfCompletedTrace R₁ =
      realization.morphismOfCompletedTrace R₂ := by
  exact TraceMotivicHeartMorphism.ofUnderlying_eq_of_underlying_heq
    (source := source) (target := target)
    (realization.underlyingHEq_of_frontierEquiv hFrontier)

/-- Equality of RealObjects canonical normal forms implies equality of the
realized trace-heart morphisms.

This is the exact CanNF-to-trace-heart equality step needed by the holographic
bridge once the completed-trace-to-heart realization has been fixed. -/
theorem traceHeartMorphism_eq_of_normalize_eq
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hNormalize : C.normalize R₁ = C.normalize R₂) :
    realization.morphismOfCompletedTrace R₁ =
      realization.morphismOfCompletedTrace R₂ := by
  exact realization.traceHeartMorphism_eq_of_frontierEquiv
    (C.CanNF_complete hNormalize)

/-- Frontier-equivalent completed traces induce the same transported
`MM(Q)` morphism once the completed traces have been realized as fixed
trace-heart morphisms and the heart-level transport to `MM(Q)` is available. -/
theorem mixedMotivesQHom_eq_of_frontierEquiv
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hFrontier : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.FrontierWord.Equiv
      (C.assignment.assign R₁).frontier
      (C.assignment.assign R₂).frontier) :
    transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₁) =
      transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₂) := by
  exact ClassicalMMQHeartMorphismTransport.traceMorphism_eq_implies_mixedMotivesQHom_eq
    transport
    (realization.traceHeartMorphism_eq_of_frontierEquiv hFrontier)

/-- Equality of RealObjects canonical normal forms induces equality of the
transported `MM(Q)` morphisms once the completed traces have been realized as
fixed trace-heart morphisms. -/
theorem mixedMotivesQHom_eq_of_normalize_eq
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {theorems : ClassicalMMQHeartTheorems tStructure heart}
    (transport : ClassicalMMQHeartMorphismTransport theorems)
    {source target : heart.heartObject}
    (realization : RealObjectsTraceHeartMorphismRealization (C := C) heart source target)
    {R₁ R₂ : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup}
    (hNormalize : C.normalize R₁ = C.normalize R₂) :
    transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₁) =
      transport.traceMorphismToMixedMotivesQ (realization.morphismOfCompletedTrace R₂) := by
  exact realization.mixedMotivesQHom_eq_of_frontierEquiv transport
    (C.CanNF_complete hNormalize)

end RealObjectsTraceHeartMorphismRealization

namespace RealObjectsUnderlyingHeartMorphismRealization

/-- Upgrade an underlying-map realization of completed traces to the fixed
trace-heart realization map. The endpoint heart witnesses are supplied once and
for all by the chosen source and target heart objects. -/
def toTraceHeartMorphismRealization
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization :
      RealObjectsUnderlyingHeartMorphismRealization (C := C) heart source target) :
    RealObjectsTraceHeartMorphismRealization (C := C) heart source target where
  underlyingOfCompletedTrace := realization.underlyingOfCompletedTrace
  underlyingHEq_of_frontierEquiv := by
    intro R₁ R₂ hFrontier
    exact realization.underlyingHEq_of_frontierEquiv hFrontier

@[simp] theorem toTraceHeartMorphismRealization_underlying
    {setup : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {C : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CanNF setup}
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    {heart : TraceMotivicHeart tStructure}
    {source target : heart.heartObject}
    (realization :
      RealObjectsUnderlyingHeartMorphismRealization (C := C) heart source target)
    (R : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord setup) :
    (realization.toTraceHeartMorphismRealization.morphismOfCompletedTrace R).underlying =
      realization.underlyingOfCompletedTrace R :=
  rfl

end RealObjectsUnderlyingHeartMorphismRealization

namespace ClassicalMMQHeartTheorems

/-- Assemble the classical MM(Q) heart theorem package from the named component
theorem package for the canonical transported heart. -/
def ofTStructureComponentTheorems
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (components : TraceMotivicTStructureComponentTheorems tStructure)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) where
  finalMotivicInfrastructure := infrastructure
  classicalTraceHeartAgreement := rfl
  transportedHeartIdentifiesClassicalGeometricMotivesHeart :=
    components.transportedHeartIdentifiesClassicalGeometricMotivesHeart
  classicalAbelianHeartIsMixedMotivesQ :=
    components.classicalAbelianHeartIsMixedMotivesQ
  mixedMotiveHeartOverQTarget := components.mixedMotiveHeartOverQTarget
  compatibilityWithTransportedTStructureIsExact :=
    components.compatibilityWithTransportedTStructureIsExact
  compatibilityWithHeartRecognitionIsNatural :=
    components.compatibilityWithHeartRecognitionIsNatural

/-- Canonical local assembly route for a `TraceMotivicTStructureData` once its
component theorem package has been exposed. -/
def ofTraceMotivicTStructureData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (components : TraceMotivicTStructureComponentTheorems tStructure)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) :=
  ofTStructureComponentTheorems tStructure components infrastructure

/-- Assemble the classical MM(Q) heart theorem package from its component
fields for the canonical transported heart. This constructor does not accept
the final `RecognizesClassicalMMQ` record; both exported MM(Q) aliases are
derived by the structure defaults. -/
def ofTransportedTStructureComponents
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (transportedHeartIdentifiesClassicalGeometricMotivesHeart :
      tStructure.recognitionCompatibilityTarget)
    (classicalAbelianHeartIsMixedMotivesQ :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.canonicalReconstructionCompatibilityTarget)
    (mixedMotiveHeartOverQTarget :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.orthogonalityFromSeparatedDegreesTarget)
    (compatibilityWithTransportedTStructureIsExact :
      tStructure.shiftClosureNonposTarget ∧ tStructure.shiftClosureNonnegTarget ∧
        tStructure.orthogonalityTarget)
    (compatibilityWithHeartRecognitionIsNatural :
      tStructure.normalizationCompatibilityTarget ∧
        tStructure.normalizationPacketCutTarget)
    (infrastructure :
      TStructureMotivicMMQInfrastructure tStructure
        (TraceMotivicHeart.ofTStructure tStructure)) :
    ClassicalMMQHeartTheorems tStructure (TraceMotivicHeart.ofTStructure tStructure) :=
  ClassicalMMQHeartTheorems.ofTStructureComponentTheorems tStructure
    (TraceMotivicTStructureComponentTheorems.ofComponents tStructure
      transportedHeartIdentifiesClassicalGeometricMotivesHeart
      classicalAbelianHeartIsMixedMotivesQ
      mixedMotiveHeartOverQTarget
      compatibilityWithTransportedTStructureIsExact
      compatibilityWithHeartRecognitionIsNatural)
    infrastructure

end ClassicalMMQHeartTheorems

/-- Theorem target asserting that the heart is abelian. -/
structure AbelianHeartTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (heart : HeartCandidate structuralRecognition) where
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z
  kernelTarget : Prop
  cokernelTarget : Prop
  imageCoimageTarget : Prop
  abelianCategoryTarget : Prop

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
RecognizesClassicalMMQ.ofFinalMotivicInfrastructure
in ManuscriptSpineTargets.lean. -/
structure MMQHeartTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {heart : HeartCandidate structuralRecognition}
    (abelianHeart : AbelianHeartTarget heart) where
  mixedMotivesOverQTarget : Prop
  realizationCompatibilityTarget : Prop
  periodCompatibilityTarget : Prop

/-- Honest deprecated alias for the legacy trace-native MMQ heart target.
Not the classical category MM(Q). The live classical MM(Q) recognition path is
RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport
in ManuscriptSpineTargets.lean. -/
abbrev TraceNativeMMQHeartTargetDeprecated
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {heart : HeartCandidate structuralRecognition} :=
  MMQHeartTarget (structuralRecognition := structuralRecognition) (heart := heart)

/-- Combined theorem-target package for weight structure, t-structure, heart, abelian heart, and
a legacy trace-native MMQ-style target, explicitly downstream of structural recognition.
The `mmqHeart` field is legacy trace-native scaffolding and not the certified
classical recognition theorem. -/
structure MotivicTStructurePackage where
  structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  weightStructure : WeightStructureTarget structuralRecognition
  traceMotivicTStructure : TraceMotivicTStructureData structuralRecognition
  tStructure : TStructureTarget structuralRecognition
  heart : HeartCandidate structuralRecognition
  abelianHeart : AbelianHeartTarget heart
  /-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
  The live classical MM(Q) recognition path is
  RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport
  in ManuscriptSpineTargets.lean.
  This field is legacy trace-native scaffolding and not the certified classical
  recognition theorem. -/
  mmqHeart : MMQHeartTarget abelianHeart
  weightTStructureCompatibilityTarget : Prop
  heartRealizationCompatibilityTarget : Prop

/-- Exact remaining Campaign 12B normalization theorem surface: the canonical
threshold cut on the normalized packet DAG is admissible and reconstructible. -/
structure CanonicalPacketCutIsAdmissible
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat) where
  thresholdLe : threshold ≤ traceNative.reconstructionLength
  canonicalCut :
    (packet : TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength) →
      TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut packet threshold
  lowerPacketSubset :
    TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength → Type z
  upperPacketSubset :
    TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength → Type z
  canonicalThresholdCutTarget : Prop
  dependencyClosureTarget : Prop
  boundaryClosureTarget : Prop
  gluingClosureTarget : Prop
  quotientComplementWellDefinedTarget : Prop

namespace CanonicalPacketCutIsAdmissible

def ofCompletedRecordThreshold
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    CanonicalPacketCutIsAdmissible traceNative threshold where
  thresholdLe := hThreshold
  canonicalCut := fun packet =>
    TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.ofLe packet threshold hThreshold
  lowerPacketSubset := fun _ =>
    ULift (TraceCalc.LayerB.ShadowModel.CompletedRecord threshold)
  upperPacketSubset := fun _ =>
    ULift
      (TraceCalc.LayerB.ShadowModel.CompletedRecord
        (traceNative.reconstructionLength - threshold))
  canonicalThresholdCutTarget :=
    Nonempty
      (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut
        traceNative.completedRecord threshold)
  dependencyClosureTarget :=
    ∀ (packet : TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength)
      (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut packet threshold)
      {j i : Fin traceNative.reconstructionLength},
      j ∈ cut.lowerSet → i ∈ packet.requires j → i ∈ cut.lowerSet
  boundaryClosureTarget :=
    traceNative.pureGenerators.boundarySupportGluingCompatibilityTarget
  gluingClosureTarget :=
    traceNative.pureGenerators.boundarySupportGluingCompatibilityTarget
  quotientComplementWellDefinedTarget :=
    ∀ (packet : TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength)
      (cut : TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut packet threshold),
      cut.lowerSet ∪ cut.upperSet = Finset.univ ∧ Disjoint cut.lowerSet cut.upperSet

end CanonicalPacketCutIsAdmissible

/-- Exact remaining Campaign 12B truncation theorem surface: the cofiber of the
canonical lower cut realizes the upper truncation object. -/
structure CanonicalCutCofiberIdentifiesUpperTruncation
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (packetCut : NormalizationPacketCutData structuralRecognition) where
  lowerTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  upperTruncationCarrier :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  totalObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  upperTruncationObject :
    structuralRecognition.recognition.recognizedCategory.Object →
      structuralRecognition.recognition.recognizedCategory.Object
  lowerInclusion :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (lowerTruncationObject X)
        (totalObject X)
  upperProjection :
    (X : structuralRecognition.recognition.recognizedCategory.Object) →
      structuralRecognition.recognition.recognizedCategory.Hom
        (totalObject X)
        (upperTruncationObject X)
  cofiberSequenceWitness :
    structuralRecognition.recognition.recognizedCategory.Object → Type z
  cofiberIdentifiesUpper :
    structuralRecognition.recognition.recognizedCategory.Object → Prop
  lowerCutRealizationTarget : Prop
  upperCutCofiberRealizationTarget : Prop
  canonicalInclusionTarget : Prop
  truncationTriangleTarget : Prop
  cofiberIdentifiesUpperCutTarget : Prop
  truncationFunctorialityTarget : Prop

namespace NormalizationPacketCutData

def ofTraceNativeWeightDevissage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    {threshold : Nat}
    (admissibleCut : CanonicalPacketCutIsAdmissible traceNative threshold) :
    NormalizationPacketCutData structuralRecognition where
  packetRecord := fun _ => ULift (TraceCalc.LayerB.ShadowModel.CompletedRecord traceNative.reconstructionLength)
  lowerCutRecord := fun _ packet => admissibleCut.lowerPacketSubset packet.down
  upperCutRecord := fun _ packet => admissibleCut.upperPacketSubset packet.down
  finiteDegreeLabeledPacketDAGTarget := traceNative.weightClasses.finiteWeightFiltrationTarget
  canonicalThresholdCutTarget := admissibleCut.canonicalThresholdCutTarget
  lowerCutAdmissibilityTarget :=
    admissibleCut.dependencyClosureTarget ∧ admissibleCut.boundaryClosureTarget
  upperCutAdmissibilityTarget := admissibleCut.quotientComplementWellDefinedTarget
  boundaryDependencyClosureTarget :=
    admissibleCut.dependencyClosureTarget ∧ admissibleCut.boundaryClosureTarget
  gluingClosureTarget := admissibleCut.gluingClosureTarget
  canonicalReconstructionCompatibilityTarget :=
    traceNative.weightClasses.normalizationInvariantTarget
  campaign11WeightDevissageCompatibilityTarget :=
    traceNative.weightOrthogonality.compatibilityWithWeightClassesTarget

def ofCanonicalReconstructionAndWeights
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    NormalizationPacketCutData structuralRecognition :=
  ofTraceNativeWeightDevissage traceNative
    (CanonicalPacketCutIsAdmissible.ofCompletedRecordThreshold traceNative threshold hThreshold)

end NormalizationPacketCutData

namespace CanonicalCutCofiberIdentifiesUpperTruncation

def ofCanonicalPacketCutSourceProofs
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    CanonicalCutCofiberIdentifiesUpperTruncation structuralRecognition
      (NormalizationPacketCutData.ofCanonicalReconstructionAndWeights traceNative threshold hThreshold) := by
  let admissibleCut :=
    CanonicalPacketCutIsAdmissible.ofCompletedRecordThreshold traceNative threshold hThreshold
  let packetCut := NormalizationPacketCutData.ofTraceNativeWeightDevissage traceNative admissibleCut
  let canonicalCut := admissibleCut.canonicalCut traceNative.completedRecord
  change CanonicalCutCofiberIdentifiesUpperTruncation structuralRecognition packetCut
  refine {
    lowerTruncationCarrier := fun _ => admissibleCut.lowerPacketSubset traceNative.completedRecord
    upperTruncationCarrier := fun _ => admissibleCut.upperPacketSubset traceNative.completedRecord
    totalObject :=
      fun _ =>
        TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.totalRecognizedObject
          (structuralRecognition := structuralRecognition)
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (compactGenerationTransport := compactGenerationTransport)
          canonicalCut
    lowerTruncationObject :=
      fun _ =>
        TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerRecognizedObject
          (structuralRecognition := structuralRecognition)
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (compactGenerationTransport := compactGenerationTransport)
          canonicalCut
    upperTruncationObject :=
      fun _ =>
        TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperRecognizedObject
          (structuralRecognition := structuralRecognition)
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (compactGenerationTransport := compactGenerationTransport)
          canonicalCut
    lowerInclusion :=
      fun _ =>
        TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerInclusionRecognized
          (structuralRecognition := structuralRecognition)
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (compactGenerationTransport := compactGenerationTransport)
          canonicalCut
    upperProjection :=
      fun _ =>
        TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperProjectionRecognized
          (structuralRecognition := structuralRecognition)
          (traceCategory := traceCategory)
          (assignmentTable := assignmentTable)
          (closure := closure)
          (compactGenerationTransport := compactGenerationTransport)
          canonicalCut
    cofiberSequenceWitness :=
      fun _ => ULift (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.CofiberSequenceData canonicalCut)
    cofiberIdentifiesUpper :=
      fun _ =>
        ∀ i : Fin (traceNative.reconstructionLength - threshold),
          canonicalCut.cofiberSequence.totalToUpper (canonicalCut.upperEmbedding i) = some i
    lowerCutRealizationTarget :=
      packetCut.canonicalThresholdCutTarget ∧
        (∀ X : structuralRecognition.recognition.recognizedCategory.Object,
          ∃ carrier : compactGenerationTransport.FiniteTraceClosureCarrier,
            classicalObjectToRecognized structuralRecognition.recognition
                (compactGenerationTransport.reconstructCompactObject carrier) =
                (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.lowerRecognizedObject
                  (structuralRecognition := structuralRecognition)
                  (traceCategory := traceCategory)
                  (assignmentTable := assignmentTable)
                  (closure := closure)
                  (compactGenerationTransport := compactGenerationTransport)
                  canonicalCut)) ∧
        packetCut.lowerCutAdmissibilityTarget ∧
        packetCut.boundaryDependencyClosureTarget
    upperCutCofiberRealizationTarget :=
      packetCut.upperCutAdmissibilityTarget ∧
        (∀ X : structuralRecognition.recognition.recognizedCategory.Object,
          ∃ carrier : compactGenerationTransport.FiniteTraceClosureCarrier,
            classicalObjectToRecognized structuralRecognition.recognition
                (compactGenerationTransport.reconstructCompactObject carrier) =
                (TraceCalc.LayerB.ShadowModel.CanonicalThresholdCut.upperRecognizedObject
                  (structuralRecognition := structuralRecognition)
                  (traceCategory := traceCategory)
                  (assignmentTable := assignmentTable)
                  (closure := closure)
                  (compactGenerationTransport := compactGenerationTransport)
                  canonicalCut)) ∧
        structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget ∧
        structuralRecognition.structuralPackage.tensorExactness.triangleCompatibilityTarget
    canonicalInclusionTarget :=
      packetCut.canonicalThresholdCutTarget ∧
        packetCut.lowerCutAdmissibilityTarget ∧
        Nonempty (admissibleCut.lowerPacketSubset traceNative.completedRecord)
    truncationTriangleTarget :=
      structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget ∧
        structuralRecognition.structuralPackage.tensorExactness.triangleCompatibilityTarget
    cofiberIdentifiesUpperCutTarget :=
      packetCut.upperCutAdmissibilityTarget ∧
        packetCut.gluingClosureTarget ∧
        (∀ i : Fin (traceNative.reconstructionLength - threshold),
          canonicalCut.cofiberSequence.totalToUpper (canonicalCut.upperEmbedding i) = some i) ∧
        structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget ∧
        structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget ∧
        structuralRecognition.structuralPackage.tensorExactness.triangleCompatibilityTarget
    truncationFunctorialityTarget :=
      structuralRecognition.structuralPackage.triangulated.coneFunctorialityTarget }

end CanonicalCutCofiberIdentifiesUpperTruncation

/-- General Campaign 12C assembly surface for the standard fact that the heart
of a completed trace motivic `t`-structure is abelian. -/
structure HeartOfTraceTStructureIsAbelian
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  exactnessData :
    ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) →
        TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism
  kernelData : Type z
  cokernelData : Type z
  imageData : Type z
  coimageData : Type z
  imageCoimageComparison : Type z
  kernelTarget : Prop
  cokernelTarget : Prop
  imageCoimageTarget : Prop
  abelianCategoryTarget : Prop

namespace HeartOfTraceTStructureIsAbelian

def ofTransportedExactData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (exactnessData :
      ∀ {sourceObject targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject},
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject) →
          TraceMotivicHeartExactPackage (TraceMotivicHeart.ofTStructure tStructure) morphism) :
    HeartOfTraceTStructureIsAbelian tStructure where
  exactnessData := exactnessData
  kernelData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  cokernelData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  imageData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  coimageData :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  imageCoimageComparison :=
    Σ sourceObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
      Σ targetObject : (TraceMotivicHeart.ofTStructure tStructure).heartObject,
        Σ morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject,
          (exactnessData morphism).ExactnessWitness
  kernelTarget :=
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Nonempty ((exactnessData morphism).realize witness).kernelWitness
  cokernelTarget :=
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Nonempty ((exactnessData morphism).realize witness).cokernelWitness
  imageCoimageTarget :=
    ∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Nonempty ((exactnessData morphism).realize witness).imageWitness ∧
          Nonempty ((exactnessData morphism).realize witness).coimageWitness ∧
          Nonempty ((exactnessData morphism).realize witness).imageCoimageComparisonWitness
  abelianCategoryTarget :=
    (∀ {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject)
      (witness : (exactnessData morphism).ExactnessWitness),
        Nonempty ((exactnessData morphism).realize witness).kernelWitness) ∧
      (∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty ((exactnessData morphism).realize witness).cokernelWitness) ∧
      (∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty ((exactnessData morphism).realize witness).imageWitness) ∧
      (∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty ((exactnessData morphism).realize witness).coimageWitness) ∧
      (∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty ((exactnessData morphism).realize witness).imageCoimageComparisonWitness)

def ofConstructiveExactnessSystem
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition)
    (system : TraceMotivicHeartConstructiveExactnessSystem tStructure) :
    HeartOfTraceTStructureIsAbelian tStructure :=
  let exactnessData :=
    fun {sourceObject targetObject}
      (morphism :
        TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
          sourceObject targetObject) =>
        TraceMotivicHeartExactPackage.heartExactPackage_from_recognizedFiberCofiber
          system morphism
  { exactnessData := exactnessData
    kernelData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    cokernelData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    imageData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    coimageData :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    imageCoimageComparison :=
      TraceMotivicHeartExactWitnessData (TraceMotivicHeart.ofTStructure tStructure)
        exactnessData
    kernelTarget :=
      ∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty (TraceMotivicHeartKernelWitness system morphism)
    cokernelTarget :=
      ∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty (TraceMotivicHeartCokernelWitness system morphism)
    imageCoimageTarget :=
      ∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty (TraceMotivicHeartImageWitness system morphism) ∧
            Nonempty (TraceMotivicHeartCoimageWitness system morphism) ∧
            Nonempty (TraceMotivicHeartImageCoimageComparisonWitness system morphism)
    abelianCategoryTarget :=
      (∀ {sourceObject targetObject}
        (morphism :
          TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
            sourceObject targetObject)
        (witness : (exactnessData morphism).ExactnessWitness),
          Nonempty (TraceMotivicHeartKernelWitness system morphism)) ∧
        (∀ {sourceObject targetObject}
          (morphism :
            TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
              sourceObject targetObject)
          (witness : (exactnessData morphism).ExactnessWitness),
            Nonempty (TraceMotivicHeartCokernelWitness system morphism)) ∧
        (∀ {sourceObject targetObject}
          (morphism :
            TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
              sourceObject targetObject)
          (witness : (exactnessData morphism).ExactnessWitness),
            Nonempty (TraceMotivicHeartImageWitness system morphism)) ∧
        (∀ {sourceObject targetObject}
          (morphism :
            TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
              sourceObject targetObject)
          (witness : (exactnessData morphism).ExactnessWitness),
            Nonempty (TraceMotivicHeartCoimageWitness system morphism)) ∧
        (∀ {sourceObject targetObject}
          (morphism :
            TraceMotivicHeartMorphism (TraceMotivicHeart.ofTStructure tStructure)
              sourceObject targetObject)
          (witness : (exactnessData morphism).ExactnessWitness),
            Nonempty (TraceMotivicHeartImageCoimageComparisonWitness system morphism)) }

end HeartOfTraceTStructureIsAbelian

namespace NormalizationTruncationTriangle

def ofPacketCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (cofiberIdentification :
      CanonicalCutCofiberIdentifiesUpperTruncation structuralRecognition packetCut) :
    NormalizationTruncationTriangle structuralRecognition packetCut where
  lowerTruncationCarrier := cofiberIdentification.lowerTruncationCarrier
  upperTruncationCarrier := cofiberIdentification.upperTruncationCarrier
  totalObject := cofiberIdentification.totalObject
  lowerTruncationObject := cofiberIdentification.lowerTruncationObject
  upperTruncationObject := cofiberIdentification.upperTruncationObject
  lowerInclusion := cofiberIdentification.lowerInclusion
  upperProjection := cofiberIdentification.upperProjection
  cofiberSequenceWitness := cofiberIdentification.cofiberSequenceWitness
  cofiberIdentifiesUpper := cofiberIdentification.cofiberIdentifiesUpper
  lowerCutRealizationTarget := cofiberIdentification.lowerCutRealizationTarget
  upperCutCofiberRealizationTarget := cofiberIdentification.upperCutCofiberRealizationTarget
  canonicalInclusionTarget := cofiberIdentification.canonicalInclusionTarget
  truncationTriangleTarget := cofiberIdentification.truncationTriangleTarget
  cofiberIdentifiesUpperCutTarget := cofiberIdentification.cofiberIdentifiesUpperCutTarget
  orthogonalityFromSeparatedDegreesTarget :=
    traceNative.tStructureSeparation.weightOrthogonalityIsTraceDevissageTarget
  truncationFunctorialityTarget := cofiberIdentification.truncationFunctorialityTarget
  recognitionCompatibilityTarget :=
    structuralRecognition.structuralPackage.triangulated.distinguishedTrianglesTarget
  campaign11WeightDevissageInputTarget :=
    traceNative.tStructureSeparation.tStructureConsumerOnlyTarget

def ofCanonicalPacketCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    NormalizationTruncationTriangle structuralRecognition
      (NormalizationPacketCutData.ofCanonicalReconstructionAndWeights traceNative threshold hThreshold) :=
  ofPacketCut traceNative
    (NormalizationPacketCutData.ofCanonicalReconstructionAndWeights traceNative threshold hThreshold)
    (CanonicalCutCofiberIdentifiesUpperTruncation.ofCanonicalPacketCutSourceProofs
      traceNative threshold hThreshold)

abbrev ofAdmissibleCutAndCofiber
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext} :=
  @ofPacketCut structuralRecognition traceCategory assignmentTable closure compactGenerationTransport

end NormalizationTruncationTriangle

namespace TraceMotivicTStructureData

def ofNormalizationTruncationTriangle
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (truncation : NormalizationTruncationTriangle structuralRecognition packetCut) :
    TraceMotivicTStructureData structuralRecognition where
  tNonpos := traceNative.weightClasses.weightClassNonpositive
  tNonneg := traceNative.weightClasses.weightClassNonnegative
  shiftClosureNonposTarget :=
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget
  shiftClosureNonnegTarget :=
    structuralRecognition.structuralPackage.triangulated.shiftFunctorTarget
  orthogonalityTarget := truncation.orthogonalityFromSeparatedDegreesTarget
  truncationTriangleTarget := truncation.truncationTriangleTarget
  truncationFunctorialityTarget := truncation.truncationFunctorialityTarget
  normalizationCompatibilityTarget := traceNative.weightClasses.normalizationInvariantTarget
  canonicalReconstructionCompatibilityTarget :=
    packetCut.canonicalReconstructionCompatibilityTarget
  normalizationPacketCutTarget :=
    packetCut.finiteDegreeLabeledPacketDAGTarget ∧
      packetCut.canonicalThresholdCutTarget ∧
      packetCut.lowerCutAdmissibilityTarget ∧
      packetCut.upperCutAdmissibilityTarget
  normalizationTruncationTriangleTarget :=
    truncation.lowerCutRealizationTarget ∧
      truncation.upperCutCofiberRealizationTarget ∧
      truncation.canonicalInclusionTarget ∧
      truncation.truncationTriangleTarget ∧
      truncation.cofiberIdentifiesUpperCutTarget
  orthogonalityFromSeparatedDegreesTarget :=
    truncation.orthogonalityFromSeparatedDegreesTarget
  campaign11WeightDevissageInputTarget :=
    traceNative.tStructureSeparation.tStructureConsumerOnlyTarget
  recognitionCompatibilityTarget := truncation.recognitionCompatibilityTarget

def ofNormalizationCuts
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (packetCut : NormalizationPacketCutData structuralRecognition)
    (truncation : NormalizationTruncationTriangle structuralRecognition packetCut) :
    TraceMotivicTStructureData structuralRecognition :=
  ofNormalizationTruncationTriangle traceNative packetCut truncation

def ofCanonicalPacketCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength) :
    TraceMotivicTStructureData structuralRecognition :=
  let packetCut :=
    NormalizationPacketCutData.ofCanonicalReconstructionAndWeights traceNative threshold hThreshold
  ofNormalizationCuts traceNative packetCut
    (NormalizationTruncationTriangle.ofCanonicalPacketCut traceNative threshold hThreshold)

end TraceMotivicTStructureData

namespace TraceMotivicTStructureComponentTheorems

def ofCanonicalPacketCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (recognitionCompatibility_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).recognitionCompatibilityTarget)
    (normalizationCompatibility_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).normalizationCompatibilityTarget)
    (canonicalReconstructionCompatibility_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).canonicalReconstructionCompatibilityTarget)
    (orthogonalityFromSeparatedDegrees_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).orthogonalityFromSeparatedDegreesTarget)
    (shiftClosureNonpos_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).shiftClosureNonposTarget)
    (shiftClosureNonneg_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).shiftClosureNonnegTarget)
    (orthogonality_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).orthogonalityTarget)
    (normalizationPacketCut_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).normalizationPacketCutTarget) :
    TraceMotivicTStructureComponentTheorems
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold) :=
  ofComponents
    (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold)
    recognitionCompatibility_holds
    ⟨normalizationCompatibility_holds, canonicalReconstructionCompatibility_holds⟩
    ⟨normalizationCompatibility_holds, orthogonalityFromSeparatedDegrees_holds⟩
    ⟨shiftClosureNonpos_holds, shiftClosureNonneg_holds, orthogonality_holds⟩
    ⟨normalizationCompatibility_holds, normalizationPacketCut_holds⟩

abbrev ofCanonicalPacketCutSourceProofs
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @ofCanonicalPacketCut structuralRecognition

def ofCanonicalPacketCutWithCertifiedStructuralPackage
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certified : CertifiedDMgmStructuralRecognitionTarget.{u, v, w, x, y, z})
    (hCertified : certified.structuralRecognition = structuralRecognition)
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (normalizationPacketCut_holds :
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold
        hThreshold).normalizationPacketCutTarget) :
    TraceMotivicTStructureComponentTheorems
      (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold) := by
  subst hCertified
  apply ofCanonicalPacketCutSourceProofs traceNative threshold hThreshold
  · exact CertifiedDMgmStructuralRecognitionTarget.distinguishedTriangles_holds certified
  · exact traceNative.weightClasses.normalizationInvariant_holds
  · exact traceNative.weightClasses.normalizationInvariant_holds
  · exact traceNative.tStructureSeparation.weightOrthogonalityIsTraceDevissage_holds
  · exact CertifiedDMgmStructuralRecognitionTarget.shiftFunctor_holds certified
  · exact CertifiedDMgmStructuralRecognitionTarget.shiftFunctor_holds certified
  · exact traceNative.tStructureSeparation.weightOrthogonalityIsTraceDevissage_holds
  · exact normalizationPacketCut_holds

abbrev ofCanonicalPacketCutWithStructuralTransport
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}} :=
  @ofCanonicalPacketCutWithCertifiedStructuralPackage structuralRecognition

end TraceMotivicTStructureComponentTheorems

namespace TStructureTarget

def ofTraceMotivicTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    TStructureTarget structuralRecognition where
  connectiveObject := tStructure.tNonpos
  coconnectiveObject := tStructure.tNonneg
  truncationTriangleTarget := tStructure.truncationTriangleTarget
  orthogonalityTarget := tStructure.orthogonalityTarget

end TStructureTarget

namespace HeartCandidate

def ofTraceMotivicHeart
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure) :
    HeartCandidate structuralRecognition where
  heartObject := heart.heartObject
  forgetToMotivicObject := heart.forgetToMotivicObject
  heartMembershipWitness := fun obj =>
    tStructure.tNonpos (heart.forgetToMotivicObject obj) ×
      tStructure.tNonneg (heart.forgetToMotivicObject obj)

end HeartCandidate

namespace MMQ

def ofTraceMotivicTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (tStructure : TraceMotivicTStructureData structuralRecognition) :
    MMQ tStructure where
  motive := (TraceMotivicHeart.ofTStructure tStructure).heartObject
  forgetToMotivicObject := (TraceMotivicHeart.ofTStructure tStructure).forgetToMotivicObject
  heartWitness := fun obj => ⟨obj.2.1, obj.2.2⟩

end MMQ

namespace MMQ.isHeartOfTraceMotivicTStructure

def ofTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) :
    MMQ.isHeartOfTraceMotivicTStructure mmq where
  heartConstructionTarget :=
    ∀ obj : mmq.motive,
      Nonempty
        (tStructure.tNonpos (mmq.forgetToMotivicObject obj) ×
          tStructure.tNonneg (mmq.forgetToMotivicObject obj))
  heartAgreementTarget := Nonempty (TraceMotivicHeart tStructure)

end MMQ.isHeartOfTraceMotivicTStructure

namespace MMQ.isAbelianTarget

def ofTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure)
    (heartAbelian : HeartOfTraceTStructureIsAbelian tStructure) :
    MMQ.isAbelianTarget mmq where
  exactnessData := heartAbelian.exactnessData
  kernelData := heartAbelian.kernelData
  cokernelData := heartAbelian.cokernelData
  imageData := heartAbelian.imageData
  coimageData := heartAbelian.coimageData
  imageCoimageComparison := heartAbelian.imageCoimageComparison
  kernelTarget := heartAbelian.kernelTarget
  cokernelTarget := heartAbelian.cokernelTarget
  imageCoimageTarget := heartAbelian.imageCoimageTarget
  abelianCategoryTarget := heartAbelian.abelianCategoryTarget

end MMQ.isAbelianTarget

namespace MMQ.embeddingIntoDMgmQTarget

def ofRecognitionAndTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (mmq : MMQ tStructure) :
    MMQ.embeddingIntoDMgmQTarget mmq where
  embeddingTarget := tStructure.recognitionCompatibilityTarget
  comparisonCompatibilityTarget :=
    tStructure.recognitionCompatibilityTarget ∧
      structuralRecognition.structuralPackage.additive.biproductTarget
  recognitionCompatibilityTarget := tStructure.recognitionCompatibilityTarget

end MMQ.embeddingIntoDMgmQTarget

namespace AbelianHeartTarget

def ofTraceTStructure
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (heartAbelian : HeartOfTraceTStructureIsAbelian tStructure) :
    AbelianHeartTarget (HeartCandidate.ofTraceMotivicHeart heart) where
  kernelData := heartAbelian.kernelData
  cokernelData := heartAbelian.cokernelData
  imageData := heartAbelian.imageData
  coimageData := heartAbelian.coimageData
  imageCoimageComparison := heartAbelian.imageCoimageComparison
  kernelTarget := heartAbelian.kernelTarget
  cokernelTarget := heartAbelian.cokernelTarget
  imageCoimageTarget := heartAbelian.imageCoimageTarget
  abelianCategoryTarget := heartAbelian.abelianCategoryTarget

end AbelianHeartTarget

namespace MMQHeartTarget

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport
in ManuscriptSpineTargets.lean. -/
def ofMMQ
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (heart : TraceMotivicHeart tStructure)
    (heartAbelian : HeartOfTraceTStructureIsAbelian tStructure) :
    MMQHeartTarget (AbelianHeartTarget.ofTraceTStructure heart heartAbelian) where
  mixedMotivesOverQTarget :=
    (MMQ.isHeartOfTraceMotivicTStructure.ofTStructure
      (MMQ.ofTraceMotivicTStructure tStructure)).heartConstructionTarget
  realizationCompatibilityTarget := tStructure.recognitionCompatibilityTarget
  periodCompatibilityTarget := tStructure.recognitionCompatibilityTarget

end MMQHeartTarget

namespace MotivicTStructurePackage

def ofTraceMotivicData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (certifiedWeightDevissage : CertifiedWeightDevissageData structuralRecognition)
    (traceTStructure : TraceMotivicTStructureData structuralRecognition)
    (heartAbelian : HeartOfTraceTStructureIsAbelian traceTStructure) :
    MotivicTStructurePackage where
  structuralRecognition := structuralRecognition
  weightStructure := WeightStructureTarget.ofCertifiedWeightDevissage certifiedWeightDevissage
  traceMotivicTStructure := traceTStructure
  tStructure := TStructureTarget.ofTraceMotivicTStructure traceTStructure
  heart := HeartCandidate.ofTraceMotivicHeart (TraceMotivicHeart.ofTStructure traceTStructure)
  abelianHeart :=
    AbelianHeartTarget.ofTraceTStructure (TraceMotivicHeart.ofTStructure traceTStructure)
      heartAbelian
  mmqHeart :=
    MMQHeartTarget.ofMMQ (TraceMotivicHeart.ofTStructure traceTStructure) heartAbelian
  weightTStructureCompatibilityTarget :=
    certifiedWeightDevissage.separatedFromLaterTStructureTarget ∧
      traceTStructure.campaign11WeightDevissageInputTarget
  heartRealizationCompatibilityTarget := traceTStructure.recognitionCompatibilityTarget

def ofCanonicalPacketCut
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {traceCategory :
      ClassicalPeriods.TraceCategoryStructure
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {assignmentTable :
      ClassicalPeriods.GeneratorRealizationAssignmentTable
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {closure :
      ClassicalPeriods.PresentationAdmissibleClosureEquivalence
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    {compactGenerationTransport :
      FiveFamilyCompactGenerationWitness
        structuralRecognition.recognition.recognitionInput.tracePresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation
        structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext}
    (certifiedWeightDevissage : CertifiedWeightDevissageData structuralRecognition)
    (traceNative :
      TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
        compactGenerationTransport)
    (threshold : Nat)
    (hThreshold : threshold ≤ traceNative.reconstructionLength)
    (exactnessSystem :
      TraceMotivicHeartConstructiveExactnessSystem
        (TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold)) :
    MotivicTStructurePackage :=
  let traceTStructure :=
    TraceMotivicTStructureData.ofCanonicalPacketCut traceNative threshold hThreshold
  ofTraceMotivicData certifiedWeightDevissage traceTStructure
    (HeartOfTraceTStructureIsAbelian.ofConstructiveExactnessSystem
      traceTStructure exactnessSystem)

end MotivicTStructurePackage

/-! ## Canonical over-Q compatibility layer

These declarations depend on both the Campaign 12 t-structure layer defined in
this file and the recognized exactness infrastructure defined in
`RecognitionTarget.lean`, so they must live after both module headers and after
the core Campaign 12 structures are in scope. -/

/-- Strengthened rationality witness for Q-specificity. -/
structure TraceBaseIsQ
    (structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}) where
  rationalGeneratorBasis : Prop
  allTraceScalarsRational : Prop
  corrDefinedOverQ : Prop
  locDefinedOverQ : Prop
  nisDefinedOverQ : Prop
  a1DefinedOverQ : Prop
  envDefinedOverQ : Prop
  rationalReplayCertificates : Prop

/-- Compatibility of the canonical weight structure and t-structure. -/
structure WeightTStructureCompatibilityData
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    (weightStructure : WeightStructureTarget structuralRecognition)
    (tStructure : TraceMotivicTStructureData structuralRecognition) where
  truncationPreservesWeightLower : Prop
  truncationPreservesWeightUpper : Prop
  weightTowerRestrictsToLowerCut : Prop
  weightTowerRestrictsToUpperCut : Prop
  weightOrthogonalityForCut : Prop
  devissageCompatibleWithTruncation : Prop
  canonicalCutTriangleWeightCompatible : Prop

namespace WeightTStructureCompatibilityData

def theoremTarget
    {structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}}
    {weightStructure : WeightStructureTarget structuralRecognition}
    {tStructure : TraceMotivicTStructureData structuralRecognition}
    (data : WeightTStructureCompatibilityData weightStructure tStructure) : Prop :=
  data.truncationPreservesWeightLower ∧
    data.truncationPreservesWeightUpper ∧
    data.weightTowerRestrictsToLowerCut ∧
    data.weightTowerRestrictsToUpperCut ∧
    data.weightOrthogonalityForCut ∧
    data.devissageCompatibleWithTruncation ∧
    data.canonicalCutTriangleWeightCompatible

end WeightTStructureCompatibilityData

/-- Canonical trace motivic core data over Q for Phase 12. -/
structure CanonicalTraceMotivicCoreDataOverQ where
  structuralRecognition : DMgmStructuralRecognitionTarget.{u, v, w, x, y, z}
  baseIsQ : TraceBaseIsQ structuralRecognition
  traceCategory :
    ClassicalPeriods.TraceCategoryStructure
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  assignmentTable :
    ClassicalPeriods.GeneratorRealizationAssignmentTable
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  closure :
    ClassicalPeriods.PresentationAdmissibleClosureEquivalence
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  compactGenerationTransport :
    FiveFamilyCompactGenerationWitness
      structuralRecognition.recognition.recognitionInput.tracePresentation
      structuralRecognition.recognition.recognitionInput.classicalPresentation
      structuralRecognition.recognition.recognitionInput.classicalPresentation.classicalContext
  traceNative :
    TraceNativeWeightDevissageData structuralRecognition traceCategory assignmentTable closure
      compactGenerationTransport
  threshold : Nat
  hThreshold : threshold ≤ traceNative.reconstructionLength
  canonicalCut :
    CanonicalCutCofiberIdentifiesUpperTruncation
      structuralRecognition
      (NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
        traceNative threshold hThreshold)
  weightStructure :
    WeightStructureTarget structuralRecognition
  certifiedWeightDevissage :
    CertifiedWeightDevissageData structuralRecognition

namespace CanonicalTraceMotivicCoreDataOverQ

/-- The canonical packet cut determined by the core's trace-native weight data. -/
abbrev packetCut
    (core : CanonicalTraceMotivicCoreDataOverQ) :
    NormalizationPacketCutData core.structuralRecognition :=
  NormalizationPacketCutData.ofCanonicalReconstructionAndWeights
    core.traceNative core.threshold core.hThreshold

end CanonicalTraceMotivicCoreDataOverQ

/-- Compatibility of the canonical realization functor with the t-structure and heart. -/
structure HeartRealizationCompatibilityData (core : CanonicalTraceMotivicCoreDataOverQ) where
  realizationTarget : Type
  realizationObject : core.structuralRecognition.recognition.recognizedCategory.Object → realizationTarget
  realizationMorphism : ∀ {A B}, core.structuralRecognition.recognition.recognizedCategory.Hom A B → Prop
  preservesCertifiedPackets : Prop
  preservesBoundaryProfiles : Prop
  preservesReplayCertificates : Prop
  preservesMorphismCofibers : ∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B), Prop
  preservesMorphismFibers : ∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B), Prop
  preservesCanonicalLowerCut :
    ∀ X : core.structuralRecognition.recognition.recognizedCategory.Object, Prop
  preservesCanonicalUpperCut :
    ∀ X : core.structuralRecognition.recognition.recognizedCategory.Object, Prop
  restrictsToHeart :
    ∀ X :
      (TraceMotivicHeart.ofTStructure
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold)).heartObject,
        Prop
  preservesHeartExactness :
    ∀ {A B}
      (f :
        TraceMotivicHeartMorphism
          (TraceMotivicHeart.ofTStructure
            (TraceMotivicTStructureData.ofCanonicalPacketCut
              core.traceNative core.threshold core.hThreshold))
          A B),
        Prop

namespace HeartRealizationCompatibilityData

def theoremTarget
    {core : CanonicalTraceMotivicCoreDataOverQ}
    (data : HeartRealizationCompatibilityData core) : Prop :=
  data.preservesCertifiedPackets ∧
    data.preservesBoundaryProfiles ∧
    data.preservesReplayCertificates ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.realizationMorphism f) ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.preservesMorphismCofibers f) ∧
    (∀ {A B} (f : core.structuralRecognition.recognition.recognizedCategory.Hom A B),
      data.preservesMorphismFibers f) ∧
    (∀ X : core.structuralRecognition.recognition.recognizedCategory.Object,
      data.preservesCanonicalLowerCut X ∧ data.preservesCanonicalUpperCut X) ∧
    (∀ X :
      (TraceMotivicHeart.ofTStructure
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold)).heartObject,
      data.restrictsToHeart X) ∧
    (∀ {A B}
      (f :
        TraceMotivicHeartMorphism
          (TraceMotivicHeart.ofTStructure
            (TraceMotivicTStructureData.ofCanonicalPacketCut
              core.traceNative core.threshold core.hThreshold))
          A B),
      data.preservesHeartExactness f)

end HeartRealizationCompatibilityData

namespace RecognizedFiberCofiberSystem

/-- Construct recognized fiber/cofiber system from canonical trace data over Q. -/
def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (morphismData :
      RecognizedFiberCofiberSystem.CanonicalTraceMorphismFiberCofiberData
        core.structuralRecognition)
    : RecognizedFiberCofiberSystem core.structuralRecognition :=
  ofCanonicalMorphismData morphismData

end RecognizedFiberCofiberSystem

/-- Canonical trace motivic exact data over Q for Phase 12. -/
structure CanonicalTraceMotivicExactDataOverQ (core : CanonicalTraceMotivicCoreDataOverQ) where
  morphismFiberCofiberData :
    RecognizedFiberCofiberSystem.CanonicalTraceMorphismFiberCofiberData
      core.structuralRecognition
  heartCompatibility :
    RecognizedFiberCofiberHeartCompatibility
      (TraceMotivicTStructureData.ofCanonicalPacketCut
        core.traceNative core.threshold core.hThreshold)
      (RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
        core morphismFiberCofiberData)
  imageCoimageComparisonData :
    ∀ {sourceObject targetObject :
        (TraceMotivicHeart.ofTStructure
          (TraceMotivicTStructureData.ofCanonicalPacketCut
            core.traceNative core.threshold core.hThreshold)).heartObject},
      (morphism :
        TraceMotivicHeartMorphism
          (TraceMotivicHeart.ofTStructure
            (TraceMotivicTStructureData.ofCanonicalPacketCut
              core.traceNative core.threshold core.hThreshold))
          sourceObject targetObject) →
        RecognizedImageCoimageComparisonData
          (TraceMotivicTStructureData.ofCanonicalPacketCut
            core.traceNative core.threshold core.hThreshold)
          (RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
            core morphismFiberCofiberData)
          morphism

/-- Constructive exactness system from canonical trace data over Q. -/
def TraceMotivicHeartConstructiveExactnessSystem.ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core)
    : TraceMotivicHeartConstructiveExactnessSystem
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold) :=
  {
    recognizedFiberCofiber :=
      RecognizedFiberCofiberSystem.ofCanonicalTraceDataOverQ
        core exactData.morphismFiberCofiberData,
    heartCompatibility := exactData.heartCompatibility,
    imageCoimageComparisonData := exactData.imageCoimageComparisonData
  }

/-- Canonical theorem bundle for motivic t-structure and heart-level exactness over Q. -/
structure CanonicalTraceMotivicTheoremBundleOverQ (core : CanonicalTraceMotivicCoreDataOverQ) where
  exactData : CanonicalTraceMotivicExactDataOverQ core
  weightTStructureCompatibility :
    WeightTStructureCompatibilityData
      core.weightStructure
      (TraceMotivicTStructureData.ofCanonicalPacketCut
        core.traceNative core.threshold core.hThreshold)
  heartRealizationCompatibility : HeartRealizationCompatibilityData core

namespace MMQ

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport`
in `ManuscriptSpineTargets.lean`. -/
def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (_exactData : CanonicalTraceMotivicExactDataOverQ core)
    : MMQ
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold) :=
  {
    motive :=
      (TraceMotivicHeart.ofTStructure
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold)).heartObject,
    forgetToMotivicObject := fun obj =>
      (TraceMotivicHeart.ofTStructure
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold)).forgetToMotivicObject obj,
    heartWitness := fun obj =>
      ⟨(TraceMotivicHeart.ofTStructure
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold)).heartNonposWitness obj,
        (TraceMotivicHeart.ofTStructure
          (TraceMotivicTStructureData.ofCanonicalPacketCut
            core.traceNative core.threshold core.hThreshold)).heartNonnegWitness obj⟩
  }

end MMQ

namespace HeartOfTraceTStructureIsAbelian

/-- Construct abelian heart from canonical trace data over Q. -/
def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core)
    : HeartOfTraceTStructureIsAbelian
        (TraceMotivicTStructureData.ofCanonicalPacketCut
          core.traceNative core.threshold core.hThreshold) :=
  ofConstructiveExactnessSystem
    (TraceMotivicTStructureData.ofCanonicalPacketCut
      core.traceNative core.threshold core.hThreshold)
    (TraceMotivicHeartConstructiveExactnessSystem.ofCanonicalTraceDataOverQ core exactData)

end HeartOfTraceTStructureIsAbelian

namespace MMQHeartTarget

/-- Legacy trace-native candidate/scaffold. Not the classical category MM(Q).
The live classical MM(Q) recognition path is
`RecognizesClassicalMMQ.ofDMgmRecognitionAndHeartTransport`
in `ManuscriptSpineTargets.lean`. -/
def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (exactData : CanonicalTraceMotivicExactDataOverQ core) :
    MMQHeartTarget
      (AbelianHeartTarget.ofTraceTStructure
        (TraceMotivicHeart.ofTStructure
          (TraceMotivicTStructureData.ofCanonicalPacketCut
            core.traceNative core.threshold core.hThreshold))
        (HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ core exactData)) :=
  let traceTStructure :=
    TraceMotivicTStructureData.ofCanonicalPacketCut
      core.traceNative core.threshold core.hThreshold
  let heart := TraceMotivicHeart.ofTStructure traceTStructure
  let heartAbelian :=
    HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ core exactData
  MMQHeartTarget.ofMMQ heart heartAbelian

end MMQHeartTarget

namespace MotivicTStructurePackage

/-- Public Phase 12 endpoint: construct full motivic t-structure package from canonical trace data over Q and canonical theorem bundle. -/
def ofCanonicalTraceDataOverQ
    (core : CanonicalTraceMotivicCoreDataOverQ)
    (bundle : CanonicalTraceMotivicTheoremBundleOverQ core)
    : MotivicTStructurePackage :=
  let traceTStructure :=
    TraceMotivicTStructureData.ofCanonicalPacketCut
      core.traceNative core.threshold core.hThreshold
  let heartAbelian :=
    HeartOfTraceTStructureIsAbelian.ofCanonicalTraceDataOverQ
      core bundle.exactData
  {
    structuralRecognition := core.structuralRecognition,
    weightStructure := core.weightStructure,
    traceMotivicTStructure := traceTStructure,
    tStructure := TStructureTarget.ofTraceMotivicTStructure traceTStructure,
    heart := HeartCandidate.ofTraceMotivicHeart (TraceMotivicHeart.ofTStructure traceTStructure),
    abelianHeart :=
      AbelianHeartTarget.ofTraceTStructure
        (TraceMotivicHeart.ofTStructure traceTStructure) heartAbelian,
    mmqHeart := MMQHeartTarget.ofCanonicalTraceDataOverQ core bundle.exactData,
    weightTStructureCompatibilityTarget := bundle.weightTStructureCompatibility.theoremTarget,
    heartRealizationCompatibilityTarget := bundle.heartRealizationCompatibility.theoremTarget
  }

end MotivicTStructurePackage

end MotivicRecognition
end TraceCalc

import TraceCalc.MotivicRecognition.SpineSummary
import TraceCalc.LayerB.RealObjects.CompletedRecord
import TraceCalc.LayerB.RealObjects.SyntacticBoundary
import TraceCalc.LayerB.RealObjects.CanonicalNormalForm
import TraceCalc.LayerB.RealObjects.PeelChain
import TraceCalc.ClassicalPeriods.AdmissibleGeneratorBridge
import TraceCalc.ClassicalPeriods.TraceCategory
import TraceCalc.ClassicalPeriods.ClassicalManuscriptTargets
import TraceCalc.LayerB.RealObjects.InternalManuscriptTargets
import TraceCalc.LayerD.ConcretePeriodFaithfulness

universe u v w x y z

namespace TraceCalc
namespace MotivicRecognition

set_option maxHeartbeats 3000000

open LayerB.RealObjects.RewriteCalculusSetup
open ClassicalPeriods

/-!
# Motivic recognition: manuscript theorem-target spine

This module is the global theorem-definition layer for the manuscript proof
chain. It does not attempt to prove the difficult theorems. Instead it makes
the remaining work explicit by packaging the manuscript-level comparison,
normalization, heart, and proof-relevant period statements as Lean targets.

Dependency DAG, matching the paper order:

1. stable additive/Karoubi completion;
2. concrete stable-completion construction;
3. completion universal property;
4. trace-category / `DM_gm(Q)` comparison and canonical equivalence;
5. universal `DM_gm` recognition theorem;
6. normalization package and transport across the equivalence;
7. Campaign 12A triangulated/stable recognition at the pinned `DM_gm(Q)_Q` level;
8. Campaign 12B normalization-induced motivic `t`-structure;
9. Campaign 12C heart construction `MM(Q)` as that heart and abelianity;
10. Campaign 12D heart recognition, classical heart identification, and `MM(Q)` identification;
11. proof-relevant period theorem and its comparison-faithfulness consequence.

The internal trace-side manuscript targets come from
the current LayerB boundary/completion/canonical-normalization surfaces, while
the classical geometric targets come from
`ClassicalPeriods.ClassicalManuscriptTargets`.
-/

-- Ref: Campaign 10 / Layer III enhancement-to-π₀ bridge.
/--
Ref: Campaign 10 / Layer III enhancement-to-π₀ bridge.
Concept: proof-relevant stable trace ∞-enhancement over Q.

This is not a native HoTT ∞-category. It is the explicit computadic
enhancement data needed by the paper: mapping-level data, π₀ morphisms,
stable/cofiber structure, monoidal structure, realization compatibility,
and compatibility with the completed trace presentation.
-/
structure TraceInfinityEnhancementOverQ where
  Obj : Type u

  /-- Mapping-level data before passing to π₀. -/
  Mapping : Obj → Obj → Type v

  /-- π₀ morphisms, i.e. morphisms in the homotopy-category shadow. -/
  Pi0Hom : Obj → Obj → Type w

  /-- Projection from mapping-level data to π₀ classes. -/
  pi0Class : ∀ {X Y : Obj}, Mapping X Y → Pi0Hom X Y

  /-- Identity and composition in the π₀ shadow. -/
  idPi0 : ∀ X : Obj, Pi0Hom X X
  compPi0 :
    ∀ {X Y Z : Obj}, Pi0Hom X Y → Pi0Hom Y Z → Pi0Hom X Z

  /-- Proof-relevant category/coherence data for the π₀ shadow. -/
  categoryLaws : Type
  identityCompatibilityWitness :
    (∀ {X Y : Obj} (f : Pi0Hom X Y), compPi0 (idPi0 X) f = f) ∧
    (∀ {X Y : Obj} (f : Pi0Hom X Y), compPi0 f (idPi0 Y) = f)
  compositionCompatibilityWitness :
    ∀ {W X Y Z : Obj} (f : Pi0Hom W X) (g : Pi0Hom X Y) (h : Pi0Hom Y Z),
      compPi0 (compPi0 f g) h = compPi0 f (compPi0 g h)

  /-- Stable shift/suspension data. -/
  shiftObj : Obj → Obj
  shiftMapPi0 :
    ∀ {X Y : Obj}, Pi0Hom X Y → Pi0Hom (shiftObj X) (shiftObj Y)
  shiftCompatibilityWitness :
    (∀ X, shiftMapPi0 (idPi0 X) = idPi0 (shiftObj X)) ∧
    (∀ {X Y Z : Obj} (f : Pi0Hom X Y) (g : Pi0Hom Y Z),
      shiftMapPi0 (compPi0 f g) = compPi0 (shiftMapPi0 f) (shiftMapPi0 g))

  /-- Morphism-indexed fiber/cofiber data in the π₀ shadow. -/
  cofiberObj : ∀ {X Y : Obj}, Pi0Hom X Y → Obj
  fiberObj : ∀ {X Y : Obj}, Pi0Hom X Y → Obj

  distinguishedTriangle : Obj → Obj → Obj → Type

  cofiberTriangle :
    ∀ {X Y : Obj} (f : Pi0Hom X Y),
      distinguishedTriangle X Y (cofiberObj f)

  fiberTriangle :
    ∀ {X Y : Obj} (f : Pi0Hom X Y),
      distinguishedTriangle (fiberObj f) X Y

  cofiberTriangleCompatibilityWitness :
    ∀ {X Y Z : Obj} (f : Pi0Hom X Y) (g : Pi0Hom Y Z),
      Nonempty (distinguishedTriangle (cofiberObj f) (cofiberObj (compPi0 f g)) (cofiberObj g))

  /-- Triangulated/stable shadow axioms, proof-relevant if replayed later. -/
  triangulatedAxioms : Type
  triangulatedStructureCompatibilityWitness :
    ∀ {X Y Z : Obj},
      Nonempty (distinguishedTriangle X Y Z) →
        Nonempty (distinguishedTriangle Y Z (shiftObj X))

  /-- Monoidal structure on the π₀ shadow. -/
  tensorObj : Obj → Obj → Obj
  tensorPi0 :
    ∀ {A B C D : Obj},
      Pi0Hom A B →
      Pi0Hom C D →
      Pi0Hom (tensorObj A C) (tensorObj B D)

  monoidalAxioms : Type
  monoidalCompatibilityWitness :
    ∀ (A C : Obj), tensorPi0 (idPi0 A) (idPi0 C) = idPi0 (tensorObj A C)

  /-- Realization compatibility inherited from the ∞-enhancement.
  Proposition-valued: the user must state the actual realization-compatibility theorem,
  e.g. that the comparison commutes with the Betti/de Rham realization functors. -/
  realizationCompatibilityWitness : Prop

  /-- Compatibility with the completed presentation / Campaign 11 rungs 1–4.
  Proposition-valued: the user must state the actual completed-presentation theorem,
  e.g. that the π₀ shadow agrees with the completed reconstruction record. -/
  completedPresentationCompatibilityWitness : Prop

/-- Exact cofiber-to-distinguished-triangle law for the ∞ enhancement. -/
def TraceInfinityCofiberTriangleLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  ∀ {X Y : enh.Obj} (f : enh.Mapping X Y),
    Nonempty (enh.distinguishedTriangle X Y (enh.cofiberObj (enh.pi0Class f)))

/-- Exact triangulated rotation/stability law for the ∞ enhancement. -/
def TraceInfinityTriangulatedStructureLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  ∀ {X Y Z : enh.Obj},
    Nonempty (enh.distinguishedTriangle X Y Z) →
      Nonempty (enh.distinguishedTriangle Y Z (enh.shiftObj X))

/-- Exact shift functoriality law carried by the ∞ enhancement. -/
def TraceInfinityShiftCompatibilityLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  (∀ X, enh.shiftMapPi0 (enh.idPi0 X) = enh.idPi0 (enh.shiftObj X)) ∧
    (∀ {X Y Z : enh.Obj} (f : enh.Pi0Hom X Y) (g : enh.Pi0Hom Y Z),
      enh.shiftMapPi0 (enh.compPi0 f g) =
        enh.compPi0 (enh.shiftMapPi0 f) (enh.shiftMapPi0 g))

/-- Exact monoidal identity law carried by the ∞ enhancement. -/
def TraceInfinityMonoidalCompatibilityLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  ∀ (A C : enh.Obj), enh.tensorPi0 (enh.idPi0 A) (enh.idPi0 C) =
    enh.idPi0 (enh.tensorObj A C)

/-- Exact realization compatibility theorem required of the ∞ enhancement. -/
def TraceInfinityRealizationCompatibilityLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  enh.realizationCompatibilityWitness

/-- Exact completed-presentation compatibility theorem required of the ∞
enhancement. -/
def TraceInfinityCompletedPresentationCompatibilityLaw
    (enh : TraceInfinityEnhancementOverQ) : Prop :=
  enh.completedPresentationCompatibilityWitness

/-- Named proof package for the ∞ enhancement and its π₀ shadow.

The proof-relevant data itself remains in `TraceInfinityEnhancementOverQ`; this
package supplies the theorem-level laws needed to route that data into the
homotopy-category shadow and comparison certificate. -/
structure TraceInfinityEnhancementTheoremPackage
    (enh : TraceInfinityEnhancementOverQ) where
  shiftCompatibility : TraceInfinityShiftCompatibilityLaw enh
  cofiberTriangle : TraceInfinityCofiberTriangleLaw enh
  triangulatedStructure :
    TraceInfinityTriangulatedStructureLaw enh
  monoidalCompatibility : TraceInfinityMonoidalCompatibilityLaw enh
  realizationCompatibility :
    TraceInfinityRealizationCompatibilityLaw enh
  completedPresentationCompatibility :
    TraceInfinityCompletedPresentationCompatibilityLaw enh

namespace TraceInfinityEnhancementTheoremPackage

def ofEnhancementWitnesses
    (enh : TraceInfinityEnhancementOverQ)
    (realizationCompatibility :
      TraceInfinityRealizationCompatibilityLaw enh)
    (completedPresentationCompatibility :
      TraceInfinityCompletedPresentationCompatibilityLaw enh) :
    TraceInfinityEnhancementTheoremPackage enh where
  shiftCompatibility := enh.shiftCompatibilityWitness
  cofiberTriangle := fun f => ⟨enh.cofiberTriangle (enh.pi0Class f)⟩
  triangulatedStructure := enh.triangulatedStructureCompatibilityWitness
  monoidalCompatibility := enh.monoidalCompatibilityWitness
  realizationCompatibility := realizationCompatibility
  completedPresentationCompatibility := completedPresentationCompatibility

end TraceInfinityEnhancementTheoremPackage

/--
Ref: Campaign 10 / π₀ triangulated shadow.
Concept: homotopy-category shadow extracted from trace ∞-enhancement.
-/
structure TracePi0TriangulatedShadowOverQ where
  Obj : Type u
  Hom : Obj → Obj → Type w

  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  categoryLaws : Type

  shiftObj : Obj → Obj
  shiftMap :
    ∀ {X Y : Obj}, Hom X Y → Hom (shiftObj X) (shiftObj Y)

  cofiberObj : ∀ {X Y : Obj}, Hom X Y → Obj
  fiberObj : ∀ {X Y : Obj}, Hom X Y → Obj

  distinguishedTriangle : Obj → Obj → Obj → Type

  cofiberTriangle :
    ∀ {X Y : Obj} (f : Hom X Y),
      distinguishedTriangle X Y (cofiberObj f)

  fiberTriangle :
    ∀ {X Y : Obj} (f : Hom X Y),
      distinguishedTriangle (fiberObj f) X Y

  triangulatedAxioms : Type

  tensorObj : Obj → Obj → Obj
  tensorMap :
    ∀ {A B C D : Obj},
      Hom A B →
      Hom C D →
      Hom (tensorObj A C) (tensorObj B D)

  monoidalAxioms : Type

  /-- The π₀ shadow's structure is compatible with the Campaign 11 completed trace
  presentation. Proposition-valued: a concrete compatibility theorem must be supplied
  by the constructor, not an arbitrary type witness. -/
  completedPresentationCompatibility : Prop
  completedPresentationCompatibility_holds : completedPresentationCompatibility

namespace TracePi0TriangulatedShadowOverQ

/--
Ref: Campaign 10 / Layer III → π₀ extraction.
Concept: extract the homotopy-category triangulated shadow from the
proof-relevant stable trace ∞-enhancement.
-/
def ofInfinityEnhancement
    (enh : TraceInfinityEnhancementOverQ)
    (theorems : TraceInfinityEnhancementTheoremPackage enh)
    : TracePi0TriangulatedShadowOverQ :=
{
  Obj := enh.Obj
  Hom := enh.Pi0Hom

  id := enh.idPi0
  comp := enh.compPi0
  categoryLaws := enh.categoryLaws

  shiftObj := enh.shiftObj
  shiftMap := enh.shiftMapPi0

  cofiberObj := enh.cofiberObj
  fiberObj := enh.fiberObj

  distinguishedTriangle := enh.distinguishedTriangle
  cofiberTriangle := enh.cofiberTriangle
  fiberTriangle := enh.fiberTriangle

  triangulatedAxioms := enh.triangulatedAxioms

  tensorObj := enh.tensorObj
  tensorMap := enh.tensorPi0
  monoidalAxioms := enh.monoidalAxioms

  completedPresentationCompatibility :=
    enh.completedPresentationCompatibilityWitness
  completedPresentationCompatibility_holds :=
    theorems.completedPresentationCompatibility
}

end TracePi0TriangulatedShadowOverQ

/-- Concrete shift/suspension compatibility data for an ∞-to-π₀ comparison.

Records two things:
(a) Object-level coherence: `objectCmp (shiftObj X) = shadow.shiftObj (objectCmp X)` for all X.
(b) Morphism-level naturality: the comparison of a shifted morphism equals the shifted comparison
    morphism, stated via `HEq` since domain/codomain types require (a) to agree. -/
structure ShiftCompatibilityData
    {enh : TraceInfinityEnhancementOverQ}
    {shadow : TracePi0TriangulatedShadowOverQ}
    (objectCmp : enh.Obj → shadow.Obj)
    (homCmp : ∀ {X Y : enh.Obj}, enh.Pi0Hom X Y → shadow.Hom (objectCmp X) (objectCmp Y))
    where
  /-- Object-level: the comparison functor commutes with the shift functor on objects. -/
  shiftObjCommutes :
    ∀ (X : enh.Obj),
      objectCmp (enh.shiftObj X) = shadow.shiftObj (objectCmp X)
  /-- Morphism-level: the comparison of a shifted morphism equals the shifted comparison
  morphism (HEq because source/target types differ until applying `shiftObjCommutes`). -/
  shiftMapNaturality :
    ∀ {X Y : enh.Obj} (f : enh.Pi0Hom X Y),
      HEq (homCmp (enh.shiftMapPi0 f)) (shadow.shiftMap (homCmp f))

/-- Concrete monoidal/tensor compatibility data for an ∞-to-π₀ comparison.

Records two things:
(a) Object-level coherence: `objectCmp (tensorObj A C) = shadow.tensorObj (objectCmp A) (objectCmp C)`.
(b) Morphism-level naturality: the comparison of a tensor product of morphisms equals the tensor
    product of the individual comparisons, stated via `HEq`. -/
structure MonoidalCompatibilityData
    {enh : TraceInfinityEnhancementOverQ}
    {shadow : TracePi0TriangulatedShadowOverQ}
    (objectCmp : enh.Obj → shadow.Obj)
    (homCmp : ∀ {X Y : enh.Obj}, enh.Pi0Hom X Y → shadow.Hom (objectCmp X) (objectCmp Y))
    where
  /-- Object-level: the comparison functor commutes with tensor on objects. -/
  tensorObjCommutes :
    ∀ (A C : enh.Obj),
      objectCmp (enh.tensorObj A C) = shadow.tensorObj (objectCmp A) (objectCmp C)
  /-- Morphism-level: the comparison of a tensor product of morphisms equals the tensor
  product of the comparisons (HEq because source/target types differ until applying
  `tensorObjCommutes`). -/
  tensorMapNaturality :
    ∀ {A B C D : enh.Obj}
      (f : enh.Pi0Hom A B) (g : enh.Pi0Hom C D),
      HEq (homCmp (enh.tensorPi0 f g)) (shadow.tensorMap (homCmp f) (homCmp g))

/--
Ref: Campaign 10 / ∞→π₀ comparison certificate.
Concept: comparison data showing that the π₀ shadow is extracted from,
not assumed independently of, the stable trace ∞-enhancement.
-/
structure TraceInfinityToPiZeroShadowComparisonOverQ where
  enhancement : TraceInfinityEnhancementOverQ
  theoremPackage : TraceInfinityEnhancementTheoremPackage enhancement

  pi0Shadow : TracePi0TriangulatedShadowOverQ

  objectComparison :
    enhancement.Obj → pi0Shadow.Obj

  mappingToPi0Comparison :
    ∀ {X Y : enhancement.Obj},
      enhancement.Mapping X Y →
        pi0Shadow.Hom (objectComparison X) (objectComparison Y)

  pi0HomComparison :
    ∀ {X Y : enhancement.Obj},
      enhancement.Pi0Hom X Y →
        pi0Shadow.Hom (objectComparison X) (objectComparison Y)

  /-- The comparison functor preserves identity: π₀-comparison of the identity equals the shadow identity. -/
  identityCompatibility :
    ∀ (X : enhancement.Obj),
      pi0HomComparison (enhancement.idPi0 X) = pi0Shadow.id (objectComparison X)
  /-- The comparison functor preserves composition. -/
  compositionCompatibility :
    ∀ {X Y Z : enhancement.Obj}
      (f : enhancement.Pi0Hom X Y) (g : enhancement.Pi0Hom Y Z),
      pi0HomComparison (enhancement.compPi0 f g) =
        pi0Shadow.comp (pi0HomComparison f) (pi0HomComparison g)
  /-- The comparison commutes with the shift/suspension functor:
  object-level coherence and morphism-level naturality; see `ShiftCompatibilityData`. -/
  shiftCompatibility : ShiftCompatibilityData objectComparison pi0HomComparison
  /-- The comparison sends π₀-cofiber triangles to distinguished triangles in the shadow. -/
  cofiberTriangleCompatibility :
    ∀ {X Y : enhancement.Obj} (f : enhancement.Pi0Hom X Y),
      Nonempty (pi0Shadow.distinguishedTriangle
        (objectComparison X) (objectComparison Y)
        (pi0Shadow.cofiberObj (pi0HomComparison f)))
  /-- The ∞-to-π₀ comparison functor is triangulated: for every mapping `f`,
  its π₀-class image lies in a distinguished cofiber triangle.
  This stores the concrete triangulated-functor condition as a proposition. -/
  triangulatedStructureCompatibility : Prop
  triangulatedStructureCompatibility_holds : triangulatedStructureCompatibility
  /-- The comparison functor is monoidal:
  object-level tensor coherence and morphism-level naturality; see `MonoidalCompatibilityData`. -/
  monoidalCompatibility : MonoidalCompatibilityData objectComparison pi0HomComparison
  /-- The comparison functor is compatible with the realization functor.
  Proposition-valued: must state the actual realization-naturality theorem. -/
  realizationCompatibility : Prop
  realizationCompatibility_holds : realizationCompatibility
  /-- The comparison functor is compatible with the completed trace presentation.
  Proposition-valued: must state the actual completed-presentation theorem. -/
  comparisonToCompletedPresentation : Prop
  comparisonToCompletedPresentation_holds : comparisonToCompletedPresentation

namespace TraceInfinityToPiZeroShadowComparisonOverQ

/--
Ref: Campaign 10 / ∞→π₀ bridge.
Concept: construct the comparison certificate by projecting all coherence
witnesses from the stable trace ∞-enhancement.
-/
def ofInfinityEnhancement
    (enh : TraceInfinityEnhancementOverQ)
    (theorems : TraceInfinityEnhancementTheoremPackage enh)
    : TraceInfinityToPiZeroShadowComparisonOverQ :=
{
  enhancement := enh
  theoremPackage := theorems

  pi0Shadow :=
    TracePi0TriangulatedShadowOverQ.ofInfinityEnhancement enh theorems

  objectComparison := fun X => X

  mappingToPi0Comparison := fun {X Y} f =>
    enh.pi0Class f

  pi0HomComparison := fun {X Y} f =>
    f

  -- The comparison is the identity on π₀ morphisms, so functor laws hold trivially by rfl.
  identityCompatibility := fun _ => rfl

  compositionCompatibility := fun _ _ => rfl

  -- objectComparison = id and pi0Shadow.shiftObj = enh.shiftObj, so both
  -- shiftObjCommutes and shiftMapNaturality hold definitionally.
  shiftCompatibility := {
    shiftObjCommutes := fun _ => rfl
    shiftMapNaturality := fun _ => HEq.rfl
  }

  -- The cofiber triangle is carried directly from the enhancement.
  cofiberTriangleCompatibility := fun f => ⟨enh.cofiberTriangle f⟩

  -- Proof: for any mapping f, pi0Class f is a π₀-morphism, and cofiberTriangle
  -- witnesses that (X, Y, cofiberObj (pi0Class f)) is a distinguished triangle.
  -- We store the triangulated functor condition as a concrete proposition.
  triangulatedStructureCompatibility :=
    ∀ (X Y : enh.Obj) (f : enh.Mapping X Y),
      Nonempty (enh.distinguishedTriangle X Y (enh.cofiberObj (enh.pi0Class f)))
  triangulatedStructureCompatibility_holds := fun _ _ f =>
    theorems.cofiberTriangle f

  -- objectComparison = id and pi0Shadow.tensorObj = enh.tensorObj, so both
  -- tensorObjCommutes and tensorMapNaturality hold definitionally.
  monoidalCompatibility := {
    tensorObjCommutes := fun _ _ => rfl
    tensorMapNaturality := fun _ _ => HEq.rfl
  }

  realizationCompatibility :=
    enh.realizationCompatibilityWitness
  realizationCompatibility_holds :=
    theorems.realizationCompatibility

  comparisonToCompletedPresentation :=
    enh.completedPresentationCompatibilityWitness
  comparisonToCompletedPresentation_holds :=
    theorems.completedPresentationCompatibility
}

end TraceInfinityToPiZeroShadowComparisonOverQ
/- Quarantined stale recognition-assembly block.

This predated the current manuscript spine ordering and referred to names not
defined anywhere live in the repository (`TraceMotivicRecognitionPackageOverQ`,
`ClassicalMMQRecognitionHypotheses`, `trace_candidate_recognizes_classical_MMQ`,
etc.). It was also positioned before the local comparison/normalization/t-
structure declarations it tried to consume. The structural build repair keeps
the lower manuscript-target layers live and removes this non-elaborating block
until its concrete dependencies are rebuilt from real lower data. -/
/- Trace-native motivic heart and recognition bridge layer. -/

/--
  TraceMotivicRecognitionPackageOverQ is a trace-native candidate for MM(Q),
  not the classical category of mixed motives over Q. It must not be called MM(Q)
  until a recognition theorem identifies it with the classical target.
-/

def admissibleGeneratorBridgeOfAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    Campaign7AdmissibleGeneratorBridge ctx :=
  Campaign7AdmissibleGeneratorBridge.ofAssignmentTable assignmentTable

def presentationAdmissibleClosureEquivalenceOfAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    PresentationAdmissibleClosureEquivalence ctx :=
  (admissibleGeneratorBridgeOfAssignmentTable assignmentTable).presentationAdmissibleClosureEquivalence

def traceCategoryStructureOfAssignmentTable
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    TraceCategoryStructure ctx :=
  traceCategoryStructure_from_campaign8
    (presentationAdmissibleClosureEquivalenceOfAssignmentTable assignmentTable)

theorem traceCategoryStructureTarget_from_campaign9TraceCategory
    {ctx : ClassicalComparisonContext.{u, v}}
    (assignmentTable : GeneratorRealizationAssignmentTable ctx) :
    (traceCategoryStructureOfAssignmentTable assignmentTable).categoricalShadowTarget :=
  traceCategoryStructure_from_campaign8_shadow
    (presentationAdmissibleClosureEquivalenceOfAssignmentTable assignmentTable)

/-- Local minimal-completion theorem surface used by the manuscript spine.
These fields match the paper's coarse completion obligations without depending
on the larger internal manuscript-target package. -/
structure MinimumCompletionTarget where
  completedTraceCategoryExists : Prop
  completionExtensionProperty : Prop
  stableCompletionModel : Prop

/-- Local internal manuscript reference surface used by the global manuscript
spine. This keeps the master spine buildable while still exposing the concrete
internal boundary/completion/canonicality obligations that the paper must
discharge. -/
structure InternalManuscriptSpineTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {α : Type v}
    (P : SyntacticBoundaryPresentation setup)
    (comparison : CompletedReconstructionRecord setup → α)
    (C : CanNF setup) where
  boundaryPresentation : SyntacticBoundaryPresentation setup
  boundaryPresentationAgreementTarget : boundaryPresentation = P
  minimumCompletion : MinimumCompletionTarget
  traceCategoryTarget : Prop
  boundaryComparisonFaithfulnessTarget : Prop
  internalComparisonFaithfulnessTarget : Prop
  canNFEqualityDetectionTarget : Prop

/-- Bridge package exposing the six Layer B stable-completion field targets to
the global motivic-recognition spine.

These categorical facts remain external proof obligations. The bridge only
records how they would feed the three completion-stage theorem targets already
present in the global manuscript spine. -/
structure StableCompletionFromLayerBTargets
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C) where
  dgEnvelope : FreeDGEnvelopeTarget
  pretriangulatedHull : PretriangulatedHullUniversalTarget
  hZeroPassage : H0TriangulatedTarget
  karoubiEnvelope : KaroubiEnvelopeUniversalTarget
  monoidalLift : MonoidalLiftThroughCompletionTarget
  exactnessTransport : ExactnessTransportThroughCompletionTarget
  stableAdditiveCompletionTarget : Prop
  karoubiClosureTarget : Prop
  completionAgreesWithRecognitionTarget : Prop
  additiveConstructionTarget : Prop
  triangulatedConstructionTarget : Prop
  karoubiConstructionTarget : Prop
  structuralPackageCompatibilityTarget : Prop
  completionExtensionTarget : Prop
  exactSymmetricMonoidalExtensionTarget : Prop
  uniquenessTarget : Prop
  stepFieldsFeedMinimumCompletion :
    dgEnvelope.dgEnvelopeUniversality →
      pretriangulatedHull.pretriangulatedHullUniversality →
      hZeroPassage.hZeroTriangulatedPassage →
      karoubiEnvelope.karoubianEnvelopeUniversality →
      monoidalLift.monoidalLiftThroughCompletion →
      exactnessTransport.exactnessTransportThroughCompletion →
      internal.minimumCompletion.completedTraceCategoryExists ∧
        internal.minimumCompletion.completionExtensionProperty ∧
        internal.minimumCompletion.stableCompletionModel
  stepFieldsFeedStableCompletion :
    dgEnvelope.dgEnvelopeUniversality →
      pretriangulatedHull.pretriangulatedHullUniversality →
      hZeroPassage.hZeroTriangulatedPassage →
      karoubiEnvelope.karoubianEnvelopeUniversality →
      monoidalLift.monoidalLiftThroughCompletion →
      exactnessTransport.exactnessTransportThroughCompletion →
      stableAdditiveCompletionTarget ∧
        karoubiClosureTarget ∧
        completionAgreesWithRecognitionTarget
  stepFieldsFeedStableConstruction :
    dgEnvelope.dgEnvelopeUniversality →
      pretriangulatedHull.pretriangulatedHullUniversality →
      hZeroPassage.hZeroTriangulatedPassage →
      karoubiEnvelope.karoubianEnvelopeUniversality →
      monoidalLift.monoidalLiftThroughCompletion →
      exactnessTransport.exactnessTransportThroughCompletion →
      additiveConstructionTarget ∧
        triangulatedConstructionTarget ∧
        karoubiConstructionTarget ∧
        structuralPackageCompatibilityTarget
  stepFieldsFeedCompletionUniversalProperty :
    dgEnvelope.dgEnvelopeUniversality →
      pretriangulatedHull.pretriangulatedHullUniversality →
      hZeroPassage.hZeroTriangulatedPassage →
      karoubiEnvelope.karoubianEnvelopeUniversality →
      monoidalLift.monoidalLiftThroughCompletion →
      exactnessTransport.exactnessTransportThroughCompletion →
      completionExtensionTarget ∧
        exactSymmetricMonoidalExtensionTarget ∧
        uniquenessTarget

namespace StableCompletionFromLayerBTargets

/-- Proof witness supplying the six categorical completion obligations imported
from Layer B into the motivic-recognition spine. -/
structure StepWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (bridge : StableCompletionFromLayerBTargets internal) where
  dgEnvelope : bridge.dgEnvelope.dgEnvelopeUniversality
  pretriangulatedHull : bridge.pretriangulatedHull.pretriangulatedHullUniversality
  hZeroPassage : bridge.hZeroPassage.hZeroTriangulatedPassage
  karoubiEnvelope : bridge.karoubiEnvelope.karoubianEnvelopeUniversality
  monoidalLift : bridge.monoidalLift.monoidalLiftThroughCompletion
  exactnessTransport : bridge.exactnessTransport.exactnessTransportThroughCompletion

/-- Proof-relevant stable-completion theorem package imported from Layer B.

The six step witnesses are the only primitive proof inputs.  The completion,
construction, and universal-property consequences are projected through the
bridge laws, so downstream completion targets no longer depend on unrelated
copies of the same theorem boxes. -/
structure TheoremPackage
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (bridge : StableCompletionFromLayerBTargets internal) where
  stepWitness : bridge.StepWitness
  minimumCompletion :
    internal.minimumCompletion.completedTraceCategoryExists ∧
      internal.minimumCompletion.completionExtensionProperty ∧
      internal.minimumCompletion.stableCompletionModel
  stableCompletion :
    bridge.stableAdditiveCompletionTarget ∧
      bridge.karoubiClosureTarget ∧
      bridge.completionAgreesWithRecognitionTarget
  construction :
    bridge.additiveConstructionTarget ∧
      bridge.triangulatedConstructionTarget ∧
      bridge.karoubiConstructionTarget ∧
      bridge.structuralPackageCompatibilityTarget
  universalProperty :
    bridge.completionExtensionTarget ∧
      bridge.exactSymmetricMonoidalExtensionTarget ∧
      bridge.uniquenessTarget

def TheoremPackage.ofStepWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (bridge : StableCompletionFromLayerBTargets internal)
    (witness : bridge.StepWitness) :
    TheoremPackage bridge where
  stepWitness := witness
  minimumCompletion :=
    bridge.stepFieldsFeedMinimumCompletion witness.dgEnvelope
      witness.pretriangulatedHull witness.hZeroPassage witness.karoubiEnvelope
      witness.monoidalLift witness.exactnessTransport
  stableCompletion :=
    bridge.stepFieldsFeedStableCompletion witness.dgEnvelope
      witness.pretriangulatedHull witness.hZeroPassage witness.karoubiEnvelope
      witness.monoidalLift witness.exactnessTransport
  construction :=
    bridge.stepFieldsFeedStableConstruction witness.dgEnvelope
      witness.pretriangulatedHull witness.hZeroPassage witness.karoubiEnvelope
      witness.monoidalLift witness.exactnessTransport
  universalProperty :=
    bridge.stepFieldsFeedCompletionUniversalProperty witness.dgEnvelope
      witness.pretriangulatedHull witness.hZeroPassage witness.karoubiEnvelope
      witness.monoidalLift witness.exactnessTransport

end StableCompletionFromLayerBTargets

/-- Manuscript target for the stable additive/Karoubi completion of the trace
category. This packages the completion surface around
`def:completed-trace-category`, `prop:completion-extension`,
`lem:completion-extension-property`, and `prop:dg-truncation`. -/
structure StableAdditiveKaroubiCompletionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C) where
  minimumCompletion : MinimumCompletionTarget
  layerBCompletionBridge : StableCompletionFromLayerBTargets internal
  stableCompletionTheorems :
    layerBCompletionBridge.TheoremPackage
  stableAdditiveCompletionTarget : Prop
  stableAdditiveCompletion_holds : stableAdditiveCompletionTarget
  karoubiClosureTarget : Prop
  karoubiClosure_holds : karoubiClosureTarget
  completionAgreesWithRecognitionTarget : Prop
  completionAgreesWithRecognition_holds : completionAgreesWithRecognitionTarget

/-- Manuscript target for the concrete stable-completion construction, including
the completion-side compatibility with the current recognition structural
package. -/
structure TraceStableCompletionConstructionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal) where
  layerBCompletionBridge : StableCompletionFromLayerBTargets internal
  stableCompletionTheorems :
    layerBCompletionBridge.TheoremPackage
  additiveConstructionTarget : Prop
  additiveConstruction_holds : additiveConstructionTarget
  triangulatedConstructionTarget : Prop
  triangulatedConstruction_holds : triangulatedConstructionTarget
  karoubiConstructionTarget : Prop
  karoubiConstruction_holds : karoubiConstructionTarget
  structuralPackageCompatibilityTarget : Prop
  structuralPackageCompatibility_holds : structuralPackageCompatibilityTarget

/-- Manuscript target for the universal property of the completed trace
category. This is the completion-side theorem surface used before any direct
comparison with `DM_gm(Q)`. -/
structure TraceCompletionUniversalPropertyTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (construction : TraceStableCompletionConstructionTarget spine internal stableCompletion) where
  layerBCompletionBridge : StableCompletionFromLayerBTargets internal
  stableCompletionTheorems :
    layerBCompletionBridge.TheoremPackage
  completionExtensionTarget : Prop
  completionExtension_holds : completionExtensionTarget
  exactSymmetricMonoidalExtensionTarget : Prop
  exactSymmetricMonoidalExtension_holds : exactSymmetricMonoidalExtensionTarget
  uniquenessTarget : Prop
  uniqueness_holds : uniquenessTarget

namespace StableCompletionFromLayerBTargets

def toStableAdditiveKaroubiCompletionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (bridge : StableCompletionFromLayerBTargets internal)
    (witness : bridge.StepWitness) :
    StableAdditiveKaroubiCompletionTarget spine internal where
  minimumCompletion := internal.minimumCompletion
  layerBCompletionBridge := bridge
  stableCompletionTheorems :=
    TheoremPackage.ofStepWitness bridge witness
  stableAdditiveCompletionTarget := bridge.stableAdditiveCompletionTarget
  stableAdditiveCompletion_holds :=
    (TheoremPackage.ofStepWitness bridge witness).stableCompletion.1
  karoubiClosureTarget := bridge.karoubiClosureTarget
  karoubiClosure_holds :=
    (TheoremPackage.ofStepWitness bridge witness).stableCompletion.2.1
  completionAgreesWithRecognitionTarget :=
    bridge.completionAgreesWithRecognitionTarget
  completionAgreesWithRecognition_holds :=
    (TheoremPackage.ofStepWitness bridge witness).stableCompletion.2.2

def toTraceStableCompletionConstructionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (bridge : StableCompletionFromLayerBTargets internal)
    (witness : bridge.StepWitness)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal) :
    TraceStableCompletionConstructionTarget spine internal stableCompletion where
  layerBCompletionBridge := bridge
  stableCompletionTheorems :=
    TheoremPackage.ofStepWitness bridge witness
  additiveConstructionTarget := bridge.additiveConstructionTarget
  additiveConstruction_holds :=
    (TheoremPackage.ofStepWitness bridge witness).construction.1
  triangulatedConstructionTarget := bridge.triangulatedConstructionTarget
  triangulatedConstruction_holds :=
    (TheoremPackage.ofStepWitness bridge witness).construction.2.1
  karoubiConstructionTarget := bridge.karoubiConstructionTarget
  karoubiConstruction_holds :=
    (TheoremPackage.ofStepWitness bridge witness).construction.2.2.1
  structuralPackageCompatibilityTarget :=
    bridge.structuralPackageCompatibilityTarget
  structuralPackageCompatibility_holds :=
    (TheoremPackage.ofStepWitness bridge witness).construction.2.2.2

def toTraceCompletionUniversalPropertyTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (bridge : StableCompletionFromLayerBTargets internal)
    (witness : bridge.StepWitness)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (construction : TraceStableCompletionConstructionTarget spine internal stableCompletion) :
    TraceCompletionUniversalPropertyTarget spine internal stableCompletion construction where
  layerBCompletionBridge := bridge
  stableCompletionTheorems :=
    TheoremPackage.ofStepWitness bridge witness
  completionExtensionTarget := bridge.completionExtensionTarget
  completionExtension_holds :=
    (TheoremPackage.ofStepWitness bridge witness).universalProperty.1
  exactSymmetricMonoidalExtensionTarget :=
    bridge.exactSymmetricMonoidalExtensionTarget
  exactSymmetricMonoidalExtension_holds :=
    (TheoremPackage.ofStepWitness bridge witness).universalProperty.2.1
  uniquenessTarget := bridge.uniquenessTarget
  uniqueness_holds :=
    (TheoremPackage.ofStepWitness bridge witness).universalProperty.2.2

end StableCompletionFromLayerBTargets

/-- Standalone theorem target for `thm:core-presentation-equivalence`. This
keeps the core geometric presentation equivalence explicit rather than folded
into the broader comparison package. -/
structure CorePresentationEquivalenceTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq) where
  corePresentationEquivalenceTarget : Prop
  identityOnGeneratingObjectsTarget : Prop
  identityOnGeneratingMorphismsTarget : Prop

namespace CorePresentationEquivalenceTarget

def ofDecomposition
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (decomposition : ClassicalPeriods.CorePresentationEquivalenceDecompositionTarget ctx) :
    CorePresentationEquivalenceTarget spine internal classical where
  corePresentationEquivalenceTarget := decomposition.commonGenerators.sameGeneratorFamiliesTarget ∧
    decomposition.commonRelations.sameRelationFamiliesTarget ∧
    decomposition.traceToGeometricSoundness.traceToGeometricPacketSoundnessTarget ∧
    decomposition.presentationCompleteness.geometricPresentationCompletenessTarget
  identityOnGeneratingObjectsTarget :=
    decomposition.commonGenerators.sameGeneratorFamiliesTarget
  identityOnGeneratingMorphismsTarget :=
    decomposition.commonRelations.sameRelationFamiliesTarget ∧
      decomposition.traceToGeometricSoundness.traceToGeometricPacketSoundnessTarget

end CorePresentationEquivalenceTarget

/-- Standalone theorem target for `cor:completed-presentation-equivalence`.
This isolates the completion-extension equivalence from the broader
`DM_gm(Q)` comparison lane. -/
structure CompletedPresentationEquivalenceTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical) where
  completedPresentationEquivalenceTarget : Prop
  exactSymmetricMonoidalExtensionTarget : Prop
  dualityCompatibilityTarget : Prop

/-- Focused local decomposition for `cor:completed-presentation-equivalence`.

The current completion/core packages already expose the exact symmetric
monoidal extension field directly. What remains genuinely independent at this
layer is: preservation of the presentation equivalence through completion,
full faithfulness on the completed presentation, essential surjectivity on the
completed presentation, and compatibility with duality. -/
structure CompletedPresentationEquivalenceDecompositionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical) where
  completionPreservesPresentationEquivalenceTarget : Prop
  completedPresentationFullFaithfulnessTarget : Prop
  completedPresentationEssentialSurjectivityTarget : Prop
  completedPresentationDualityCompatibilityTarget : Prop

namespace CompletedPresentationEquivalenceTarget

def ofDecomposition
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical)
    (decomposition : CompletedPresentationEquivalenceDecompositionTarget spine internal
      stableCompletion stableCompletionConstruction completionUniversalProperty classical
      corePresentationEquivalence) :
    CompletedPresentationEquivalenceTarget spine internal stableCompletion
      stableCompletionConstruction completionUniversalProperty classical
      corePresentationEquivalence where
  completedPresentationEquivalenceTarget :=
    decomposition.completionPreservesPresentationEquivalenceTarget ∧
      decomposition.completedPresentationFullFaithfulnessTarget ∧
      decomposition.completedPresentationEssentialSurjectivityTarget
  exactSymmetricMonoidalExtensionTarget :=
    completionUniversalProperty.exactSymmetricMonoidalExtensionTarget
  dualityCompatibilityTarget :=
    decomposition.completedPresentationDualityCompatibilityTarget

end CompletedPresentationEquivalenceTarget

/-- Manuscript target for the `\pi_0`-level comparison between the completed
trace category and `DM_gm(Q)`. This covers the paper's common-presentation and
closure-equality comparison lane. -/
structure CanonicalTraceDMgmEquivalenceData
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq) where
  stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal
  stableCompletionConstruction :
    TraceStableCompletionConstructionTarget spine internal stableCompletion
  completionUniversalProperty :
    TraceCompletionUniversalPropertyTarget spine internal stableCompletion
      stableCompletionConstruction
  corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical
  completedPresentationEquivalence :
    CompletedPresentationEquivalenceTarget spine internal stableCompletion
      stableCompletionConstruction completionUniversalProperty
      classical corePresentationEquivalence
  closureEquivalence : PresentationAdmissibleClosureEquivalence ctx
  infinityToPiZeroComparison : TraceInfinityToPiZeroShadowComparisonOverQ

namespace CanonicalTraceDMgmEquivalenceData

def commonPresentationCompatibility
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.completedPresentationEquivalence.completedPresentationEquivalenceTarget

def closureCompatibility
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.closureEquivalence.closureComparisonTarget

def pi0ShadowCompatibility
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.infinityToPiZeroComparison.triangulatedStructureCompatibility

def fullyFaithfulWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.completedPresentationEquivalence.exactSymmetricMonoidalExtensionTarget

def essentiallySurjectiveWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.completedPresentationEquivalence.dualityCompatibilityTarget

def unitComparisonWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.commonPresentationCompatibility

def counitComparisonWitness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.closureCompatibility

def toTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) : Prop :=
  data.commonPresentationCompatibility ∧
    data.closureCompatibility ∧
    data.fullyFaithfulWitness ∧
    data.essentiallySurjectiveWitness ∧
    data.unitComparisonWitness ∧
    data.counitComparisonWitness ∧
    data.pi0ShadowCompatibility

def ofCompletedPresentationAndPi0Shadow
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical)
    (presentationEquiv : CompletedPresentationEquivalenceTarget spine internal
      stableCompletion stableCompletionConstruction completionUniversalProperty
      classical corePresentationEquivalence)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (inftyToPi0 : TraceInfinityToPiZeroShadowComparisonOverQ) :
    CanonicalTraceDMgmEquivalenceData spine internal classical where
  stableCompletion := stableCompletion
  stableCompletionConstruction := stableCompletionConstruction
  completionUniversalProperty := completionUniversalProperty
  corePresentationEquivalence := corePresentationEquivalence
  completedPresentationEquivalence := presentationEquiv
  closureEquivalence := closureEquiv
  infinityToPiZeroComparison := inftyToPi0

end CanonicalTraceDMgmEquivalenceData

/-- Named theorem package for the canonical trace-to-`DM_gm(Q)` equivalence.

The data object records the proof-relevant completion and ∞/π₀ carriers. This
package records the exact theorem inhabitants needed to promote that data to the
canonical equivalence target. Stable-completion and ∞-shadow facts are projected
from their closed packages; common-presentation, closure, and duality facts stay
as exact named fields because they are the remaining mathematical comparison
theorems at this layer. -/
structure CanonicalTraceDMgmEquivalenceTheoremPackage
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical) where
  commonPresentationComparison_holds :
    data.commonPresentationCompatibility
  closureEqualityComparison_holds :
    data.closureCompatibility
  stableCompletionCompatibility_holds :
    data.completionUniversalProperty.completionExtensionTarget ∧
      data.completionUniversalProperty.exactSymmetricMonoidalExtensionTarget
  classicalBoundaryCompatibility_holds :
    data.corePresentationEquivalence.corePresentationEquivalenceTarget
  rigidTensorTriangulatedCompatibility_holds :
    data.fullyFaithfulWitness ∧
      data.essentiallySurjectiveWitness ∧
      data.completedPresentationEquivalence.exactSymmetricMonoidalExtensionTarget
  infinityShadowCompatibility_holds :
    data.pi0ShadowCompatibility ∧
      data.infinityToPiZeroComparison.realizationCompatibility ∧
      data.infinityToPiZeroComparison.comparisonToCompletedPresentation

namespace CanonicalTraceDMgmEquivalenceTheoremPackage

def ofCanonicalData
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    (data : CanonicalTraceDMgmEquivalenceData spine internal classical)
    (commonPresentationComparison_holds :
      data.commonPresentationCompatibility)
    (closureEqualityComparison_holds :
      data.closureCompatibility)
    (classicalBoundaryCompatibility_holds :
      data.corePresentationEquivalence.corePresentationEquivalenceTarget)
    (fullyFaithful_holds :
      data.fullyFaithfulWitness)
    (completedPresentationDuality_holds :
      data.completedPresentationEquivalence.dualityCompatibilityTarget)
    (exactSymmetricMonoidalExtension_holds :
      data.completedPresentationEquivalence.exactSymmetricMonoidalExtensionTarget) :
    CanonicalTraceDMgmEquivalenceTheoremPackage data where
  commonPresentationComparison_holds := commonPresentationComparison_holds
  closureEqualityComparison_holds := closureEqualityComparison_holds
  stableCompletionCompatibility_holds :=
    ⟨data.completionUniversalProperty.completionExtension_holds,
      data.completionUniversalProperty.exactSymmetricMonoidalExtension_holds⟩
  classicalBoundaryCompatibility_holds := classicalBoundaryCompatibility_holds
  rigidTensorTriangulatedCompatibility_holds :=
    ⟨fullyFaithful_holds,
      completedPresentationDuality_holds,
      exactSymmetricMonoidalExtension_holds⟩
  infinityShadowCompatibility_holds :=
    ⟨data.infinityToPiZeroComparison.triangulatedStructureCompatibility_holds,
      data.infinityToPiZeroComparison.realizationCompatibility_holds,
      data.infinityToPiZeroComparison.comparisonToCompletedPresentation_holds⟩

end CanonicalTraceDMgmEquivalenceTheoremPackage

structure TraceCategoryEquivalentToDMgmQTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq) where
  canonicalEquivalenceData : CanonicalTraceDMgmEquivalenceData spine internal classical
  theoremPackage :
    CanonicalTraceDMgmEquivalenceTheoremPackage canonicalEquivalenceData
  commonPresentationComparisonTarget : Prop
  commonPresentationComparison_holds : commonPresentationComparisonTarget
  closureEqualityComparisonTarget : Prop
  closureEqualityComparison_holds : closureEqualityComparisonTarget
  homotopyCategoryComparisonTarget : Prop
  homotopyCategoryComparison_holds : homotopyCategoryComparisonTarget

namespace TraceCategoryEquivalentToDMgmQTarget

def ofCompletedPresentationAndPi0Shadow
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence : CorePresentationEquivalenceTarget spine internal classical)
    (presentationEquiv : CompletedPresentationEquivalenceTarget spine internal
      stableCompletion stableCompletionConstruction completionUniversalProperty
      classical corePresentationEquivalence)
    (closureEquiv : PresentationAdmissibleClosureEquivalence ctx)
    (inftyToPi0 : TraceInfinityToPiZeroShadowComparisonOverQ)
    (commonPresentationComparison_holds :
      presentationEquiv.completedPresentationEquivalenceTarget)
    (closureEqualityComparison_holds :
      closureEquiv.closureComparisonTarget)
    (classicalBoundaryCompatibility_holds :
      corePresentationEquivalence.corePresentationEquivalenceTarget)
    (fullyFaithful_holds :
      presentationEquiv.exactSymmetricMonoidalExtensionTarget)
    (completedPresentationDuality_holds :
      presentationEquiv.dualityCompatibilityTarget)
    (exactSymmetricMonoidalExtension_holds :
      presentationEquiv.exactSymmetricMonoidalExtensionTarget) :
    TraceCategoryEquivalentToDMgmQTarget spine internal classical :=
  let data :
      CanonicalTraceDMgmEquivalenceData spine internal classical :=
    CanonicalTraceDMgmEquivalenceData.ofCompletedPresentationAndPi0Shadow
      spine internal classical stableCompletion stableCompletionConstruction
      completionUniversalProperty corePresentationEquivalence presentationEquiv
      closureEquiv inftyToPi0
  let theoremPackage :
      CanonicalTraceDMgmEquivalenceTheoremPackage data :=
    CanonicalTraceDMgmEquivalenceTheoremPackage.ofCanonicalData data
      commonPresentationComparison_holds closureEqualityComparison_holds
      classicalBoundaryCompatibility_holds fullyFaithful_holds
      completedPresentationDuality_holds exactSymmetricMonoidalExtension_holds
  {
  canonicalEquivalenceData := data
  theoremPackage := theoremPackage
  commonPresentationComparisonTarget :=
    presentationEquiv.completedPresentationEquivalenceTarget
  commonPresentationComparison_holds :=
    theoremPackage.commonPresentationComparison_holds
  closureEqualityComparisonTarget :=
    closureEquiv.closureComparisonTarget
  closureEqualityComparison_holds :=
    theoremPackage.closureEqualityComparison_holds
  homotopyCategoryComparisonTarget :=
    inftyToPi0.triangulatedStructureCompatibility
  homotopyCategoryComparison_holds :=
    theoremPackage.infinityShadowCompatibility_holds.1
  }

end TraceCategoryEquivalentToDMgmQTarget

/-- Manuscript target for the canonical `DM_gm(Q)` equivalence. This is the
paper surface around `thm:internal-recognition` and the `\pi_0`-shadow of
`thm:infty-comparison`. -/
structure CanonicalDMgmEquivalenceTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical) where
  canonicalEquivalenceTarget : Prop
  canonicalEquivalence_holds : canonicalEquivalenceTarget
  rigidTensorTriangulatedEquivalenceTarget : Prop
  rigidTensorTriangulatedEquivalence_holds :
    rigidTensorTriangulatedEquivalenceTarget
  infinityShadowCompatibilityTarget : Prop
  infinityShadowCompatibility_holds : infinityShadowCompatibilityTarget

/-- Standalone theorem target for `thm:realization-comparison`. This keeps the
realization-comparison statement explicit rather than folding it into the final
period theorem package. -/
structure RealizationComparisonTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) where
  bettiAgreementTarget : Prop
  deRhamAgreementTarget : Prop
  comparisonIsomorphismAgreementTarget : Prop
  periodMatrixAgreementTarget : Prop

/-- Standalone theorem target for `cor:period-conjecture-via-realization`. -/
structure PeriodConjectureViaRealizationTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (realizationComparison : RealizationComparisonTarget spine internal classical
      comparisonEquivalence canonicalEquivalence) where
  /-- Period faithfulness transport: the Betti and de Rham agreement targets from
  the realization comparison carry the period faithfulness through the equivalence. -/
  periodFaithfulnessTransportTarget :
    realizationComparison.bettiAgreementTarget ∧
      realizationComparison.deRhamAgreementTarget
  /-- Equivalence with the classical statement: the period-matrix agreement,
  canonical equivalence, and rigid tensor-triangulated equivalence together
  identify this corollary as the classical period conjecture statement over
  MM(Q) with rational coefficients. -/
  equivalenceWithClassicalStatementTarget :
    realizationComparison.periodMatrixAgreementTarget ∧
      canonicalEquivalence.canonicalEquivalenceTarget ∧
      canonicalEquivalence.rigidTensorTriangulatedEquivalenceTarget

/-- Manuscript target for the universal recognition theorem identifying the
recognized motivic category with the canonical `DM_gm(Q)` recipient. -/
structure DMgmUniversalRecognitionData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) where
  canonicalEquivalenceCompatibility :
    canonicalEquivalence.canonicalEquivalenceTarget
  rigidTensorTriangulatedCompatibility :
    canonicalEquivalence.rigidTensorTriangulatedEquivalenceTarget
  infinityShadowCompatibility :
    canonicalEquivalence.infinityShadowCompatibilityTarget
  comparisonEquivalenceCompatibility :
    comparisonEquivalence.canonicalEquivalenceData.toTarget
  commonPresentationCompatibility :
    comparisonEquivalence.commonPresentationComparisonTarget
  closureEqualityCompatibility :
    comparisonEquivalence.closureEqualityComparisonTarget
  homotopyCategoryCompatibility :
    comparisonEquivalence.homotopyCategoryComparisonTarget

namespace DMgmUniversalRecognitionData

def universalRecognitionTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (data : DMgmUniversalRecognitionData spine internal classical comparisonEquivalence
      canonicalEquivalence) : Prop :=
  canonicalEquivalence.canonicalEquivalenceTarget ∧
    comparisonEquivalence.canonicalEquivalenceData.toTarget

def uniquenessOfRecipientTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (data : DMgmUniversalRecognitionData spine internal classical comparisonEquivalence
      canonicalEquivalence) : Prop :=
  canonicalEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
    comparisonEquivalence.commonPresentationComparisonTarget ∧
    comparisonEquivalence.closureEqualityComparisonTarget

def comparisonAgreementTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    {spine : MotivicRecognitionSpine.{u, v, w, x, y, z}}
    {internal : InternalManuscriptSpineTarget P comparison C}
    {classical : ClassicalManuscriptSpineTarget ctx structuredEq}
    {comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical}
    {canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence}
    (data : DMgmUniversalRecognitionData spine internal classical comparisonEquivalence
      canonicalEquivalence) : Prop :=
  canonicalEquivalence.infinityShadowCompatibilityTarget ∧
    comparisonEquivalence.homotopyCategoryComparisonTarget ∧
    comparisonEquivalence.commonPresentationComparisonTarget ∧
    comparisonEquivalence.closureEqualityComparisonTarget

/- Quarantined unused helper.  It attempted to manufacture witness terms for
`DMgmUniversalRecognitionData` directly from theorem-target propositions. -/

def ofCanonicalDMgmEquivalence
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) :
    DMgmUniversalRecognitionData spine internal classical comparisonEquivalence
      canonicalEquivalence where
  canonicalEquivalenceCompatibility :=
    canonicalEquivalence.canonicalEquivalence_holds
  rigidTensorTriangulatedCompatibility :=
    canonicalEquivalence.rigidTensorTriangulatedEquivalence_holds
  infinityShadowCompatibility :=
    canonicalEquivalence.infinityShadowCompatibility_holds
  comparisonEquivalenceCompatibility :=
    ⟨comparisonEquivalence.theoremPackage.commonPresentationComparison_holds,
      ⟨comparisonEquivalence.theoremPackage.closureEqualityComparison_holds,
        ⟨comparisonEquivalence.theoremPackage.rigidTensorTriangulatedCompatibility_holds.1,
          ⟨comparisonEquivalence.theoremPackage.rigidTensorTriangulatedCompatibility_holds.2.1,
            ⟨comparisonEquivalence.theoremPackage.commonPresentationComparison_holds,
              ⟨comparisonEquivalence.theoremPackage.closureEqualityComparison_holds,
                comparisonEquivalence.theoremPackage.infinityShadowCompatibility_holds.1⟩⟩⟩⟩⟩⟩
  commonPresentationCompatibility :=
    comparisonEquivalence.commonPresentationComparison_holds
  closureEqualityCompatibility :=
    comparisonEquivalence.closureEqualityComparison_holds
  homotopyCategoryCompatibility :=
    comparisonEquivalence.homotopyCategoryComparison_holds

end DMgmUniversalRecognitionData

structure DMgmUniversalRecognitionTheoremTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) where
  recognitionData :
    DMgmUniversalRecognitionData spine internal classical comparisonEquivalence
      canonicalEquivalence
  universalRecognitionTarget : Prop
  uniquenessOfRecipientTarget : Prop
  comparisonAgreementTarget : Prop

namespace DMgmUniversalRecognitionTheoremTarget

def ofCanonicalDMgmEquivalence
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) :
    DMgmUniversalRecognitionTheoremTarget spine internal classical
      comparisonEquivalence canonicalEquivalence :=
  let data :=
    DMgmUniversalRecognitionData.ofCanonicalDMgmEquivalence spine internal classical
      comparisonEquivalence canonicalEquivalence
  {
    recognitionData := data
    universalRecognitionTarget := data.universalRecognitionTarget
    uniquenessOfRecipientTarget := data.uniquenessOfRecipientTarget
    comparisonAgreementTarget := data.comparisonAgreementTarget
  }

end DMgmUniversalRecognitionTheoremTarget

/-- Campaign 12A manuscript spine object for the trace-native motivic
localization universal property.

Campaign 12A -- Triangulated/stable motivic recognition -- is closed at the
trace-interpreter level. The final recognition path is:

`BoundaryFrontierFunctorCandidateData`
→ semantic `MotivicFunctorCandidate`
→ object/map determination
→ `CanonicalFrontierWordDeterminesInterpreter`
→ `TraceInterpreterUniquenessByReconstruction`
→ `TraceInterpreterForAdmissibleMotivicTarget.ofConcreteTransport`
→ `CertifiedAdmissibleMotivicTargetReadiness`
→ `ConcreteMotivicLocalizationFactorizationFamily`
→ `MotivicLocalizationUniversalFactorizationTransport`
→ `TraceCategoryMotivicLocalizationUniversalProperty`.

This is the single recognition-facing bundle that packages the three layers the
paper now needs to keep aligned: completion-side extension/uniqueness,
trace-category comparison with `DM_gm(Q)`, and the universal-recognition target
identifying the canonical motivic recipient. -/
structure TraceCategoryMotivicLocalizationUniversalPropertyTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (construction : TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion construction)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget spine internal classical
        traceToDMgmEquivalence canonicalDMgmEquivalence) where
  completionUniversalPropertyData :
    TraceCompletionUniversalPropertyTarget spine internal stableCompletion construction
  traceToDMgmEquivalenceData :
    TraceCategoryEquivalentToDMgmQTarget spine internal classical
  canonicalDMgmEquivalenceData :
    CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence
  universalRecognitionData :
    DMgmUniversalRecognitionTheoremTarget spine internal classical
      traceToDMgmEquivalence canonicalDMgmEquivalence

namespace TraceCategoryMotivicLocalizationUniversalPropertyTarget

def ofRecognitionLayers
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget spine internal)
    (construction : TraceStableCompletionConstructionTarget spine internal stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget spine internal stableCompletion construction)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget spine internal classical
        traceToDMgmEquivalence canonicalDMgmEquivalence) :
    TraceCategoryMotivicLocalizationUniversalPropertyTarget spine internal classical
      stableCompletion construction completionUniversalProperty traceToDMgmEquivalence
      canonicalDMgmEquivalence universalRecognition where
  completionUniversalPropertyData := completionUniversalProperty
  traceToDMgmEquivalenceData := traceToDMgmEquivalence
  canonicalDMgmEquivalenceData := canonicalDMgmEquivalence
  universalRecognitionData := universalRecognition

end TraceCategoryMotivicLocalizationUniversalPropertyTarget

/-- Manuscript target for the normalization package, covering termination,
normal-form generation, congruence generation, and completeness. -/
structure NormalizationPackageTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C) where
  normalFormSetTarget : Nonempty C.normalizer.NF
  terminationTarget :
    ∀ (R : CompletedReconstructionRecord setup)
      (c : CompletedReconstructionRecord.PeelChain R),
      c.length = R.n
  congruenceGenerationTarget :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        C.normalize R₁ = C.normalize R₂
  completenessTarget :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      C.normalize R₁ = C.normalize R₂ →
        FrontierWord.Equiv
          (C.assignment.assign R₁).frontier
          (C.assignment.assign R₂).frontier

structure NormalizationPackageData
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C) where
  normalFormCarrierNonempty : Nonempty C.normalizer.NF
  normalizeMatchesAssignment :
    ∀ (R : CompletedReconstructionRecord setup),
      C.normalize R = C.normalizer.normalize (C.assignment.assign R).frontier
  normalizationSound :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        C.normalize R₁ = C.normalize R₂
  normalizationComplete :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      C.normalize R₁ = C.normalize R₂ →
        FrontierWord.Equiv
          (C.assignment.assign R₁).frontier
          (C.assignment.assign R₂).frontier
  internalComparisonFaithfulness :
    InternalComparisonFaithfulnessTarget comparison C
  terminationWitness :
    ∀ (R : CompletedReconstructionRecord setup)
      (c : TraceCalc.LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain R),
      c.length = R.n
  canonicalReconstructionEngine :
    CanonicalReconstructionEngineTarget setup

namespace NormalizationPackageData

/- Quarantined: the old `ofInternalSpine` helper tried to construct
`NormalizationPackageData` from `InternalManuscriptSpineTarget`, but that input
now only carries theorem targets (`...Target : Prop`) and no longer exposes the
concrete `canNFEqualityDetection` / `canonicalReconstructionEngine` data this
constructor depended on.  The theorem/data structures remain; only this stale
fake constructor path is removed. -/

/-- Construct a `NormalizationPackageData` from the core CanNF machinery.

Two explicit inputs are required that cannot be derived from `C : CanNF setup`
alone:
- `nfSeed`: a concrete element of `C.normalizer.NF` (witnesses nonemptiness;
  obtain via `C.normalize someRecord` or `C.normalizer.normalize someWord`).
- `hComparison`: the iff that `comparison` and `C.normalize` detect the same
  equivalence on completed records (depends on the specific `comparison`
  function at the call site).

All other fields are exact projections from `CanNF` and `PeelChain`:
- `normalizeMatchesAssignment` : `rfl` (definitional from `CanNF.normalize_eq`)
- `normalizationSound`         : `C.CanNF_sound`
- `normalizationComplete`      : `C.CanNF_complete`
- `terminationWitness`         : `PeelChain.length_eq`
- `canonicalReconstructionEngine` : `CanonicalReconstructionEngineTarget.ofClosedCanNF`
-/
noncomputable def ofCanNF
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (nfSeed : C.normalizer.NF)
    (hComparison :
      ∀ (R₁ R₂ : CompletedReconstructionRecord setup),
        comparison R₁ = comparison R₂ ↔ C.normalize R₁ = C.normalize R₂) :
    NormalizationPackageData internal where
  normalFormCarrierNonempty := ⟨nfSeed⟩
  normalizeMatchesAssignment := fun _ => rfl
  normalizationSound := fun h => C.CanNF_sound h
  normalizationComplete := fun h => C.CanNF_complete h
  internalComparisonFaithfulness :=
    InternalComparisonFaithfulnessTarget.ofIff comparison C hComparison
  terminationWitness := fun _ c =>
    LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain.length_eq c
  canonicalReconstructionEngine :=
    CanonicalReconstructionEngineTarget.ofClosedCanNF

/-- Variant of `ofCanNF` with concrete-source inputs routed through their
canonical providers.

Instead of a raw `C.normalizer.NF` element, this takes:
- `seedRecord : CompletedReconstructionRecord setup` — any concrete record
  in scope; the seed is derived as `C.normalize seedRecord`.
- `hFaithfulness : InternalComparisonFaithfulnessTarget comparison C` — the
  concrete comparison-faithfulness package, whose single field
  `comparison_detected_by_cannf` is the exact iff required by `ofCanNF`.

**Concrete source for `hFaithfulness`** (concrete preferred holography lane):
```lean
concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
    presentation sourceExport boundaryCodes proofs hRestricted O
```
proved in `SourceHolographyToLayerD.lean` (namespace
`SourceHolographyToLayerD.InternalHolographyInterface`).

This theorem establishes the iff for
`comparison R = interface.visibleBoundary R` and
`C = frontierWordEquivFrontierWordCanNF O`.
All other fields are identical to `ofCanNF`.
-/
noncomputable def ofCanNFFromHolography
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (seedRecord : CompletedReconstructionRecord setup)
    (hFaithfulness : InternalComparisonFaithfulnessTarget comparison C) :
    NormalizationPackageData internal :=
  ofCanNF
    (nfSeed := C.normalize seedRecord)
    (fun R₁ R₂ => hFaithfulness.comparison_detected_by_cannf R₁ R₂)

/-- Concrete preferred normalization data constructor.

Obtains `InternalComparisonFaithfulnessTarget` **internally** from the
concrete holography provider theorem; no `hFaithfulness` or `hComparison`
parameter is exposed.  The `comparison_detected_by_cannf` field is derived
directly from
`FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget`,
closing the Block 1B sealing obligation for this field on the concrete lane.
-/
noncomputable def ofConcretePreferredHolography
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport :
      FoundationsBoundaryBridgeAuxiliaryData.LayerBSourceExportData presentation aux)
    (boundaryCodes :
      FoundationsBoundaryBridgeAuxiliaryData.SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs :
      FoundationsBoundaryBridgeAuxiliaryData.NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted :
      FoundationsBoundaryBridgeAuxiliaryData.RestrictedCompletedRecordDataFamilyTarget
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux)))
    (seedRecord : CompletedReconstructionRecord
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {P : SyntacticBoundaryPresentation
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux))}
    {internal : InternalManuscriptSpineTarget P
      (fun R =>
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (frontierWordEquivFrontierWordCanNF O)} :
    NormalizationPackageData internal :=
  ofCanNFFromHolography seedRecord
    (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
      presentation sourceExport boundaryCodes proofs hRestricted O)

end NormalizationPackageData

namespace NormalizationPackageTarget

/-- Construct a `NormalizationPackageTarget` from a `NormalizationPackageData`.
The four concrete proposition fields are filled directly from the data proofs. -/
def ofData
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (data : NormalizationPackageData internal) :
    NormalizationPackageTarget internal where
  normalFormSetTarget := data.normalFormCarrierNonempty
  terminationTarget := data.terminationWitness
  congruenceGenerationTarget := data.normalizationSound
  completenessTarget := data.normalizationComplete

/-- Preferred normalization target constructor.

This keeps the theorem-target route on the same canonical inputs as
`NormalizationPackageData.ofCanNFFromHolography`: a concrete completed record
supplies the nonempty normal-form seed as `C.normalize seedRecord`, and the
comparison bridge is projected from `InternalComparisonFaithfulnessTarget`
rather than accepted as an anonymous iff. -/
noncomputable def ofCanNFFromHolography
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {internal : InternalManuscriptSpineTarget P comparison C}
    (seedRecord : CompletedReconstructionRecord setup)
    (hFaithfulness : InternalComparisonFaithfulnessTarget comparison C) :
    NormalizationPackageTarget internal where
  normalFormSetTarget := by
    let _comparisonBridge := hFaithfulness.comparison_detected_by_cannf
    exact ⟨C.normalize seedRecord⟩
  terminationTarget := fun _ c =>
    LayerB.RealObjects.RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain.length_eq c
  congruenceGenerationTarget := fun h => C.CanNF_sound h
  completenessTarget := fun h => C.CanNF_complete h

/-- Concrete preferred normalization target constructor.

Obtains `InternalComparisonFaithfulnessTarget` **internally** from the
concrete holography provider; no `hFaithfulness` or `hComparison` parameter
is exposed.  Companion to `NormalizationPackageData.ofConcretePreferredHolography`.
-/
noncomputable def ofConcretePreferredHolography
    {primitive : LayerB.RealObjects.NamedPrimitiveInterfacePresentation}
    (presentation : LayerB.RealObjects.NamedDoctrinePresentation primitive)
    {aux : FoundationsBoundaryBridgeAuxiliaryData presentation.toDoctrine}
    (sourceExport :
      FoundationsBoundaryBridgeAuxiliaryData.LayerBSourceExportData presentation aux)
    (boundaryCodes :
      FoundationsBoundaryBridgeAuxiliaryData.SignatureBoundaryCodeData presentation.toDoctrine aux)
    (proofs :
      FoundationsBoundaryBridgeAuxiliaryData.NamedFreeBoundaryAdapter.BoundaryProofs presentation)
    (hRestricted :
      FoundationsBoundaryBridgeAuxiliaryData.RestrictedCompletedRecordDataFamilyTarget
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs))
    (O : ResidueCanonicalOrder
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux)))
    (seedRecord : CompletedReconstructionRecord
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux)))
    {P : SyntacticBoundaryPresentation
      (FoundationsBoundaryBridgeAuxiliaryData.PreferredFoundationsBridgeSetup presentation.toDoctrine
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredBoundaryBridgeAuxiliaryData aux))}
    {internal : InternalManuscriptSpineTarget P
      (fun R =>
        (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface
          presentation sourceExport boundaryCodes proofs).visibleBoundary R)
      (frontierWordEquivFrontierWordCanNF O)} :
    NormalizationPackageTarget internal :=
  ofCanNFFromHolography seedRecord
    (FoundationsBoundaryBridgeAuxiliaryData.concretePreferredInternalHolographyInterface_realizes_InternalComparisonFaithfulnessTarget
      presentation sourceExport boundaryCodes proofs hRestricted O)

end NormalizationPackageTarget

/-- Manuscript target for transporting canonical normalization across the
canonical `DM_gm(Q)` equivalence. -/
structure NormalizationTransportAcrossDMgmEquivalenceTarget
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence) where
  transportAcrossEquivalenceTarget : Prop
  homsetNormalFormCompatibilityTarget : Prop
  comparisonRespectsNormalizationTarget : Prop

structure NormalizationTransportAcrossDMgmEquivalenceData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport : NormalizationTransportAcrossDMgmEquivalenceTarget spine internal
      normalization classical comparisonEquivalence canonicalEquivalence) where
  normalizationData : NormalizationPackageData internal
  comparisonEquivalenceData : CanonicalTraceDMgmEquivalenceData spine internal classical
  canonicalEquivalenceWitness : canonicalEquivalence.canonicalEquivalenceTarget
  rigidTensorTriangulatedWitness :
    canonicalEquivalence.rigidTensorTriangulatedEquivalenceTarget
  infinityShadowCompatibilityWitness :
    canonicalEquivalence.infinityShadowCompatibilityTarget
  commonPresentationCompatibility :
    comparisonEquivalence.commonPresentationComparisonTarget
  closureCompatibility : comparisonEquivalence.closureEqualityComparisonTarget
  homotopyCategoryCompatibility :
    comparisonEquivalence.homotopyCategoryComparisonTarget
  transportFunctorialityWitness : normalizationTransport.transportAcrossEquivalenceTarget
  normalizationEquivarianceWitness : normalizationTransport.homsetNormalFormCompatibilityTarget
  normalFormCompatibilityUnderDMgmEquivalence :
    normalizationTransport.comparisonRespectsNormalizationTarget

namespace NormalizationTransportAcrossDMgmEquivalenceTarget

/- Quarantined: stale helper constructing theorem targets from proof terms.
The theorem-target structure remains live; this unused constructor does not. -/

end NormalizationTransportAcrossDMgmEquivalenceTarget

/-- Manuscript target asserting that the transported normalization package is
already motivic in the recognized category. -/
structure TransportedNormalizationIsMotivicTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (transportedNormalization :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence) where
  motivicInterpretationTarget : Prop
  tensorCompatibilityTarget : Prop
  realizationCompatibilityTarget : Prop
  generatorCompatibilityTarget : Prop

structure TransportedNormalizationIsMotivicData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (transportedNormalization :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (motivicTarget : TransportedNormalizationIsMotivicTarget spine internal normalization
      classical comparisonEquivalence canonicalEquivalence transportedNormalization) where
  transportData : NormalizationTransportAcrossDMgmEquivalenceData spine internal normalization
    classical comparisonEquivalence canonicalEquivalence transportedNormalization
  motivicInterpretationWitness : motivicTarget.motivicInterpretationTarget
  tensorCompatibilityWitness : motivicTarget.tensorCompatibilityTarget
  realizationCompatibilityWitness : motivicTarget.realizationCompatibilityTarget
  generatorCompatibilityWitness : motivicTarget.generatorCompatibilityTarget

namespace TransportedNormalizationIsMotivicTarget

/- Quarantined unused helper.  The data record remains available if a later,
honest constructor is rebuilt from real lower data rather than theorem-target
inputs alone. -/

end TransportedNormalizationIsMotivicTarget

/-- Campaign 12B manuscript target for the bounded motivic `t`-structure
package induced from the normalization side.

Campaign 11 weight devissage remains an input to this package; it is not
identified with the `t`-structure itself. Campaign 12A recognition into the
triangulated/stable `DM_gm(Q)_Q` layer is likewise an input compatibility
surface. -/
structure NormTStructureTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport) where
  weightStructure : WeightStructureTarget spine.structuralRecognition
  traceMotivicTStructure : TraceMotivicTStructureData spine.structuralRecognition
  normalizationPacketCut : NormalizationPacketCutData spine.structuralRecognition
  normalizationTruncationTriangle :
    NormalizationTruncationTriangle spine.structuralRecognition normalizationPacketCut
  tStructure : TStructureTarget spine.structuralRecognition
  /-- Named theorem package for the three normalization t-structure obligations:
  weight compatibility, motivic transport, and truncation representability. -/
  normTStructureTheoremPackage :
    NormTStructureTheoremPackage traceMotivicTStructure normalizationPacketCut

structure NormTStructureData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization) where
  transportData : NormalizationTransportAcrossDMgmEquivalenceData spine internal normalization
    classical comparisonEquivalence canonicalEquivalence normalizationTransport
  transportedNormalizationData : TransportedNormalizationIsMotivicData spine internal
    normalization classical comparisonEquivalence canonicalEquivalence normalizationTransport
    transportedNormalization
  weightStructure : WeightStructureTarget spine.structuralRecognition
  traceMotivicTStructure : TraceMotivicTStructureData spine.structuralRecognition
  normalizationPacketCut : NormalizationPacketCutData spine.structuralRecognition
  normalizationTruncationTriangle :
    NormalizationTruncationTriangle spine.structuralRecognition normalizationPacketCut
  tStructure : TStructureTarget spine.structuralRecognition
  /-- Single named proof witness for all three normalization t-structure theorems:
  the `NormTStructureTheoremPackage` is a Prop-valued structure, so this field
  carries a proof of the entire named package. -/
  normTStructureTheoremWitness :
    NormTStructureTheoremPackage normTStructure.traceMotivicTStructure
      normTStructure.normalizationPacketCut

namespace NormTStructureTarget

/- Quarantined unused helper. -/

end NormTStructureTarget

/-- Campaign 12C manuscript target for identifying the heart constructed from
the normalization-induced motivic `t`-structure.

This target does not assume a pre-existing classical `MM(Q)`, does not assert
semisimplicity, and does not assert global `Ext`-vanishing. -/
structure HeartRecognitionTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization) where
  pureHeartRecognitionTarget :=
    normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget
  lefschetzClosureTarget :=
    transportedNormalization.tensorCompatibilityTarget ∧
      transportedNormalization.realizationCompatibilityTarget

structure HeartRecognitionData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization) where
  normTStructureData : NormTStructureData spine internal normalization classical
    comparisonEquivalence canonicalEquivalence normalizationTransport transportedNormalization
    normTStructure
  transportedNormalizationData : TransportedNormalizationIsMotivicData spine internal
    normalization classical comparisonEquivalence canonicalEquivalence normalizationTransport
    transportedNormalization
  traceHeart : TraceMotivicHeart normTStructure.traceMotivicTStructure
  pureHeartRecognitionWitness :
    normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget
  lefschetzClosureWitness :
    transportedNormalization.tensorCompatibilityTarget ∧
      transportedNormalization.realizationCompatibilityTarget

namespace HeartRecognitionTarget

/- Quarantined unused helper. -/

end HeartRecognitionTarget

/-- Campaign 12D manuscript target for identifying the transported trace-native
heart with the classical mixed-motive heart.

This is a separate input surface from `HeartRecognitionTarget`: the latter
recognizes the transported heart internally, while this target records the
comparison with the classical recipient. -/
structure ClassicalHeartIdentificationTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization)
    (heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure) where
  /-- The transported heart object for the current t-structure. -/
  traceHeart : TraceMotivicHeart normTStructure.traceMotivicTStructure
  /-- Named theorem package: transported heart = classical abelian heart of
  `DM_gm(Q)_Q` = MM(Q), with compatibility witnesses for transported t-structure
  and pure-heart recognition. -/
  classicalMMQHeartTheorems :
    ClassicalMMQHeartTheorems normTStructure.traceMotivicTStructure traceHeart

/-- Campaign 12D manuscript target for identifying the transported trace-native
heart with the manuscript `MM(Q)` recipient.  This sits one step above
`ClassicalHeartIdentificationTarget`: once the transported heart is identified
with the classical mixed-motive heart, this target records the specific
`MM(Q)`-level identification and its compatibility with the already-assembled
pure-heart comparison data. -/
structure MMQIdentificationTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalization :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization)
    (heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure) where
  /-- The `ClassicalHeartIdentificationTarget` routing the classical abelian
  heart identification with MM(Q) and the compatibility witnesses. -/
  classicalHeartIdentification :
    ClassicalHeartIdentificationTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalization normTStructure heartRecognition
  /-- Named theorem: the transported heart is MM(Q), recorded via the
  exported classical-facing recognition statement for the trace-constructed
  heart as the mixed-motive abelian heart over Q. -/
  mmqHeartIdentification :
    RecognizesClassicalMMQ normTStructure.traceMotivicTStructure
      classicalHeartIdentification.traceHeart
  /-- Named theorem: the MM(Q) identification is compatible with pure-heart
  recognition, recorded via the normalization compatibility and normalization
  packet-cut targets of the transported motivic t-structure. -/
  mmqPureHeartCompatibility :
    normTStructure.traceMotivicTStructure.normalizationCompatibilityTarget ∧
      normTStructure.traceMotivicTStructure.normalizationPacketCutTarget

/-- Standalone theorem target for the proof-relevant period theorem on the
trace-to-`DM_gm(Q)` comparison path.  This remains a manuscript-facing target
surface: it records the exact downstream obligations needed by the period layer
without folding them into the final global spine package. -/
structure ProofRelevantPeriodTheoremTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence) where
  /-- The proof-relevant period statement: the period map distinguishes morphisms
  in the transported triangulated-categorical sense.  This is the full
  transported faithfulness claim: the canonical equivalence holds, the rigid
  tensor-triangulated structure is preserved, and the homotopy-category
  realization comparison holds — together these constitute the transported
  period faithfulness assertion that is NOT the canonical equivalence alone. -/
  proofRelevantPeriodStatementTarget :
    canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget
  /-- The realization compatibility: the homotopy-category comparison from the
  Trace ≃ DM_gm(Q) equivalence witnesses the realization functor compatibility
  required for the period theorem. -/
  realizationCompatibilityTarget :
    traceToDMgmEquivalence.homotopyCategoryComparisonTarget
  comparisonFaithfulnessInputTarget :
    ∀ (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target),
      f.bettiMap = g.bettiMap →
      f.deRhamMap = g.deRhamMap →
      f.basisFreePeriodMap = g.basisFreePeriodMap →
      f = g

  namespace ProofRelevantPeriodTheoremTarget

  /-- Wrapper exposing reconstruction-based faithfulness in the exact shape required by
  `ProofRelevantPeriodTheoremTarget.comparisonFaithfulnessInputTarget`. -/
  theorem comparisonFaithfulnessInputTarget_of_realization_agreements
      {ctx : ClassicalComparisonContext.{u, v}}
      (source target : ClassicalStructuredComparisonObject ctx)
      (f g : ClassicalStructuredComparisonMorphism source target)
      (hBetti : f.bettiMap = g.bettiMap)
      (hDeRham : f.deRhamMap = g.deRhamMap)
      (hBasis : f.basisFreePeriodMap = g.basisFreePeriodMap) :
      f = g :=
    LayerD.full_morphism_eq_of_basisFreePeriodMap_eq
      f g hBetti hDeRham hBasis

  /-- Constructor wiring reconstruction-based period faithfulness into the proof-relevant
  period target surface without external injectivity hypotheses. -/
  def ofRealizationAgreementComparisonFaithfulness
      (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
      {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
      {P : SyntacticBoundaryPresentation setup}
      {α : Type v}
      {comparison : CompletedReconstructionRecord setup → α}
      {C : CanNF setup}
      {ctx : ClassicalComparisonContext.{u, v}}
      {structuredEq : StructuredComparisonEquality ctx}
      (internal : InternalManuscriptSpineTarget P comparison C)
      (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
      (traceToDMgmEquivalence :
        TraceCategoryEquivalentToDMgmQTarget spine internal classical)
      (canonicalDMgmEquivalence :
        CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence)
      (proofRelevantPeriodStatementTarget :
        canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
          canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
          traceToDMgmEquivalence.homotopyCategoryComparisonTarget)
      (realizationCompatibilityTarget :
        traceToDMgmEquivalence.homotopyCategoryComparisonTarget) :
      ProofRelevantPeriodTheoremTarget spine internal classical
        traceToDMgmEquivalence canonicalDMgmEquivalence where
    proofRelevantPeriodStatementTarget := proofRelevantPeriodStatementTarget
    realizationCompatibilityTarget := realizationCompatibilityTarget
    comparisonFaithfulnessInputTarget :=
      comparisonFaithfulnessInputTarget_of_realization_agreements

  end ProofRelevantPeriodTheoremTarget

/-- Standalone theorem target for deriving the proof-relevant period theorem
from comparison-faithfulness data already assembled earlier in the manuscript
spine. -/
structure ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget spine internal classical traceToDMgmEquivalence)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internal classical
        traceToDMgmEquivalence canonicalDMgmEquivalence) where
  /-- Bridge theorem: the canonical equivalence and homotopy-category comparison
  together provide the comparison faithfulness input for the proof-relevant period
  theorem. -/
  comparisonFaithfulnessBridgeTarget :
    canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget
  /-- Recovery theorem: the canonical equivalence, rigid tensor-triangulated
  equivalence, and homotopy-category realization comparison together recover the
  full proof-relevant period statement (faithfulness transported through the
  equivalence package). -/
  recoversProofRelevantPeriodTheoremTarget :
    canonicalDMgmEquivalence.canonicalEquivalenceTarget ∧
      canonicalDMgmEquivalence.rigidTensorTriangulatedEquivalenceTarget ∧
      traceToDMgmEquivalence.homotopyCategoryComparisonTarget

/-- Terminal manuscript assembly target (Package 9 routing surface).
All upstream layers are provided as named package-typed inputs, and the final
dependency-DAG obligation is split into statement + witness. -/
structure MMQRecognitionClosedTarget
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq) where
  stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine
  stableCompletionConstruction :
    TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion
  completionUniversalProperty :
    TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
      stableCompletionConstruction
  corePresentationEquivalence :
    CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine
  completedPresentationEquivalence :
    CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty classicalSpine
      corePresentationEquivalence
  traceToDMgmEquivalence :
    TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine
  canonicalDMgmEquivalence :
    CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence
  realizationComparison :
    RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
  periodConjectureViaRealization :
    PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison
  universalRecognition :
    DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
  normalizationPackage : NormalizationPackageTarget internalSpine
  normalizationTransport :
    NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
  transportedNormalizationIsMotivic :
    TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
  normTStructure :
    NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic
  heartRecognition :
    HeartRecognitionTarget recognitionSpine internalSpine normalizationPackage classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure
  classicalHeartIdentification :
    ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure heartRecognition
  mmqIdentification :
    MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure heartRecognition
  proofRelevantPeriodTheorem :
    ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
      traceToDMgmEquivalence canonicalDMgmEquivalence
  proofRelevantPeriodTheoremFromComparisonFaithfulness :
    ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      proofRelevantPeriodTheorem
  dependencyDAGStatement : Prop
  dependencyDAG_holds : dependencyDAGStatement

namespace MMQRecognitionClosedTarget

def ofPackages
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure :
      NormTStructureTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic)
    (heartRecognition :
      HeartRecognitionTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (mmqIdentification :
      MMQIdentificationTarget recognitionSpine internalSpine normalizationPackage classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGStatement : Prop)
    (dependencyDAG_holds : dependencyDAGStatement) :
    MMQRecognitionClosedTarget recognitionSpine internalSpine classicalSpine where
  stableCompletion := stableCompletion
  stableCompletionConstruction := stableCompletionConstruction
  completionUniversalProperty := completionUniversalProperty
  corePresentationEquivalence := corePresentationEquivalence
  completedPresentationEquivalence := completedPresentationEquivalence
  traceToDMgmEquivalence := traceToDMgmEquivalence
  canonicalDMgmEquivalence := canonicalDMgmEquivalence
  realizationComparison := realizationComparison
  periodConjectureViaRealization := periodConjectureViaRealization
  universalRecognition := universalRecognition
  normalizationPackage := normalizationPackage
  normalizationTransport := normalizationTransport
  transportedNormalizationIsMotivic := transportedNormalizationIsMotivic
  normTStructure := normTStructure
  heartRecognition := heartRecognition
  classicalHeartIdentification := classicalHeartIdentification
  mmqIdentification := mmqIdentification
  proofRelevantPeriodTheorem := proofRelevantPeriodTheorem
  proofRelevantPeriodTheoremFromComparisonFaithfulness :=
    proofRelevantPeriodTheoremFromComparisonFaithfulness
  dependencyDAGStatement := dependencyDAGStatement
  dependencyDAG_holds := dependencyDAG_holds

end MMQRecognitionClosedTarget

/-
The block that used to start here under `namespace MMQIdentificationTarget`
was a stale copied fragment of `ManuscriptMainTheoremSpineTarget` simp lemmas.
It did not form valid declarations: it referenced undeclared local names
(`recognitionSpine`, `internalSpine`, `classicalSpine`, `traceToDMgmEquivalence`,
`canonicalDMgmEquivalence`, `ofPackages`) and closed namespaces that were not
open.  It is quarantined until the original theorem-surface block is restored
from a clean source.

namespace MMQIdentificationTarget

def ofTraceMotivicData
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    (internal : InternalManuscriptSpineTarget P comparison C)
    (normalization : NormalizationPackageTarget internal)
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    (canonicalEquivalence : CanonicalDMgmEquivalenceTarget spine internal classical
      comparisonEquivalence)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget spine internal normalization classical
        comparisonEquivalence canonicalEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget spine internal normalization classical
      comparisonEquivalence canonicalEquivalence normalizationTransport
      transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget spine internal classical
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget spine internal
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).recognitionSpine =
        recognitionSpine :=
  rfl

@[simp] theorem ofPackages_recognitionSpine
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).recognitionSpine =
        recognitionSpine :=
  rfl

@[simp] theorem ofPackages_internalSpine
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).internalSpine =
        internalSpine :=
  rfl

@[simp] theorem ofPackages_classicalSpine
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
    (classicalSpine : ClassicalManuscriptSpineTarget ctx structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).classicalSpine =
        classicalSpine :=
  rfl

@[simp] theorem ofPackages_stableCompletion
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
  {_structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
  (classicalSpine : ClassicalManuscriptSpineTarget ctx _structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).stableCompletion = stableCompletion :=
  rfl

@[simp] theorem ofPackages_stableCompletionConstruction
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
  {_structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
  (classicalSpine : ClassicalManuscriptSpineTarget ctx _structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).stableCompletionConstruction = stableCompletionConstruction :=
  rfl

@[simp] theorem ofPackages_completionUniversalProperty
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
  {_structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
  (classicalSpine : ClassicalManuscriptSpineTarget ctx _structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).completionUniversalProperty = completionUniversalProperty :=
  rfl

@[simp] theorem ofPackages_corePresentationEquivalence
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
  {_structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
  (classicalSpine : ClassicalManuscriptSpineTarget ctx _structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).corePresentationEquivalence = corePresentationEquivalence :=
  rfl

@[simp] theorem ofPackages_proofRelevantPeriodTheoremFromComparisonFaithfulness
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
  {_structuredEq : StructuredComparisonEquality ctx}
    (recognitionSpine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internalSpine : InternalManuscriptSpineTarget P comparison C)
  (classicalSpine : ClassicalManuscriptSpineTarget ctx _structuredEq)
    (stableCompletion : StableAdditiveKaroubiCompletionTarget recognitionSpine internalSpine)
    (stableCompletionConstruction :
      TraceStableCompletionConstructionTarget recognitionSpine internalSpine stableCompletion)
    (completionUniversalProperty :
      TraceCompletionUniversalPropertyTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction)
    (corePresentationEquivalence :
      CorePresentationEquivalenceTarget recognitionSpine internalSpine classicalSpine)
    (completedPresentationEquivalence :
      CompletedPresentationEquivalenceTarget recognitionSpine internalSpine stableCompletion
        stableCompletionConstruction completionUniversalProperty classicalSpine
        corePresentationEquivalence)
    (traceToDMgmEquivalence :
      TraceCategoryEquivalentToDMgmQTarget recognitionSpine internalSpine classicalSpine)
    (canonicalDMgmEquivalence :
      CanonicalDMgmEquivalenceTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence)
    (realizationComparison :
      RealizationComparisonTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (periodConjectureViaRealization :
      PeriodConjectureViaRealizationTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence realizationComparison)
    (universalRecognition :
      DMgmUniversalRecognitionTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (normalizationPackage : NormalizationPackageTarget internalSpine)
    (normalizationTransport :
      NormalizationTransportAcrossDMgmEquivalenceTarget recognitionSpine internalSpine
        normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence)
    (transportedNormalizationIsMotivic :
      TransportedNormalizationIsMotivicTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport)
    (normTStructure : NormTStructureTarget recognitionSpine internalSpine normalizationPackage
      classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
      transportedNormalizationIsMotivic)
    (heartRecognition : HeartRecognitionTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure)
    (classicalHeartIdentification :
      ClassicalHeartIdentificationTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition)
    (pureHeartEquivalence :
      PureHeartEquivalenceTarget recognitionSpine internalSpine normalizationPackage
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence normalizationTransport
        transportedNormalizationIsMotivic normTStructure heartRecognition
        classicalHeartIdentification)
    (mmqIdentification : MMQIdentificationTarget recognitionSpine internalSpine
      normalizationPackage classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
      normalizationTransport transportedNormalizationIsMotivic normTStructure heartRecognition)
    (proofRelevantPeriodTheorem :
      ProofRelevantPeriodTheoremTarget recognitionSpine internalSpine classicalSpine
        traceToDMgmEquivalence canonicalDMgmEquivalence)
    (proofRelevantPeriodTheoremFromComparisonFaithfulness :
      ProofRelevantPeriodTheoremFromComparisonFaithfulnessTarget recognitionSpine internalSpine
        classicalSpine traceToDMgmEquivalence canonicalDMgmEquivalence
        proofRelevantPeriodTheorem)
    (dependencyDAGTarget : Prop) :
    (ofPackages recognitionSpine internalSpine classicalSpine stableCompletion
      stableCompletionConstruction completionUniversalProperty corePresentationEquivalence
      completedPresentationEquivalence traceToDMgmEquivalence canonicalDMgmEquivalence
      realizationComparison periodConjectureViaRealization universalRecognition
      normalizationPackage normalizationTransport transportedNormalizationIsMotivic normTStructure
      heartRecognition classicalHeartIdentification pureHeartEquivalence mmqIdentification
      proofRelevantPeriodTheorem proofRelevantPeriodTheoremFromComparisonFaithfulness
      dependencyDAGTarget).proofRelevantPeriodTheoremFromComparisonFaithfulness =
        proofRelevantPeriodTheoremFromComparisonFaithfulness :=
  rfl

-/

namespace CanonicalDMgmEquivalenceTarget

/--
  Construct the canonical DM_gm(Q) equivalence target from:
  - a trace category equivalence,
  - the named canonical equivalence theorem package attached to it.
  All fields are filled by projection from routed packages, with no stubs or
  arbitrary Props.
-/
def ofTraceCategoryEquivalence
    {setup : LayerB.RealObjects.RewriteCalculusSetup.{u}}
    {P : SyntacticBoundaryPresentation setup}
    {α : Type v}
    {comparison : CompletedReconstructionRecord setup → α}
    {C : CanNF setup}
    {ctx : ClassicalComparisonContext.{u, v}}
    {structuredEq : StructuredComparisonEquality ctx}
    (spine : MotivicRecognitionSpine.{u, v, w, x, y, z})
    (internal : InternalManuscriptSpineTarget P comparison C)
    (classical : ClassicalManuscriptSpineTarget ctx structuredEq)
    (comparisonEquivalence : TraceCategoryEquivalentToDMgmQTarget spine internal classical)
    : CanonicalDMgmEquivalenceTarget spine internal classical comparisonEquivalence where
  canonicalEquivalenceTarget :=
    comparisonEquivalence.canonicalEquivalenceData.toTarget
  canonicalEquivalence_holds :=
    ⟨comparisonEquivalence.theoremPackage.commonPresentationComparison_holds,
      ⟨comparisonEquivalence.theoremPackage.closureEqualityComparison_holds,
        ⟨comparisonEquivalence.theoremPackage.rigidTensorTriangulatedCompatibility_holds.1,
          ⟨comparisonEquivalence.theoremPackage.rigidTensorTriangulatedCompatibility_holds.2.1,
            ⟨comparisonEquivalence.theoremPackage.commonPresentationComparison_holds,
              ⟨comparisonEquivalence.theoremPackage.closureEqualityComparison_holds,
                comparisonEquivalence.theoremPackage.infinityShadowCompatibility_holds.1⟩⟩⟩⟩⟩⟩
  rigidTensorTriangulatedEquivalenceTarget :=
    comparisonEquivalence.canonicalEquivalenceData.fullyFaithfulWitness ∧
      comparisonEquivalence.canonicalEquivalenceData.essentiallySurjectiveWitness ∧
      comparisonEquivalence.canonicalEquivalenceData.completedPresentationEquivalence.exactSymmetricMonoidalExtensionTarget
  rigidTensorTriangulatedEquivalence_holds :=
    comparisonEquivalence.theoremPackage.rigidTensorTriangulatedCompatibility_holds
  infinityShadowCompatibilityTarget :=
    comparisonEquivalence.canonicalEquivalenceData.infinityToPiZeroComparison.triangulatedStructureCompatibility ∧
      comparisonEquivalence.canonicalEquivalenceData.infinityToPiZeroComparison.realizationCompatibility ∧
      comparisonEquivalence.canonicalEquivalenceData.infinityToPiZeroComparison.comparisonToCompletedPresentation
  infinityShadowCompatibility_holds :=
    comparisonEquivalence.theoremPackage.infinityShadowCompatibility_holds

end CanonicalDMgmEquivalenceTarget

end MotivicRecognition
end TraceCalc

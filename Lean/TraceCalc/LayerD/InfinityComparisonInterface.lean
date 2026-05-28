import TraceCalc.LayerD.DMgmQInterface
import TraceCalc.LayerD.MotivicRecognition.InfinityEnhancementSurface
import TraceCalc.LayerD.UniversalProperty

universe u v w x y z

namespace TraceCalc
namespace LayerD

open MotivicRecognition

/-- Generic proof-relevant stable infinity-category surface used on the Layer D
comparison lane.

Layer E already packages this surface as `TraceInfinityEnhancementOverQ`.  The
Layer D comparison story needs the same sort of object twice: once for the
source `T^∞_can`, and once for the target recipient `DM_gm^∞(Q)`.  This abbrev
gives that common semantic role a neutral name at the comparison layer. -/
abbrev StableInfinityCategoryOverQ :=
  TraceInfinityEnhancementOverQ.{u, v, w}

/-- Explicit functor-shaped comparison datum between proof-relevant stable
infinity-category surfaces.

This is the concrete interface for the manuscript's `T^∞_can → DM_gm^∞(Q)`
comparison functor: object and mapping assignments, compatibility with `π₀`,
and the exact/stable/monoidal theorem frontiers the comparison theorem must
ultimately prove. -/
structure StableInfinityFunctorOverQ
    (source : StableInfinityCategoryOverQ.{u, v, w})
    (target : StableInfinityCategoryOverQ.{u, v, w}) where
  obj : source.Obj → target.Obj
  map :
    ∀ {X Y : source.Obj},
      source.Mapping X Y → target.Mapping (obj X) (obj Y)
  mapPi0 :
    ∀ {X Y : source.Obj},
      source.Pi0Hom X Y → target.Pi0Hom (obj X) (obj Y)
  pi0Compatibility :
    ∀ {X Y : source.Obj} (f : source.Mapping X Y),
      target.pi0Class (map f) = mapPi0 (source.pi0Class f)
  exactnessCompatibility : Prop
  stableCompatibility : Prop
  symmetricMonoidalCompatibility : Prop
  realizationCompatibility : Prop

/-- Canonical Layer D recipient interface for the stable infinity category
`DM_gm^∞(Q)`.

This does not assert that the target has already been constructed from the
quotient-zigzag/Karoubi spine.  Instead it names the exact data a construction
must eventually provide:

* the proof-relevant stable infinity-category surface,
* its comparison with the already-defined `π₀`-level `DM_gm(Q)_Q` interface,
* and the concrete recognition statements inherited from the certified classical
  target package.

Theorems downstream of Layer D can therefore depend on one canonical target
object instead of loose `Prop` placeholders. -/
structure DMgmInfinityQInterface where
  piZeroInterface : DMgmQPiZeroInterface.{u, v, w, x, y, z}
  infinityCategory : StableInfinityCategoryOverQ.{u, v, w}
  piZeroObjectComparison :
    infinityCategory.Obj → piZeroInterface.presentation.motivicCategory.Object
  piZeroHomComparison :
    ∀ {X Y : infinityCategory.Obj},
      infinityCategory.Pi0Hom X Y →
        piZeroInterface.presentation.motivicCategory.Hom
          (piZeroObjectComparison X)
          (piZeroObjectComparison Y)
  shiftCompatibility : Prop
  cofiberCompatibility : Prop
  tensorCompatibility : Prop
  realizationCompatibility : Prop

namespace DMgmInfinityQInterface

/-- The `π₀` recipient recognized by the infinity interface is exactly the
certified classical `DM_gm(Q)_Q` interface already carried by Layer D. -/
def piZeroRecognitionStatement
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) : Prop :=
  iface.piZeroInterface.piZeroRecognitionStatement

theorem piZeroRecognition_holds
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) :
    iface.piZeroRecognitionStatement :=
  iface.piZeroInterface.piZeroRecognition_holds

/-- The idempotent-complete infinity-side recognition statement inherited from
the certified `DM_gm(Q)_Q` recipient. -/
def infinityRecognitionStatement
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) : Prop :=
  iface.piZeroInterface.infinityRecognitionStatement

theorem infinityRecognition_holds
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) :
    iface.infinityRecognitionStatement :=
  iface.piZeroInterface.infinityRecognition_holds

/-- The target-side universal-property recognition statement inherited from the
certified classical recipient. -/
def universalPropertyRecognitionStatement
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) : Prop :=
  iface.piZeroInterface.universalPropertyRecognitionStatement

theorem universalPropertyRecognition_holds
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) :
    iface.universalPropertyRecognitionStatement :=
  iface.piZeroInterface.universalPropertyRecognition_holds

/-- The rational-field realization statement inherited from the `π₀`-level
recipient interface. -/
def realizationStructureRecognitionStatement
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) : Prop :=
  iface.piZeroInterface.realizationStructureRecognitionStatement

theorem realizationStructureRecognition_holds
    (iface : DMgmInfinityQInterface.{u, v, w, x, y, z}) :
    iface.realizationStructureRecognitionStatement :=
  ⟨⟨iface.piZeroInterface.target.baseFieldIsQTarget⟩,
    ⟨iface.piZeroInterface.target.coefficientFieldIsQTarget⟩⟩

end DMgmInfinityQInterface

/-- Layer D formalization of the Robalo-style universal property for the
candidate `DM_gm^∞(Q)` recipient.

The source-side initiality contract is already defined generically in
`UniversalProperty.lean`.  This structure records the additional comparison-side
information needed for the infinity comparison theorem: which admissible
frontier realization lands in the candidate recipient, and how the infinity
initiality contract projects to the `π₀` shadow. -/
structure RobaloUniversalPropertyInterface
    (ML : LayerB.MotivicLocalization.{u, v})
    (target : DMgmInfinityQInterface.{u, v, w, x, y, z}) where
  recipientRealization : AdmissibleFrontierRealization ML
  recipientScope :
    recipientRealization.scope = FrontierRealizationScope.allLocalizedObjects
  recipientExactnessCompatibility : recipientRealization.exactnessCompatibility
  recipientMonoidalCompatibility : recipientRealization.monoidalCompatibility
  recipientIdempotentCompatibility :
    recipientRealization.idempotentCompletionCompatibility
  infinityInitiality : FrontierInfinityInitialityContract ML
  shadowContract : FrontierInfinityToPiZeroShadowContract ML
  recipientComparisonCompatibility : Prop

namespace RobaloUniversalPropertyInterface

def ofPiZeroInitialityAndLifts
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (recipientRealization : AdmissibleFrontierRealization ML)
    (recipientScope :
      recipientRealization.scope = FrontierRealizationScope.allLocalizedObjects)
    (recipientExactnessCompatibility : recipientRealization.exactnessCompatibility)
    (recipientMonoidalCompatibility : recipientRealization.monoidalCompatibility)
    (recipientIdempotentCompatibility :
      recipientRealization.idempotentCompletionCompatibility)
    (piZeroInitiality : FrontierPiZeroInitialityContract ML)
    (liftData : FrontierInfinityLiftData ML)
    (reflection : FrontierInfinityReflectionData ML)
    (recipientComparisonCompatibility : Prop) :
    RobaloUniversalPropertyInterface ML target where
  recipientRealization := recipientRealization
  recipientScope := recipientScope
  recipientExactnessCompatibility := recipientExactnessCompatibility
  recipientMonoidalCompatibility := recipientMonoidalCompatibility
  recipientIdempotentCompatibility := recipientIdempotentCompatibility
  infinityInitiality :=
    FrontierInfinityInitialityContract.ofPiZeroInitialityAndLifts
      piZeroInitiality liftData reflection
  shadowContract := FrontierInfinityToPiZeroShadowContract.ofLiftData liftData
  recipientComparisonCompatibility := recipientComparisonCompatibility

def piZeroUniversalPropertyStatement
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) : Prop :=
  U.infinityInitiality.piZero.initialityStatement

theorem piZeroUniversalProperty_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) :
    U.piZeroUniversalPropertyStatement :=
  FrontierInfinityInitialityContract.piZero_initialityStatement U.infinityInitiality

def infinityUniversalPropertyStatement
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) : Prop :=
  U.infinityInitiality.initialityStatement

theorem infinityUniversalProperty_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) :
    U.infinityUniversalPropertyStatement :=
  FrontierInfinityInitialityContract.initialityStatement_of_contract U.infinityInitiality

/-- Exact statement behind the `factorizationShadowExtraction` item in the Layer D
comparison package: every `π₀` factorization is the shadow of some infinity
factorization. -/
def factorizationShadowExtractionStatement
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) : Prop :=
  ∀ (R : AdmissibleFrontierRealization ML)
    (F : FrontierPiZeroFactorization ML R),
      Nonempty { FInf : FrontierInfinityFactorization ML R //
        U.shadowContract.shadow FInf = F }

theorem factorizationShadowExtraction_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (U : RobaloUniversalPropertyInterface ML target) :
    U.factorizationShadowExtractionStatement := by
  intro R F
  exact U.shadowContract.liftsPiZero F

theorem ofPiZeroInitialityAndLifts_piZeroUniversalProperty_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (recipientRealization : AdmissibleFrontierRealization ML)
    (recipientScope :
      recipientRealization.scope = FrontierRealizationScope.allLocalizedObjects)
    (recipientExactnessCompatibility : recipientRealization.exactnessCompatibility)
    (recipientMonoidalCompatibility : recipientRealization.monoidalCompatibility)
    (recipientIdempotentCompatibility :
      recipientRealization.idempotentCompletionCompatibility)
    (piZeroInitiality : FrontierPiZeroInitialityContract ML)
    (liftData : FrontierInfinityLiftData ML)
    (reflection : FrontierInfinityReflectionData ML)
    (recipientComparisonCompatibility : Prop) :
    RobaloUniversalPropertyInterface.piZeroUniversalPropertyStatement
      (ofPiZeroInitialityAndLifts (target := target)
        recipientRealization recipientScope recipientExactnessCompatibility
        recipientMonoidalCompatibility recipientIdempotentCompatibility
        piZeroInitiality liftData reflection recipientComparisonCompatibility) :=
  FrontierPiZeroInitialityContract.initialityStatement_of_contract _

theorem ofPiZeroInitialityAndLifts_infinityUniversalProperty_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    {target : DMgmInfinityQInterface.{u, v, w, x, y, z}}
    (recipientRealization : AdmissibleFrontierRealization ML)
    (recipientScope :
      recipientRealization.scope = FrontierRealizationScope.allLocalizedObjects)
    (recipientExactnessCompatibility : recipientRealization.exactnessCompatibility)
    (recipientMonoidalCompatibility : recipientRealization.monoidalCompatibility)
    (recipientIdempotentCompatibility :
      recipientRealization.idempotentCompletionCompatibility)
    (piZeroInitiality : FrontierPiZeroInitialityContract ML)
    (liftData : FrontierInfinityLiftData ML)
    (reflection : FrontierInfinityReflectionData ML)
    (recipientComparisonCompatibility : Prop) :
    RobaloUniversalPropertyInterface.infinityUniversalPropertyStatement
      (ofPiZeroInitialityAndLifts (target := target)
        recipientRealization recipientScope recipientExactnessCompatibility
        recipientMonoidalCompatibility recipientIdempotentCompatibility
        piZeroInitiality liftData reflection recipientComparisonCompatibility) :=
  FrontierInfinityInitialityContract.initialityStatement_of_contract _

end RobaloUniversalPropertyInterface

/-- Named higher-rigidity frontier for the witness families appearing in the
full infinity conservativity theorem.

The paper's remaining obstruction is not ordinary `π₀` faithfulness: it is the
higher boundary-rigidity needed to upgrade witness families from shadow data to
mapping-spectrum-level conservativity.  This structure records that exact
obligation surface family-by-family, without pretending those theorems are
already available. -/
structure HigherBoundaryRigidityTarget
    (source : StableInfinityCategoryOverQ.{u, v, w}) where
  WitnessFamily : Type x
  familyCarrier : WitnessFamily → source.Obj
  higherBoundaryRigidity : WitnessFamily → Prop
  mappingSpectrumConservativityTarget :
    ∀ family : WitnessFamily,
      higherBoundaryRigidity family → Prop
  exactTriangleConservativityTarget :
    ∀ family : WitnessFamily,
      higherBoundaryRigidity family → Prop
  monoidalConservativityTarget :
    ∀ family : WitnessFamily,
      higherBoundaryRigidity family → Prop

namespace HigherBoundaryRigidityTarget

def allFamiliesRigidStatement
    {source : StableInfinityCategoryOverQ.{u, v, w}}
    (rigidity : HigherBoundaryRigidityTarget.{u, v, w, x} source) : Prop :=
  ∀ family : rigidity.WitnessFamily, rigidity.higherBoundaryRigidity family

end HigherBoundaryRigidityTarget

/-- Canonical Layer D bundle for the two remaining top comparison theorems.

This is the comparison-facing object that should feed any future honest proof of

* `T^∞_can ≃ DM_gm^∞(Q)`, and
* full infinity conservativity of the realization functor.

It keeps the source infinity enhancement, target infinity recipient, comparison
functor, Robalo-style universal property, and higher boundary rigidity in one
place. -/
structure InfinityComparisonInterface
    (ML : LayerB.MotivicLocalization.{u, v}) where
  source : StableInfinityCategoryOverQ.{u, v, w}
  target : DMgmInfinityQInterface.{u, v, w, x, y, z}
  comparisonFunctor : StableInfinityFunctorOverQ source target.infinityCategory
  robaloUniversalProperty : RobaloUniversalPropertyInterface ML target
  higherBoundaryRigidity : HigherBoundaryRigidityTarget source

namespace InfinityComparisonInterface

def infinityComparisonStatement
    {ML : LayerB.MotivicLocalization.{u, v}}
    (I : InfinityComparisonInterface.{u, v, w, x, y, z} ML) : Prop :=
  I.target.infinityRecognitionStatement ∧
    I.target.universalPropertyRecognitionStatement ∧
    I.robaloUniversalProperty.infinityUniversalPropertyStatement ∧
    I.comparisonFunctor.exactnessCompatibility ∧
    I.comparisonFunctor.stableCompatibility ∧
    I.comparisonFunctor.symmetricMonoidalCompatibility

def fullInfinityConservativityStatement
    {ML : LayerB.MotivicLocalization.{u, v}}
    (I : InfinityComparisonInterface.{u, v, w, x, y, z} ML) : Prop :=
  I.infinityComparisonStatement ∧
    HigherBoundaryRigidityTarget.allFamiliesRigidStatement
      I.higherBoundaryRigidity

end InfinityComparisonInterface

end LayerD
end TraceCalc
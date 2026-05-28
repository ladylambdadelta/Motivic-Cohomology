import TraceCalc.LayerD.InfinityComparisonInterface
import TraceCalc.LayerE.MotivicRecognition.SyntacticDMgmClassicalBridge

universe u v w x y z

namespace TraceCalc
namespace LayerD

open MotivicRecognition
open CategoryInfra.SyntacticTraceDMgm
open CategoryInfra.SyntacticInfinity

/-- Canonical constructive candidate for `DM_gm^∞(Q)` coming from the existing
syntactic stable infinity enhancement. -/
def canonicalDMgmInfinityCategory
    (syntacticPresentation : Type u) :
    StableInfinityCategoryOverQ.{u, u, u} :=
  syntacticInfinityEnhancement syntacticPresentation

/-- The existing constructive `∞ → π₀` comparison extracted from the canonical
syntactic infinity enhancement. -/
def canonicalDMgmInfinityToPiZeroComparison
    (syntacticPresentation : Type u) :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  syntacticDMgm_p5InfinityToPiZeroComparison syntacticPresentation

/-- The object-level comparison from the canonical infinity candidate to the
classical `DM_gm(Q)_Q` recipient induced by the Package 6 interpretation. -/
def canonicalDMgmInfinityObjectComparison
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (canonicalDMgmInfinityCategory syntacticPresentation).Obj →
      iface.presentation.motivicCategory.Object :=
  fun X =>
    interp.interpretObj
      ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)

/-- The `π₀`-morphism comparison from the canonical infinity candidate to the
classical `DM_gm(Q)_Q` recipient induced by the Package 6 interpretation. -/
def canonicalDMgmInfinityPiZeroHomComparison
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    ∀ {X Y : (canonicalDMgmInfinityCategory syntacticPresentation).Obj},
      (canonicalDMgmInfinityCategory syntacticPresentation).Pi0Hom X Y →
        iface.presentation.motivicCategory.Hom
          (canonicalDMgmInfinityObjectComparison interp X)
          (canonicalDMgmInfinityObjectComparison interp Y) :=
  fun f => interp.interpretPi0 f

def canonicalDMgmInfinityShiftCompatibilityStatement
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  ∀ X : (canonicalDMgmInfinityCategory syntacticPresentation).Obj,
    interp.interpretObj
        (DMgmObj.shift
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)) =
      interp.classicalShiftObj
        (interp.interpretObj
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X))

theorem canonicalDMgmInfinityShiftCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    canonicalDMgmInfinityShiftCompatibilityStatement interp := by
  intro X
  simpa using
    interp.shiftObjPreservation
      ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)

def canonicalDMgmInfinityCofiberCompatibilityStatement
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  (∀ X Y : (canonicalDMgmInfinityCategory syntacticPresentation).Obj,
      interp.interpretObj
          (DMgmObj.cofiber
            ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)
            ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y)) =
        interp.classicalCofiberObj
          (interp.interpretObj
            ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X))
          (interp.interpretObj
            ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y))) ∧
    (canonicalDMgmInfinityToPiZeroComparison syntacticPresentation).triangulatedStructureCompatibility

theorem canonicalDMgmInfinityCofiberCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    canonicalDMgmInfinityCofiberCompatibilityStatement interp := by
  refine ⟨?_, ?_⟩
  · intro X Y
    simpa using
      interp.cofiberObjPreservation
        ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)
        ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y)
  · exact p5InfinityToPiZeroTriangulatedWitness syntacticPresentation

def canonicalDMgmInfinityTensorCompatibilityStatement
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  ∀ X Y : (canonicalDMgmInfinityCategory syntacticPresentation).Obj,
    interp.interpretObj
        (DMgmObj.tensor
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y)) =
      interp.classicalTensorObj
        (interp.interpretObj
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X))
        (interp.interpretObj
          ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y))

theorem canonicalDMgmInfinityTensorCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    canonicalDMgmInfinityTensorCompatibilityStatement interp := by
  intro X Y
  simpa using
    interp.tensorObjPreservation
      ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison X)
      ((concreteTraceToDMgmComparisonTarget syntacticPresentation).objectComparison Y)

def canonicalDMgmInfinityRealizationCompatibilityStatement
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) : Prop :=
  syntacticDMgm_piZeroCompatibilityStatement interp ∧
    (canonicalDMgmInfinityToPiZeroComparison syntacticPresentation).realizationCompatibility ∧
    (canonicalDMgmInfinityToPiZeroComparison syntacticPresentation).comparisonToCompletedPresentation

theorem canonicalDMgmInfinityRealizationCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    canonicalDMgmInfinityRealizationCompatibilityStatement interp := by
  exact ⟨piZeroCompatibilityTargetWitnessFromInterpretation interp,
    p5InfinityToPiZeroRealizationWitness syntacticPresentation,
    p5InfinityToPiZeroCompletedPresentationWitness syntacticPresentation⟩

namespace DMgmInfinityQInterface

/-- Constructive `DM_gm^∞(Q)` recipient extracted from Package 5/6 data.

The infinity category is the existing syntactic stable enhancement; the map to
the classical recipient is the already-defined recursive interpretation into the
certified `DM_gm(Q)_Q` target. -/
def ofSyntacticInterpretationData
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    DMgmInfinityQInterface.{u, v, w, x, y, z} where
  piZeroInterface := iface
  infinityCategory := canonicalDMgmInfinityCategory syntacticPresentation
  piZeroObjectComparison := canonicalDMgmInfinityObjectComparison interp
  piZeroHomComparison := canonicalDMgmInfinityPiZeroHomComparison interp
  shiftCompatibility := canonicalDMgmInfinityShiftCompatibilityStatement interp
  cofiberCompatibility := canonicalDMgmInfinityCofiberCompatibilityStatement interp
  tensorCompatibility := canonicalDMgmInfinityTensorCompatibilityStatement interp
  realizationCompatibility := canonicalDMgmInfinityRealizationCompatibilityStatement interp

/-- Sealed-source constructor for `DM_gm^∞(Q)` using the strengthened classical
interface as the concrete receiving-side operation package. -/
def ofClassicalOperationsData
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (data : ClassicalDMgmQOperationsData syntacticPresentation iface) :
    DMgmInfinityQInterface.{u, v, w, x, y, z} :=
  ofSyntacticInterpretationData
    (SyntacticDMgmClassicalInterpretationData.ofClassicalOperationsData data)

/-- Sealed-source constructor for `DM_gm^∞(Q)` using the strengthened classical
interface as the concrete receiving-side operation package. -/
def ofSealedSources
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}) :
    DMgmInfinityQInterface.{u, v, w, x, y, z} :=
  ofClassicalOperationsData
    (ClassicalDMgmQOperationsData.ofSealedSources syntacticPresentation iface)

theorem ofSyntacticInterpretationData_shiftCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (ofSyntacticInterpretationData interp).shiftCompatibility :=
  canonicalDMgmInfinityShiftCompatibility_holds interp

theorem ofSyntacticInterpretationData_cofiberCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (ofSyntacticInterpretationData interp).cofiberCompatibility :=
  canonicalDMgmInfinityCofiberCompatibility_holds interp

theorem ofSyntacticInterpretationData_tensorCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (ofSyntacticInterpretationData interp).tensorCompatibility :=
  canonicalDMgmInfinityTensorCompatibility_holds interp

theorem ofSyntacticInterpretationData_realizationCompatibility_holds
    {syntacticPresentation : Type u}
    {iface : DMgmQPiZeroInterface.{u, v, w, x, y, z}}
    (interp : SyntacticDMgmClassicalInterpretationData syntacticPresentation iface) :
    (ofSyntacticInterpretationData interp).realizationCompatibility :=
  canonicalDMgmInfinityRealizationCompatibility_holds interp

end DMgmInfinityQInterface

namespace StableInfinityFunctorOverQ

/-- Identity comparison functor on the canonical syntactic infinity category.

This is the concrete source-to-target comparison map for the current canonical
candidate: both sides are the same proof-relevant infinity category, while the
nontrivial mathematics is carried by the recipient interpretation into the
classical `DM_gm(Q)_Q` shadow. -/
def canonicalIdentityOnSyntacticDMgmInfinity
    (syntacticPresentation : Type u) :
    StableInfinityFunctorOverQ
      (canonicalDMgmInfinityCategory syntacticPresentation)
      (canonicalDMgmInfinityCategory syntacticPresentation) where
  obj := fun X => X
  map := fun f => f
  mapPi0 := fun f => f
  pi0Compatibility := by
    intro X Y f
    rfl
  exactnessCompatibility :=
    ∀ {X Y : (canonicalDMgmInfinityCategory syntacticPresentation).Obj}
      (f : (canonicalDMgmInfinityCategory syntacticPresentation).Mapping X Y),
      Nonempty
        ((canonicalDMgmInfinityCategory syntacticPresentation).distinguishedTriangle
          X Y
          ((canonicalDMgmInfinityCategory syntacticPresentation).cofiberObj
            ((canonicalDMgmInfinityCategory syntacticPresentation).pi0Class f)))
  stableCompatibility :=
    TraceInfinityTriangulatedStructureLaw
      (canonicalDMgmInfinityCategory syntacticPresentation)
  symmetricMonoidalCompatibility :=
    TraceInfinityMonoidalCompatibilityLaw
      (canonicalDMgmInfinityCategory syntacticPresentation)
  realizationCompatibility :=
    TraceInfinityRealizationCompatibilityLaw
      (canonicalDMgmInfinityCategory syntacticPresentation)

theorem canonicalIdentityOnSyntacticDMgmInfinity_exactness_holds
    (syntacticPresentation : Type u) :
    (canonicalIdentityOnSyntacticDMgmInfinity syntacticPresentation).exactnessCompatibility := by
  intro X Y f
  exact (syntacticInfinityTheoremPackage syntacticPresentation).cofiberTriangle f

theorem canonicalIdentityOnSyntacticDMgmInfinity_stable_holds
    (syntacticPresentation : Type u) :
    (canonicalIdentityOnSyntacticDMgmInfinity syntacticPresentation).stableCompatibility :=
  (syntacticInfinityTheoremPackage syntacticPresentation).triangulatedStructure

theorem canonicalIdentityOnSyntacticDMgmInfinity_monoidal_holds
    (syntacticPresentation : Type u) :
    (canonicalIdentityOnSyntacticDMgmInfinity syntacticPresentation).symmetricMonoidalCompatibility :=
  (syntacticInfinityTheoremPackage syntacticPresentation).monoidalCompatibility

theorem canonicalIdentityOnSyntacticDMgmInfinity_realization_holds
    (syntacticPresentation : Type u) :
    (canonicalIdentityOnSyntacticDMgmInfinity syntacticPresentation).realizationCompatibility :=
  (syntacticInfinityTheoremPackage syntacticPresentation).realizationCompatibility

end StableInfinityFunctorOverQ

namespace InfinityComparisonInterface

/-- Canonical assembly of the global infinity-comparison bundle from the
constructive Package 5/6 recipient and the still-open Robalo/rigidity inputs.

This is the honest staging point for the top comparison theorems: the infinity
category, the recipient, and the comparison functor are now concrete; only the
universal-property and higher-rigidity mathematics remain as explicit inputs. -/
def ofSyntacticSealedSources
    {ML : LayerB.MotivicLocalization.{u, v}}
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (robalo :
      RobaloUniversalPropertyInterface ML
        (DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface))
    (rigidity :
      HigherBoundaryRigidityTarget
        (canonicalDMgmInfinityCategory syntacticPresentation)) :
    InfinityComparisonInterface.{u, v, w, x, y, z} ML where
  source := canonicalDMgmInfinityCategory syntacticPresentation
  target := DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface
  comparisonFunctor :=
    StableInfinityFunctorOverQ.canonicalIdentityOnSyntacticDMgmInfinity
      syntacticPresentation
  robaloUniversalProperty := robalo
  higherBoundaryRigidity := rigidity

theorem ofSyntacticSealedSources_comparisonFunctor_exactness_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (robalo :
      RobaloUniversalPropertyInterface ML
        (DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface))
    (rigidity :
      HigherBoundaryRigidityTarget
        (canonicalDMgmInfinityCategory syntacticPresentation)) :
    (ofSyntacticSealedSources syntacticPresentation iface robalo rigidity).comparisonFunctor
      .exactnessCompatibility :=
  StableInfinityFunctorOverQ.canonicalIdentityOnSyntacticDMgmInfinity_exactness_holds
    syntacticPresentation

theorem ofSyntacticSealedSources_comparisonFunctor_stable_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (robalo :
      RobaloUniversalPropertyInterface ML
        (DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface))
    (rigidity :
      HigherBoundaryRigidityTarget
        (canonicalDMgmInfinityCategory syntacticPresentation)) :
    (ofSyntacticSealedSources syntacticPresentation iface robalo rigidity).comparisonFunctor
      .stableCompatibility :=
  StableInfinityFunctorOverQ.canonicalIdentityOnSyntacticDMgmInfinity_stable_holds
    syntacticPresentation

theorem ofSyntacticSealedSources_comparisonFunctor_monoidal_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (robalo :
      RobaloUniversalPropertyInterface ML
        (DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface))
    (rigidity :
      HigherBoundaryRigidityTarget
        (canonicalDMgmInfinityCategory syntacticPresentation)) :
    (ofSyntacticSealedSources syntacticPresentation iface robalo rigidity).comparisonFunctor
      .symmetricMonoidalCompatibility :=
  StableInfinityFunctorOverQ.canonicalIdentityOnSyntacticDMgmInfinity_monoidal_holds
    syntacticPresentation

theorem ofSyntacticSealedSources_comparisonFunctor_realization_holds
    {ML : LayerB.MotivicLocalization.{u, v}}
    (syntacticPresentation : Type u)
    (iface : DMgmQPiZeroInterface.{u, v, w, x, y, z})
    (robalo :
      RobaloUniversalPropertyInterface ML
        (DMgmInfinityQInterface.ofSealedSources syntacticPresentation iface))
    (rigidity :
      HigherBoundaryRigidityTarget
        (canonicalDMgmInfinityCategory syntacticPresentation)) :
    (ofSyntacticSealedSources syntacticPresentation iface robalo rigidity).comparisonFunctor
      .realizationCompatibility :=
  StableInfinityFunctorOverQ.canonicalIdentityOnSyntacticDMgmInfinity_realization_holds
    syntacticPresentation

end InfinityComparisonInterface

end LayerD
end TraceCalc
import TraceCalc.LayerE.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerALegacy.Extensions.SyntacticInfinityEnhancement

universe u

namespace TraceCalc
namespace MotivicRecognition

open CategoryInfra.SyntacticInfinity

abbrev ConcreteInfEnhancement :=
  TraceInfinityEnhancementOverQ.{u, u, u}

def concreteInfinityEnhancementTarget (presentation : Type u)
    [PresentationQuiver presentation] :
    StableInfinityEnhancementTarget presentation :=
  StableInfinityEnhancementTarget.syntactic presentation

def concreteInfinityEnhancementData (presentation : Type u)
    [PresentationQuiver presentation] :
    StableInfinityEnhancementData (concreteInfinityEnhancementTarget presentation) :=
  StableInfinityEnhancementData.syntactic presentation

structure Pi0CategoryLawCarrier (presentation : Type u)
    [PresentationQuiver presentation] where
  leftId :
    ∀ {X Y : InfObj presentation}
      (f : CategoryInfra.SyntacticInfinity.Pi0Hom X Y),
      CategoryInfra.SyntacticInfinity.compPi0
        (CategoryInfra.SyntacticInfinity.idPi0 X) f = f
  rightId :
    ∀ {X Y : InfObj presentation}
      (f : CategoryInfra.SyntacticInfinity.Pi0Hom X Y),
      CategoryInfra.SyntacticInfinity.compPi0 f
        (CategoryInfra.SyntacticInfinity.idPi0 Y) = f
  assoc :
    ∀ {W X Y Z : InfObj presentation}
      (f : CategoryInfra.SyntacticInfinity.Pi0Hom W X)
      (g : CategoryInfra.SyntacticInfinity.Pi0Hom X Y)
      (h : CategoryInfra.SyntacticInfinity.Pi0Hom Y Z),
      CategoryInfra.SyntacticInfinity.compPi0
          (CategoryInfra.SyntacticInfinity.compPi0 f g) h =
        CategoryInfra.SyntacticInfinity.compPi0 f
          (CategoryInfra.SyntacticInfinity.compPi0 g h)

structure TriangulatedLawCarrier (presentation : Type u)
  [PresentationQuiver presentation] where
  rotate :
    ∀ {X Y Z : InfObj presentation},
      DistinguishedTriangle X Y Z →
        DistinguishedTriangle Y Z (CategoryInfra.SyntacticInfinity.shiftObj X)

structure MonoidalLawCarrier (presentation : Type u)
  [PresentationQuiver presentation] where
  tensorId :
    ∀ A C : InfObj presentation,
      CategoryInfra.SyntacticInfinity.tensorPi0
          (CategoryInfra.SyntacticInfinity.idPi0 A)
          (CategoryInfra.SyntacticInfinity.idPi0 C) =
        CategoryInfra.SyntacticInfinity.idPi0
          (CategoryInfra.SyntacticInfinity.tensorObj A C)

inductive TriangleWitness : Type where
  | cofiber
  | fiber
  | rotate
  | cofiberComp

namespace TraceInfinityEnhancementOverQ

def ofStableInfinityEnhancementPackage (presentation : Type u)
  [PresentationQuiver presentation] :
    ConcreteInfEnhancement where
  Obj := (concreteInfinityEnhancementTarget presentation).Obj
  Mapping := (concreteInfinityEnhancementTarget presentation).category.Mapping
  Pi0Hom := (concreteInfinityEnhancementTarget presentation).category.Pi0Hom
  pi0Class := (concreteInfinityEnhancementTarget presentation).category.pi0Class
  idPi0 := (concreteInfinityEnhancementTarget presentation).category.idPi0
  compPi0 := (concreteInfinityEnhancementTarget presentation).category.compPi0
  categoryLaws := (concreteInfinityEnhancementTarget presentation).category.categoryLaws
  identityCompatibilityWitness :=
    ⟨(concreteInfinityEnhancementData presentation).categoryData.categoryLawsWitness.1,
      (concreteInfinityEnhancementData presentation).categoryData.categoryLawsWitness.2.1⟩
  compositionCompatibilityWitness :=
    (concreteInfinityEnhancementData presentation).categoryData.categoryLawsWitness.2.2
  shiftObj := (concreteInfinityEnhancementTarget presentation).shift.shiftObj
  shiftMapPi0 := (concreteInfinityEnhancementTarget presentation).shift.shiftMapPi0
  shiftCompatibilityWitness :=
    (concreteInfinityEnhancementData presentation).shiftData.shiftCompatibilityWitness
  cofiberObj := (concreteInfinityEnhancementTarget presentation).triangulated.cofiberObj
  fiberObj := (concreteInfinityEnhancementTarget presentation).triangulated.fiberObj
  distinguishedTriangle := (concreteInfinityEnhancementTarget presentation).triangulated.distinguishedTriangle
  cofiberTriangle := fun f =>
    Classical.choice
      ((concreteInfinityEnhancementData presentation).triangulatedData.cofiberTriangleCompatibilityWitness f)
  fiberTriangle := fun f =>
    Classical.choice
      ((concreteInfinityEnhancementData presentation).triangulatedData.fiberTriangleCompatibilityWitness f)
  cofiberTriangleCompatibilityWitness :=
    (concreteInfinityEnhancementData presentation).triangulatedData.cofiberCompositionCompatibilityWitness
  triangulatedAxioms := (concreteInfinityEnhancementTarget presentation).triangulated.rotationCompatibility
  triangulatedStructureCompatibilityWitness := by
    exact (concreteInfinityEnhancementData presentation).triangulatedData.rotationCompatibilityWitness
  tensorObj := (concreteInfinityEnhancementTarget presentation).monoidal.tensorObj
  tensorPi0 := (concreteInfinityEnhancementTarget presentation).monoidal.tensorPi0
  monoidalAxioms := (concreteInfinityEnhancementTarget presentation).monoidal.monoidalCompatibility
  monoidalCompatibilityWitness :=
    (concreteInfinityEnhancementData presentation).monoidalData.monoidalCompatibilityWitness
  realizationCompatibility :=
    (concreteInfinityEnhancementTarget presentation).realization.identityCompatibility ∧
      (concreteInfinityEnhancementTarget presentation).realization.compositionCompatibility ∧
      (concreteInfinityEnhancementTarget presentation).realization.shiftCompatibility ∧
      (concreteInfinityEnhancementTarget presentation).realization.triangulatedCompatibility ∧
      (concreteInfinityEnhancementTarget presentation).realization.monoidalCompatibility
  realizationCompatibility_holds := by
    exact ⟨(concreteInfinityEnhancementData presentation).realizationData.identityCompatibilityWitness,
      (concreteInfinityEnhancementData presentation).realizationData.compositionCompatibilityWitness,
      (concreteInfinityEnhancementData presentation).realizationData.shiftCompatibilityWitness,
      (concreteInfinityEnhancementData presentation).realizationData.triangulatedCompatibilityWitness,
      (concreteInfinityEnhancementData presentation).realizationData.monoidalCompatibilityWitness⟩
  completedPresentationCompatibility :=
    (concreteInfinityEnhancementTarget presentation).completedPresentation.compatibilityWithCompletedPresentation ∧
      (concreteInfinityEnhancementTarget presentation).completedPresentation.compatibilityWithLocalization
  completedPresentationCompatibility_holds := by
    exact ⟨(concreteInfinityEnhancementData presentation).completedPresentationData.compatibilityWithCompletedPresentationWitness,
      (concreteInfinityEnhancementData presentation).completedPresentationData.compatibilityWithLocalizationWitness⟩

end TraceInfinityEnhancementOverQ

def syntacticInfinityEnhancement (presentation : Type u)
  [PresentationQuiver presentation] :
    ConcreteInfEnhancement :=
  TraceInfinityEnhancementOverQ.ofStableInfinityEnhancementPackage presentation

namespace TraceInfinityEnhancementTheoremPackage

def ofSyntacticInfinityEnhancement (presentation : Type u)
    [PresentationQuiver presentation] :
    TraceInfinityEnhancementTheoremPackage
      (syntacticInfinityEnhancement presentation) :=
  TraceInfinityEnhancementTheoremPackage.ofEnhancement
    (syntacticInfinityEnhancement presentation)

end TraceInfinityEnhancementTheoremPackage

def syntacticInfinityTheoremPackage (presentation : Type u)
    [PresentationQuiver presentation] :
    TraceInfinityEnhancementTheoremPackage
      (syntacticInfinityEnhancement presentation) :=
  TraceInfinityEnhancementTheoremPackage.ofSyntacticInfinityEnhancement presentation

def syntacticPi0Shadow (presentation : Type u)
    [PresentationQuiver presentation] :
    TracePi0TriangulatedShadowOverQ :=
  TracePi0TriangulatedShadowOverQ.ofInfinityEnhancement
    (syntacticInfinityEnhancement presentation)
    (syntacticInfinityTheoremPackage presentation)

namespace TracePi0TriangulatedShadowOverQ

def ofSyntacticInfinityEnhancement (presentation : Type u)
  [PresentationQuiver presentation] :
    TracePi0TriangulatedShadowOverQ :=
  syntacticPi0Shadow presentation

end TracePi0TriangulatedShadowOverQ

def syntacticInfinityToPi0Comparison (presentation : Type u)
    [PresentationQuiver presentation] :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  TraceInfinityToPiZeroShadowComparisonOverQ.ofInfinityEnhancement
    (syntacticInfinityEnhancement presentation)
    (syntacticInfinityTheoremPackage presentation)

namespace TraceInfinityToPiZeroShadowComparisonOverQ

def ofSyntacticInfinityEnhancement (presentation : Type u)
  [PresentationQuiver presentation] :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  syntacticInfinityToPi0Comparison presentation

end TraceInfinityToPiZeroShadowComparisonOverQ

end MotivicRecognition
end TraceCalc

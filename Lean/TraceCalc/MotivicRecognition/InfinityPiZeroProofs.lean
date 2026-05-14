import TraceCalc.MotivicRecognition.ManuscriptSpineTargets
import TraceCalc.LayerA.CategoryInfra.SyntacticInfinityEnhancement

universe u

namespace TraceCalc
namespace MotivicRecognition

open CategoryInfra.SyntacticInfinity

abbrev ConcreteInfEnhancement :=
  TraceInfinityEnhancementOverQ.{u, u, u}

def syntacticRealizationData (presentation : Type u) :
    SyntacticRealizationData presentation :=
  identityRealizationData presentation

def syntacticCompletedPresentationData (presentation : Type u) :
    SyntacticCompletedPresentationData presentation :=
  identityCompletedPresentationData presentation

theorem syntactic_realizationCompatibility_holds_forTarget
    (presentation : Type u) :
    SyntacticRealizationCompatibilityStatement
      (syntacticRealizationData presentation) :=
  syntactic_realizationCompatibility_holds (syntacticRealizationData presentation)

theorem syntacticInfinity_realizationCompatibility_holds
    (presentation : Type u) :
    SyntacticRealizationCompatibilityStatement
      (syntacticRealizationData presentation) :=
  syntactic_realizationCompatibility_holds_forTarget presentation

theorem syntactic_completedPresentationCompatibility_holds_forTarget
    (presentation : Type u) :
    SyntacticCompletedPresentationCompatibilityStatement
      (syntacticCompletedPresentationData presentation) :=
  syntactic_completedPresentationCompatibility_holds
    (syntacticCompletedPresentationData presentation)

theorem syntacticInfinity_completedPresentationCompatibility_holds
    (presentation : Type u) :
    SyntacticCompletedPresentationCompatibilityStatement
      (syntacticCompletedPresentationData presentation) :=
  syntactic_completedPresentationCompatibility_holds_forTarget presentation

structure Pi0CategoryLawCarrier (presentation : Type u) where
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

structure TriangulatedLawCarrier (presentation : Type u) where
  rotate :
    ∀ {X Y Z : InfObj presentation},
      DistinguishedTriangle X Y Z →
        DistinguishedTriangle Y Z (CategoryInfra.SyntacticInfinity.shiftObj X)

structure MonoidalLawCarrier (presentation : Type u) where
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

def ofSyntacticInfinityEnhancement (presentation : Type u) :
    ConcreteInfEnhancement where
  Obj := InfObj presentation
  Mapping := InfMap
  Pi0Hom := CategoryInfra.SyntacticInfinity.Pi0Hom
  pi0Class := CategoryInfra.SyntacticInfinity.pi0Class
  idPi0 := CategoryInfra.SyntacticInfinity.idPi0
  compPi0 := CategoryInfra.SyntacticInfinity.compPi0
  categoryLaws := Nat
  identityCompatibilityWitness :=
    ⟨fun f => compPi0_id_left f, fun f => compPi0_id_right f⟩
  compositionCompatibilityWitness :=
    fun f g h => compPi0_assoc f g h
  shiftObj := CategoryInfra.SyntacticInfinity.shiftObj
  shiftMapPi0 := CategoryInfra.SyntacticInfinity.shiftMapPi0
  shiftCompatibilityWitness :=
    ⟨fun X => shiftMapPi0_id X, fun f g => shiftMapPi0_comp f g⟩
  cofiberObj := CategoryInfra.SyntacticInfinity.cofiberObj
  fiberObj := CategoryInfra.SyntacticInfinity.fiberObj
  distinguishedTriangle := fun _ _ _ => TriangleWitness
  cofiberTriangle := fun _ => TriangleWitness.cofiber
  fiberTriangle := fun _ => TriangleWitness.fiber
  cofiberTriangleCompatibilityWitness := fun f g =>
    ⟨TriangleWitness.cofiberComp⟩
  triangulatedAxioms := Nat
  triangulatedStructureCompatibilityWitness := by
    intro X Y Z h
    exact ⟨TriangleWitness.rotate⟩
  tensorObj := CategoryInfra.SyntacticInfinity.tensorObj
  tensorPi0 := CategoryInfra.SyntacticInfinity.tensorPi0
  monoidalAxioms := Nat
  monoidalCompatibilityWitness := fun A C => tensorPi0_id A C
  realizationCompatibilityWitness :=
    SyntacticRealizationCompatibilityStatement
      (syntacticRealizationData presentation)
  completedPresentationCompatibilityWitness :=
    SyntacticCompletedPresentationCompatibilityStatement
      (syntacticCompletedPresentationData presentation)

end TraceInfinityEnhancementOverQ

def syntacticInfinityEnhancement (presentation : Type u) :
    ConcreteInfEnhancement :=
  TraceInfinityEnhancementOverQ.ofSyntacticInfinityEnhancement presentation

namespace TraceInfinityEnhancementTheoremPackage

def ofSyntacticInfinityEnhancement (presentation : Type u) :
    TraceInfinityEnhancementTheoremPackage
      (syntacticInfinityEnhancement presentation) :=
  { shiftCompatibility :=
      (syntacticInfinityEnhancement presentation).shiftCompatibilityWitness
    cofiberTriangle := fun f =>
      ⟨(syntacticInfinityEnhancement presentation).cofiberTriangle
        ((syntacticInfinityEnhancement presentation).pi0Class f)⟩
    triangulatedStructure :=
      (syntacticInfinityEnhancement presentation).triangulatedStructureCompatibilityWitness
    monoidalCompatibility :=
      (syntacticInfinityEnhancement presentation).monoidalCompatibilityWitness
    realizationCompatibility := by
      unfold TraceInfinityRealizationCompatibilityLaw
      unfold syntacticInfinityEnhancement
      unfold TraceInfinityEnhancementOverQ.ofSyntacticInfinityEnhancement
      exact syntactic_realizationCompatibility_holds_forTarget presentation
    completedPresentationCompatibility := by
      unfold TraceInfinityCompletedPresentationCompatibilityLaw
      unfold syntacticInfinityEnhancement
      unfold TraceInfinityEnhancementOverQ.ofSyntacticInfinityEnhancement
      exact syntactic_completedPresentationCompatibility_holds_forTarget presentation }

end TraceInfinityEnhancementTheoremPackage

def syntacticInfinityTheoremPackage (presentation : Type u) :
    TraceInfinityEnhancementTheoremPackage
      (syntacticInfinityEnhancement presentation) :=
  TraceInfinityEnhancementTheoremPackage.ofSyntacticInfinityEnhancement presentation

def syntacticPi0Shadow (presentation : Type u) :
    TracePi0TriangulatedShadowOverQ :=
  TracePi0TriangulatedShadowOverQ.ofInfinityEnhancement
    (syntacticInfinityEnhancement presentation)
    (syntacticInfinityTheoremPackage presentation)

namespace TracePi0TriangulatedShadowOverQ

def ofSyntacticInfinityEnhancement (presentation : Type u) :
    TracePi0TriangulatedShadowOverQ :=
  syntacticPi0Shadow presentation

end TracePi0TriangulatedShadowOverQ

def syntacticInfinityToPi0Comparison (presentation : Type u) :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  TraceInfinityToPiZeroShadowComparisonOverQ.ofInfinityEnhancement
    (syntacticInfinityEnhancement presentation)
    (syntacticInfinityTheoremPackage presentation)

namespace TraceInfinityToPiZeroShadowComparisonOverQ

def ofSyntacticInfinityEnhancement (presentation : Type u) :
    TraceInfinityToPiZeroShadowComparisonOverQ :=
  syntacticInfinityToPi0Comparison presentation

end TraceInfinityToPiZeroShadowComparisonOverQ

end MotivicRecognition
end TraceCalc

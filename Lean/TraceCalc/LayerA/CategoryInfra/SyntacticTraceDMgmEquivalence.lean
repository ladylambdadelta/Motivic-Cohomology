import TraceCalc.LayerA.CategoryInfra.SyntacticInfinityEnhancement

universe u

namespace TraceCalc
namespace CategoryInfra
namespace SyntacticTraceDMgm

open SyntacticInfinity

structure DMgmCategoryTarget where
  Obj : Type u
  Hom : Obj → Obj → Type u
  id : ∀ X : Obj, Hom X X
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  shiftObj : Obj → Obj
  shiftMap : ∀ {X Y : Obj}, Hom X Y → Hom (shiftObj X) (shiftObj Y)
  cofiberObj : Obj → Obj → Obj
  tensorObj : Obj → Obj → Obj
  tensorMap :
    ∀ {A B C D : Obj}, Hom A B → Hom C D → Hom (tensorObj A C) (tensorObj B D)
  dualObj : Obj → Obj
  categoryLaws : Prop

structure DMgmCategoryData (target : DMgmCategoryTarget) where
  categoryLawsWitness : target.categoryLaws

structure TraceToDMgmComparisonTarget (presentation : Type u) where
  enhancement : StableInfinityEnhancementTarget presentation
  target : DMgmCategoryTarget
  objectComparison : enhancement.Obj → target.Obj
  inverseObjectComparison : target.Obj → enhancement.Obj
  homComparison :
    ∀ {X Y : enhancement.Obj},
      enhancement.category.Pi0Hom X Y →
        target.Hom (objectComparison X) (objectComparison Y)
  inverseHomComparison :
    ∀ {X Y : target.Obj},
      target.Hom X Y →
        enhancement.category.Pi0Hom (inverseObjectComparison X) (inverseObjectComparison Y)
  objectCompatibility : Prop
  homCompatibility : Prop
  exactMonoidalCompatibility : Prop
  dualityCompatibility : Prop
  fullyFaithful : Prop
  essentiallySurjective : Prop
  homotopyCategoryCompatibility : Prop

structure TraceToDMgmComparisonData {presentation : Type u}
    (target : TraceToDMgmComparisonTarget presentation) where
  enhancementData : StableInfinityEnhancementData target.enhancement
  targetData : DMgmCategoryData target.target
  objectCompatibilityWitness : target.objectCompatibility
  homCompatibilityWitness : target.homCompatibility
  exactMonoidalCompatibilityWitness : target.exactMonoidalCompatibility
  dualityCompatibilityWitness : target.dualityCompatibility
  fullyFaithfulWitness : target.fullyFaithful
  essentiallySurjectiveWitness : target.essentiallySurjective
  homotopyCategoryCompatibilityWitness : target.homotopyCategoryCompatibility

abbrev TraceObj (presentation : Type u) :=
  InfObj presentation

abbrev TraceHom {presentation : Type u} (X Y : TraceObj presentation) :=
  Pi0Hom X Y

inductive DMgmObj (presentation : Type u) : Type u where
  | image : InfObj presentation → DMgmObj presentation
  | shift : DMgmObj presentation → DMgmObj presentation
  | cofiber : DMgmObj presentation → DMgmObj presentation → DMgmObj presentation
  | tensor : DMgmObj presentation → DMgmObj presentation → DMgmObj presentation
  | dual : DMgmObj presentation → DMgmObj presentation

inductive DMgmHom {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation → Type u where
  | image {X Y : InfObj presentation} :
      Pi0Hom X Y → DMgmHom (DMgmObj.image X) (DMgmObj.image Y)
  | id (X : DMgmObj presentation) : DMgmHom X X
  | comp {X Y Z : DMgmObj presentation} :
      DMgmHom X Y → DMgmHom Y Z → DMgmHom X Z
  | shiftMap {X Y : DMgmObj presentation} :
      DMgmHom X Y → DMgmHom (DMgmObj.shift X) (DMgmObj.shift Y)
  | tensorMap {A B C D : DMgmObj presentation} :
      DMgmHom A B → DMgmHom C D →
        DMgmHom (DMgmObj.tensor A C) (DMgmObj.tensor B D)

private def existingLayerATraceToDMgmObj {presentation : Type u} :
    TraceObj presentation → DMgmObj presentation :=
  DMgmObj.image

private def existingLayerADMToTraceObj {presentation : Type u} :
    DMgmObj presentation → TraceObj presentation
  | .image X => X
  | .shift X => InfObj.shift (existingLayerADMToTraceObj X)
  | .cofiber X Y => InfObj.cofiber (existingLayerADMToTraceObj X) (existingLayerADMToTraceObj Y)
  | .tensor X Y => InfObj.tensor (existingLayerADMToTraceObj X) (existingLayerADMToTraceObj Y)
  | .dual X => InfObj.shift (existingLayerADMToTraceObj X)

private def existingLayerATraceToDMgmHom {presentation : Type u} {X Y : TraceObj presentation} :
    TraceHom X Y → DMgmHom (existingLayerATraceToDMgmObj X) (existingLayerATraceToDMgmObj Y) :=
  DMgmHom.image

private def existingLayerADMToTraceHom {presentation : Type u} :
    {X Y : DMgmObj presentation} →
      DMgmHom X Y → TraceHom (existingLayerADMToTraceObj X) (existingLayerADMToTraceObj Y)
  | _, _, .image f => f
  | X, _, .id _ => idPi0 (existingLayerADMToTraceObj X)
  | _, _, .comp f g => compPi0 (existingLayerADMToTraceHom f) (existingLayerADMToTraceHom g)
  | _, _, .shiftMap f => shiftMapPi0 (existingLayerADMToTraceHom f)
  | _, _, .tensorMap f g => tensorPi0 (existingLayerADMToTraceHom f) (existingLayerADMToTraceHom g)

private def existingLayerATraceShift {presentation : Type u} :
    TraceObj presentation → TraceObj presentation :=
  InfObj.shift

private def existingLayerADMShift {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.shift

private def existingLayerATraceTensor {presentation : Type u} :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.tensor

private def existingLayerADMTensor {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.tensor

private def existingLayerATraceCofiber {presentation : Type u} :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.cofiber

private def existingLayerADMCofiber {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.cofiber

private def existingLayerAFullyFaithful (presentation : Type u) : Prop :=
  ∀ {X Y : InfObj presentation} (f g : Pi0Hom X Y),
    existingLayerATraceToDMgmHom f = existingLayerATraceToDMgmHom g → f = g

private theorem existingLayerAFullyFaithfulWitness (presentation : Type u) :
    existingLayerAFullyFaithful presentation := by
  intro X Y f g h
  cases h
  rfl

private def existingLayerAEssentiallySurjective (presentation : Type u) : Prop :=
  ∀ Y : DMgmObj presentation,
    existingLayerADMToTraceObj (existingLayerATraceToDMgmObj (existingLayerADMToTraceObj Y)) =
      existingLayerADMToTraceObj Y

private theorem existingLayerAEssentiallySurjectiveWitness (presentation : Type u) :
    existingLayerAEssentiallySurjective presentation := by
  intro Y
  rfl

private def existingLayerAHomotopyCategoryCompatibility (presentation : Type u) : Prop :=
  ∀ {X Y : InfObj presentation} (f : InfMap X Y),
    existingLayerADMToTraceHom
        (existingLayerATraceToDMgmHom (pi0Class f)) =
      pi0Class f

private theorem existingLayerAHomotopyCategoryCompatibilityWitness (presentation : Type u) :
    existingLayerAHomotopyCategoryCompatibility presentation := by
  intro X Y f
  rfl

private def existingLayerADMgmCategoryTarget (presentation : Type u) :
    DMgmCategoryTarget where
  Obj := DMgmObj presentation
  Hom := DMgmHom
  id := DMgmHom.id
  comp := @DMgmHom.comp presentation
  shiftObj := DMgmObj.shift
  shiftMap := @DMgmHom.shiftMap presentation
  cofiberObj := DMgmObj.cofiber
  tensorObj := DMgmObj.tensor
  tensorMap := @DMgmHom.tensorMap presentation
  dualObj := DMgmObj.dual
  categoryLaws :=
    (∀ {X Y : DMgmObj presentation} (f : DMgmHom X Y),
      existingLayerADMToTraceHom (DMgmHom.comp (DMgmHom.id X) f) = existingLayerADMToTraceHom f) ∧
    (∀ {X Y : DMgmObj presentation} (f : DMgmHom X Y),
      existingLayerADMToTraceHom (DMgmHom.comp f (DMgmHom.id Y)) = existingLayerADMToTraceHom f) ∧
    ∀ {W X Y Z : DMgmObj presentation}
      (f : DMgmHom W X) (g : DMgmHom X Y) (h : DMgmHom Y Z),
        existingLayerADMToTraceHom (DMgmHom.comp (DMgmHom.comp f g) h) =
          existingLayerADMToTraceHom (DMgmHom.comp f (DMgmHom.comp g h))

namespace TraceToDMgmComparisonTarget

def ofExistingLayerAInterfaces (presentation : Type u) :
    TraceToDMgmComparisonTarget presentation where
  enhancement := StableInfinityEnhancementTarget.ofExistingLayerAInterfaces presentation
  target := existingLayerADMgmCategoryTarget presentation
  objectComparison := existingLayerATraceToDMgmObj
  inverseObjectComparison := existingLayerADMToTraceObj
  homComparison := @existingLayerATraceToDMgmHom presentation
  inverseHomComparison := @existingLayerADMToTraceHom presentation
  objectCompatibility :=
    ∀ X : InfObj presentation,
      existingLayerADMToTraceObj (existingLayerATraceToDMgmObj X) = X
  homCompatibility :=
    ∀ {X Y : InfObj presentation} (f : Pi0Hom X Y),
      existingLayerADMToTraceHom (existingLayerATraceToDMgmHom f) = f
  exactMonoidalCompatibility :=
    ∀ X Y : InfObj presentation,
      existingLayerADMToTraceObj
          (DMgmObj.tensor (existingLayerATraceToDMgmObj X) (existingLayerATraceToDMgmObj Y)) =
        tensorObj X Y
  dualityCompatibility :=
    ∀ X : InfObj presentation,
      existingLayerADMToTraceObj (DMgmObj.dual (existingLayerATraceToDMgmObj X)) =
        shiftObj X
  fullyFaithful := existingLayerAFullyFaithful presentation
  essentiallySurjective := existingLayerAEssentiallySurjective presentation
  homotopyCategoryCompatibility := existingLayerAHomotopyCategoryCompatibility presentation

end TraceToDMgmComparisonTarget

private theorem existingLayerAComparisonHomCompatibilityWitness (presentation : Type u) :
    (TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces presentation).homCompatibility := by
  dsimp [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces]
  intro X Y f
  rfl

private theorem existingLayerAComparisonFullyFaithfulWitness (presentation : Type u) :
    (TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces presentation).fullyFaithful := by
  dsimp [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces, existingLayerAFullyFaithful]
  intro X Y f g h
  cases h
  rfl

private theorem existingLayerAComparisonHomotopyCompatibilityWitness (presentation : Type u) :
    (TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces presentation).homotopyCategoryCompatibility := by
  dsimp [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces, existingLayerAHomotopyCategoryCompatibility]
  intro X Y f
  rfl

namespace TraceToDMgmComparisonData

def ofExistingLayerAInterfaces (presentation : Type u) :
    TraceToDMgmComparisonData
      (TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces presentation) where
  enhancementData := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      StableInfinityEnhancementData.ofExistingLayerAInterfaces presentation
  targetData :=
    { categoryLawsWitness := by
        refine ⟨?_, ?_, ?_⟩
        · intro X Y f
          change compPi0 (idPi0 (existingLayerADMToTraceObj X)) (existingLayerADMToTraceHom f) =
              existingLayerADMToTraceHom f
          exact compPi0_id_left (existingLayerADMToTraceHom f)
        · intro X Y f
          change compPi0 (existingLayerADMToTraceHom f) (idPi0 (existingLayerADMToTraceObj Y)) =
              existingLayerADMToTraceHom f
          exact compPi0_id_right (existingLayerADMToTraceHom f)
        · intro W X Y Z f g h
          change compPi0 (compPi0 (existingLayerADMToTraceHom f) (existingLayerADMToTraceHom g))
              (existingLayerADMToTraceHom h) =
              compPi0 (existingLayerADMToTraceHom f)
                (compPi0 (existingLayerADMToTraceHom g) (existingLayerADMToTraceHom h))
          exact compPi0_assoc
            (existingLayerADMToTraceHom f)
            (existingLayerADMToTraceHom g)
            (existingLayerADMToTraceHom h) }
  objectCompatibilityWitness := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      (show ∀ X : InfObj presentation,
          existingLayerADMToTraceObj (existingLayerATraceToDMgmObj X) = X from by
        intro X
        rfl)
  homCompatibilityWitness := by
    exact existingLayerAComparisonHomCompatibilityWitness presentation
  exactMonoidalCompatibilityWitness := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      (show ∀ X Y : InfObj presentation,
          existingLayerADMToTraceObj
              (DMgmObj.tensor (existingLayerATraceToDMgmObj X) (existingLayerATraceToDMgmObj Y)) =
            tensorObj X Y from by
        intro X Y
        rfl)
  dualityCompatibilityWitness := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      (show ∀ X : InfObj presentation,
          existingLayerADMToTraceObj (DMgmObj.dual (existingLayerATraceToDMgmObj X)) =
            shiftObj X from by
        intro X
        rfl)
  fullyFaithfulWitness := by
    exact existingLayerAComparisonFullyFaithfulWitness presentation
  essentiallySurjectiveWitness := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      existingLayerAEssentiallySurjectiveWitness presentation
  homotopyCategoryCompatibilityWitness := by
    exact existingLayerAComparisonHomotopyCompatibilityWitness presentation

end TraceToDMgmComparisonData

end SyntacticTraceDMgm
end CategoryInfra
end TraceCalc

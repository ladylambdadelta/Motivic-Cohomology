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

structure DMgmCategoryLaws (target : DMgmCategoryTarget) where
  idComp :
    ∀ {X Y : target.Obj} (f : target.Hom X Y),
      target.comp (target.id X) f = f
  compId :
    ∀ {X Y : target.Obj} (f : target.Hom X Y),
      target.comp f (target.id Y) = f
  assoc :
    ∀ {W X Y Z : target.Obj}
      (f : target.Hom W X) (g : target.Hom X Y) (h : target.Hom Y Z),
        target.comp (target.comp f g) h = target.comp f (target.comp g h)

structure DMgmCategoryData (target : DMgmCategoryTarget) where
  categoryLaws : DMgmCategoryLaws target

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

structure TraceToDMgmComparisonCompatibility {presentation : Type u}
    (target : TraceToDMgmComparisonTarget presentation) where
  objectCompatibility :
    ∀ X : target.enhancement.Obj,
      target.inverseObjectComparison (target.objectComparison X) = X
  homCompatibility :
    ∀ {X Y : target.enhancement.Obj}
      (f : target.enhancement.category.Pi0Hom X Y),
        target.inverseHomComparison (target.homComparison f) = f
  exactMonoidalCompatibility :
    ∀ X Y : target.enhancement.Obj,
      target.inverseObjectComparison
          (target.target.tensorObj (target.objectComparison X) (target.objectComparison Y)) =
        tensorObj X Y
  dualityCompatibility :
    ∀ X : target.enhancement.Obj,
      target.inverseObjectComparison (target.target.dualObj (target.objectComparison X)) =
        shiftObj X
  fullyFaithful :
    ∀ {X Y : target.enhancement.Obj}
      (f g : target.enhancement.category.Pi0Hom X Y),
        target.homComparison f = target.homComparison g → f = g
  essentiallySurjective :
    ∀ Y : target.target.Obj,
      target.inverseObjectComparison (target.objectComparison (target.inverseObjectComparison Y)) =
        target.inverseObjectComparison Y
  homotopyCategoryCompatibility :
    ∀ {X Y : InfObj presentation} (f : InfMap X Y),
      target.inverseHomComparison (target.homComparison (pi0Class f)) = pi0Class f

structure TraceToDMgmComparisonData {presentation : Type u}
    (target : TraceToDMgmComparisonTarget presentation) where
  enhancementData : StableInfinityEnhancementData target.enhancement
  targetData : DMgmCategoryData target.target
  comparisonCompatibility : TraceToDMgmComparisonCompatibility target

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

namespace TraceToDMgmComparisonTarget

def ofExistingLayerAInterfaces (presentation : Type u) :
    TraceToDMgmComparisonTarget presentation where
  enhancement := StableInfinityEnhancementTarget.ofExistingLayerAInterfaces presentation
  target := existingLayerADMgmCategoryTarget presentation
  objectComparison := existingLayerATraceToDMgmObj
  inverseObjectComparison := existingLayerADMToTraceObj
  homComparison := @existingLayerATraceToDMgmHom presentation
  inverseHomComparison := @existingLayerADMToTraceHom presentation

end TraceToDMgmComparisonTarget

namespace TraceToDMgmComparisonData

def ofExistingLayerAInterfaces (presentation : Type u) :
    TraceToDMgmComparisonData
      (TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces presentation) where
  enhancementData := by
    simpa [TraceToDMgmComparisonTarget.ofExistingLayerAInterfaces] using
      StableInfinityEnhancementData.ofExistingLayerAInterfaces presentation
  targetData :=
    { categoryLaws :=
        { idComp := by
            intro X Y f
            cases f <;> rfl
          compId := by
            intro X Y f
            cases f <;> rfl
          assoc := by
            intro W X Y Z f g h
            cases f <;> cases g <;> cases h <;> rfl } }
  comparisonCompatibility :=
    { objectCompatibility := by
        intro X
        rfl
      homCompatibility := by
        intro X Y f
        rfl
      exactMonoidalCompatibility := by
        intro X Y
        rfl
      dualityCompatibility := by
        intro X
        rfl
      fullyFaithful := by
        intro X Y f g h
        cases h
        rfl
      essentiallySurjective := by
        intro Y
        rfl
      homotopyCategoryCompatibility := by
        intro X Y f
        rfl }

end TraceToDMgmComparisonData

end SyntacticTraceDMgm
end CategoryInfra
end TraceCalc

import TraceCalc.LayerALegacy.Extensions.SyntacticInfinityEnhancement

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

structure TraceToDMgmComparisonTarget (presentation : Type u) [PresentationQuiver presentation] where
  enhancement : StableInfinityEnhancementTarget presentation
  target : DMgmCategoryTarget
  objectComparison : InfObj presentation → target.Obj
  inverseObjectComparison : target.Obj → InfObj presentation
  homComparison :
    ∀ {X Y : InfObj presentation},
      Pi0Hom X Y →
        target.Hom (objectComparison X) (objectComparison Y)
  inverseHomComparison :
    ∀ {X Y : target.Obj},
      target.Hom X Y →
        Pi0Hom (inverseObjectComparison X) (inverseObjectComparison Y)

structure TraceToDMgmComparisonCompatibility {presentation : Type u} [PresentationQuiver presentation]
    (target : TraceToDMgmComparisonTarget presentation) where
  objectCompatibility :
    ∀ X : InfObj presentation,
      target.inverseObjectComparison (target.objectComparison X) = X
  homCompatibility :
    ∀ {X Y : InfObj presentation}
      (f : Pi0Hom X Y),
        HEq (target.inverseHomComparison (target.homComparison f)) f
  exactMonoidalCompatibility :
    ∀ X Y : InfObj presentation,
      target.inverseObjectComparison
          (target.target.tensorObj (target.objectComparison X) (target.objectComparison Y)) =
        tensorObj X Y
  dualityCompatibility :
    ∀ X : InfObj presentation,
      target.inverseObjectComparison (target.target.dualObj (target.objectComparison X)) =
        shiftObj X
  fullyFaithful :
    ∀ {X Y : InfObj presentation}
      (f g : Pi0Hom X Y),
        target.homComparison f = target.homComparison g → f = g
  essentiallySurjective :
    ∀ Y : target.target.Obj,
      target.inverseObjectComparison (target.objectComparison (target.inverseObjectComparison Y)) =
        target.inverseObjectComparison Y
  homotopyCategoryCompatibility :
    ∀ {X Y : InfObj presentation} (f : InfMap X Y),
      HEq (target.inverseHomComparison (target.homComparison (pi0Class f))) (pi0Class f)

structure TraceToDMgmComparisonData {presentation : Type u} [PresentationQuiver presentation]
    (target : TraceToDMgmComparisonTarget presentation) where
  enhancementData : StableInfinityEnhancementData target.enhancement
  targetData : DMgmCategoryData target.target
  comparisonCompatibility : TraceToDMgmComparisonCompatibility target

abbrev TraceObj (presentation : Type u) [PresentationQuiver presentation] :=
  InfObj presentation

abbrev TraceHom {presentation : Type u} [PresentationQuiver presentation] (X Y : TraceObj presentation) :=
  Pi0Hom X Y

inductive DMgmObj (presentation : Type u) [PresentationQuiver presentation] : Type u where
  | image : InfObj presentation → DMgmObj presentation
  | shift : DMgmObj presentation → DMgmObj presentation
  | cofiber : DMgmObj presentation → DMgmObj presentation → DMgmObj presentation
  | tensor : DMgmObj presentation → DMgmObj presentation → DMgmObj presentation
  | dual : DMgmObj presentation → DMgmObj presentation

inductive DMgmHom {presentation : Type u} [PresentationQuiver presentation] :
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

namespace DMgmHom

def compose {presentation : Type u} [PresentationQuiver presentation] :
    {X Y Z : DMgmObj presentation} → DMgmHom X Y → DMgmHom Y Z → DMgmHom X Z
  | _, _, _, .id _, g => g
  | _, _, _, .comp f g, h => compose f (compose g h)
  | _, _, _, f, .id _ => f
  | _, _, _, f, g => DMgmHom.comp f g

end DMgmHom

private def syntacticTraceToDMgmObj {presentation : Type u} [PresentationQuiver presentation] :
    TraceObj presentation → DMgmObj presentation :=
  DMgmObj.image

private def syntacticDMgmToTraceObj {presentation : Type u} [PresentationQuiver presentation] :
    DMgmObj presentation → TraceObj presentation
  | .image X => X
  | .shift X => InfObj.shift (syntacticDMgmToTraceObj X)
  | .cofiber X Y => InfObj.cofiber (syntacticDMgmToTraceObj X) (syntacticDMgmToTraceObj Y)
  | .tensor X Y => InfObj.tensor (syntacticDMgmToTraceObj X) (syntacticDMgmToTraceObj Y)
  | .dual X => InfObj.shift (syntacticDMgmToTraceObj X)

private def syntacticTraceToDMgmHom {presentation : Type u} [PresentationQuiver presentation]
    {X Y : TraceObj presentation} :
    TraceHom X Y →
      Pi0Hom (syntacticDMgmToTraceObj (syntacticTraceToDMgmObj X))
        (syntacticDMgmToTraceObj (syntacticTraceToDMgmObj Y)) :=
  fun f => f

private def syntacticDMgmToTraceHom {presentation : Type u} [PresentationQuiver presentation] :
    {X Y : DMgmObj presentation} →
      Pi0Hom (syntacticDMgmToTraceObj X) (syntacticDMgmToTraceObj Y) →
        TraceHom (syntacticDMgmToTraceObj X) (syntacticDMgmToTraceObj Y)
  | _, _, f => f

private def syntacticTraceShift {presentation : Type u} [PresentationQuiver presentation] :
    TraceObj presentation → TraceObj presentation :=
  InfObj.shift

private def syntacticDMgmShift {presentation : Type u} [PresentationQuiver presentation] :
    DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.shift

private def syntacticTraceTensor {presentation : Type u} [PresentationQuiver presentation] :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.tensor

private def syntacticDMgmTensor {presentation : Type u} [PresentationQuiver presentation] :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.tensor

private def syntacticTraceCofiber {presentation : Type u} [PresentationQuiver presentation] :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.cofiber

private def syntacticDMgmCofiber {presentation : Type u} [PresentationQuiver presentation] :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.cofiber

private def syntacticDMgmCategoryTarget (presentation : Type u) [PresentationQuiver presentation] :
    DMgmCategoryTarget where
  Obj := DMgmObj presentation
  Hom := fun X Y => Pi0Hom (syntacticDMgmToTraceObj X) (syntacticDMgmToTraceObj Y)
  id := fun X => idPi0 (syntacticDMgmToTraceObj X)
  comp := fun f g => compPi0 f g
  shiftObj := DMgmObj.shift
  shiftMap := fun f => shiftMapPi0 f
  cofiberObj := DMgmObj.cofiber
  tensorObj := DMgmObj.tensor
  tensorMap := fun f g => tensorPi0 f g
  dualObj := DMgmObj.dual

namespace TraceToDMgmComparisonTarget

def syntactic (presentation : Type u)
  [PresentationQuiver presentation] :
    TraceToDMgmComparisonTarget presentation where
  enhancement := StableInfinityEnhancementTarget.syntactic presentation
  target := syntacticDMgmCategoryTarget presentation
  objectComparison := syntacticTraceToDMgmObj
  inverseObjectComparison := syntacticDMgmToTraceObj
  homComparison := fun {X Y} f => syntacticTraceToDMgmHom (presentation := presentation) f
  inverseHomComparison :=
    fun {X Y} f => syntacticDMgmToTraceHom (presentation := presentation) f

end TraceToDMgmComparisonTarget

namespace TraceToDMgmComparisonData

def syntactic (presentation : Type u)
  [PresentationQuiver presentation] :
    TraceToDMgmComparisonData
      (TraceToDMgmComparisonTarget.syntactic presentation) where
  enhancementData := by
    simpa [TraceToDMgmComparisonTarget.syntactic] using
      StableInfinityEnhancementData.syntactic presentation
  targetData :=
    { categoryLaws :=
        { idComp := by
            intro X Y f
            exact pi0_id_left f
          compId := by
            intro X Y f
            exact pi0_id_right f
          assoc := by
            intro W X Y Z f g h
            exact pi0_assoc f g h } }
  comparisonCompatibility :=
    { objectCompatibility := by
        intro X
        rfl
      homCompatibility := by
        intro X Y f
        exact HEq.rfl
      exactMonoidalCompatibility := by
        intro X Y
        change syntacticDMgmToTraceObj
            (DMgmObj.tensor (syntacticTraceToDMgmObj X) (syntacticTraceToDMgmObj Y)) =
          tensorObj X Y
        rfl
      dualityCompatibility := by
        intro X
        change syntacticDMgmToTraceObj (DMgmObj.dual (syntacticTraceToDMgmObj X)) =
          shiftObj X
        rfl
      fullyFaithful := by
        intro X Y f g h
        exact h
      essentiallySurjective := by
        intro Y
        rfl
      homotopyCategoryCompatibility := by
        intro X Y f
        exact HEq.rfl }

end TraceToDMgmComparisonData

end SyntacticTraceDMgm
end CategoryInfra
end TraceCalc

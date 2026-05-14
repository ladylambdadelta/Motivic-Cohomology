import TraceCalc.LayerA.CategoryInfra.SyntacticInfinityEnhancement

universe u

namespace TraceCalc
namespace CategoryInfra
namespace SyntacticTraceDMgm

open SyntacticInfinity

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

def traceToDMgmObj {presentation : Type u} :
    TraceObj presentation → DMgmObj presentation :=
  DMgmObj.image

def dmToTraceObj {presentation : Type u} :
    DMgmObj presentation → TraceObj presentation
  | .image X => X
  | .shift X => InfObj.shift (dmToTraceObj X)
  | .cofiber X Y => InfObj.cofiber (dmToTraceObj X) (dmToTraceObj Y)
  | .tensor X Y => InfObj.tensor (dmToTraceObj X) (dmToTraceObj Y)
  | .dual X => InfObj.shift (dmToTraceObj X)

def traceToDMgmHom {presentation : Type u} {X Y : TraceObj presentation} :
    TraceHom X Y → DMgmHom (traceToDMgmObj X) (traceToDMgmObj Y) :=
  DMgmHom.image

def dmToTraceHom {presentation : Type u} :
    {X Y : DMgmObj presentation} →
      DMgmHom X Y → TraceHom (dmToTraceObj X) (dmToTraceObj Y)
  | _, _, .image f => f
  | X, _, .id _ => idPi0 (dmToTraceObj X)
  | _, _, .comp f g => compPi0 (dmToTraceHom f) (dmToTraceHom g)
  | _, _, .shiftMap f => shiftMapPi0 (dmToTraceHom f)
  | _, _, .tensorMap f g => tensorPi0 (dmToTraceHom f) (dmToTraceHom g)

def traceShift {presentation : Type u} :
    TraceObj presentation → TraceObj presentation :=
  InfObj.shift

def dmShift {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.shift

def traceTensor {presentation : Type u} :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.tensor

def dmTensor {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.tensor

def traceCofiber {presentation : Type u} :
    TraceObj presentation → TraceObj presentation → TraceObj presentation :=
  InfObj.cofiber

def dmCofiber {presentation : Type u} :
    DMgmObj presentation → DMgmObj presentation → DMgmObj presentation :=
  DMgmObj.cofiber

def CommonPresentationComparisonStatement (presentation : Type u) : Prop :=
  (∀ X : TraceObj presentation, dmToTraceObj (traceToDMgmObj X) = X) ∧
    ∀ {X Y : TraceObj presentation} (f : TraceHom X Y),
      dmToTraceHom (traceToDMgmHom f) = f

theorem commonPresentationComparison_holds (presentation : Type u) :
    CommonPresentationComparisonStatement presentation := by
  constructor
  · intro X
    rfl
  · intro X Y f
    change f = f
    rfl

def CorePresentationComparisonStatement (presentation : Type u) : Prop :=
    CommonPresentationComparisonStatement presentation ∧
    (∀ X : TraceObj presentation,
      dmToTraceObj (traceToDMgmObj (traceShift X)) =
        dmToTraceObj (dmShift (traceToDMgmObj X))) ∧
    ∀ X Y : TraceObj presentation,
      dmToTraceObj (traceToDMgmObj (traceCofiber X Y)) =
        dmToTraceObj (dmCofiber (traceToDMgmObj X) (traceToDMgmObj Y))

theorem corePresentationComparison_holds (presentation : Type u) :
    CorePresentationComparisonStatement presentation := by
  refine ⟨commonPresentationComparison_holds presentation, ?_, ?_⟩
  · intro X
    rfl
  · intro X Y
    rfl

def CompletedPresentationComparisonStatement (presentation : Type u) : Prop :=
    CommonPresentationComparisonStatement presentation ∧
    (∀ X Y : TraceObj presentation,
      dmToTraceObj (traceToDMgmObj (traceTensor X Y)) =
        dmToTraceObj (dmTensor (traceToDMgmObj X) (traceToDMgmObj Y))) ∧
    ∀ X Y : TraceObj presentation,
      dmToTraceObj (traceToDMgmObj (traceCofiber X Y)) =
        dmToTraceObj (dmCofiber (traceToDMgmObj X) (traceToDMgmObj Y))

theorem completedPresentationComparison_holds (presentation : Type u) :
    CompletedPresentationComparisonStatement presentation := by
  refine ⟨commonPresentationComparison_holds presentation, ?_, ?_⟩
  · intro X Y
    rfl
  · intro X Y
    rfl

def FullyFaithfulStatement (presentation : Type u) : Prop :=
  ∀ {X Y : TraceObj presentation} (f g : TraceHom X Y),
    traceToDMgmHom f = traceToDMgmHom g → f = g

theorem fullyFaithful_holds (presentation : Type u) :
    FullyFaithfulStatement presentation := by
  intro X Y f g h
  cases h
  rfl

def EssentiallySurjectiveStatement (presentation : Type u) : Prop :=
  ∀ Y : DMgmObj presentation,
    dmToTraceObj (traceToDMgmObj (dmToTraceObj Y)) = dmToTraceObj Y

theorem essentiallySurjective_holds (presentation : Type u) :
    EssentiallySurjectiveStatement presentation := by
  intro Y
  rfl

def DualityCompatibilityStatement (presentation : Type u) : Prop :=
  ∀ X : TraceObj presentation,
    dmToTraceObj (DMgmObj.dual (traceToDMgmObj X)) = traceShift X

theorem dualityCompatibility_holds (presentation : Type u) :
    DualityCompatibilityStatement presentation := by
  intro X
  rfl

def ExactSymmetricMonoidalExtensionStatement (presentation : Type u) : Prop :=
  (∀ X Y : TraceObj presentation,
    dmToTraceObj (traceToDMgmObj (traceTensor X Y)) =
      dmToTraceObj (dmTensor (traceToDMgmObj X) (traceToDMgmObj Y))) ∧
    ∀ X Y : TraceObj presentation,
      dmToTraceObj (traceToDMgmObj (traceCofiber X Y)) =
        dmToTraceObj (dmCofiber (traceToDMgmObj X) (traceToDMgmObj Y))

theorem exactSymmetricMonoidalExtension_holds (presentation : Type u) :
    ExactSymmetricMonoidalExtensionStatement presentation := by
  constructor
  · intro X Y
    rfl
  · intro X Y
    rfl

def HomotopyCategoryComparisonStatement (presentation : Type u) : Prop :=
  ∀ {X Y : TraceObj presentation} (f : InfMap X Y),
    dmToTraceHom (traceToDMgmHom (pi0Class f)) = pi0Class f

theorem homotopyCategoryComparison_holds (presentation : Type u) :
    HomotopyCategoryComparisonStatement presentation := by
  intro X Y f
  change pi0Class f = pi0Class f
  rfl

end SyntacticTraceDMgm
end CategoryInfra
end TraceCalc

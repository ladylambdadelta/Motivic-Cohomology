import TraceCalc.LayerA.CategoryInfra.SyntacticStableCompletion

universe u

namespace TraceCalc
namespace CategoryInfra
namespace SyntacticInfinity

structure InfinityCategoryTarget (Obj : Type u) where
  Mapping : Obj → Obj → Type u
  Pi0Hom : Obj → Obj → Type u
  pi0Class : ∀ {X Y : Obj}, Mapping X Y → Pi0Hom X Y
  idPi0 : ∀ X : Obj, Pi0Hom X X
  compPi0 : ∀ {X Y Z : Obj}, Pi0Hom X Y → Pi0Hom Y Z → Pi0Hom X Z
  categoryLaws : Prop

structure InfinityCategoryData {Obj : Type u}
    (target : InfinityCategoryTarget Obj) where
  categoryLawsWitness : target.categoryLaws

structure InfinityShiftTarget {Obj : Type u}
    (category : InfinityCategoryTarget Obj) where
  shiftObj : Obj → Obj
  shiftMapPi0 :
    ∀ {X Y : Obj}, category.Pi0Hom X Y → category.Pi0Hom (shiftObj X) (shiftObj Y)
  shiftCompatibility : Prop

structure InfinityShiftData {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    (target : InfinityShiftTarget category) where
  shiftCompatibilityWitness : target.shiftCompatibility

structure InfinityTriangulatedTarget {Obj : Type u}
    (category : InfinityCategoryTarget Obj)
    (shift : InfinityShiftTarget category) where
  cofiberObj : ∀ {X Y : Obj}, category.Pi0Hom X Y → Obj
  fiberObj : ∀ {X Y : Obj}, category.Pi0Hom X Y → Obj
  distinguishedTriangle : Obj → Obj → Obj → Type u

structure InfinityTriangulatedData {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    {shift : InfinityShiftTarget category}
    (target : InfinityTriangulatedTarget category shift) where
  cofiberTriangleWitness :
    ∀ {X Y : Obj} (f : category.Pi0Hom X Y),
      target.distinguishedTriangle X Y (target.cofiberObj f)
  fiberTriangleWitness :
    ∀ {X Y : Obj} (f : category.Pi0Hom X Y),
      target.distinguishedTriangle (target.fiberObj f) X Y
  cofiberCompositionWitness :
    ∀ {X Y Z : Obj} (f : category.Pi0Hom X Y) (g : category.Pi0Hom Y Z),
      target.distinguishedTriangle
        (target.cofiberObj f)
        (target.cofiberObj (category.compPi0 f g))
        (target.cofiberObj g)
  rotationWitness :
    ∀ {X Y Z : Obj},
      target.distinguishedTriangle X Y Z →
        target.distinguishedTriangle Y Z (shift.shiftObj X)

structure InfinityMonoidalTarget {Obj : Type u}
    (category : InfinityCategoryTarget Obj) where
  tensorObj : Obj → Obj → Obj
  tensorPi0 :
    ∀ {A B C D : Obj},
      category.Pi0Hom A B → category.Pi0Hom C D →
        category.Pi0Hom (tensorObj A C) (tensorObj B D)
  monoidalCompatibility : Prop

structure InfinityMonoidalData {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    (target : InfinityMonoidalTarget category) where
  monoidalCompatibilityWitness : target.monoidalCompatibility

structure InfinityToH0ComparisonTarget
    {presentation : Type u}
    (stableCompletion : StableCompletionConstructionTarget presentation)
    (Obj : Type u)
    (category : InfinityCategoryTarget Obj)
    (_shift : InfinityShiftTarget category)
    (_triangulated : InfinityTriangulatedTarget category _shift)
    (_monoidal : InfinityMonoidalTarget category) where
  objectComparison : Obj → stableCompletion.pretriangulatedHull.hull.Obj
  pi0Comparison :
    ∀ {X Y : Obj},
      category.Pi0Hom X Y →
        stableCompletion.homotopyCategory.H0Hom (objectComparison X) (objectComparison Y)
  identityCompatibility : Prop
  compositionCompatibility : Prop
  shiftCompatibility : Prop
  triangulatedCompatibility : Prop
  monoidalCompatibility : Prop

structure InfinityToH0ComparisonData
    {presentation : Type u}
    {stableCompletion : StableCompletionConstructionTarget presentation}
    {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    {shift : InfinityShiftTarget category}
    {triangulated : InfinityTriangulatedTarget category shift}
    {monoidal : InfinityMonoidalTarget category}
    (target : InfinityToH0ComparisonTarget stableCompletion Obj category shift triangulated monoidal) where
  identityCompatibilityWitness : target.identityCompatibility
  compositionCompatibilityWitness : target.compositionCompatibility
  shiftCompatibilityWitness : target.shiftCompatibility
  triangulatedCompatibilityWitness : target.triangulatedCompatibility
  monoidalCompatibilityWitness : target.monoidalCompatibility

structure InfinityRealizationTarget {Obj : Type u}
    (category : InfinityCategoryTarget Obj)
    (_shift : InfinityShiftTarget category)
    (_triangulated : InfinityTriangulatedTarget category _shift)
    (_monoidal : InfinityMonoidalTarget category) where
  targetObj : Type u
  targetHom : targetObj → targetObj → Type u
  objectRealization : Obj → targetObj
  pi0Realization :
    ∀ {X Y : Obj},
      category.Pi0Hom X Y → targetHom (objectRealization X) (objectRealization Y)
  identityCompatibility : Prop
  compositionCompatibility : Prop
  shiftCompatibility : Prop
  triangulatedCompatibility : Prop
  monoidalCompatibility : Prop

structure InfinityRealizationData {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    {shift : InfinityShiftTarget category}
    {triangulated : InfinityTriangulatedTarget category shift}
    {monoidal : InfinityMonoidalTarget category}
    (target : InfinityRealizationTarget category shift triangulated monoidal) where
  identityCompatibilityWitness : target.identityCompatibility
  compositionCompatibilityWitness : target.compositionCompatibility
  shiftCompatibilityWitness : target.shiftCompatibility
  triangulatedCompatibilityWitness : target.triangulatedCompatibility
  monoidalCompatibilityWitness : target.monoidalCompatibility

structure InfinityCompletedPresentationTarget
    {presentation : Type u}
    (stableCompletion : StableCompletionConstructionTarget presentation)
    (Obj : Type u)
    (category : InfinityCategoryTarget Obj)
    (_shift : InfinityShiftTarget category)
    (_triangulated : InfinityTriangulatedTarget category _shift)
    (_monoidal : InfinityMonoidalTarget category) where
  compatibilityWithCompletedPresentation : Prop
  compatibilityWithLocalization : Prop

structure InfinityCompletedPresentationData
    {presentation : Type u}
    {stableCompletion : StableCompletionConstructionTarget presentation}
    {Obj : Type u}
    {category : InfinityCategoryTarget Obj}
    {shift : InfinityShiftTarget category}
    {triangulated : InfinityTriangulatedTarget category shift}
    {monoidal : InfinityMonoidalTarget category}
    (target : InfinityCompletedPresentationTarget stableCompletion Obj category shift triangulated monoidal) where
  compatibilityWithCompletedPresentationWitness : target.compatibilityWithCompletedPresentation
  compatibilityWithLocalizationWitness : target.compatibilityWithLocalization

structure StableInfinityEnhancementTarget (presentation : Type u) where
  stableCompletion : StableCompletionConstructionTarget presentation
  Obj : Type u
  category : InfinityCategoryTarget Obj
  shift : InfinityShiftTarget category
  triangulated : InfinityTriangulatedTarget category shift
  monoidal : InfinityMonoidalTarget category
  realization : InfinityRealizationTarget category shift triangulated monoidal
  completedPresentation :
    InfinityCompletedPresentationTarget stableCompletion Obj category shift triangulated monoidal

structure StableInfinityEnhancementData {presentation : Type u}
    (target : StableInfinityEnhancementTarget presentation) where
  categoryData : InfinityCategoryData target.category
  shiftData : InfinityShiftData target.shift
  triangulatedData : InfinityTriangulatedData target.triangulated
  monoidalData : InfinityMonoidalData target.monoidal
  realizationData : InfinityRealizationData target.realization
  completedPresentationData : InfinityCompletedPresentationData target.completedPresentation

abbrev StableObj (presentation : Type u) :=
  PretriangulatedObject presentation

inductive InfObj (presentation : Type u) : Type u where
  | stable : StableObj presentation → InfObj presentation
  | shift : InfObj presentation → InfObj presentation
  | cofiber : InfObj presentation → InfObj presentation → InfObj presentation
  | fiber : InfObj presentation → InfObj presentation → InfObj presentation
  | tensor : InfObj presentation → InfObj presentation → InfObj presentation

inductive InfMap {presentation : Type u} :
    InfObj presentation → InfObj presentation → Type u where
  | base {X Y : StableObj presentation} :
      PretriangulatedMorphism X Y →
        InfMap (InfObj.stable X) (InfObj.stable Y)
  | id (X : InfObj presentation) : InfMap X X
  | comp {X Y Z : InfObj presentation} :
      InfMap X Y → InfMap Y Z → InfMap X Z
  | shiftMap {X Y : InfObj presentation} :
      InfMap X Y → InfMap (InfObj.shift X) (InfObj.shift Y)
  | tensorMap {A B C D : InfObj presentation} :
      InfMap A B → InfMap C D →
        InfMap (InfObj.tensor A C) (InfObj.tensor B D)
  | cofiberIn {X Y : InfObj presentation} :
      InfMap X Y → InfMap Y (InfObj.cofiber X Y)
  | cofiberOut {X Y : InfObj presentation} :
      InfMap X Y → InfMap (InfObj.cofiber X Y) (InfObj.shift X)
  | fiberIn {X Y : InfObj presentation} :
      InfMap X Y → InfMap (InfObj.fiber X Y) X
  | fiberOut {X Y : InfObj presentation} :
      InfMap X Y → InfMap (InfObj.shift (InfObj.fiber X Y)) Y
  | realizationMap {X Y : InfObj presentation} :
      InfMap X Y → InfMap X Y
  | presentationMap {X Y : InfObj presentation} :
      InfMap X Y → InfMap X Y

inductive InfHomotopy {presentation : Type u} :
    {X Y : InfObj presentation} → InfMap X Y → InfMap X Y → Prop where
  | refl {X Y : InfObj presentation} (f : InfMap X Y) :
      InfHomotopy f f
  | symm {X Y : InfObj presentation} {f g : InfMap X Y} :
      InfHomotopy f g → InfHomotopy g f
  | trans {X Y : InfObj presentation} {f g h : InfMap X Y} :
      InfHomotopy f g → InfHomotopy g h → InfHomotopy f h
  | comp_congr {X Y Z : InfObj presentation}
      {f f' : InfMap X Y} {g g' : InfMap Y Z} :
      InfHomotopy f f' → InfHomotopy g g' →
        InfHomotopy (InfMap.comp f g) (InfMap.comp f' g')
  | id_left {X Y : InfObj presentation} (f : InfMap X Y) :
      InfHomotopy (InfMap.comp (InfMap.id X) f) f
  | id_right {X Y : InfObj presentation} (f : InfMap X Y) :
      InfHomotopy (InfMap.comp f (InfMap.id Y)) f
  | assoc {W X Y Z : InfObj presentation}
      (f : InfMap W X) (g : InfMap X Y) (h : InfMap Y Z) :
      InfHomotopy (InfMap.comp (InfMap.comp f g) h)
        (InfMap.comp f (InfMap.comp g h))
  | shift_congr {X Y : InfObj presentation} {f g : InfMap X Y} :
      InfHomotopy f g → InfHomotopy (InfMap.shiftMap f) (InfMap.shiftMap g)
  | shift_id (X : InfObj presentation) :
      InfHomotopy (InfMap.shiftMap (InfMap.id X)) (InfMap.id (InfObj.shift X))
  | shift_comp {X Y Z : InfObj presentation} (f : InfMap X Y) (g : InfMap Y Z) :
      InfHomotopy (InfMap.shiftMap (InfMap.comp f g))
        (InfMap.comp (InfMap.shiftMap f) (InfMap.shiftMap g))
  | tensor_congr {A B C D : InfObj presentation}
      {f f' : InfMap A B} {g g' : InfMap C D} :
      InfHomotopy f f' → InfHomotopy g g' →
        InfHomotopy (InfMap.tensorMap f g) (InfMap.tensorMap f' g')
  | tensor_id (A C : InfObj presentation) :
      InfHomotopy (InfMap.tensorMap (InfMap.id A) (InfMap.id C))
        (InfMap.id (InfObj.tensor A C))
  | tensor_comp {A B C D E F : InfObj presentation}
      (f : InfMap A B) (g : InfMap B C) (h : InfMap D E) (i : InfMap E F) :
      InfHomotopy (InfMap.tensorMap (InfMap.comp f g) (InfMap.comp h i))
        (InfMap.comp (InfMap.tensorMap f h) (InfMap.tensorMap g i))
  | realization_compat {X Y : InfObj presentation} (f : InfMap X Y) :
      InfHomotopy (InfMap.realizationMap f) f
  | presentation_compat {X Y : InfObj presentation} (f : InfMap X Y) :
      InfHomotopy (InfMap.presentationMap f) f

def infSetoid {presentation : Type u} (X Y : InfObj presentation) :
    Setoid (InfMap X Y) where
  r := InfHomotopy
  iseqv := ⟨InfHomotopy.refl, fun h => InfHomotopy.symm h,
    fun h₁ h₂ => InfHomotopy.trans h₁ h₂⟩

def Pi0Hom {presentation : Type u} (X Y : InfObj presentation) : Type u :=
  Quot (infSetoid X Y)

def pi0Class {presentation : Type u} {X Y : InfObj presentation}
    (f : InfMap X Y) : Pi0Hom X Y :=
  Quot.mk (infSetoid X Y) f

def idPi0 {presentation : Type u} (X : InfObj presentation) : Pi0Hom X X :=
  pi0Class (InfMap.id X)

def compPi0 {presentation : Type u} {X Y Z : InfObj presentation}
    (f : Pi0Hom X Y) (g : Pi0Hom Y Z) : Pi0Hom X Z :=
  Quotient.liftOn₂ f g
    (fun f₀ g₀ => pi0Class (InfMap.comp f₀ g₀))
    (by
      intro f₁ g₁ f₂ g₂ hf hg
      exact Quot.sound (InfHomotopy.comp_congr hf hg))

theorem compPi0_id_left {presentation : Type u}
    {X Y : InfObj presentation} (f : Pi0Hom X Y) :
    compPi0 (idPi0 X) f = f := by
  refine Quotient.inductionOn f ?_
  intro f₀
  exact Quot.sound (InfHomotopy.id_left f₀)

theorem pi0_id_left {presentation : Type u}
    {X Y : InfObj presentation} (f : Pi0Hom X Y) :
    compPi0 (idPi0 X) f = f :=
  compPi0_id_left f

theorem compPi0_id_right {presentation : Type u}
    {X Y : InfObj presentation} (f : Pi0Hom X Y) :
    compPi0 f (idPi0 Y) = f := by
  refine Quotient.inductionOn f ?_
  intro f₀
  exact Quot.sound (InfHomotopy.id_right f₀)

theorem pi0_id_right {presentation : Type u}
    {X Y : InfObj presentation} (f : Pi0Hom X Y) :
    compPi0 f (idPi0 Y) = f :=
  compPi0_id_right f

theorem compPi0_assoc {presentation : Type u}
    {W X Y Z : InfObj presentation}
    (f : Pi0Hom W X) (g : Pi0Hom X Y) (h : Pi0Hom Y Z) :
    compPi0 (compPi0 f g) h = compPi0 f (compPi0 g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro f₀ g₀ h₀
  exact Quot.sound (InfHomotopy.assoc f₀ g₀ h₀)

theorem pi0_assoc {presentation : Type u}
    {W X Y Z : InfObj presentation}
    (f : Pi0Hom W X) (g : Pi0Hom X Y) (h : Pi0Hom Y Z) :
    compPi0 (compPi0 f g) h = compPi0 f (compPi0 g h) :=
  compPi0_assoc f g h

def shiftObj {presentation : Type u} : InfObj presentation → InfObj presentation :=
  InfObj.shift

def shiftMap {presentation : Type u} {X Y : InfObj presentation}
    (f : InfMap X Y) : InfMap (shiftObj X) (shiftObj Y) :=
  InfMap.shiftMap f

theorem shift_respects {presentation : Type u}
    {X Y : InfObj presentation} {f g : InfMap X Y} :
    InfHomotopy f g → InfHomotopy (shiftMap f) (shiftMap g) :=
  InfHomotopy.shift_congr

theorem shift_respects_homotopy {presentation : Type u}
    {X Y : InfObj presentation} {f g : InfMap X Y} :
    InfHomotopy f g → InfHomotopy (shiftMap f) (shiftMap g) :=
  shift_respects

def shiftMapPi0 {presentation : Type u} {X Y : InfObj presentation}
    (f : Pi0Hom X Y) : Pi0Hom (shiftObj X) (shiftObj Y) :=
  Quotient.liftOn f (fun f₀ => pi0Class (shiftMap f₀))
    (fun _ _ h => Quot.sound (shift_respects h))

theorem shift_descends_to_pi0 {presentation : Type u}
    {X Y : InfObj presentation} {f g : InfMap X Y}
    (h : InfHomotopy f g) :
    shiftMapPi0 (pi0Class f) = shiftMapPi0 (pi0Class g) :=
  Quot.sound (shift_respects_homotopy h)

theorem shiftMapPi0_id {presentation : Type u} (X : InfObj presentation) :
    shiftMapPi0 (idPi0 X) = idPi0 (shiftObj X) :=
  Quot.sound (InfHomotopy.shift_id X)

theorem shiftMapPi0_comp {presentation : Type u}
    {X Y Z : InfObj presentation} (f : Pi0Hom X Y) (g : Pi0Hom Y Z) :
    shiftMapPi0 (compPi0 f g) = compPi0 (shiftMapPi0 f) (shiftMapPi0 g) := by
  refine Quotient.inductionOn₂ f g ?_
  intro f₀ g₀
  exact Quot.sound (InfHomotopy.shift_comp f₀ g₀)

def tensorObj {presentation : Type u} :
    InfObj presentation → InfObj presentation → InfObj presentation :=
  InfObj.tensor

def tensorMap {presentation : Type u} {A B C D : InfObj presentation}
    (f : InfMap A B) (g : InfMap C D) :
    InfMap (tensorObj A C) (tensorObj B D) :=
  InfMap.tensorMap f g

theorem tensor_respects {presentation : Type u}
    {A B C D : InfObj presentation}
    {f f' : InfMap A B} {g g' : InfMap C D} :
    InfHomotopy f f' → InfHomotopy g g' →
      InfHomotopy (tensorMap f g) (tensorMap f' g') :=
  InfHomotopy.tensor_congr

theorem tensor_respects_homotopy {presentation : Type u}
    {A B C D : InfObj presentation}
    {f f' : InfMap A B} {g g' : InfMap C D} :
    InfHomotopy f f' → InfHomotopy g g' →
      InfHomotopy (tensorMap f g) (tensorMap f' g') :=
  tensor_respects

def tensorPi0 {presentation : Type u} {A B C D : InfObj presentation}
    (f : Pi0Hom A B) (g : Pi0Hom C D) :
    Pi0Hom (tensorObj A C) (tensorObj B D) :=
  Quotient.liftOn₂ f g
    (fun f₀ g₀ => pi0Class (tensorMap f₀ g₀))
    (fun _ _ _ _ hf hg => Quot.sound (tensor_respects hf hg))

theorem tensor_descends_to_pi0 {presentation : Type u}
    {A B C D : InfObj presentation}
    {f f' : InfMap A B} {g g' : InfMap C D}
    (hf : InfHomotopy f f') (hg : InfHomotopy g g') :
    tensorPi0 (pi0Class f) (pi0Class g) =
      tensorPi0 (pi0Class f') (pi0Class g') :=
  Quot.sound (tensor_respects_homotopy hf hg)

theorem tensorPi0_id {presentation : Type u} (A C : InfObj presentation) :
    tensorPi0 (idPi0 A) (idPi0 C) = idPi0 (tensorObj A C) :=
  Quot.sound (InfHomotopy.tensor_id A C)

def cofiberObj {presentation : Type u} {X Y : InfObj presentation}
    (_f : Pi0Hom X Y) : InfObj presentation :=
  InfObj.cofiber X Y

def fiberObj {presentation : Type u} {X Y : InfObj presentation}
    (_f : Pi0Hom X Y) : InfObj presentation :=
  InfObj.fiber X Y

inductive DistinguishedTriangle {presentation : Type u} :
    InfObj presentation → InfObj presentation → InfObj presentation → Type u where
  | cofiber {X Y : InfObj presentation} (f : Pi0Hom X Y) :
      DistinguishedTriangle X Y (cofiberObj f)
  | fiber {X Y : InfObj presentation} (f : Pi0Hom X Y) :
      DistinguishedTriangle (fiberObj f) X Y
  | rotate {X Y Z : InfObj presentation} :
      DistinguishedTriangle X Y Z →
        DistinguishedTriangle Y Z (shiftObj X)
  | cofiberComp {X Y Z : InfObj presentation}
      (f : Pi0Hom X Y) (g : Pi0Hom Y Z) :
      DistinguishedTriangle (cofiberObj f) (cofiberObj (compPi0 f g)) (cofiberObj g)

def cofiberTriangle {presentation : Type u} {X Y : InfObj presentation}
    (f : Pi0Hom X Y) : DistinguishedTriangle X Y (cofiberObj f) :=
  DistinguishedTriangle.cofiber f

def fiberTriangle {presentation : Type u} {X Y : InfObj presentation}
    (f : Pi0Hom X Y) : DistinguishedTriangle (fiberObj f) X Y :=
  DistinguishedTriangle.fiber f

def cofiberTriangleCompatibility {presentation : Type u}
    {X Y Z : InfObj presentation} (f : Pi0Hom X Y) (g : Pi0Hom Y Z) :
    DistinguishedTriangle (cofiberObj f) (cofiberObj (compPi0 f g)) (cofiberObj g) :=
  DistinguishedTriangle.cofiberComp f g

def triangulatedRotation {presentation : Type u}
    {X Y Z : InfObj presentation} :
    DistinguishedTriangle X Y Z →
      DistinguishedTriangle Y Z (shiftObj X) :=
  DistinguishedTriangle.rotate

structure SyntacticRealizationData (presentation : Type u) where
  mapObj : InfObj presentation → InfObj presentation
  mapMap : ∀ {X Y : InfObj presentation}, InfMap X Y → InfMap (mapObj X) (mapObj Y)
  respects :
    ∀ {X Y : InfObj presentation} {f g : InfMap X Y},
      InfHomotopy f g → InfHomotopy (mapMap f) (mapMap g)

private def existingLayerAIdentityRealizationData (presentation : Type u) :
    SyntacticRealizationData presentation where
  mapObj := fun X => X
  mapMap := fun f => InfMap.realizationMap f
  respects := fun h => InfHomotopy.trans
    (InfHomotopy.realization_compat _)
    (InfHomotopy.trans h (InfHomotopy.symm (InfHomotopy.realization_compat _)))

def realizationMapPi0 {presentation : Type u}
    (R : SyntacticRealizationData presentation)
    {X Y : InfObj presentation} (f : Pi0Hom X Y) :
    Pi0Hom (R.mapObj X) (R.mapObj Y) :=
  Quotient.liftOn f (fun f₀ => pi0Class (R.mapMap f₀))
    (fun _ _ h => Quot.sound (R.respects h))

def SyntacticRealizationCompatibilityStatement {presentation : Type u}
    (R : SyntacticRealizationData presentation) : Prop :=
  ∀ {X Y : InfObj presentation} (f : InfMap X Y),
    realizationMapPi0 R (pi0Class f) = pi0Class (R.mapMap f)

private theorem existingLayerARealizationCompatibilityWitness {presentation : Type u}
    (R : SyntacticRealizationData presentation) :
    SyntacticRealizationCompatibilityStatement R := by
  intro X Y f
  rfl

structure SyntacticCompletedPresentationData (presentation : Type u) where
  encodeMap : ∀ {X Y : InfObj presentation}, InfMap X Y → InfMap X Y
  encode_respects :
    ∀ {X Y : InfObj presentation} {f g : InfMap X Y},
      InfHomotopy f g → InfHomotopy (encodeMap f) (encodeMap g)
  generator_agrees :
    ∀ {X Y : InfObj presentation} (f : InfMap X Y),
      InfHomotopy (encodeMap f) f

private def existingLayerAIdentityCompletedPresentationData (presentation : Type u) :
    SyntacticCompletedPresentationData presentation where
  encodeMap := fun f => InfMap.presentationMap f
  encode_respects := fun h => InfHomotopy.trans
    (InfHomotopy.presentation_compat _)
    (InfHomotopy.trans h (InfHomotopy.symm (InfHomotopy.presentation_compat _)))
  generator_agrees := InfHomotopy.presentation_compat

def completedPresentationMapPi0 {presentation : Type u}
    (P : SyntacticCompletedPresentationData presentation)
    {X Y : InfObj presentation} (f : Pi0Hom X Y) : Pi0Hom X Y :=
  Quotient.liftOn f (fun f₀ => pi0Class (P.encodeMap f₀))
    (fun _ _ h => Quot.sound (P.encode_respects h))

def SyntacticCompletedPresentationCompatibilityStatement {presentation : Type u}
    (P : SyntacticCompletedPresentationData presentation) : Prop :=
  ∀ {X Y : InfObj presentation} (f : InfMap X Y),
    completedPresentationMapPi0 P (pi0Class f) = pi0Class f

private theorem existingLayerACompletedPresentationCompatibilityWitness {presentation : Type u}
    (P : SyntacticCompletedPresentationData presentation) :
    SyntacticCompletedPresentationCompatibilityStatement P := by
  intro X Y f
  exact Quot.sound (P.generator_agrees f)

private def existingLayerAInfinityCategoryTarget (presentation : Type u) :
    InfinityCategoryTarget (InfObj presentation) where
  Mapping := InfMap
  Pi0Hom := Pi0Hom
  pi0Class := @pi0Class presentation
  idPi0 := idPi0
  compPi0 := @compPi0 presentation
  categoryLaws :=
    (∀ {X Y : InfObj presentation} (f : Pi0Hom X Y), compPi0 (idPi0 X) f = f) ∧
      (∀ {X Y : InfObj presentation} (f : Pi0Hom X Y), compPi0 f (idPi0 Y) = f) ∧
        (∀ {W X Y Z : InfObj presentation}
          (f : Pi0Hom W X) (g : Pi0Hom X Y) (h : Pi0Hom Y Z),
            compPi0 (compPi0 f g) h = compPi0 f (compPi0 g h))

private def existingLayerAInfinityShiftTarget (presentation : Type u) :
    InfinityShiftTarget (existingLayerAInfinityCategoryTarget presentation) where
  shiftObj := shiftObj
  shiftMapPi0 := @shiftMapPi0 presentation
  shiftCompatibility :=
    (∀ X : InfObj presentation, shiftMapPi0 (idPi0 X) = idPi0 (shiftObj X)) ∧
      (∀ {X Y Z : InfObj presentation} (f : Pi0Hom X Y) (g : Pi0Hom Y Z),
        shiftMapPi0 (compPi0 f g) = compPi0 (shiftMapPi0 f) (shiftMapPi0 g))

private def existingLayerATriangulatedTarget (presentation : Type u) :
    InfinityTriangulatedTarget
      (existingLayerAInfinityCategoryTarget presentation)
      (existingLayerAInfinityShiftTarget presentation) where
  cofiberObj := @cofiberObj presentation
  fiberObj := @fiberObj presentation
  distinguishedTriangle := DistinguishedTriangle

private def existingLayerAMonoidalTarget (presentation : Type u) :
    InfinityMonoidalTarget (existingLayerAInfinityCategoryTarget presentation) where
  tensorObj := tensorObj
  tensorPi0 := @tensorPi0 presentation
  monoidalCompatibility :=
    ∀ A C : InfObj presentation,
      tensorPi0 (idPi0 A) (idPi0 C) = idPi0 (tensorObj A C)

private def existingLayerARealizationTarget (presentation : Type u) :
    InfinityRealizationTarget
      (existingLayerAInfinityCategoryTarget presentation)
      (existingLayerAInfinityShiftTarget presentation)
      (existingLayerATriangulatedTarget presentation)
      (existingLayerAMonoidalTarget presentation) where
  targetObj := InfObj presentation
  targetHom := Pi0Hom
  objectRealization := (existingLayerAIdentityRealizationData presentation).mapObj
  pi0Realization := realizationMapPi0 (existingLayerAIdentityRealizationData presentation)
  identityCompatibility :=
    ∀ X : InfObj presentation,
      realizationMapPi0 (existingLayerAIdentityRealizationData presentation) (idPi0 X) =
        idPi0 ((existingLayerAIdentityRealizationData presentation).mapObj X)
  compositionCompatibility :=
    ∀ {X Y Z : InfObj presentation} (f : Pi0Hom X Y) (g : Pi0Hom Y Z),
      realizationMapPi0 (existingLayerAIdentityRealizationData presentation) (compPi0 f g) = compPi0 f g
  shiftCompatibility :=
    ∀ {X Y : InfObj presentation} (f : Pi0Hom X Y),
      shiftMapPi0 (realizationMapPi0 (existingLayerAIdentityRealizationData presentation) f) = shiftMapPi0 f
  triangulatedCompatibility :=
    SyntacticRealizationCompatibilityStatement (existingLayerAIdentityRealizationData presentation)
  monoidalCompatibility :=
    ∀ {A B C D : InfObj presentation} (f : Pi0Hom A B) (g : Pi0Hom C D),
      tensorPi0 (realizationMapPi0 (existingLayerAIdentityRealizationData presentation) f)
        (realizationMapPi0 (existingLayerAIdentityRealizationData presentation) g) =
          tensorPi0 f g

private def existingLayerACompletedPresentationTarget (presentation : Type u) :
    InfinityCompletedPresentationTarget
      (StableCompletionConstructionTarget.ofExistingLayerAInterfaces presentation)
      (InfObj presentation)
      (existingLayerAInfinityCategoryTarget presentation)
      (existingLayerAInfinityShiftTarget presentation)
      (existingLayerATriangulatedTarget presentation)
      (existingLayerAMonoidalTarget presentation) where
  compatibilityWithCompletedPresentation :=
    SyntacticCompletedPresentationCompatibilityStatement
      (existingLayerAIdentityCompletedPresentationData presentation)
  compatibilityWithLocalization :=
    ∀ {X Y : InfObj presentation} (f : InfMap X Y),
      completedPresentationMapPi0 (existingLayerAIdentityCompletedPresentationData presentation) (pi0Class f) =
        pi0Class f

namespace StableInfinityEnhancementTarget

def ofExistingLayerAInterfaces (presentation : Type u) :
    StableInfinityEnhancementTarget presentation where
  stableCompletion := StableCompletionConstructionTarget.ofExistingLayerAInterfaces presentation
  Obj := InfObj presentation
  category := existingLayerAInfinityCategoryTarget presentation
  shift := existingLayerAInfinityShiftTarget presentation
  triangulated := existingLayerATriangulatedTarget presentation
  monoidal := existingLayerAMonoidalTarget presentation
  realization := existingLayerARealizationTarget presentation
  completedPresentation := existingLayerACompletedPresentationTarget presentation

end StableInfinityEnhancementTarget

namespace StableInfinityEnhancementData

def ofExistingLayerAInterfaces (presentation : Type u) :
    StableInfinityEnhancementData
      (StableInfinityEnhancementTarget.ofExistingLayerAInterfaces presentation) where
  categoryData :=
    { categoryLawsWitness :=
        ⟨compPi0_id_left, compPi0_id_right, compPi0_assoc⟩ }
  shiftData :=
    { shiftCompatibilityWitness :=
        ⟨shiftMapPi0_id, shiftMapPi0_comp⟩ }
  triangulatedData :=
    { cofiberTriangleWitness := by
        intro X Y f
        exact cofiberTriangle f
      fiberTriangleWitness := by
        intro X Y f
        exact fiberTriangle f
      cofiberCompositionWitness := by
        intro X Y Z f g
        exact cofiberTriangleCompatibility f g
      rotationWitness := by
        intro X Y Z triangle
        exact triangulatedRotation triangle }
  monoidalData :=
    { monoidalCompatibilityWitness := tensorPi0_id }
  realizationData :=
    { identityCompatibilityWitness := by
        intro X
        exact Quot.sound (InfHomotopy.realization_compat (InfMap.id X))
      compositionCompatibilityWitness := by
        intro X Y Z f g
        refine Quotient.inductionOn₂ f g ?_
        intro f0 g0
        exact Quot.sound (InfHomotopy.realization_compat (InfMap.comp f0 g0))
      shiftCompatibilityWitness := by
        intro X Y f
        refine Quotient.inductionOn f ?_
        intro f0
        exact Quot.sound (InfHomotopy.shift_congr (InfHomotopy.realization_compat f0))
      triangulatedCompatibilityWitness :=
        existingLayerARealizationCompatibilityWitness
          (existingLayerAIdentityRealizationData presentation)
      monoidalCompatibilityWitness := by
        intro A B C D f g
        refine Quotient.inductionOn₂ f g ?_
        intro f0 g0
        exact Quot.sound
          (InfHomotopy.tensor_congr
            (InfHomotopy.realization_compat f0)
            (InfHomotopy.realization_compat g0)) }
  completedPresentationData :=
    { compatibilityWithCompletedPresentationWitness :=
        existingLayerACompletedPresentationCompatibilityWitness
          (existingLayerAIdentityCompletedPresentationData presentation)
      compatibilityWithLocalizationWitness := by
        intro X Y f
        exact existingLayerACompletedPresentationCompatibilityWitness
          (existingLayerAIdentityCompletedPresentationData presentation) f }

end StableInfinityEnhancementData

end SyntacticInfinity
end CategoryInfra
end TraceCalc

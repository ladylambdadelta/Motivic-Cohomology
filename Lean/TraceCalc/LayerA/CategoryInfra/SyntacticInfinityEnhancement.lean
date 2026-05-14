import TraceCalc.LayerA.CategoryInfra.SyntacticStableCompletion

universe u

namespace TraceCalc
namespace CategoryInfra
namespace SyntacticInfinity

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

def identityRealizationData (presentation : Type u) :
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

theorem syntactic_realizationCompatibility_holds {presentation : Type u}
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

def identityCompletedPresentationData (presentation : Type u) :
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

theorem syntactic_completedPresentationCompatibility_holds {presentation : Type u}
    (P : SyntacticCompletedPresentationData presentation) :
    SyntacticCompletedPresentationCompatibilityStatement P := by
  intro X Y f
  exact Quot.sound (P.generator_agrees f)

end SyntacticInfinity
end CategoryInfra
end TraceCalc

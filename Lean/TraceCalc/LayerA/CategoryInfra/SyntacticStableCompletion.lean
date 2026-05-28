import Batteries.Data.List.FinRange
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Logic.Equiv.Fin
import TraceCalc.LayerA.CategoryInfra.ExactnessTransport
import TraceCalc.LayerA.CategoryInfra.MonoidalPresentation
import TraceCalc.LayerA.CategoryInfra.MonoidalTransport

universe u v

namespace TraceCalc
namespace CategoryInfra

open CategoryTheory
open scoped BigOperators

/-- Honest source data for the concrete Layer A constructor: a quiver of generating
objects and arrows, rather than a bare object type with untyped word syntax. -/
class PresentationQuiver (presentation : Type u) where
  HomGen : presentation → presentation → Type u

/-- Composable generator paths in the free category on the presentation quiver. -/
inductive PresentationPath (presentation : Type u) [PresentationQuiver presentation] :
    presentation → presentation → Type u where
  | nil (X : presentation) : PresentationPath presentation X X
  | cons {X Y Z : presentation} :
      PresentationQuiver.HomGen X Y →
        PresentationPath presentation Y Z →
          PresentationPath presentation X Z

compile_inductive% PresentationPath

namespace PresentationPath

def append {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : presentation}
    (left : PresentationPath presentation X Y)
    (right : PresentationPath presentation Y Z) :
    PresentationPath presentation X Z := by
  induction left with
  | nil _ => exact right
  | cons gen tail ih => exact cons gen (ih right)

@[simp] theorem nil_append {presentation : Type u} [PresentationQuiver presentation]
    {X Y : presentation} (path : PresentationPath presentation X Y) :
    append (nil X) path = path := by
  rfl

@[simp] theorem append_nil {presentation : Type u} [PresentationQuiver presentation]
    {X Y : presentation} (path : PresentationPath presentation X Y) :
    append path (nil Y) = path := by
  induction path with
  | nil _ => rfl
  | cons gen tail ih => exact congrArg (PresentationPath.cons gen) ih

@[simp] theorem append_assoc {presentation : Type u} [PresentationQuiver presentation]
    {W X Y Z : presentation}
    (first : PresentationPath presentation W X)
    (second : PresentationPath presentation X Y)
    (third : PresentationPath presentation Y Z) :
    append (append first second) third = append first (append second third) := by
  induction first with
  | nil _ => rfl
  | cons gen tail ih => exact congrArg (PresentationPath.cons gen) (ih second)

end PresentationPath

structure DGMorphismCompositionTarget (C : DGCategoryLike.{u, v}) where
  id : ∀ X : C.Obj, C.HomComplex X X
  comp : ∀ {X Y Z : C.Obj}, C.HomComplex X Y → C.HomComplex Y Z → C.HomComplex X Z

structure DGMorphismCompositionLaws {C : DGCategoryLike.{u, v}}
    (target : DGMorphismCompositionTarget C) where
  idComp :
    ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
      target.comp (target.id X) f = f
  compId :
    ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
      target.comp f (target.id Y) = f
  assoc :
    ∀ {W X Y Z : C.Obj}
      (f : C.HomComplex W X)
      (g : C.HomComplex X Y)
      (h : C.HomComplex Y Z),
        target.comp (target.comp f g) h =
          target.comp f (target.comp g h)

structure DGMorphismCompositionData {C : DGCategoryLike.{u, v}}
    (target : DGMorphismCompositionTarget C) where
  laws : DGMorphismCompositionLaws target

structure StableCompletionConstructionTarget (presentation : Type u) where
  freeDG : FreeDGEnvelope.{u, u} presentation
  freeDGComposition : DGMorphismCompositionTarget freeDG.envelope
  pretriangulatedHull : PretriangulatedHull freeDG.envelope
  h0Source : StandardDGCategoryLike.{u, u}
  h0Target : StandardH0CategoryTarget h0Source
  karoubiEnvelope : StandardH0CategoryTarget.AsCategory.KaroubiCompletion h0Target
  exactnessTransport :
    ExactnessTransportTarget freeDG pretriangulatedHull h0Target

structure StableCompletionConstructionData {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) where
  freeDGCompositionData : DGMorphismCompositionData target.freeDGComposition
  exactnessTransportData : ExactnessTransportData target.exactnessTransport

namespace StableCompletionConstructionTarget

def homotopyCategory {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) :
    H0TriangulatedData target.pretriangulatedHull :=
  target.exactnessTransport.exactnessForH0

def idempotentSplitting {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) : Prop :=
  CategoryTheory.IsIdempotentComplete
    (StandardH0CategoryTarget.AsCategory.KaroubiCompletion target.h0Target)

def karoubiUniversalProperty {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) : Prop :=
  Nonempty
    (CategoryTheory.Functor
      (StandardH0CategoryTarget.AsCategory target.h0Target)
      (StandardH0CategoryTarget.AsCategory.KaroubiCompletion target.h0Target))

theorem karoubiUniversalProperty_holds {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) :
    target.karoubiUniversalProperty := by
  exact ⟨StandardH0CategoryTarget.AsCategory.toKaroubi target.h0Target⟩

abbrev h0Category {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) : Type u :=
  StandardH0CategoryTarget.AsCategory target.h0Target

abbrev karoubiCompletion {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) : Type u :=
  StandardH0CategoryTarget.AsCategory.KaroubiCompletion target.h0Target

end StableCompletionConstructionTarget

/-- Objects in the free dg envelope generated by a presentation. -/
inductive FreeDGObject (presentation : Type u) : Type u where
  | base : presentation → FreeDGObject presentation

namespace FreeDGObject

def carrier {presentation : Type u} : FreeDGObject presentation → presentation
  | base p => p

def recTo {presentation : Type u} {D : Type u}
    (ι : presentation → D) : FreeDGObject presentation → D
  | base p => ι p

@[simp] theorem carrier_base {presentation : Type u} (p : presentation) :
    carrier (base p) = p :=
  rfl

@[simp] theorem recTo_base {presentation : Type u} {D : Type u}
    (ι : presentation → D) (p : presentation) :
    recTo ι (base p) = ι p :=
  rfl

def tensor {presentation : Type u} [MonoidalPresentation presentation] :
    FreeDGObject presentation → FreeDGObject presentation → FreeDGObject presentation
  | base p, base q => base (MonoidalPresentation.tensorObj p q)

@[simp] theorem carrier_tensor {presentation : Type u} [MonoidalPresentation presentation]
    (X Y : FreeDGObject presentation) :
    carrier (tensor X Y) =
      MonoidalPresentation.tensorObj (carrier X) (carrier Y) := by
  cases X
  cases Y
  rfl

@[simp] theorem tensor_assoc {presentation : Type u} [MonoidalPresentation presentation]
    (X Y Z : FreeDGObject presentation) :
    tensor (tensor X Y) Z = tensor X (tensor Y Z) := by
  cases X
  cases Y
  cases Z
  simp [tensor, MonoidalPresentation.tensorAssoc]

end FreeDGObject

/-- Formal composable arrows in the free dg envelope.

Each morphism is either a genuinely composable path in the presentation quiver
or the adjoined zero morphism. The differential remains zero, i.e. this is the
free path category with zero morphisms viewed as a zero-differential dg model. -/
structure FreeDGMorphism {presentation : Type u} [PresentationQuiver presentation]
    (X Y : FreeDGObject presentation) : Type u where
  path? : Option (PresentationPath presentation (FreeDGObject.carrier X) (FreeDGObject.carrier Y))

namespace FreeDGMorphism

def zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation} :
    FreeDGMorphism X Y where
  path? := none

def id {presentation : Type u} [PresentationQuiver presentation]
    (X : FreeDGObject presentation) :
    FreeDGMorphism X X where
  path? := some (PresentationPath.nil (FreeDGObject.carrier X))

def comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : FreeDGObject presentation}
    (f : FreeDGMorphism X Y) (g : FreeDGMorphism Y Z) :
    FreeDGMorphism X Z where
  path? :=
    match f.path?, g.path? with
    | some left, some right => some (PresentationPath.append left right)
    | _, _ => none

def differential {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation}
    (_f : FreeDGMorphism X Y) : FreeDGMorphism X Y :=
  zero

theorem differential_squared_zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation} (f : FreeDGMorphism X Y) :
    differential (differential f) = zero :=
  rfl

@[simp] theorem id_comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation} (f : FreeDGMorphism X Y) :
    comp (id X) f = f := by
  cases f with
  | mk path? =>
      cases path? <;> rfl

@[simp] theorem comp_id {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation} (f : FreeDGMorphism X Y) :
    comp f (id Y) = f := by
  cases f with
  | mk path? =>
      cases path? with
      | none => rfl
      | some path => simp [comp, id, PresentationPath.append_nil]

@[simp] theorem comp_assoc {presentation : Type u} [PresentationQuiver presentation]
    {W X Y Z : FreeDGObject presentation}
    (f : FreeDGMorphism W X)
    (g : FreeDGMorphism X Y)
    (h : FreeDGMorphism Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | mk fpath =>
      cases g with
      | mk gpath =>
          cases h with
          | mk hpath =>
              cases fpath <;> cases gpath <;> cases hpath <;>
                simp [comp, PresentationPath.append_assoc]

end FreeDGMorphism

def syntacticDGCategory (presentation : Type u) [PresentationQuiver presentation] :
    DGCategoryLike.{u, u} where
  Obj := FreeDGObject presentation
  HomComplex := FreeDGMorphism
  zero := FreeDGMorphism.zero
  differential := FreeDGMorphism.differential

private def syntacticDGCategoryData (presentation : Type u) [PresentationQuiver presentation] :
    DGCategoryData (syntacticDGCategory presentation) where
  laws :=
    { differentialSquaredZero := by
        intro X Y f
        simpa [syntacticDGCategory] using FreeDGMorphism.differential_squared_zero f }

def freeDGEnvelopeUniversalProperty (presentation : Type u) [PresentationQuiver presentation] :
    FreeDGUniversalProperty
      presentation
      (FreeDGObject presentation)
      FreeDGObject.base where
  liftObj := fun {D} ι => FreeDGObject.recTo ι
  lift_include := by
    intro D ι p
    rfl

private def syntacticFreeDGEnvelope (presentation : Type u) [PresentationQuiver presentation] :
    FreeDGEnvelope.{u, u} presentation where
  envelope := syntacticDGCategory presentation
  includeObj := FreeDGObject.base
  universalProperty := freeDGEnvelopeUniversalProperty presentation

/-- A shifted dg generator in the additive closure of the free dg envelope. -/
structure StandardPretriangulatedSummand (presentation : Type u) where
  base : FreeDGObject presentation
  shift : Int

namespace StandardPretriangulatedSummand

def tensor {presentation : Type u} [MonoidalPresentation presentation]
    (X Y : StandardPretriangulatedSummand presentation) :
    StandardPretriangulatedSummand presentation where
  base := FreeDGObject.tensor X.base Y.base
  shift := X.shift + Y.shift

@[simp] theorem tensor_assoc {presentation : Type u} [MonoidalPresentation presentation]
    (X Y Z : StandardPretriangulatedSummand presentation) :
    tensor (tensor X Y) Z = tensor X (tensor Y Z) := by
  cases X
  cases Y
  cases Z
  simp [tensor, FreeDGObject.tensor_assoc, Int.add_assoc]

end StandardPretriangulatedSummand

/-- Honest object-level skeleton for the pretriangulated hull: finite direct sums
of integer shifts of dg generators. This is the standard additive-envelope shape
used by the normalized dg and `H0` constructions below. -/
abbrev StandardPretriangulatedObject (presentation : Type u) : Type u :=
  List (StandardPretriangulatedSummand presentation)

namespace StandardPretriangulatedObject

def ofDG {presentation : Type u} (X : FreeDGObject presentation) :
    StandardPretriangulatedObject presentation :=
  [{ base := X, shift := 0 }]

def shiftBy {presentation : Type u} (n : Int)
    (X : StandardPretriangulatedObject presentation) :
    StandardPretriangulatedObject presentation :=
  X.map fun summand => { summand with shift := summand.shift + n }

def shift {presentation : Type u} :
    StandardPretriangulatedObject presentation →
      StandardPretriangulatedObject presentation :=
  shiftBy 1

def biproduct {presentation : Type u}
    (X Y : StandardPretriangulatedObject presentation) :
    StandardPretriangulatedObject presentation :=
  X ++ Y

def cone {presentation : Type u}
    (X Y : StandardPretriangulatedObject presentation) :
    StandardPretriangulatedObject presentation :=
  biproduct (shift X) Y

def tensor {presentation : Type u} [MonoidalPresentation presentation]
    (X Y : StandardPretriangulatedObject presentation) :
    StandardPretriangulatedObject presentation :=
  X.bind fun x =>
    Y.bind fun y => [StandardPretriangulatedSummand.tensor x y]

@[simp] theorem tensor_nil_left {presentation : Type u} [MonoidalPresentation presentation]
    (X : StandardPretriangulatedObject presentation) :
    tensor [] X = [] :=
  rfl

@[simp] theorem tensor_nil_right {presentation : Type u} [MonoidalPresentation presentation]
    (X : StandardPretriangulatedObject presentation) :
    tensor X [] = [] := by
  simp [tensor]

@[simp] theorem tensor_ofDG {presentation : Type u} [MonoidalPresentation presentation]
    (X Y : FreeDGObject presentation) :
    tensor (ofDG X) (ofDG Y) = ofDG (FreeDGObject.tensor X Y) := by
  cases X
  cases Y
  simp [tensor, ofDG, StandardPretriangulatedSummand.tensor, FreeDGObject.tensor]

@[simp] theorem tensor_assoc {presentation : Type u} [MonoidalPresentation presentation]
    (X Y Z : StandardPretriangulatedObject presentation) :
    tensor (tensor X Y) Z = tensor X (tensor Y Z) := by
  simp [tensor, List.bind_assoc, StandardPretriangulatedSummand.tensor_assoc]

end StandardPretriangulatedObject

/-- An integer-weighted basis path in a matrix entry of the additive envelope. -/
structure WeightedPresentationPath {presentation : Type u}
    [PresentationQuiver presentation]
    (X Y : presentation) where
  coeff : Int
  path : PresentationPath presentation X Y

namespace WeightedPresentationPath

def append {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : presentation}
    (left : WeightedPresentationPath X Y)
    (right : WeightedPresentationPath Y Z) :
    WeightedPresentationPath X Z where
  coeff := left.coeff * right.coeff
  path := PresentationPath.append left.path right.path

def neg {presentation : Type u} [PresentationQuiver presentation]
    {X Y : presentation}
    (term : WeightedPresentationPath X Y) :
    WeightedPresentationPath X Y where
  coeff := -term.coeff
  path := term.path

end WeightedPresentationPath

/-- Basis elements for a degree-`n` matrix component. Compatibility with the
grading is encoded by the existence of the witness `h`, so incompatible entries
have no basis elements at all. -/
abbrev StandardGradedComponentBasis {presentation : Type u}
    [PresentationQuiver presentation]
    (X Y : StandardPretriangulatedObject presentation)
    (n : Int)
    (i : Fin X.length)
    (j : Fin Y.length) : Type u :=
    PLift ((X.get i).shift + n = (Y.get j).shift) ×
      WeightedPresentationPath
        (presentation := presentation)
        (FreeDGObject.carrier (X.get i).base)
        (FreeDGObject.carrier (Y.get j).base)

def reindexBasis {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {m n : Int}
    {i : Fin X.length}
    {j : Fin Y.length}
    (h : m = n) :
    StandardGradedComponentBasis X Y m i j →
      StandardGradedComponentBasis X Y n i j
  | ⟨hshift, term⟩ =>
      ⟨⟨by
          cases h
          exact hshift.down⟩,
        term⟩

@[simp] theorem reindexBasis_rfl {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    {i : Fin X.length}
    {j : Fin Y.length}
    (basis : StandardGradedComponentBasis X Y n i j) :
    reindexBasis (X := X) (Y := Y) (i := i) (j := j) rfl basis = basis := by
  cases basis
  rfl

def reindexComponent {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {m n : Int}
    {i : Fin X.length}
    {j : Fin Y.length}
    (h : m = n) :
    FreeAbelianGroup (StandardGradedComponentBasis X Y m i j) →
      FreeAbelianGroup (StandardGradedComponentBasis X Y n i j) :=
  FreeAbelianGroup.map (reindexBasis (X := X) (Y := Y) (i := i) (j := j) h)

@[simp] theorem reindexComponent_rfl {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    {i : Fin X.length}
    {j : Fin Y.length}
    (component : FreeAbelianGroup (StandardGradedComponentBasis X Y n i j)) :
    reindexComponent (X := X) (Y := Y) (i := i) (j := j) rfl component = component := by
  refine FreeAbelianGroup.induction_on component ?_ ?_ ?_ ?_
  · rfl
  · intro basis
    simpa [reindexComponent] using congrArg FreeAbelianGroup.of
      (reindexBasis_rfl (X := X) (Y := Y) (i := i) (j := j) basis)
  · intro basis ih
    simpa [reindexComponent] using congrArg Neg.neg ih
  · intro x y hx hy
    calc
      reindexComponent (X := X) (Y := Y) (i := i) (j := j) rfl (x + y)
          = reindexComponent (X := X) (Y := Y) (i := i) (j := j) rfl x +
              reindexComponent (X := X) (Y := Y) (i := i) (j := j) rfl y := by
                simp [reindexComponent]
      _ = x + y := by simpa [hx, hy]

/-- Concrete graded homs on normalized pretriangulated objects: finite formal
integer combinations of generator paths placed in entries with the right shift
difference. -/
structure StandardGradedPretriangulatedMorphism {presentation : Type u}
    [PresentationQuiver presentation]
    (X Y : StandardPretriangulatedObject presentation)
    (n : Int) : Type u where
  entries :
    (i : Fin X.length) → (j : Fin Y.length) →
      FreeAbelianGroup (StandardGradedComponentBasis X Y n i j)

namespace StandardGradedPretriangulatedMorphism

@[ext] theorem ext {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} {n : Int}
    {f g : StandardGradedPretriangulatedMorphism X Y n}
  (h : f.entries = g.entries) : f = g := by
  cases f
  cases g
  cases h
  rfl

def reindex {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {m n : Int}
    (h : m = n)
    (f : StandardGradedPretriangulatedMorphism X Y m) :
    StandardGradedPretriangulatedMorphism X Y n where
  entries := fun i j =>
    reindexComponent (X := X) (Y := Y) (i := i) (j := j) h (f.entries i j)

@[simp] theorem reindex_rfl {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    reindex (X := X) (Y := Y) rfl f = f := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext i j
  exact reindexComponent_rfl (X := X) (Y := Y) (i := i) (j := j) (f.entries i j)

theorem reindex_eq_mp {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {m n : Int}
    (h : m = n)
    (f : StandardGradedPretriangulatedMorphism X Y m) :
    reindex (X := X) (Y := Y) h f = Eq.mp (by cases h; rfl) f := by
  cases h
  simpa using reindex_rfl (X := X) (Y := Y) f

def zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} (n : Int) :
    StandardGradedPretriangulatedMorphism X Y n where
  entries := fun _ _ => 0

def add {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} {n : Int}
    (f g : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism X Y n where
  entries := fun i j => f.entries i j + g.entries i j

def neg {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} {n : Int}
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism X Y n where
  entries := fun i j => -f.entries i j

def sub {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} {n : Int}
    (f g : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism X Y n :=
  add f (neg g)

def signedByParity {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation} {n : Int}
    (parity : Int)
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism X Y n :=
  if parity % 2 = 0 then f else neg f

def id {presentation : Type u} [PresentationQuiver presentation]
    (X : StandardPretriangulatedObject presentation) :
    StandardGradedPretriangulatedMorphism X X 0 where
  entries := fun i j =>
    if h : i = j then
      by
        subst h
        exact FreeAbelianGroup.of
          ⟨⟨by simp⟩,
            { coeff := 1, path := PresentationPath.nil (FreeDGObject.carrier (X.get i).base) }⟩
    else
      0

def composeComponent {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j))
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    FreeAbelianGroup (StandardGradedComponentBasis X Z (a + b) i k) :=
  FreeAbelianGroup.lift
    (fun leftBasis =>
      FreeAbelianGroup.lift
        (fun rightBasis =>
          FreeAbelianGroup.of
            ⟨⟨by
                calc
                  (X.get i).shift + (a + b) = ((X.get i).shift + a) + b := by simp [Int.add_assoc]
                  _ = (Y.get j).shift + b := by rw [leftBasis.1.down]
                  _ = (Z.get k).shift := by rw [rightBasis.1.down]⟩,
              WeightedPresentationPath.append leftBasis.2 rightBasis.2⟩)
        right)
    left

def composeComponentLeftAddHom {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    FreeAbelianGroup (StandardGradedComponentBasis X Y a i j) →+
      FreeAbelianGroup (StandardGradedComponentBasis X Z (a + b) i k) where
  toFun := fun left => composeComponent i j k left right
  map_zero' := by
    unfold composeComponent
    simp
  map_add' := by
    intro x y
    unfold composeComponent
    simp

def composeComponentRightAddHom {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j)) :
    FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k) →+
      FreeAbelianGroup (StandardGradedComponentBasis X Z (a + b) i k) :=
  FreeAbelianGroup.lift
    (fun leftBasis =>
      FreeAbelianGroup.lift
        (fun rightBasis =>
          FreeAbelianGroup.of
            ⟨⟨by
                calc
                  (X.get i).shift + (a + b) = ((X.get i).shift + a) + b := by
                    simp [Int.add_assoc]
                  _ = (Y.get j).shift + b := by rw [leftBasis.1.down]
                  _ = (Z.get k).shift := by rw [rightBasis.1.down]⟩,
              WeightedPresentationPath.append leftBasis.2 rightBasis.2⟩))
    left

def comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {i j : Int}
    (f : StandardGradedPretriangulatedMorphism X Y i)
    (g : StandardGradedPretriangulatedMorphism Y Z j) :
    StandardGradedPretriangulatedMorphism X Z (i + j) where
  entries := fun source target =>
    ∑ middle : Fin Y.length,
      composeComponent source middle target (f.entries source middle) (g.entries middle target)

@[simp] theorem composeComponent_zero_left {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    composeComponent (a := a) (b := b) i j k
      (0 : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j)) right = 0 := by
  simpa [composeComponentLeftAddHom] using
    (composeComponentLeftAddHom (a := a) (b := b) i j k right).map_zero

@[simp] theorem composeComponent_zero_right {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j)) :
    composeComponent (a := a) (b := b) i j k left
      (0 : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) = 0 := by
  refine FreeAbelianGroup.induction_on left ?_ ?_ ?_ ?_
  · simp [composeComponent]
  · intro leftBasis
    simp [composeComponent]
  · intro leftBasis ih
    simpa [composeComponent] using congrArg Neg.neg ih
  · intro left₁ left₂ hLeft₁ hLeft₂
    simpa [composeComponent] using congrArg₂ HAdd.hAdd hLeft₁ hLeft₂

@[simp] theorem composeComponent_add_left {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left₁ left₂ : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j))
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    composeComponent i j k (left₁ + left₂) right =
      composeComponent i j k left₁ right + composeComponent i j k left₂ right := by
  simpa [composeComponentLeftAddHom] using
    (composeComponentLeftAddHom (a := a) (b := b) i j k right).map_add left₁ left₂

@[simp] theorem composeComponent_add_right {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j))
    (right₁ right₂ : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    composeComponent i j k left (right₁ + right₂) =
      composeComponent i j k left right₁ + composeComponent i j k left right₂ := by
  refine FreeAbelianGroup.induction_on left ?_ ?_ ?_ ?_
  · simp [composeComponent]
  · intro leftBasis
    simp [composeComponent]
  · intro leftBasis ih
    calc
      composeComponent i j k (-FreeAbelianGroup.of leftBasis) (right₁ + right₂)
          = -composeComponent i j k (FreeAbelianGroup.of leftBasis) (right₁ + right₂) := by
              simp [composeComponent]
      _ = -(composeComponent i j k (FreeAbelianGroup.of leftBasis) right₁ +
            composeComponent i j k (FreeAbelianGroup.of leftBasis) right₂) := by
              rw [ih]
      _ = -composeComponent i j k (FreeAbelianGroup.of leftBasis) right₁ +
            -composeComponent i j k (FreeAbelianGroup.of leftBasis) right₂ := by
              simpa [add_comm]
      _ = composeComponent i j k (-FreeAbelianGroup.of leftBasis) right₁ +
            composeComponent i j k (-FreeAbelianGroup.of leftBasis) right₂ := by
              simp [composeComponent]
  · intro left₁ left₂ hLeft₁ hLeft₂
    calc
      composeComponent i j k (left₁ + left₂) (right₁ + right₂)
          = composeComponent i j k left₁ (right₁ + right₂) +
              composeComponent i j k left₂ (right₁ + right₂) := by
                rw [composeComponent_add_left]
      _ = (composeComponent i j k left₁ right₁ + composeComponent i j k left₁ right₂) +
            (composeComponent i j k left₂ right₁ + composeComponent i j k left₂ right₂) := by
              rw [hLeft₁, hLeft₂]
      _ = (composeComponent i j k left₁ right₁ + composeComponent i j k left₂ right₁) +
            (composeComponent i j k left₁ right₂ + composeComponent i j k left₂ right₂) := by
              simpa [add_assoc, add_left_comm, add_comm]
      _ = composeComponent i j k (left₁ + left₂) right₁ +
            composeComponent i j k (left₁ + left₂) right₂ := by
              rw [composeComponent_add_left, composeComponent_add_left]

@[simp] theorem composeComponent_sum_left {presentation : Type u}
    [PresentationQuiver presentation]
    {ι : Type*}
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (s : Finset ι)
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : ι → FreeAbelianGroup (StandardGradedComponentBasis X Y a i j))
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    composeComponent i j k (∑ t in s, left t) right =
      ∑ t in s, composeComponent i j k (left t) right := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa [composeComponentLeftAddHom] using
      (composeComponentLeftAddHom (a := a) (b := b) i j k right).map_zero
  · intro x s hx hs
    simp [Finset.sum_insert, hx, hs, composeComponent_add_left]

@[simp] theorem composeComponent_sum_right {presentation : Type u}
    [PresentationQuiver presentation]
    {ι : Type*}
    {X Y Z : StandardPretriangulatedObject presentation}
    {a b : Int}
    (s : Finset ι)
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y a i j))
    (right : ι → FreeAbelianGroup (StandardGradedComponentBasis Y Z b j k)) :
    composeComponent i j k left (∑ t in s, right t) =
      ∑ t in s, composeComponent i j k left (right t) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · exact composeComponent_zero_right i j k left
  · intro x s hx hs
    simp [Finset.sum_insert, hx, hs, composeComponent_add_right]

@[simp] theorem composeComponent_id_left {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (i : Fin X.length)
    (k : Fin Y.length)
    (right : FreeAbelianGroup (StandardGradedComponentBasis X Y n i k)) :
    composeComponent (a := 0) (b := n) i i k
      (FreeAbelianGroup.of
        ⟨⟨by simp⟩,
          { coeff := 1
            path := PresentationPath.nil (FreeDGObject.carrier (X.get i).base) }⟩)
      right = reindexComponent (X := X) (Y := Y) (i := i) (j := k)
        (by simp [Int.zero_add]) right := by
  refine FreeAbelianGroup.induction_on right ?_ ?_ ?_ ?_
  · simp [composeComponent, reindexComponent]
  · intro rightBasis
    rcases rightBasis with ⟨hshift, term⟩
    cases hshift
    cases term
    simp [composeComponent, reindexComponent, reindexBasis,
      WeightedPresentationPath.append, PresentationPath.nil_append]
  · intro rightBasis ih
    simpa [composeComponent, reindexComponent] using congrArg Neg.neg ih
  · intro x y hx hy
    rw [composeComponent_add_right, hx, hy]
    simp [reindexComponent]

@[simp] theorem composeComponent_id_right {presentation : Type u}
    [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (i : Fin X.length)
    (k : Fin Y.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis X Y n i k)) :
    composeComponent (a := n) (b := 0) i k k left
      (FreeAbelianGroup.of
        ⟨⟨by simp⟩,
          { coeff := 1
            path := PresentationPath.nil (FreeDGObject.carrier (Y.get k).base) }⟩) =
      reindexComponent (X := X) (Y := Y) (i := i) (j := k)
        (by simp [Int.add_zero]) left := by
  refine FreeAbelianGroup.induction_on left ?_ ?_ ?_ ?_
  · simp [composeComponent, reindexComponent]
  · intro leftBasis
    rcases leftBasis with ⟨hshift, term⟩
    cases hshift
    cases term
    simp [composeComponent, reindexComponent, reindexBasis,
      WeightedPresentationPath.append, PresentationPath.append_nil]
  · intro leftBasis ih
    simpa [composeComponent, reindexComponent] using congrArg Neg.neg ih
  · intro x y hx hy
    rw [composeComponent_add_left, hx, hy]
    simp [reindexComponent]

@[simp] theorem composeComponent_assoc {presentation : Type u}
    [PresentationQuiver presentation]
    {W X Y Z : StandardPretriangulatedObject presentation}
    {a b c : Int}
    (i : Fin W.length)
    (j : Fin X.length)
    (k : Fin Y.length)
    (l : Fin Z.length)
    (left : FreeAbelianGroup (StandardGradedComponentBasis W X a i j))
    (middle : FreeAbelianGroup (StandardGradedComponentBasis X Y b j k))
    (right : FreeAbelianGroup (StandardGradedComponentBasis Y Z c k l)) :
    composeComponent i k l (composeComponent i j k left middle) right =
      reindexComponent (X := W) (Y := Z) (i := i) (j := l)
        (by simp [Int.add_assoc])
        (composeComponent i j l left (composeComponent j k l middle right)) := by
  refine FreeAbelianGroup.induction_on left ?_ ?_ ?_ ?_
  · simp [composeComponent, reindexComponent]
  · intro leftBasis
    refine FreeAbelianGroup.induction_on middle ?_ ?_ ?_ ?_
    · simp [composeComponent, reindexComponent]
    · intro middleBasis
      refine FreeAbelianGroup.induction_on right ?_ ?_ ?_ ?_
      · simp [composeComponent, reindexComponent]
      · intro rightBasis
        rcases leftBasis with ⟨hleft, leftTerm⟩
        rcases middleBasis with ⟨hmiddle, middleTerm⟩
        rcases rightBasis with ⟨hright, rightTerm⟩
        simp [composeComponent, reindexComponent, reindexBasis, WeightedPresentationPath.append,
          PresentationPath.append_assoc, hleft.down, hmiddle.down, hright.down, Int.add_assoc,
          mul_assoc]
      · intro rightBasis ih
        simpa [composeComponent, reindexComponent] using congrArg Neg.neg ih
      · intro x y hx hy
        calc
          composeComponent i k l
              (composeComponent i j k (FreeAbelianGroup.of leftBasis)
                (FreeAbelianGroup.of middleBasis)) (x + y)
              = composeComponent i k l
                  (composeComponent i j k (FreeAbelianGroup.of leftBasis)
                    (FreeAbelianGroup.of middleBasis)) x +
                  composeComponent i k l
                    (composeComponent i j k (FreeAbelianGroup.of leftBasis)
                      (FreeAbelianGroup.of middleBasis)) y := by
                        rw [composeComponent_add_right]
          _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
                (by simp [Int.add_assoc])
                (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                  (composeComponent j k l (FreeAbelianGroup.of middleBasis) x) +
                 composeComponent i j l (FreeAbelianGroup.of leftBasis)
                  (composeComponent j k l (FreeAbelianGroup.of middleBasis) y)) := by
                    simpa [reindexComponent, Int.add_assoc] using congrArg₂ HAdd.hAdd hx hy
          _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
                (by simp [Int.add_assoc])
                (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                  (composeComponent j k l (FreeAbelianGroup.of middleBasis) x +
                   composeComponent j k l (FreeAbelianGroup.of middleBasis) y)) := by
                    congr 1
                    exact
                      (composeComponent_add_right i j l (FreeAbelianGroup.of leftBasis)
                        (composeComponent j k l (FreeAbelianGroup.of middleBasis) x)
                        (composeComponent j k l (FreeAbelianGroup.of middleBasis) y)).symm
          _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
                (by simp [Int.add_assoc])
                (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                  (composeComponent j k l (FreeAbelianGroup.of middleBasis) (x + y))) := by
                    exact congrArg
                      (reindexComponent (X := W) (Y := Z) (i := i) (j := l)
                        (by simp [Int.add_assoc]))
                      (congrArg
                        (composeComponent i j l (FreeAbelianGroup.of leftBasis))
                        ((composeComponent_add_right j k l (FreeAbelianGroup.of middleBasis) x y).symm))
    · intro middleBasis ih
      simpa [composeComponent, reindexComponent] using congrArg Neg.neg ih
    · intro x y hx hy
      calc
        composeComponent i k l
            (composeComponent i j k (FreeAbelianGroup.of leftBasis) (x + y)) right
            = composeComponent i k l
                (composeComponent i j k (FreeAbelianGroup.of leftBasis) x +
                  composeComponent i j k (FreeAbelianGroup.of leftBasis) y) right := by
                    rw [composeComponent_add_right]
        _ = composeComponent i k l
              (composeComponent i j k (FreeAbelianGroup.of leftBasis) x) right +
            composeComponent i k l
              (composeComponent i j k (FreeAbelianGroup.of leftBasis) y) right := by
                rw [composeComponent_add_left]
        _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
              (by simp [Int.add_assoc])
              (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                (composeComponent j k l x right) +
               composeComponent i j l (FreeAbelianGroup.of leftBasis)
                (composeComponent j k l y right)) := by
                  simpa [reindexComponent, Int.add_assoc] using congrArg₂ HAdd.hAdd hx hy
        _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
              (by simp [Int.add_assoc])
              (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                (composeComponent j k l x right + composeComponent j k l y right)) := by
                  rw [composeComponent_add_right]
        _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
              (by simp [Int.add_assoc])
              (composeComponent i j l (FreeAbelianGroup.of leftBasis)
                (composeComponent j k l (x + y) right)) := by
                  rw [composeComponent_add_left]
  · intro leftBasis ih
    simpa [composeComponent, reindexComponent] using congrArg Neg.neg ih
  · intro x y hx hy
    calc
      composeComponent i k l (composeComponent i j k (x + y) middle) right
          = composeComponent i k l
              (composeComponent i j k x middle + composeComponent i j k y middle) right := by
                rw [composeComponent_add_left]
      _ = composeComponent i k l (composeComponent i j k x middle) right +
            composeComponent i k l (composeComponent i j k y middle) right := by
              rw [composeComponent_add_left]
      _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
        (by simp [Int.add_assoc])
        (composeComponent i j l x (composeComponent j k l middle right) +
         composeComponent i j l y (composeComponent j k l middle right)) := by
          simpa [reindexComponent, Int.add_assoc] using congrArg₂ HAdd.hAdd hx hy
      _ = reindexComponent (X := W) (Y := Z) (i := i) (j := l)
        (by simp [Int.add_assoc])
        (composeComponent i j l (x + y) (composeComponent j k l middle right)) := by
          rw [composeComponent_add_left]

/-- Reinterpret a degree-zero map as a degree-one map out of the desuspended
source object. This is the first local cone-side helper needed for an honest
map-dependent cone construction over the additive source category. -/
def shiftBothBy {presentation : Type u} [PresentationQuiver presentation]
    (shift : Int)
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism
      (StandardPretriangulatedObject.shiftBy shift X)
      (StandardPretriangulatedObject.shiftBy shift Y) n where
  entries := fun i j =>
    let sourceIndex : Fin X.length :=
      ⟨i.1, by simpa [StandardPretriangulatedObject.shiftBy] using i.2⟩
    let targetIndex : Fin Y.length :=
      ⟨j.1, by simpa [StandardPretriangulatedObject.shiftBy] using j.2⟩
    FreeAbelianGroup.map
      (fun basis =>
        match basis with
        | ⟨hshift, term⟩ =>
            ⟨⟨by
                simpa [StandardPretriangulatedObject.shiftBy, Int.add_assoc, Int.add_left_comm,
                  Int.add_comm] using hshift.down⟩,
              by
                simpa [StandardPretriangulatedObject.shiftBy] using term⟩)
      (f.entries sourceIndex targetIndex)

@[simp] theorem shiftBothBy_zero {presentation : Type u} [PresentationQuiver presentation]
    (shift : Int)
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int} :
    shiftBothBy shift (zero (X := X) (Y := Y) n) =
      zero (X := StandardPretriangulatedObject.shiftBy shift X)
        (Y := StandardPretriangulatedObject.shiftBy shift Y) n := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext i j
  simp [shiftBothBy, zero]

@[simp] theorem shiftBothBy_add {presentation : Type u} [PresentationQuiver presentation]
    (shift : Int)
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (f g : StandardGradedPretriangulatedMorphism X Y n) :
    shiftBothBy shift (add f g) =
      add (shiftBothBy shift f) (shiftBothBy shift g) := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext i j
  simp [shiftBothBy, add]

@[simp] theorem shiftBothBy_neg {presentation : Type u} [PresentationQuiver presentation]
    (shift : Int)
    {X Y : StandardPretriangulatedObject presentation}
    {n : Int}
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    shiftBothBy shift (neg f) = neg (shiftBothBy shift f) := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext i j
  simp [shiftBothBy, neg]

def sourceDesuspensionOfDegreeZero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    (f : StandardGradedPretriangulatedMorphism X Y 0) :
    StandardGradedPretriangulatedMorphism
      (StandardPretriangulatedObject.shiftBy (-1) X) Y 1 where
  entries := fun i j =>
    let sourceIndex : Fin X.length :=
      ⟨i.1, by simpa [StandardPretriangulatedObject.shiftBy] using i.2⟩
    FreeAbelianGroup.map
      (fun basis =>
        match basis with
        | ⟨hshift, term⟩ =>
            ⟨⟨by
                simpa [StandardPretriangulatedObject.shiftBy, Int.add_assoc, Int.add_left_comm,
                  Int.add_comm] using hshift.down⟩,
              by
                simpa [StandardPretriangulatedObject.shiftBy] using term⟩)
      (f.entries sourceIndex j)

@[simp] theorem comp_zero_left {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {i j : Int}
    (g : StandardGradedPretriangulatedMorphism Y Z j) :
    comp (zero (X := X) (Y := Y) i) g = zero (X := X) (Y := Z) (i + j) := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext source target
  change (∑ middle : Fin Y.length,
      composeComponent source middle target 0 (g.entries middle target)) = 0
  exact Fintype.sum_eq_zero _ (by
    intro middle
    simp [composeComponent])

@[simp] theorem comp_zero_right {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {i j : Int}
    (f : StandardGradedPretriangulatedMorphism X Y i) :
    comp f (zero (X := Y) (Y := Z) j) = zero (X := X) (Y := Z) (i + j) := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext source target
  change (∑ middle : Fin Y.length,
      composeComponent source middle target (f.entries source middle) 0) = 0
  exact Fintype.sum_eq_zero _ (by
    intro middle
    refine FreeAbelianGroup.induction_on (f.entries source middle) ?_ ?_ ?_ ?_
    · simp [composeComponent]
    · intro leftBasis
      simp [composeComponent]
    · intro leftBasis ih
      simpa [composeComponent] using congrArg Neg.neg ih
    · intro x y hx hy
      calc
        composeComponent source middle target (x + y) 0
            = composeComponent source middle target x 0 +
                composeComponent source middle target y 0 := by
                  rw [composeComponent_add_left]
        _ = 0 + 0 := by rw [hx, hy]
        _ = 0 := by simp
      )

@[simp] theorem comp_add_left {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {i j : Int}
    (f₁ f₂ : StandardGradedPretriangulatedMorphism X Y i)
    (g : StandardGradedPretriangulatedMorphism Y Z j) :
    comp (add f₁ f₂) g = add (comp f₁ g) (comp f₂ g) := by
  ext source target
  simp [comp, add, Finset.sum_add_distrib]

@[simp] theorem comp_add_right {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardPretriangulatedObject presentation}
    {i j : Int}
    (f : StandardGradedPretriangulatedMorphism X Y i)
    (g₁ g₂ : StandardGradedPretriangulatedMorphism Y Z j) :
    comp f (add g₁ g₂) = add (comp f g₁) (comp f g₂) := by
  ext source target
  simp [comp, add, Finset.sum_add_distrib]

@[simp] theorem id_comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    (f : StandardGradedPretriangulatedMorphism X Y 0) :
    comp (id X) f = f := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext source target
  classical
  change (∑ middle : Fin X.length,
      composeComponent source middle target ((id X).entries source middle)
        (f.entries middle target)) = f.entries source target
  rw [Fintype.sum_eq_single source]
  · have hreindex :
        reindexComponent (X := X) (Y := Y) (i := source) (j := target)
          (by simp [Int.zero_add]) (f.entries source target) = f.entries source target := by
        refine FreeAbelianGroup.induction_on (f.entries source target) ?_ ?_ ?_ ?_
        · rfl
        · intro basis
          rcases basis with ⟨hshift, term⟩
          have hproof : (show (0 : Int) = 0 + 0 by simp [Int.zero_add]) = rfl :=
            Subsingleton.elim _ _
          cases hproof
          cases hshift
          cases term
          simp [reindexComponent, reindexBasis]
        · intro basis ih
          simpa [reindexComponent] using congrArg Neg.neg ih
        · intro x y hx hy
          calc
            reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                (by simp [Int.zero_add]) (x + y)
                = reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                    (by simp [Int.zero_add]) x +
                  reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                    (by simp [Int.zero_add]) y := by
                      simp [reindexComponent]
            _ = x + y := by simpa [hx, hy]
    have hleft :
        composeComponent source source target ((id X).entries source source)
          (f.entries source target) =
        reindexComponent (X := X) (Y := Y) (i := source) (j := target)
          (by simp [Int.zero_add]) (f.entries source target) := by
      simpa [id] using composeComponent_id_left source target (f.entries source target)
    exact hleft.trans hreindex
  · intro middle hne
    have hsource : source ≠ middle := hne.symm
    simp [id, hsource, composeComponent]

@[simp] theorem comp_id {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    (f : StandardGradedPretriangulatedMorphism X Y 0) :
    comp f (id Y) = f := by
  apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
  funext source target
  classical
  change (∑ middle : Fin Y.length,
      composeComponent source middle target (f.entries source middle)
        ((id Y).entries middle target)) = f.entries source target
  rw [Fintype.sum_eq_single target]
  · have hreindex :
        reindexComponent (X := X) (Y := Y) (i := source) (j := target)
          (by simp [Int.add_zero]) (f.entries source target) = f.entries source target := by
        refine FreeAbelianGroup.induction_on (f.entries source target) ?_ ?_ ?_ ?_
        · rfl
        · intro basis
          rcases basis with ⟨hshift, term⟩
          have hproof : (show (0 : Int) = 0 + 0 by simp [Int.add_zero]) = rfl :=
            Subsingleton.elim _ _
          cases hproof
          cases hshift
          cases term
          simp [reindexComponent, reindexBasis]
        · intro basis ih
          simpa [reindexComponent] using congrArg Neg.neg ih
        · intro x y hx hy
          calc
            reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                (by simp [Int.add_zero]) (x + y)
                = reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                    (by simp [Int.add_zero]) x +
                  reindexComponent (X := X) (Y := Y) (i := source) (j := target)
                    (by simp [Int.add_zero]) y := by
                      simp [reindexComponent]
            _ = x + y := by simpa [hx, hy]
    have hright :
        composeComponent source target target (f.entries source target)
          ((id Y).entries target target) =
        reindexComponent (X := X) (Y := Y) (i := source) (j := target)
          (by simp [Int.add_zero]) (f.entries source target) := by
      simpa [id] using composeComponent_id_right source target (f.entries source target)
    exact hright.trans hreindex
  · intro middle hne
    refine FreeAbelianGroup.induction_on (f.entries source middle) ?_ ?_ ?_ ?_
    · simp [id, hne, composeComponent]
    · intro leftBasis
      simp [id, hne, composeComponent]
    · intro leftBasis ih
      simpa [id, hne, composeComponent] using congrArg Neg.neg ih
    · intro x y hx hy
      calc
        composeComponent source middle target (x + y) ((id Y).entries middle target)
            = composeComponent source middle target x ((id Y).entries middle target) +
                composeComponent source middle target y ((id Y).entries middle target) := by
                  rw [composeComponent_add_left]
        _ = 0 + 0 := by rw [hx, hy]
        _ = 0 := by simp

@[simp] theorem comp_assoc {presentation : Type u} [PresentationQuiver presentation]
    {W X Y Z : StandardPretriangulatedObject presentation}
    {a b c : Int}
    (f : StandardGradedPretriangulatedMorphism W X a)
    (g : StandardGradedPretriangulatedMorphism X Y b)
    (h : StandardGradedPretriangulatedMorphism Y Z c) :
    comp (comp f g) h =
      Eq.mp
        (by
          change StandardGradedPretriangulatedMorphism W Z (a + (b + c)) =
            StandardGradedPretriangulatedMorphism W Z (a + b + c)
          simp [Int.add_assoc])
        (comp f (comp g h)) := by
  have habc : a + (b + c) = a + b + c := by
    omega
  have hcomp :
      comp (comp f g) h =
        reindex (X := W) (Y := Z) habc (comp f (comp g h)) := by
    apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
    funext source target
    classical
    calc
      ((comp (comp f g) h).entries source target)
          =
      (∑ middle₁ in (Finset.univ : Finset (Fin Y.length)),
        ∑ middle₂ in (Finset.univ : Finset (Fin X.length)),
          composeComponent source middle₁ target
            (composeComponent source middle₂ middle₁ (f.entries source middle₂)
              (g.entries middle₂ middle₁))
            (h.entries middle₁ target)) := by
            simp [comp]
      _ =
      (∑ middle₁ in (Finset.univ : Finset (Fin Y.length)),
        ∑ middle₂ in (Finset.univ : Finset (Fin X.length)),
          reindexComponent (X := W) (Y := Z) (i := source) (j := target) habc
            (composeComponent source middle₂ target (f.entries source middle₂)
              (composeComponent middle₂ middle₁ target (g.entries middle₂ middle₁)
                (h.entries middle₁ target)))) := by
            refine Finset.sum_congr rfl ?_
            intro middle₁ _
            refine Finset.sum_congr rfl ?_
            intro middle₂ _
            simpa using composeComponent_assoc
              source middle₂ middle₁ target
              (f.entries source middle₂)
              (g.entries middle₂ middle₁)
              (h.entries middle₁ target)
      _ = reindexComponent (X := W) (Y := Z) (i := source) (j := target) habc
            (∑ middle₁ in (Finset.univ : Finset (Fin Y.length)),
              ∑ middle₂ in (Finset.univ : Finset (Fin X.length)),
                composeComponent source middle₂ target (f.entries source middle₂)
                  (composeComponent middle₂ middle₁ target (g.entries middle₂ middle₁)
                    (h.entries middle₁ target))) := by
              simp [reindexComponent]
      _ = reindexComponent (X := W) (Y := Z) (i := source) (j := target) habc
            (∑ middle₂ in (Finset.univ : Finset (Fin X.length)),
              ∑ middle₁ in (Finset.univ : Finset (Fin Y.length)),
                composeComponent source middle₂ target (f.entries source middle₂)
                  (composeComponent middle₂ middle₁ target (g.entries middle₂ middle₁)
                    (h.entries middle₁ target))) := by
              exact congrArg
                (reindexComponent (X := W) (Y := Z) (i := source) (j := target) habc)
                (by rw [Finset.sum_comm])
      _ = (reindex (X := W) (Y := Z) habc (comp f (comp g h))).entries source target := by
            simp [reindex, comp]
  calc
    comp (comp f g) h = reindex (X := W) (Y := Z) habc (comp f (comp g h)) := hcomp
    _ = Eq.mp
          (by
            change StandardGradedPretriangulatedMorphism W Z (a + (b + c)) =
              StandardGradedPretriangulatedMorphism W Z (a + b + c)
            simp [Int.add_assoc])
          (comp f (comp g h)) := by
            simpa using reindex_eq_mp (X := W) (Y := Z) habc (comp f (comp g h))

def differential {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    (n : Int)
    (_f : StandardGradedPretriangulatedMorphism X Y n) :
    StandardGradedPretriangulatedMorphism X Y (n + 1) :=
  zero (n + 1)

def ofFreeDG {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation}
    (f : FreeDGMorphism X Y) :
    StandardGradedPretriangulatedMorphism
      (StandardPretriangulatedObject.ofDG X)
      (StandardPretriangulatedObject.ofDG Y) 0 where
  entries := fun _ _ =>
    match f.path? with
    | none => 0
    | some path =>
        FreeAbelianGroup.of
          ⟨⟨by simp [StandardPretriangulatedObject.ofDG]⟩,
            by
              simpa [StandardPretriangulatedObject.ofDG] using
                ({ coeff := 1, path := path } : WeightedPresentationPath X.carrier Y.carrier)⟩

theorem differential_squared_zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardPretriangulatedObject presentation}
    (n : Int)
    (f : StandardGradedPretriangulatedMorphism X Y n) :
    differential (n + 1) (differential n f) =
      Eq.mp
        (by
          change StandardGradedPretriangulatedMorphism X Y (n + (1 + 1)) =
            StandardGradedPretriangulatedMorphism X Y (n + 1 + 1)
          simp [Int.add_assoc])
        (zero (X := X) (Y := Y) (n + 2)) := by
  have htwo : n + 2 = n + 1 + 1 := by
    omega
  calc
    differential (n + 1) (differential n f)
        = reindex (X := X) (Y := Y) htwo (zero (X := X) (Y := Y) (n + 2)) := by
            apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
            funext source target
            simp [differential, zero, reindex, reindexComponent]
    _ = Eq.mp
          (by
            change StandardGradedPretriangulatedMorphism X Y (n + (1 + 1)) =
              StandardGradedPretriangulatedMorphism X Y (n + 1 + 1)
            simp [Int.add_assoc])
          (zero (X := X) (Y := Y) (n + 2)) := by
            simpa using reindex_eq_mp (X := X) (Y := Y) htwo
              (zero (X := X) (Y := Y) (n + 2))

end StandardGradedPretriangulatedMorphism

def standardNormalizedPretriangulatedDGCategory (presentation : Type u)
    [PresentationQuiver presentation] :
    StandardDGCategoryLike.{u, u} where
  Obj := StandardPretriangulatedObject presentation
  Hom := StandardGradedPretriangulatedMorphism
  zero := StandardGradedPretriangulatedMorphism.zero
  add := fun _ f g => StandardGradedPretriangulatedMorphism.add f g
  neg := fun _ f => StandardGradedPretriangulatedMorphism.neg f
  id := StandardGradedPretriangulatedMorphism.id
  comp := fun f g => StandardGradedPretriangulatedMorphism.comp f g
  differential := StandardGradedPretriangulatedMorphism.differential

private def standardNormalizedPretriangulatedDGCategoryData (presentation : Type u)
    [PresentationQuiver presentation] :
    StandardDGCategoryData (standardNormalizedPretriangulatedDGCategory presentation) where
  laws :=
    { add_assoc := by
        intro X Y n a b c
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.add, add_assoc]
      add_comm := by
        intro X Y n a b
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.add, add_comm]
      zero_add := by
        intro X Y n a
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.add,
          StandardGradedPretriangulatedMorphism.zero]
      add_zero := by
        intro X Y n a
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.add,
          StandardGradedPretriangulatedMorphism.zero]
      add_left_neg := by
        intro X Y n a
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.add,
          StandardGradedPretriangulatedMorphism.neg,
          StandardGradedPretriangulatedMorphism.zero]
      id_comp := by
        intro X Y f
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.id_comp f
      comp_id := by
        intro X Y f
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_id f
      comp_assoc := by
        intro W X Y Z i j k f g h
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_assoc f g h
      comp_zero_left := by
        intro X Y Z i j g
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_zero_left g
      comp_zero_right := by
        intro X Y Z i j f
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_zero_right f
      comp_add_left := by
        intro X Y Z i j f₁ f₂ g
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_add_left f₁ f₂ g
      comp_add_right := by
        intro X Y Z i j f g₁ g₂
        exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_add_right f g₁ g₂
      differential_zero := by
        intro X Y n
        rfl
      differential_add := by
        intro X Y n a b
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.differential,
          StandardGradedPretriangulatedMorphism.add,
          StandardGradedPretriangulatedMorphism.zero]
      differential_neg := by
        intro X Y n a
        apply TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.ext
        funext source target
        simp [standardNormalizedPretriangulatedDGCategory,
          StandardGradedPretriangulatedMorphism.differential,
          StandardGradedPretriangulatedMorphism.neg,
          StandardGradedPretriangulatedMorphism.zero]
      differential_squaredZero := by
        intro X Y n f
        simpa [standardNormalizedPretriangulatedDGCategory] using
          (TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.differential_squared_zero
            (X := X) (Y := Y) n f)
      id_closed := by
        intro X
        rfl
      closed_comp := by
        intro X Y Z f g
        rfl }

def standardNormalizedPretriangulatedH0Target (presentation : Type u)
    [PresentationQuiver presentation] :
    StandardH0CategoryTarget (standardNormalizedPretriangulatedDGCategory presentation) :=
  StandardH0CategoryTarget.ofZeroDifferential
    (C := standardNormalizedPretriangulatedDGCategory presentation)
    (standardNormalizedPretriangulatedDGCategoryData presentation)
    (by
      intro X Y n f
      rfl)

abbrev StandardNormalizedPretriangulatedH0Category (presentation : Type u)
    [PresentationQuiver presentation] : Type u :=
  StandardH0CategoryTarget.AsCategory
    (standardNormalizedPretriangulatedH0Target presentation)

abbrev StandardNormalizedPretriangulatedKaroubiCompletion (presentation : Type u)
    [PresentationQuiver presentation] : Type u :=
  StandardH0CategoryTarget.AsCategory.KaroubiCompletion
    (standardNormalizedPretriangulatedH0Target presentation)

structure StandardTwistedComplex (presentation : Type u)
    [PresentationQuiver presentation] where
  carrier : StandardPretriangulatedObject presentation
  differential : StandardGradedPretriangulatedMorphism carrier carrier 1
  differential_squared_zero :
    StandardGradedPretriangulatedMorphism.comp differential differential =
      StandardGradedPretriangulatedMorphism.zero 2

namespace StandardTwistedComplex

abbrev Hom {presentation : Type u} [PresentationQuiver presentation]
    (X Y : StandardTwistedComplex presentation)
    (n : Int) : Type u :=
  StandardGradedPretriangulatedMorphism X.carrier Y.carrier n

def id {presentation : Type u} [PresentationQuiver presentation]
    (X : StandardTwistedComplex presentation) : Hom X X 0 :=
  StandardGradedPretriangulatedMorphism.id X.carrier

def comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : StandardTwistedComplex presentation}
    {i j : Int}
    (f : Hom X Y i)
    (g : Hom Y Z j) : Hom X Z (i + j) :=
  StandardGradedPretriangulatedMorphism.comp f g

def differentialOnHom {presentation : Type u} [PresentationQuiver presentation]
    {X Y : StandardTwistedComplex presentation}
    (n : Int)
    (f : Hom X Y n) : Hom X Y (n + 1) := by
  let left : Hom X Y (n + 1) :=
    StandardGradedPretriangulatedMorphism.comp f Y.differential
  let right : Hom X Y (n + 1) := by
    simpa [Int.add_comm] using
      (StandardGradedPretriangulatedMorphism.comp X.differential f)
  exact StandardGradedPretriangulatedMorphism.sub left
    (StandardGradedPretriangulatedMorphism.signedByParity n right)

def ofAdditiveObject {presentation : Type u} [PresentationQuiver presentation]
    (X : StandardPretriangulatedObject presentation) :
    StandardTwistedComplex presentation where
  carrier := X
  differential := StandardGradedPretriangulatedMorphism.zero 1
  differential_squared_zero := by
    simpa using
      (TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_zero_left
        (StandardGradedPretriangulatedMorphism.zero 1))

def ofDGObject {presentation : Type u} [PresentationQuiver presentation]
    (X : FreeDGObject presentation) : StandardTwistedComplex presentation :=
  ofAdditiveObject (StandardPretriangulatedObject.ofDG X)

end StandardTwistedComplex

def standardTwistedComplexDGCategory (presentation : Type u)
    [PresentationQuiver presentation] :
    StandardDGCategoryLike.{u, u} where
  Obj := StandardTwistedComplex presentation
  Hom := StandardTwistedComplex.Hom
  zero := StandardGradedPretriangulatedMorphism.zero
  add := fun _ f g => StandardGradedPretriangulatedMorphism.add f g
  neg := fun _ f => StandardGradedPretriangulatedMorphism.neg f
  id := StandardTwistedComplex.id
  comp := fun f g => StandardTwistedComplex.comp f g
  differential := StandardTwistedComplex.differentialOnHom

/-- Formal pretriangulated closure syntax used to express the universal-property
layer, with semantics computed through zero-differential twisted complexes. -/
inductive FormalPretriangulatedObject (presentation : Type u) : Type u where
  | ofDG : FreeDGObject presentation → FormalPretriangulatedObject presentation
  | shift : FormalPretriangulatedObject presentation → FormalPretriangulatedObject presentation
  | cone :
      FormalPretriangulatedObject presentation →
      FormalPretriangulatedObject presentation →
      FormalPretriangulatedObject presentation

namespace FormalPretriangulatedObject

def normalForm {presentation : Type u} [PresentationQuiver presentation] :
    FormalPretriangulatedObject presentation → StandardTwistedComplex presentation
  | ofDG X => StandardTwistedComplex.ofDGObject X
  | shift X =>
      StandardTwistedComplex.ofAdditiveObject
        (StandardPretriangulatedObject.shift (normalForm X).carrier)
  | cone X Y =>
      StandardTwistedComplex.ofAdditiveObject
        (StandardPretriangulatedObject.cone (normalForm X).carrier (normalForm Y).carrier)

@[simp] theorem normalForm_ofDG {presentation : Type u} [PresentationQuiver presentation]
    (X : FreeDGObject presentation) :
    normalForm (ofDG X) = StandardTwistedComplex.ofDGObject X :=
  rfl

@[simp] theorem normalForm_shift {presentation : Type u} [PresentationQuiver presentation]
    (X : FormalPretriangulatedObject presentation) :
    normalForm (shift X) =
      StandardTwistedComplex.ofAdditiveObject
        (StandardPretriangulatedObject.shift (normalForm X).carrier) :=
  rfl

@[simp] theorem normalForm_cone {presentation : Type u} [PresentationQuiver presentation]
    (X Y : FormalPretriangulatedObject presentation) :
    normalForm (cone X Y) =
      StandardTwistedComplex.ofAdditiveObject
        (StandardPretriangulatedObject.cone (normalForm X).carrier (normalForm Y).carrier) :=
  rfl

@[simp] def toStandardNormalizedObject {presentation : Type u}
    [PresentationQuiver presentation]
    (X : FormalPretriangulatedObject presentation) : StandardPretriangulatedObject presentation :=
  (normalForm X).carrier

@[simp] def toStandardNormalizedH0Object {presentation : Type u}
    [PresentationQuiver presentation]
    (X : FormalPretriangulatedObject presentation) :
    StandardNormalizedPretriangulatedH0Category presentation :=
  ⟨X.toStandardNormalizedObject⟩

@[simp] def toStandardNormalizedKaroubiObject {presentation : Type u}
    [PresentationQuiver presentation]
    (X : FormalPretriangulatedObject presentation) :
    StandardNormalizedPretriangulatedKaroubiCompletion presentation :=
  StandardH0CategoryTarget.AsCategory.karoubiOfObj
    (standardNormalizedPretriangulatedH0Target presentation)
    X.toStandardNormalizedObject

end FormalPretriangulatedObject

structure FormalPretriangulatedMorphism {presentation : Type u} [PresentationQuiver presentation]
    (X Y : FormalPretriangulatedObject presentation) : Type u where
  matrix :
    StandardTwistedComplex.Hom
      (FormalPretriangulatedObject.normalForm X)
      (FormalPretriangulatedObject.normalForm Y)
      0

namespace FormalPretriangulatedMorphism

def ofStandardDegreeZero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation}
    (f : StandardTwistedComplex.Hom
      (FormalPretriangulatedObject.normalForm X)
      (FormalPretriangulatedObject.normalForm Y)
      0) :
    FormalPretriangulatedMorphism X Y where
  matrix := f

def ofFreeDG {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FreeDGObject presentation}
    (f : FreeDGMorphism X Y) :
    FormalPretriangulatedMorphism
      (FormalPretriangulatedObject.ofDG X)
      (FormalPretriangulatedObject.ofDG Y) :=
  ofStandardDegreeZero (StandardGradedPretriangulatedMorphism.ofFreeDG f)

@[ext] theorem ext {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation}
    {f g : FormalPretriangulatedMorphism X Y}
    (h : f.matrix = g.matrix) : f = g := by
  cases f
  cases g
  cases h
  rfl

def zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation} :
    FormalPretriangulatedMorphism X Y where
  matrix := StandardGradedPretriangulatedMorphism.zero 0

def id {presentation : Type u} [PresentationQuiver presentation]
    (X : FormalPretriangulatedObject presentation) :
    FormalPretriangulatedMorphism X X where
  matrix := StandardTwistedComplex.id (FormalPretriangulatedObject.normalForm X)

def comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y Z : FormalPretriangulatedObject presentation}
    (f : FormalPretriangulatedMorphism X Y) (g : FormalPretriangulatedMorphism Y Z) :
    FormalPretriangulatedMorphism X Z where
  matrix := StandardTwistedComplex.comp f.matrix g.matrix

def differential {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation}
    (_f : FormalPretriangulatedMorphism X Y) : FormalPretriangulatedMorphism X Y :=
  zero

theorem differential_squared_zero {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation}
    (f : FormalPretriangulatedMorphism X Y) :
    differential (differential f) = zero := by
  ext
  rfl

@[simp] theorem id_comp {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation} (f : FormalPretriangulatedMorphism X Y) :
    comp (id X) f = f := by
  apply FormalPretriangulatedMorphism.ext
  exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.id_comp f.matrix

@[simp] theorem comp_id {presentation : Type u} [PresentationQuiver presentation]
    {X Y : FormalPretriangulatedObject presentation} (f : FormalPretriangulatedMorphism X Y) :
    comp f (id Y) = f := by
  apply FormalPretriangulatedMorphism.ext
  exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_id f.matrix

@[simp] theorem comp_assoc {presentation : Type u} [PresentationQuiver presentation]
    {W X Y Z : FormalPretriangulatedObject presentation}
    (f : FormalPretriangulatedMorphism W X)
    (g : FormalPretriangulatedMorphism X Y)
    (h : FormalPretriangulatedMorphism Y Z) :
    comp (comp f g) h = comp f (comp g h) := by
  apply FormalPretriangulatedMorphism.ext
  exact TraceCalc.CategoryInfra.StandardGradedPretriangulatedMorphism.comp_assoc
    f.matrix g.matrix h.matrix

end FormalPretriangulatedMorphism

def formalPretriangulatedDGCategory (presentation : Type u) [PresentationQuiver presentation] :
    DGCategoryLike.{u, u} where
  Obj := FormalPretriangulatedObject presentation
  HomComplex := FormalPretriangulatedMorphism
  zero := FormalPretriangulatedMorphism.zero
  differential := FormalPretriangulatedMorphism.differential

private def formalPretriangulatedDGCategoryData (presentation : Type u)
    [PresentationQuiver presentation] :
    DGCategoryData (formalPretriangulatedDGCategory presentation) where
  laws :=
    { differentialSquaredZero := by
        intro X Y f
        simpa [formalPretriangulatedDGCategory] using
          FormalPretriangulatedMorphism.differential_squared_zero f }

def formalPretriangulatedShift (presentation : Type u) :
    ShiftStructure (FormalPretriangulatedObject presentation) where
  obj := FormalPretriangulatedObject.shift

def formalPretriangulatedCone (presentation : Type u) :
    ConeStructure (FormalPretriangulatedObject presentation) where
  obj := FormalPretriangulatedObject.cone

def FormalPretriangulatedObject.recTo {presentation : Type u} {D : Type u}
  (ι : FreeDGObject presentation → D)
  (shift : D → D)
  (cone : D → D → D) :
  FormalPretriangulatedObject presentation → D
  | FormalPretriangulatedObject.ofDG X => ι X
  | FormalPretriangulatedObject.shift X => shift (recTo ι shift cone X)
  | FormalPretriangulatedObject.cone X Y => cone (recTo ι shift cone X) (recTo ι shift cone Y)

def formalPretriangulatedHullUniversalProperty (presentation : Type u) :
    PretriangulatedUniversalProperty
      (FreeDGObject presentation)
      (FormalPretriangulatedObject presentation)
      FormalPretriangulatedObject.ofDG
      (formalPretriangulatedShift presentation).obj
      (formalPretriangulatedCone presentation).obj where
  liftObj := fun {D} ι shift cone =>
    FormalPretriangulatedObject.recTo (D := D) ι shift cone
  lift_include := by
    intro D ι shift cone X
    rfl
  lift_shift := by
    intro D ι shift cone X
    rfl
  lift_cone := by
    intro D ι shift cone X Y
    rfl

private def formalPretriangulatedHull (presentation : Type u)
  [PresentationQuiver presentation] :
    PretriangulatedHull (syntacticFreeDGEnvelope presentation).envelope where
  hull := formalPretriangulatedDGCategory presentation
  includeObj := FormalPretriangulatedObject.ofDG
  shift := formalPretriangulatedShift presentation
  cone := formalPretriangulatedCone presentation
  universalProperty := formalPretriangulatedHullUniversalProperty presentation

def formalH0DistinguishedTriangles (presentation : Type u) :
    ConeStructure (FormalPretriangulatedObject presentation) :=
  formalPretriangulatedCone presentation

def formalH0TriangulatedAxioms (presentation : Type u) :
    ShiftStructure (FormalPretriangulatedObject presentation) ×
      ConeStructure (FormalPretriangulatedObject presentation) :=
  ⟨formalPretriangulatedShift presentation, formalPretriangulatedCone presentation⟩

def formalH0LocalizationAtAcyclics (presentation : Type u) :
    PretriangulatedUniversalProperty
      (FreeDGObject presentation)
      (FormalPretriangulatedObject presentation)
      FormalPretriangulatedObject.ofDG
      (formalPretriangulatedShift presentation).obj
      (formalPretriangulatedCone presentation).obj :=
  formalPretriangulatedHullUniversalProperty presentation

def exactnessDG (presentation : Type u) [PresentationQuiver presentation] : Prop :=
  ∀ {X Y : FreeDGObject presentation} (f : FreeDGMorphism X Y),
    FreeDGMorphism.differential (FreeDGMorphism.differential f) = FreeDGMorphism.zero

def exactnessFormalPretriangulated (presentation : Type u) [PresentationQuiver presentation] : Prop :=
  ∀ {X Y : FormalPretriangulatedObject presentation}
    (f : FormalPretriangulatedMorphism X Y),
    FormalPretriangulatedMorphism.differential
        (FormalPretriangulatedMorphism.differential f) = FormalPretriangulatedMorphism.zero

def exactnessH0 (presentation : Type u) [PresentationQuiver presentation] : Type (u + 1) :=
  H0TriangulatedData (formalPretriangulatedHull presentation)

private theorem syntacticExactnessDGWitness (presentation : Type u)
  [PresentationQuiver presentation] :
    exactnessDG presentation := by
  intro X Y f
  exact FreeDGMorphism.differential_squared_zero f

private theorem formalExactnessPretriangulatedWitness (presentation : Type u)
  [PresentationQuiver presentation] :
    exactnessFormalPretriangulated presentation := by
  exact fun {_ _} f => FormalPretriangulatedMorphism.differential_squared_zero f

private def syntacticExactnessH0Witness (presentation : Type u)
  [PresentationQuiver presentation] :
    exactnessH0 presentation :=
  { distinguishedTriangles := by
      simpa [exactnessH0, formalPretriangulatedHull, formalPretriangulatedDGCategory]
        using formalH0DistinguishedTriangles presentation
    triangulatedAxioms := by
      simpa [exactnessH0, formalPretriangulatedHull, formalPretriangulatedDGCategory]
        using formalH0TriangulatedAxioms presentation
    localizationAtAcyclics := by
      simpa [exactnessH0, formalPretriangulatedHull, syntacticFreeDGEnvelope,
        formalPretriangulatedDGCategory]
        using formalH0LocalizationAtAcyclics presentation }

private def syntacticExactnessTransport (presentation : Type u)
  [PresentationQuiver presentation] :
    ExactnessTransportTarget
      (syntacticFreeDGEnvelope presentation)
      (formalPretriangulatedHull presentation)
      (standardNormalizedPretriangulatedH0Target presentation) where
  exactnessForH0 := syntacticExactnessH0Witness presentation
  exactnessForKaroubiCompletion :=
    StandardH0CategoryTarget.AsCategory.karoubi_idempotentComplete
      (standardNormalizedPretriangulatedH0Target presentation)
  distinguishedTriangleTransport := by
    simpa [formalPretriangulatedHull, formalPretriangulatedDGCategory]
      using formalH0DistinguishedTriangles presentation

private def syntacticExactnessTransportData (presentation : Type u)
  [PresentationQuiver presentation] :
    ExactnessTransportData (syntacticExactnessTransport presentation) :=
  { laws :=
      { exactnessForDGEnvelope := syntacticExactnessDGWitness presentation
        exactnessForPretriangulatedHull := by
          intro X Y f
          exact FormalPretriangulatedMorphism.differential_squared_zero f } }

private def syntacticFreeDGCompositionTarget (presentation : Type u)
    [PresentationQuiver presentation] :
  DGMorphismCompositionTarget (syntacticFreeDGEnvelope presentation).envelope where
  id := FreeDGMorphism.id
  comp := FreeDGMorphism.comp

private def h0EqHom {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : C.Obj}
    (h : X = Y) :
    H.H0Hom X Y := by
  cases h
  exact H.identity X

private def karoubiEqHom {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : StandardH0CategoryTarget.AsCategory.KaroubiCompletion H}
    (h : X = Y) :
    X ⟶ Y :=
  CategoryTheory.eqToHom h

private theorem h0EqHom_hom_inv_id {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : C.Obj}
    (h : X = Y) :
    H.compose (h0EqHom H h) (h0EqHom H h.symm) = H.identity X := by
  cases h
  simpa [h0EqHom] using H.identity_comp (H.identity X)

private theorem h0EqHom_inv_hom_id {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : C.Obj}
    (h : X = Y) :
    H.compose (h0EqHom H h.symm) (h0EqHom H h) = H.identity Y := by
  cases h
  simpa [h0EqHom] using H.identity_comp (H.identity X)

private theorem karoubiEqHom_hom_inv_id {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : StandardH0CategoryTarget.AsCategory.KaroubiCompletion H}
    (h : X = Y) :
    (karoubiEqHom H h) ≫ (karoubiEqHom H h.symm) = 𝟙 X := by
  cases h
  simp [karoubiEqHom]

private theorem karoubiEqHom_inv_hom_id {C : StandardDGCategoryLike.{u, u}}
    (H : StandardH0CategoryTarget C)
    {X Y : StandardH0CategoryTarget.AsCategory.KaroubiCompletion H}
    (h : X = Y) :
    (karoubiEqHom H h.symm) ≫ (karoubiEqHom H h) = 𝟙 Y := by
  cases h
  simp [karoubiEqHom]

structure StableCompletionMonoidalTransportPackage {presentation : Type u}
    [MonoidalPresentation presentation]
    (target : StableCompletionConstructionTarget presentation) where
  transport :
    MonoidalTransportTarget
      target.freeDG
      target.pretriangulatedHull
      target.h0Target
  data : MonoidalTransportData transport

namespace StableCompletionMonoidalTransportPackage

def throughDGEnvelope {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) : Prop :=
  ∀ p q : presentation,
    package.transport.tensorOnDG (target.freeDG.includeObj p) (target.freeDG.includeObj q) =
      target.freeDG.includeObj (MonoidalPresentation.tensorObj p q)

def throughPretriangulatedHull {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) : Prop :=
  ∀ X Y : target.freeDG.envelope.Obj,
    package.transport.tensorOnH0
        (package.transport.h0ObjOfHull (target.pretriangulatedHull.includeObj X))
        (package.transport.h0ObjOfHull (target.pretriangulatedHull.includeObj Y)) =
      package.transport.h0ObjOfHull
        (target.pretriangulatedHull.includeObj (package.transport.tensorOnDG X Y))

def throughH0 {presentation : Type u}
  [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) : Prop :=
  Nonempty (H0TensorAssociator target.h0Target package.transport.tensorOnH0)

def throughKaroubiEnvelope {presentation : Type u}
  [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) : Prop :=
  ∀ X Y : target.h0Source.Obj,
    package.transport.tensorOnKaroubi
        (StandardH0CategoryTarget.AsCategory.karoubiOfObj target.h0Target X)
        (StandardH0CategoryTarget.AsCategory.karoubiOfObj target.h0Target Y) =
      StandardH0CategoryTarget.AsCategory.karoubiOfObj
        target.h0Target
        (package.transport.tensorOnH0 X Y)

theorem throughDGEnvelope_holds {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) :
    package.throughDGEnvelope :=
  package.data.compatibility.throughDGEnvelope

theorem throughPretriangulatedHull_holds {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) :
    package.throughPretriangulatedHull :=
  package.data.compatibility.throughPretriangulatedHull

theorem throughH0_holds {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) :
    package.throughH0 :=
  ⟨package.data.h0Associator⟩

theorem throughKaroubiEnvelope_holds {presentation : Type u}
    [MonoidalPresentation presentation]
    {target : StableCompletionConstructionTarget presentation}
    (package : StableCompletionMonoidalTransportPackage target) :
    package.throughKaroubiEnvelope :=
  package.data.compatibility.throughKaroubiCompletion

end StableCompletionMonoidalTransportPackage

namespace StableCompletionConstructionTarget

def syntactic (presentation : Type u) [PresentationQuiver presentation] :
    StableCompletionConstructionTarget presentation where
  freeDG := syntacticFreeDGEnvelope presentation
  freeDGComposition := syntacticFreeDGCompositionTarget presentation
  pretriangulatedHull := formalPretriangulatedHull presentation
  h0Source := standardNormalizedPretriangulatedDGCategory presentation
  h0Target := standardNormalizedPretriangulatedH0Target presentation
  karoubiEnvelope :=
    StandardH0CategoryTarget.AsCategory.karoubiOfObj
      (standardNormalizedPretriangulatedH0Target presentation) []
  exactnessTransport := syntacticExactnessTransport presentation

def monoidalTransport (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] :
    StableCompletionMonoidalTransportPackage
      (StableCompletionConstructionTarget.syntactic presentation) := by
  let transport :
      MonoidalTransportTarget
        (syntacticFreeDGEnvelope presentation)
        (formalPretriangulatedHull presentation)
        (standardNormalizedPretriangulatedH0Target presentation) :=
    { h0ObjOfHull := FormalPretriangulatedObject.toStandardNormalizedObject
      tensorOnDG := FreeDGObject.tensor
      tensorOnH0 := StandardPretriangulatedObject.tensor
      tensorOnKaroubi := fun X Y =>
        StandardH0CategoryTarget.AsCategory.karoubiOfObj
          (standardNormalizedPretriangulatedH0Target presentation)
          (StandardPretriangulatedObject.tensor
            (StandardH0CategoryTarget.AsCategory.karoubiCarrier
              (standardNormalizedPretriangulatedH0Target presentation) X)
            (StandardH0CategoryTarget.AsCategory.karoubiCarrier
              (standardNormalizedPretriangulatedH0Target presentation) Y)) }
  refine
    { transport := transport
      data := ?_ }
  refine
    { compatibility := ?_
      h0Associator := ?_
      karoubiAssociator := ?_ }
  · refine
      { throughDGEnvelope := ?_
        throughPretriangulatedHull := ?_
        throughKaroubiCompletion := ?_ }
    · intro p q
      rfl
    · intro X Y
      cases X
      cases Y
      simp [transport, FormalPretriangulatedObject.toStandardNormalizedObject,
        FormalPretriangulatedObject.normalForm, StandardTwistedComplex.ofDGObject,
        StandardTwistedComplex.ofAdditiveObject, StandardPretriangulatedObject.tensor,
        StandardPretriangulatedObject.ofDG, StandardPretriangulatedSummand.tensor,
        FreeDGObject.tensor]
    · intro X Y
      rfl
  · refine
      { hom := ?_
        inv := ?_
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro X Y Z
      exact h0EqHom
        (standardNormalizedPretriangulatedH0Target presentation)
        (StandardPretriangulatedObject.tensor_assoc X Y Z)
    · intro X Y Z
      exact h0EqHom
        (standardNormalizedPretriangulatedH0Target presentation)
        (StandardPretriangulatedObject.tensor_assoc X Y Z).symm
    · intro X Y Z
      exact h0EqHom_hom_inv_id
        (standardNormalizedPretriangulatedH0Target presentation)
        (StandardPretriangulatedObject.tensor_assoc X Y Z)
    · intro X Y Z
      exact h0EqHom_inv_hom_id
        (standardNormalizedPretriangulatedH0Target presentation)
        (StandardPretriangulatedObject.tensor_assoc X Y Z)
  · refine
      { hom := ?_
        inv := ?_
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · intro X Y Z
      have hAssoc :
          transport.tensorOnKaroubi (transport.tensorOnKaroubi X Y) Z =
            transport.tensorOnKaroubi X (transport.tensorOnKaroubi Y Z) := by
        apply congrArg
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj
            (standardNormalizedPretriangulatedH0Target presentation))
        exact StandardPretriangulatedObject.tensor_assoc X.X.obj Y.X.obj Z.X.obj
      exact karoubiEqHom (standardNormalizedPretriangulatedH0Target presentation) hAssoc
    · intro X Y Z
      have hAssoc :
          transport.tensorOnKaroubi (transport.tensorOnKaroubi X Y) Z =
            transport.tensorOnKaroubi X (transport.tensorOnKaroubi Y Z) := by
        apply congrArg
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj
            (standardNormalizedPretriangulatedH0Target presentation))
        exact StandardPretriangulatedObject.tensor_assoc X.X.obj Y.X.obj Z.X.obj
      exact karoubiEqHom
        (standardNormalizedPretriangulatedH0Target presentation)
        hAssoc.symm
    · intro X Y Z
      have hAssoc :
          transport.tensorOnKaroubi (transport.tensorOnKaroubi X Y) Z =
            transport.tensorOnKaroubi X (transport.tensorOnKaroubi Y Z) := by
        apply congrArg
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj
            (standardNormalizedPretriangulatedH0Target presentation))
        exact StandardPretriangulatedObject.tensor_assoc X.X.obj Y.X.obj Z.X.obj
      exact karoubiEqHom_hom_inv_id
        (standardNormalizedPretriangulatedH0Target presentation)
        hAssoc
    · intro X Y Z
      have hAssoc :
          transport.tensorOnKaroubi (transport.tensorOnKaroubi X Y) Z =
            transport.tensorOnKaroubi X (transport.tensorOnKaroubi Y Z) := by
        apply congrArg
          (StandardH0CategoryTarget.AsCategory.karoubiOfObj
            (standardNormalizedPretriangulatedH0Target presentation))
        exact StandardPretriangulatedObject.tensor_assoc X.X.obj Y.X.obj Z.X.obj
      exact karoubiEqHom_inv_hom_id
        (standardNormalizedPretriangulatedH0Target presentation)
        hAssoc

def monoidalCoherence (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation] : Prop :=
  Nonempty
    (KaroubiTensorAssociator
      (standardNormalizedPretriangulatedH0Target presentation)
      (StableCompletionConstructionTarget.monoidalTransport presentation).transport.tensorOnKaroubi)

end StableCompletionConstructionTarget

namespace StableCompletionConstructionData

structure PretriangulatedClosureData {presentation : Type u}
    (target : StableCompletionConstructionTarget presentation) where
  shiftClosureWitness : Nonempty (ShiftStructure target.pretriangulatedHull.hull.Obj)
  coneClosureWitness : Nonempty (ConeStructure target.pretriangulatedHull.hull.Obj)

def freeDGUniversalPropertyWitness {presentation : Type u}
    {target : StableCompletionConstructionTarget presentation}
    (_data : StableCompletionConstructionData target) :
    Nonempty
      (FreeDGUniversalProperty
        presentation
        target.freeDG.envelope.Obj
        target.freeDG.includeObj) :=
  ⟨target.freeDG.universalProperty⟩

def pretriangulatedClosureData {presentation : Type u}
    {target : StableCompletionConstructionTarget presentation}
    (_data : StableCompletionConstructionData target) :
    PretriangulatedClosureData target :=
  { shiftClosureWitness := ⟨target.pretriangulatedHull.shift⟩
    coneClosureWitness := ⟨target.pretriangulatedHull.cone⟩ }

def pretriangulatedUniversalPropertyWitness {presentation : Type u}
    {target : StableCompletionConstructionTarget presentation}
    (_data : StableCompletionConstructionData target) :
    Nonempty
      (PretriangulatedUniversalProperty
        target.freeDG.envelope.Obj
        target.pretriangulatedHull.hull.Obj
        target.pretriangulatedHull.includeObj
        target.pretriangulatedHull.shift.obj
        target.pretriangulatedHull.cone.obj) :=
  ⟨target.pretriangulatedHull.universalProperty⟩

def idempotentSplittingWitness {presentation : Type u}
    {target : StableCompletionConstructionTarget presentation}
    (_data : StableCompletionConstructionData target) :
    target.idempotentSplitting :=
  target.exactnessTransport.exactnessForKaroubiCompletion

theorem karoubiUniversalPropertyWitness {presentation : Type u}
    {target : StableCompletionConstructionTarget presentation}
    (_data : StableCompletionConstructionData target) :
    target.karoubiUniversalProperty :=
  StableCompletionConstructionTarget.karoubiUniversalProperty_holds target

def monoidalTransportData (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (_data : StableCompletionConstructionData
      (StableCompletionConstructionTarget.syntactic presentation)) :
    MonoidalTransportData
      ((StableCompletionConstructionTarget.monoidalTransport presentation).transport) :=
  (StableCompletionConstructionTarget.monoidalTransport presentation).data

def monoidalCoherenceWitness (presentation : Type u)
    [PresentationQuiver presentation]
    [MonoidalPresentation presentation]
    (data : StableCompletionConstructionData
      (StableCompletionConstructionTarget.syntactic presentation)) :
    StableCompletionConstructionTarget.monoidalCoherence presentation :=
  ⟨(monoidalTransportData presentation data).karoubiAssociator⟩

def syntactic (presentation : Type u) [PresentationQuiver presentation] :
    StableCompletionConstructionData
      (StableCompletionConstructionTarget.syntactic presentation) where
  freeDGCompositionData :=
    { laws :=
        { idComp := by
            intro X Y f
            exact FreeDGMorphism.id_comp f
          compId := by
            intro X Y f
            exact FreeDGMorphism.comp_id f
          assoc := by
            intro W X Y Z f g h
            exact FreeDGMorphism.comp_assoc f g h
        } }
  exactnessTransportData := by
    simpa [StableCompletionConstructionTarget.syntactic] using
      syntacticExactnessTransportData presentation

end StableCompletionConstructionData

end CategoryInfra
end TraceCalc

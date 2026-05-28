/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:1752-1917 (localization and Nisnevich descent prerequisites feeding completion arguments)
- our_paper_draft.tex:1926-2088 (effective presentation, stabilization, and completion-facing steps)
- our_paper_draft.tex:2130-2166 (minimal package, derived soundness, and classical realization interfaces)
- our_paper_draft.tex:2501-2544 (presentation matching and infinity comparison constraints)
- our_paper_draft.tex:5700-5714 (pi0 comparison consequences that rely on completion-level compatibility)

Still missing in this file/module:
- Explicit TeX-label annotations on each exported completion theorem/structure.
- Dependency lemmas restated in the exact signatures required by the manuscript order.
- Export-level dependency graph entries documenting which theorem is consumed by which downstream stage.

Coverage intent for this file:
- Keep implementation live; avoid surrogate abstractions.
- Store manuscript-traceability obligations in this header until declaration-level tags are added.
-/

import Foundation.Completion.FreeDG
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Tactic

/-!
# Concrete Pretriangulated Completion

This file begins the actual pretriangulated completion over the concrete free dg category from
`Foundation.Completion.FreeDG`. It builds the additive closure on shifted generators, the concrete
graded morphism complexes between those objects, and then twisted complexes over that graded dg
category.

No abstract hull interfaces are exported here.
-/

universe u

namespace Foundation.Completion

open scoped BigOperators

/-- A shifted generator in the additive closure of the free dg category. -/
structure PretriangulatedSummand (α : Type u) where
  base : FreeDGObject α
  shift : Int

/-- Finite sums of shifted free-dg generators. -/
abbrev PretriangulatedObject (α : Type u) : Type u :=
  List (PretriangulatedSummand α)

namespace PretriangulatedObject

def ofDG {α : Type u} (X : FreeDGObject α) : PretriangulatedObject α :=
  [{ base := X, shift := 0 }]

def shiftBy {α : Type u} (n : Int)
    (X : PretriangulatedObject α) :
    PretriangulatedObject α :=
  X.map fun summand => { summand with shift := summand.shift + n }

def shift {α : Type u} :
    PretriangulatedObject α → PretriangulatedObject α :=
  shiftBy 1

def biproduct {α : Type u}
    (X Y : PretriangulatedObject α) :
    PretriangulatedObject α :=
  X ++ Y

/-- Underlying additive object for the cone of a map from `X` to `Y`. -/
def coneCarrier {α : Type u}
    (X Y : PretriangulatedObject α) :
    PretriangulatedObject α :=
  biproduct (shift X) Y

end PretriangulatedObject

/-- An integer-weighted path in one matrix entry of the additive closure. -/
structure WeightedPath {α : Type u}
    [PresentationQuiver α]
    (X Y : α) where
  coeff : Int
  path : PresentationPath α X Y

namespace WeightedPath

def append {α : Type u} [PresentationQuiver α]
    {X Y Z : α}
    (left : WeightedPath X Y)
    (right : WeightedPath Y Z) :
    WeightedPath X Z where
  coeff := left.coeff * right.coeff
  path := PresentationPath.append left.path right.path

end WeightedPath

/-- Basis elements for a degree-`n` matrix entry between additive pretriangulated objects. -/
abbrev GradedComponentBasis {α : Type u}
    [PresentationQuiver α]
    (X Y : PretriangulatedObject α)
    (n : Int)
    (i : Fin X.length)
    (j : Fin Y.length) : Type u :=
  PLift ((X.get i).shift + n = (Y.get j).shift) ×
    WeightedPath
      (presentation := α)
      (FreeDGObject.carrier (X.get i).base)
      (FreeDGObject.carrier (Y.get j).base)

/-- Concrete graded morphisms in the additive closure: finitely supported integer combinations of
weighted generator paths in each matrix entry. -/
structure GradedPretriangulatedMorphism {α : Type u}
    [PresentationQuiver α]
    (X Y : PretriangulatedObject α)
    (n : Int) : Type u where
  entries :
    (i : Fin X.length) → (j : Fin Y.length) →
      FreeAbelianGroup (GradedComponentBasis X Y n i j)

namespace GradedPretriangulatedMorphism

@[ext] theorem ext {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} {n : Int}
    {f g : GradedPretriangulatedMorphism X Y n}
    (h : f.entries = g.entries) : f = g := by
  cases f
  cases g
  cases h
  rfl

def zero {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} (n : Int) :
    GradedPretriangulatedMorphism X Y n where
  entries := fun _ _ => 0

def add {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} {n : Int}
    (f g : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism X Y n where
  entries := fun i j => f.entries i j + g.entries i j

def neg {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} {n : Int}
    (f : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism X Y n where
  entries := fun i j => -f.entries i j

def sub {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} {n : Int}
    (f g : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism X Y n :=
  add f (neg g)

def signedByParity {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α} {n : Int}
    (parity : Int)
    (f : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism X Y n :=
  if parity % 2 = 0 then f else neg f

def id {α : Type u} [PresentationQuiver α]
    (X : PretriangulatedObject α) :
    GradedPretriangulatedMorphism X X 0 where
  entries := fun i j =>
    if h : i = j then
      by
        subst h
        exact FreeAbelianGroup.of
          ⟨⟨by simp⟩,
            { coeff := 1
              path := PresentationPath.nil (FreeDGObject.carrier (X.get i).base) }⟩
    else
      0

def composeComponent {α : Type u} [PresentationQuiver α]
    {X Y Z : PretriangulatedObject α}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (left : FreeAbelianGroup (GradedComponentBasis X Y a i j))
    (right : FreeAbelianGroup (GradedComponentBasis Y Z b j k)) :
    FreeAbelianGroup (GradedComponentBasis X Z (a + b) i k) :=
  FreeAbelianGroup.lift
    (fun leftBasis =>
      FreeAbelianGroup.lift
        (fun rightBasis =>
          FreeAbelianGroup.of
            ⟨⟨by
                calc
                  (X.get i).shift + (a + b) = ((X.get i).shift + a) + b := by
                    simp [Int.add_assoc]
                  _ = (Y.get j).shift + b := by
                    rw [leftBasis.1.down]
                  _ = (Z.get k).shift := by
                    rw [rightBasis.1.down]⟩,
              WeightedPath.append leftBasis.2 rightBasis.2⟩)
        right)
    left

def comp {α : Type u} [PresentationQuiver α]
    {X Y Z : PretriangulatedObject α}
    {i j : Int}
    (f : GradedPretriangulatedMorphism X Y i)
    (g : GradedPretriangulatedMorphism Y Z j) :
    GradedPretriangulatedMorphism X Z (i + j) where
  entries := fun source target =>
    ∑ middle : Fin Y.length,
      composeComponent source middle target (f.entries source middle) (g.entries middle target)

def differential {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α}
    (n : Int)
    (_f : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism X Y (n + 1) :=
  zero (n + 1)

def ofFreeDG {α : Type u} [PresentationQuiver α]
    {X Y : FreeDGObject α}
    (f : FreeDGMorphism X Y) :
    GradedPretriangulatedMorphism
      (PretriangulatedObject.ofDG X)
      (PretriangulatedObject.ofDG Y) 0 where
  entries := fun _ _ =>
    match f.path? with
    | none => 0
    | some path =>
        FreeAbelianGroup.of
          ⟨⟨by simp [PretriangulatedObject.ofDG]⟩,
            by
              simpa [PretriangulatedObject.ofDG] using
                ({ coeff := 1, path := path } : WeightedPath X.carrier Y.carrier)⟩

def shiftBothBy {α : Type u} [PresentationQuiver α]
    (shift : Int)
    {X Y : PretriangulatedObject α}
    {n : Int}
    (f : GradedPretriangulatedMorphism X Y n) :
    GradedPretriangulatedMorphism
      (PretriangulatedObject.shiftBy shift X)
      (PretriangulatedObject.shiftBy shift Y) n where
  entries := fun i j =>
    let sourceIndex : Fin X.length :=
      ⟨i.1, by simpa [PretriangulatedObject.shiftBy] using i.2⟩
    let targetIndex : Fin Y.length :=
      ⟨j.1, by simpa [PretriangulatedObject.shiftBy] using j.2⟩
    FreeAbelianGroup.map
      (fun basis =>
        match basis with
        | ⟨hshift, term⟩ =>
            ⟨⟨by
                simpa [PretriangulatedObject.shiftBy, Int.add_assoc, Int.add_left_comm,
                  Int.add_comm] using hshift.down⟩,
              by
                simpa [PretriangulatedObject.shiftBy] using term⟩)
      (f.entries sourceIndex targetIndex)

/-- Reinterpret a degree-zero map as a degree-one map from the desuspension of its source. -/
def sourceDesuspensionOfDegreeZero {α : Type u} [PresentationQuiver α]
    {X Y : PretriangulatedObject α}
    (f : GradedPretriangulatedMorphism X Y 0) :
    GradedPretriangulatedMorphism
      (PretriangulatedObject.shiftBy (-1) X) Y 1 where
  entries := fun i j =>
    let sourceIndex : Fin X.length :=
      ⟨i.1, by simpa [PretriangulatedObject.shiftBy] using i.2⟩
    FreeAbelianGroup.map
      (fun basis =>
        match basis with
        | ⟨hshift, term⟩ =>
            ⟨⟨by
                simpa [PretriangulatedObject.shiftBy, Int.add_assoc, Int.add_left_comm,
                  Int.add_comm] using hshift.down⟩,
              by
                simpa [PretriangulatedObject.shiftBy] using term⟩)
      (f.entries sourceIndex j)

@[simp] theorem composeComponent_zero_left {α : Type u}
    [PresentationQuiver α]
    {X Y Z : PretriangulatedObject α}
    {a b : Int}
    (i : Fin X.length)
    (j : Fin Y.length)
    (k : Fin Z.length)
    (right : FreeAbelianGroup (GradedComponentBasis Y Z b j k)) :
    composeComponent (a := a) (b := b) i j k
      (0 : FreeAbelianGroup (GradedComponentBasis X Y a i j)) right = 0 := by
  unfold composeComponent
  simp

@[simp] theorem comp_zero_left {α : Type u} [PresentationQuiver α]
    {X Y Z : PretriangulatedObject α}
    {i j : Int}
    (g : GradedPretriangulatedMorphism Y Z j) :
    comp (zero (X := X) (Y := Y) i) g = zero (X := X) (Y := Z) (i + j) := by
  ext source target
  change (∑ middle : Fin Y.length,
      composeComponent source middle target 0 (g.entries middle target)) = 0
  exact Fintype.sum_eq_zero _ (by
    intro middle
    simp [composeComponent])

end GradedPretriangulatedMorphism

/-- The concrete graded dg category on additive shifted generators. -/
def pretriangulatedDGCategory (α : Type u)
    [PresentationQuiver α] : Foundation.DG.GradedDGCategory.{u, u} where
  Obj := PretriangulatedObject α
  Hom := GradedPretriangulatedMorphism
  zero := GradedPretriangulatedMorphism.zero
  add := fun _ f g => GradedPretriangulatedMorphism.add f g
  neg := fun _ f => GradedPretriangulatedMorphism.neg f
  id := GradedPretriangulatedMorphism.id
  comp := fun f g => GradedPretriangulatedMorphism.comp f g
  differential := GradedPretriangulatedMorphism.differential

/-- A twisted complex over the additive pretriangulated envelope. -/
structure TwistedComplex (α : Type u)
    [PresentationQuiver α] where
  carrier : PretriangulatedObject α
  differential : GradedPretriangulatedMorphism carrier carrier 1
  differential_squared_zero :
    GradedPretriangulatedMorphism.comp differential differential =
      GradedPretriangulatedMorphism.zero 2

namespace TwistedComplex

abbrev Hom {α : Type u} [PresentationQuiver α]
    (X Y : TwistedComplex α)
    (n : Int) : Type u :=
  GradedPretriangulatedMorphism X.carrier Y.carrier n

def id {α : Type u} [PresentationQuiver α]
    (X : TwistedComplex α) : Hom X X 0 :=
  GradedPretriangulatedMorphism.id X.carrier

def comp {α : Type u} [PresentationQuiver α]
    {X Y Z : TwistedComplex α}
    {i j : Int}
    (f : Hom X Y i)
    (g : Hom Y Z j) : Hom X Z (i + j) :=
  GradedPretriangulatedMorphism.comp f g

def differentialOnHom {α : Type u} [PresentationQuiver α]
    {X Y : TwistedComplex α}
    (n : Int)
    (f : Hom X Y n) : Hom X Y (n + 1) := by
  let left : Hom X Y (n + 1) :=
    GradedPretriangulatedMorphism.comp f Y.differential
  let right : Hom X Y (n + 1) := by
    simpa [Int.add_comm] using
      (GradedPretriangulatedMorphism.comp X.differential f)
  exact GradedPretriangulatedMorphism.sub left
    (GradedPretriangulatedMorphism.signedByParity n right)

def ofAdditiveObject {α : Type u} [PresentationQuiver α]
    (X : PretriangulatedObject α) :
    TwistedComplex α where
  carrier := X
  differential := GradedPretriangulatedMorphism.zero 1
  differential_squared_zero := by
    simpa using
      (GradedPretriangulatedMorphism.comp_zero_left
        (GradedPretriangulatedMorphism.zero 1))

def ofDGObject {α : Type u} [PresentationQuiver α]
    (X : FreeDGObject α) : TwistedComplex α :=
  ofAdditiveObject (PretriangulatedObject.ofDG X)

end TwistedComplex

/-- The concrete dg category of twisted complexes over the free dg presentation. -/
def twistedComplexDGCategory (α : Type u)
    [PresentationQuiver α] : Foundation.DG.GradedDGCategory.{u, u} where
  Obj := TwistedComplex α
  Hom := TwistedComplex.Hom
  zero := GradedPretriangulatedMorphism.zero
  add := fun _ f g => GradedPretriangulatedMorphism.add f g
  neg := fun _ f => GradedPretriangulatedMorphism.neg f
  id := TwistedComplex.id
  comp := fun f g => TwistedComplex.comp f g
  differential := TwistedComplex.differentialOnHom

end Foundation.Completion

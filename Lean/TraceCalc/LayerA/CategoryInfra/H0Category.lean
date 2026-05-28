import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.CategoryTheory.Preadditive.Basic
import TraceCalc.LayerA.CategoryInfra.Pretriangulated

universe u v

namespace TraceCalc
namespace CategoryInfra

/-- Canonical `H^0` target attached to a standard dg category: degree-zero cycles
modulo degree-(-1) boundaries. The relation itself is fixed canonically; the
remaining fields assert the standard quotient/category compatibility facts. -/
structure StandardH0CategoryTarget (C : StandardDGCategoryLike.{u, v}) where
  dgData : StandardDGCategoryData C
  boundaryRel_refl :
    ∀ {X Y : C.Obj} (f : C.CycleHom X Y),
      C.boundaryRel f f
  boundaryRel_symm :
    ∀ {X Y : C.Obj} {f g : C.CycleHom X Y},
      C.boundaryRel f g → C.boundaryRel g f
  boundaryRel_trans :
    ∀ {X Y : C.Obj} {f g h : C.CycleHom X Y},
      C.boundaryRel f g → C.boundaryRel g h → C.boundaryRel f h
  comp_respects_boundary_left :
    ∀ {X Y Z : C.Obj}
      {f f' : C.CycleHom X Y} (g : C.CycleHom Y Z),
        C.boundaryRel f f' →
          C.boundaryRel
            ⟨C.comp f.1 g.1, dgData.laws.closed_comp f g⟩
            ⟨C.comp f'.1 g.1, dgData.laws.closed_comp f' g⟩
  comp_respects_boundary_right :
    ∀ {X Y Z : C.Obj}
      (f : C.CycleHom X Y) {g g' : C.CycleHom Y Z},
        C.boundaryRel g g' →
          C.boundaryRel
            ⟨C.comp f.1 g.1, dgData.laws.closed_comp f g⟩
            ⟨C.comp f.1 g'.1, dgData.laws.closed_comp f g'⟩

namespace StandardH0CategoryTarget

def ofZeroDifferential {C : StandardDGCategoryLike.{u, v}}
    (dgData : StandardDGCategoryData C)
    (differential_zero :
      ∀ {X Y : C.Obj} (n : Int) (f : C.Hom X Y n),
        C.differential n f = C.zero (n + 1)) :
    StandardH0CategoryTarget C := by
  let boundaryRefl :
      ∀ {X Y : C.Obj} (f : C.CycleHom X Y), C.boundaryRel f f := by
    intro X Y f
    refine ⟨C.zero (-1), ?_⟩
    letI := StandardDGCategoryData.instAddCommGroupHom dgData X Y (-1)
    letI := StandardDGCategoryData.instAddCommGroupHom dgData X Y 0
    rw [differential_zero (-1) (C.zero (-1))]
    calc
      C.zero 0 = C.add 0 (C.neg 0 f.1) f.1 := by
        symm
        exact dgData.laws.add_left_neg 0 f.1
      _ = C.add 0 f.1 (C.neg 0 f.1) := by
        rw [dgData.laws.add_comm 0 (C.neg 0 f.1) f.1]
      _ = C.sub 0 f.1 f.1 := rfl
  let boundaryEq :
      ∀ {X Y : C.Obj} {f g : C.CycleHom X Y}, C.boundaryRel f g → f = g := by
    intro X Y f g hfg
    rcases hfg with ⟨witness, hWitness⟩
    letI := StandardDGCategoryData.instAddCommGroupHom dgData X Y (-1)
    letI := StandardDGCategoryData.instAddCommGroupHom dgData X Y 0
    have hSub : f.1 - g.1 = 0 := by
      simpa [StandardDGCategoryLike.sub] using
        (hWitness.symm.trans (differential_zero (-1) witness))
    exact Subtype.ext (sub_eq_zero.mp hSub)
  exact
    { dgData := dgData
      boundaryRel_refl := boundaryRefl
      boundaryRel_symm := by
        intro X Y f g hfg
        rw [boundaryEq hfg]
        exact boundaryRefl g
      boundaryRel_trans := by
        intro X Y f g h hfg hgh
        rw [boundaryEq hfg, boundaryEq hgh]
        exact boundaryRefl h
      comp_respects_boundary_left := by
        intro X Y Z f f' g hff'
        rw [boundaryEq hff']
        exact boundaryRefl ⟨C.comp f'.1 g.1, dgData.laws.closed_comp f' g⟩
      comp_respects_boundary_right := by
        intro X Y Z f g g' hgg'
        rw [boundaryEq hgg']
        exact boundaryRefl ⟨C.comp f.1 g'.1, dgData.laws.closed_comp f g'⟩ }

def boundarySetoid {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    (X Y : C.Obj) : Setoid (C.CycleHom X Y) where
  r := C.boundaryRel
  iseqv :=
    ⟨target.boundaryRel_refl, target.boundaryRel_symm, target.boundaryRel_trans⟩

abbrev H0Hom {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    (X Y : C.Obj) : Type v :=
  Quotient (target.boundarySetoid X Y)

def quotientMap {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} :
    C.CycleHom X Y → target.H0Hom X Y :=
  Quotient.mk (target.boundarySetoid X Y)

def identity {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    (X : C.Obj) : target.H0Hom X X :=
  target.quotientMap ⟨C.id X, target.dgData.laws.id_closed X⟩

def composeCycle {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y Z : C.Obj} :
    C.CycleHom X Y → C.CycleHom Y Z → C.CycleHom X Z :=
  fun f g => ⟨C.comp f.1 g.1, target.dgData.laws.closed_comp f g⟩

def compose {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y Z : C.Obj} :
    target.H0Hom X Y → target.H0Hom Y Z → target.H0Hom X Z := by
  intro left right
  refine Quotient.liftOn₂ left right
    (fun f g => target.quotientMap (target.composeCycle f g)) ?_
  intro f g f' g' hff' hgg'
  have hLeft := target.comp_respects_boundary_left g hff'
  have hRight := target.comp_respects_boundary_right f' hgg'
  exact Quotient.sound (target.boundaryRel_trans hLeft hRight)

def zeroCycle {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} : C.CycleHom X Y :=
  ⟨C.zero 0, by
    simpa using target.dgData.laws.differential_zero (X := X) (Y := Y) 0⟩

def addCycle {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} :
    C.CycleHom X Y → C.CycleHom X Y → C.CycleHom X Y
  | f, g =>
      by
        refine ⟨C.add 0 f.1 g.1, ?_⟩
        calc
          C.differential 0 (C.add 0 f.1 g.1)
              = C.add 1 (C.differential 0 f.1) (C.differential 0 g.1) := by
                  simpa using target.dgData.laws.differential_add 0 f.1 g.1
          _ = C.add 1 (C.zero 1) (C.zero 1) := by rw [f.2, g.2]
          _ = C.zero 1 := by exact target.dgData.laws.zero_add 1 (C.zero 1)

def negCycle {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} :
    C.CycleHom X Y → C.CycleHom X Y
  | f =>
      by
        letI := StandardDGCategoryData.instAddCommGroupHom target.dgData X Y 1
        refine ⟨C.neg 0 f.1, ?_⟩
        rw [target.dgData.laws.differential_neg 0 f.1, f.2]
        calc
          C.neg 1 (C.zero 1) = C.add 1 (C.zero 1) (C.neg 1 (C.zero 1)) := by
            symm
            exact target.dgData.laws.zero_add 1 (C.neg 1 (C.zero 1))
          _ = C.add 1 (C.neg 1 (C.zero 1)) (C.zero 1) := by
            rw [target.dgData.laws.add_comm 1 (C.zero 1) (C.neg 1 (C.zero 1))]
          _ = C.zero 1 := by
            exact target.dgData.laws.add_left_neg 1 (C.zero 1)

theorem boundaryRel_add {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj}
    {f f' g g' : C.CycleHom X Y} :
    C.boundaryRel f f' → C.boundaryRel g g' →
      C.boundaryRel (target.addCycle f g) (target.addCycle f' g') := by
  intro hff' hgg'
  rcases hff' with ⟨leftWitness, hLeft⟩
  rcases hgg' with ⟨rightWitness, hRight⟩
  letI := StandardDGCategoryData.instAddCommGroupHom target.dgData X Y 0
  refine ⟨C.add (-1) leftWitness rightWitness, ?_⟩
  change C.differential (-1) (C.add (-1) leftWitness rightWitness) =
    C.sub 0 (target.addCycle f g).1 (target.addCycle f' g').1
  calc
    C.differential (-1) (C.add (-1) leftWitness rightWitness)
        = C.add 0 (C.differential (-1) leftWitness) (C.differential (-1) rightWitness) := by
            simpa using target.dgData.laws.differential_add (-1) leftWitness rightWitness
    _ = C.add 0 (C.sub 0 f.1 f'.1) (C.sub 0 g.1 g'.1) := by rw [hLeft, hRight]
    _ = C.sub 0 (C.add 0 f.1 g.1) (C.add 0 f'.1 g'.1) := by
          change (f.1 - f'.1) + (g.1 - g'.1) = (f.1 + g.1) - (f'.1 + g'.1)
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = C.sub 0 (target.addCycle f g).1 (target.addCycle f' g').1 := by rfl

theorem boundaryRel_neg {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj}
    {f f' : C.CycleHom X Y} :
    C.boundaryRel f f' → C.boundaryRel (target.negCycle f) (target.negCycle f') := by
  intro hff'
  rcases hff' with ⟨witness, hWitness⟩
  letI := StandardDGCategoryData.instAddCommGroupHom target.dgData X Y 0
  refine ⟨C.neg (-1) witness, ?_⟩
  change C.differential (-1) (C.neg (-1) witness) =
    C.sub 0 (target.negCycle f).1 (target.negCycle f').1
  calc
    C.differential (-1) (C.neg (-1) witness)
        = C.neg 0 (C.differential (-1) witness) := by
            simpa using target.dgData.laws.differential_neg (-1) witness
    _ = C.neg 0 (C.sub 0 f.1 f'.1) := by rw [hWitness]
    _ = C.sub 0 (C.neg 0 f.1) (C.neg 0 f'.1) := by
          change -(f.1 - f'.1) = (-f.1) - (-f'.1)
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = C.sub 0 (target.negCycle f).1 (target.negCycle f').1 := by rfl

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} : Zero (target.H0Hom X Y) where
  zero := target.quotientMap target.zeroCycle

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} : Add (target.H0Hom X Y) where
  add left right := by
    refine Quotient.liftOn₂ left right
      (fun f g => target.quotientMap (target.addCycle f g)) ?_
    intro f g f' g' hff' hgg'
    exact Quotient.sound (target.boundaryRel_add hff' hgg')

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} : Neg (target.H0Hom X Y) where
  neg morphism := by
    refine Quotient.liftOn morphism (fun f => target.quotientMap (target.negCycle f)) ?_
    intro f g hfg
    exact Quotient.sound (target.boundaryRel_neg hfg)

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} : AddCommGroup (target.H0Hom X Y) := by
  letI : AddGroup (target.H0Hom X Y) :=
    AddGroup.ofLeftAxioms
      (by
        intro a b c
        refine Quotient.inductionOn₃ a b c ?_
        intro f g h
        let rightRep : C.CycleHom X Y := target.addCycle f (target.addCycle g h)
        have hleft : target.addCycle (target.addCycle f g) h = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.add 0 f.1 g.1) h.1 = rightRep.1
          simpa [rightRep, StandardH0CategoryTarget.addCycle] using
            target.dgData.laws.add_assoc 0 f.1 g.1 h.1
        exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep))
      (by
        intro a
        refine Quotient.inductionOn a ?_
        intro f
        let rightRep : C.CycleHom X Y := f
        have hleft : target.addCycle target.zeroCycle f = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.zero 0) f.1 = rightRep.1
          simpa [rightRep] using target.dgData.laws.zero_add 0 f.1
        exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep))
      (by
        intro a
        refine Quotient.inductionOn a ?_
        intro f
        let rightRep : C.CycleHom X Y := target.zeroCycle (X := X) (Y := Y)
        have hleft : target.addCycle (target.negCycle f) f = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.neg 0 f.1) f.1 = rightRep.1
          simpa [rightRep, StandardH0CategoryTarget.zeroCycle] using
            target.dgData.laws.add_left_neg 0 f.1
        exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep))
  let addGroupInst : AddGroup (target.H0Hom X Y) := inferInstance
  exact
    { addGroupInst with
      add_comm := by
        intro a b
        refine Quotient.inductionOn₂ a b ?_
        intro f g
        let rightRep : C.CycleHom X Y := target.addCycle g f
        have hleft : target.addCycle f g = rightRep := by
          apply Subtype.ext
          change C.add 0 f.1 g.1 = rightRep.1
          simpa [rightRep, StandardH0CategoryTarget.addCycle] using
            target.dgData.laws.add_comm 0 f.1 g.1
        exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep) }

theorem identity_comp {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} (f : target.H0Hom X Y) :
    target.compose (target.identity X) f = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change target.quotientMap
      ⟨C.comp (C.id X) representative.1,
        target.dgData.laws.closed_comp ⟨C.id X, target.dgData.laws.id_closed X⟩ representative⟩ =
    target.quotientMap representative
  apply Quotient.sound
  change C.boundaryRel
      ⟨C.comp (C.id X) representative.1,
        target.dgData.laws.closed_comp ⟨C.id X, target.dgData.laws.id_closed X⟩ representative⟩
      representative
  let rightRep : C.CycleHom X Y := representative
  have hleft :
      (⟨C.comp (C.id X) representative.1,
          target.dgData.laws.closed_comp ⟨C.id X, target.dgData.laws.id_closed X⟩ representative⟩ :
        C.CycleHom X Y) = rightRep := by
    apply Subtype.ext
    simpa using target.dgData.laws.id_comp representative.1
  simpa [hleft] using target.boundaryRel_refl rightRep

theorem comp_identity {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {X Y : C.Obj} (f : target.H0Hom X Y) :
    target.compose f (target.identity Y) = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change target.quotientMap
      ⟨C.comp representative.1 (C.id Y),
        target.dgData.laws.closed_comp representative ⟨C.id Y, target.dgData.laws.id_closed Y⟩⟩ =
    target.quotientMap representative
  apply Quotient.sound
  change C.boundaryRel
      ⟨C.comp representative.1 (C.id Y),
        target.dgData.laws.closed_comp representative ⟨C.id Y, target.dgData.laws.id_closed Y⟩⟩
      representative
  let rightRep : C.CycleHom X Y := representative
  have hleft :
      (⟨C.comp representative.1 (C.id Y),
          target.dgData.laws.closed_comp representative ⟨C.id Y, target.dgData.laws.id_closed Y⟩⟩ :
        C.CycleHom X Y) = rightRep := by
    apply Subtype.ext
    simpa using target.dgData.laws.comp_id representative.1
  simpa [hleft] using target.boundaryRel_refl rightRep

theorem composition_assoc {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C)
    {W X Y Z : C.Obj}
    (f : target.H0Hom W X)
    (g : target.H0Hom X Y)
    (h : target.H0Hom Y Z) :
    target.compose (target.compose f g) h =
      target.compose f (target.compose g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro fRep gRep hRep
  change target.quotientMap
      ⟨C.comp (C.comp fRep.1 gRep.1) hRep.1,
        target.dgData.laws.closed_comp
          ⟨C.comp fRep.1 gRep.1, target.dgData.laws.closed_comp fRep gRep⟩ hRep⟩ =
    target.quotientMap
      ⟨C.comp fRep.1 (C.comp gRep.1 hRep.1),
        target.dgData.laws.closed_comp fRep
          ⟨C.comp gRep.1 hRep.1, target.dgData.laws.closed_comp gRep hRep⟩⟩
  apply Quotient.sound
  change C.boundaryRel
      ⟨C.comp (C.comp fRep.1 gRep.1) hRep.1,
        target.dgData.laws.closed_comp
          ⟨C.comp fRep.1 gRep.1, target.dgData.laws.closed_comp fRep gRep⟩ hRep⟩
      ⟨C.comp fRep.1 (C.comp gRep.1 hRep.1),
        target.dgData.laws.closed_comp fRep
          ⟨C.comp gRep.1 hRep.1, target.dgData.laws.closed_comp gRep hRep⟩⟩
  let rightRep : C.CycleHom W Z :=
    ⟨C.comp fRep.1 (C.comp gRep.1 hRep.1),
      target.dgData.laws.closed_comp fRep
        ⟨C.comp gRep.1 hRep.1, target.dgData.laws.closed_comp gRep hRep⟩⟩
  have hleft :
      (⟨C.comp (C.comp fRep.1 gRep.1) hRep.1,
          target.dgData.laws.closed_comp
            ⟨C.comp fRep.1 gRep.1, target.dgData.laws.closed_comp fRep gRep⟩ hRep⟩ :
        C.CycleHom W Z) = rightRep := by
    apply Subtype.ext
    simpa [Int.add_assoc] using target.dgData.laws.comp_assoc fRep.1 gRep.1 hRep.1
  simpa [hleft] using target.boundaryRel_refl rightRep

/-- Wrapper exposing the canonical standard `H^0` quotient as a mathlib category. -/
structure AsCategory {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) where
  obj : C.Obj

namespace AsCategory

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C) :
    CategoryTheory.Category (AsCategory target) where
  Hom X Y := target.H0Hom X.obj Y.obj
  id X := target.identity X.obj
  comp f g := target.compose f g
  id_comp := by
    intro X Y f
    exact target.identity_comp f
  comp_id := by
    intro X Y f
    exact target.comp_identity f
  assoc := by
    intro W X Y Z f g h
    exact target.composition_assoc f g h

instance {C : StandardDGCategoryLike.{u, v}} (target : StandardH0CategoryTarget C) :
    CategoryTheory.Preadditive (AsCategory target) where
  homGroup X Y := inferInstanceAs (AddCommGroup (target.H0Hom X.obj Y.obj))
  add_comp P Q R f f' g := by
    letI : AddCommGroup (P ⟶ Q) := inferInstanceAs (AddCommGroup (target.H0Hom P.obj Q.obj))
    letI : AddCommGroup (P ⟶ R) := inferInstanceAs (AddCommGroup (target.H0Hom P.obj R.obj))
    refine Quotient.inductionOn₃ f f' g ?_
    intro fRep fRep' gRep
    change target.quotientMap (target.composeCycle (target.addCycle fRep fRep') gRep) =
      target.quotientMap
        (target.addCycle (target.composeCycle fRep gRep) (target.composeCycle fRep' gRep))
    let rightRep : C.CycleHom P.obj R.obj :=
      target.addCycle (target.composeCycle fRep gRep) (target.composeCycle fRep' gRep)
    letI := StandardDGCategoryData.instAddCommGroupHom target.dgData P.obj Q.obj 0
    letI := StandardDGCategoryData.instAddCommGroupHom target.dgData P.obj R.obj 0
    have hleft : target.composeCycle (target.addCycle fRep fRep') gRep = rightRep := by
      apply Subtype.ext
      change (target.composeCycle (target.addCycle fRep fRep') gRep).1 = rightRep.1
      simpa [rightRep, StandardH0CategoryTarget.addCycle, StandardH0CategoryTarget.composeCycle] using
        target.dgData.laws.comp_add_left fRep.1 fRep'.1 gRep.1
    exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep)
  comp_add P Q R f g g' := by
    letI : AddCommGroup (Q ⟶ R) := inferInstanceAs (AddCommGroup (target.H0Hom Q.obj R.obj))
    letI : AddCommGroup (P ⟶ R) := inferInstanceAs (AddCommGroup (target.H0Hom P.obj R.obj))
    refine Quotient.inductionOn₃ f g g' ?_
    intro fRep gRep gRep'
    change target.quotientMap (target.composeCycle fRep (target.addCycle gRep gRep')) =
      target.quotientMap
        (target.addCycle (target.composeCycle fRep gRep) (target.composeCycle fRep gRep'))
    let rightRep : C.CycleHom P.obj R.obj :=
      target.addCycle (target.composeCycle fRep gRep) (target.composeCycle fRep gRep')
    letI := StandardDGCategoryData.instAddCommGroupHom target.dgData Q.obj R.obj 0
    letI := StandardDGCategoryData.instAddCommGroupHom target.dgData P.obj R.obj 0
    have hleft : target.composeCycle fRep (target.addCycle gRep gRep') = rightRep := by
      apply Subtype.ext
      change (target.composeCycle fRep (target.addCycle gRep gRep')).1 = rightRep.1
      simpa [rightRep, StandardH0CategoryTarget.addCycle, StandardH0CategoryTarget.composeCycle] using
        target.dgData.laws.comp_add_right fRep.1 gRep.1 gRep'.1
    exact Quotient.sound (by simpa [hleft] using target.boundaryRel_refl rightRep)

@[simp] def ofObj {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) (X : C.Obj) : AsCategory target :=
  ⟨X⟩

@[simp] theorem ofObj_obj {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) (X : C.Obj) :
  (ofObj target X).obj = X :=
  rfl

/-- Mathlib Karoubi completion of the canonical standard `H^0` category. -/
abbrev KaroubiCompletion {C : StandardDGCategoryLike.{u, v}}
  (target : StandardH0CategoryTarget C) : Type _ :=
  CategoryTheory.Idempotents.Karoubi (AsCategory target)

/-- The standard embedding of the canonical `H^0` category into its Karoubi completion. -/
abbrev toKaroubi {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) :
    CategoryTheory.Functor (AsCategory target) (KaroubiCompletion target) :=
  CategoryTheory.Idempotents.toKaroubi (AsCategory target)

@[simp] def karoubiOfObj {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) (X : C.Obj) : KaroubiCompletion target :=
  ((ofObj target X : AsCategory target) : CategoryTheory.Idempotents.Karoubi (AsCategory target))

@[simp] def karoubiCarrier {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) (P : KaroubiCompletion target) : C.Obj :=
  P.X.obj

@[simp] theorem karoubiCarrier_ofObj {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) (X : C.Obj) :
  karoubiCarrier target (karoubiOfObj target X) = X :=
  rfl

theorem karoubi_idempotentComplete {C : StandardDGCategoryLike.{u, v}}
    (target : StandardH0CategoryTarget C) :
    CategoryTheory.IsIdempotentComplete (KaroubiCompletion target) :=
  inferInstance

end AsCategory

end StandardH0CategoryTarget

/-- Triangulated/localization data carried by the `H^0` passage once the
canonical hom quotients are fixed. -/
structure H0TriangulatedData {C} (P : PretriangulatedHull C) where
  distinguishedTriangles : ConeStructure P.hull.Obj
  triangulatedAxioms : ShiftStructure P.hull.Obj × ConeStructure P.hull.Obj
  localizationAtAcyclics :
    PretriangulatedUniversalProperty C.Obj P.hull.Obj P.includeObj P.shift.obj P.cone.obj

end CategoryInfra
end TraceCalc
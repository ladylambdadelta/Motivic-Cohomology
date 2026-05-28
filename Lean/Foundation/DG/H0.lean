/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (generator-level operations whose realization pipelines depend on DG interfaces)
- our_paper_draft.tex:1926-2088 (effective presentation and stabilization layer, which depends on DG infrastructure)
- our_paper_draft.tex:2130-2166 (minimal-package and classical-realization stages requiring DG functorial consistency)
- our_paper_draft.tex:2501-2544 (comparison constructions requiring DG-level functorial control)
- our_paper_draft.tex:5700-5714 (pi0 comparison consequences that use DG/H0 compatibility)

Still missing in this file/module:
- A precise TeX-label-to-Lean symbol index for DG primitives used by the motive pipeline.
- Explicit bridge lemmas documenting where DG facts feed manuscript theorem statements.
- Export contracts pinned to downstream users (`H0`, completion, trace realization) with exact dependency signatures.

Coverage intent for this file:
- Keep implementation live and reusable.
- Use this header as the manuscript proof-coverage checkpoint until per-symbol labeling is complete.
-/

import Foundation.DG.Basic
import Foundation.DG.Homotopy
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The `H0` Category

This module extracts the canonical zeroth-homotopy category attached to a graded dg category:
degree-zero cycles modulo degree-`(-1)` boundaries. It contains the quotient-level additive and
categorical structure, together with the standard embedding into the Karoubi completion.
-/

universe u v

namespace Foundation.DG

/-- Canonical `H0` quotient attached to a graded dg category. The underlying relation is fixed by
boundaries; the fields record the compatibility needed to form a category and additive structure. -/
structure H0Category (C : GradedDGCategory.{u, v}) where
  dgData : GradedDGCategoryData C
  boundary_rel_refl :
    ∀ {X Y : C.Obj} (f : C.CycleHom X Y),
      C.boundary_rel f f
  boundary_rel_symm :
    ∀ {X Y : C.Obj} {f g : C.CycleHom X Y},
      C.boundary_rel f g → C.boundary_rel g f
  boundary_rel_trans :
    ∀ {X Y : C.Obj} {f g h : C.CycleHom X Y},
      C.boundary_rel f g → C.boundary_rel g h → C.boundary_rel f h
  comp_respects_boundary_left :
    ∀ {X Y Z : C.Obj}
      {f f' : C.CycleHom X Y} (g : C.CycleHom Y Z),
        C.boundary_rel f f' →
          C.boundary_rel
            ⟨C.comp f.1 g.1, dgData.laws.closed_comp f g⟩
            ⟨C.comp f'.1 g.1, dgData.laws.closed_comp f' g⟩
  comp_respects_boundary_right :
    ∀ {X Y Z : C.Obj}
      (f : C.CycleHom X Y) {g g' : C.CycleHom Y Z},
        C.boundary_rel g g' →
          C.boundary_rel
            ⟨C.comp f.1 g.1, dgData.laws.closed_comp f g⟩
            ⟨C.comp f.1 g'.1, dgData.laws.closed_comp f g'⟩

namespace H0Category

/-- Boundary-homotopy equivalence data induced by an `H0Category` witness. -/
def boundaryHomotopyData {C : GradedDGCategory.{u, v}}
    (target : H0Category C) : GradedDGCategory.BoundaryHomotopyData C where
  refl := target.boundary_rel_refl
  symm := @target.boundary_rel_symm
  trans := @target.boundary_rel_trans

def of_zero_differential {C : GradedDGCategory.{u, v}}
    (dgData : GradedDGCategoryData C)
    (differential_zero :
      ∀ {X Y : C.Obj} (n : Int) (f : C.Hom X Y n),
        C.differential n f = C.zero (n + 1)) :
    H0Category C := by
  let boundary_refl :
      ∀ {X Y : C.Obj} (f : C.CycleHom X Y), C.boundary_rel f f := by
    intro X Y f
    refine ⟨C.zero (-1), ?_⟩
    letI := GradedDGCategoryData.instAddCommGroupHom dgData X Y (-1)
    letI := GradedDGCategoryData.instAddCommGroupHom dgData X Y 0
    rw [differential_zero (-1) (C.zero (-1))]
    calc
      C.zero 0 = C.add 0 (C.neg 0 f.1) f.1 := by
        symm
        exact dgData.laws.add_left_neg 0 f.1
      _ = C.add 0 f.1 (C.neg 0 f.1) := by
        rw [dgData.laws.add_comm 0 (C.neg 0 f.1) f.1]
      _ = C.sub 0 f.1 f.1 := rfl
  let boundary_eq :
      ∀ {X Y : C.Obj} {f g : C.CycleHom X Y}, C.boundary_rel f g → f = g := by
    intro X Y f g hfg
    rcases hfg with ⟨witness, hWitness⟩
    letI := GradedDGCategoryData.instAddCommGroupHom dgData X Y (-1)
    letI := GradedDGCategoryData.instAddCommGroupHom dgData X Y 0
    have hSub : f.1 - g.1 = 0 := by
      simpa [GradedDGCategory.sub] using
        (hWitness.symm.trans (differential_zero (-1) witness))
    exact Subtype.ext (sub_eq_zero.mp hSub)
  exact
    { dgData := dgData
      boundary_rel_refl := boundary_refl
      boundary_rel_symm := by
        intro X Y f g hfg
        rw [boundary_eq hfg]
        exact boundary_refl g
      boundary_rel_trans := by
        intro X Y f g h hfg hgh
        rw [boundary_eq hfg, boundary_eq hgh]
        exact boundary_refl h
      comp_respects_boundary_left := by
        intro X Y Z f f' g hff'
        rw [boundary_eq hff']
        exact boundary_refl ⟨C.comp f'.1 g.1, dgData.laws.closed_comp f' g⟩
      comp_respects_boundary_right := by
        intro X Y Z f g g' hgg'
        rw [boundary_eq hgg']
        exact boundary_refl ⟨C.comp f.1 g'.1, dgData.laws.closed_comp f g'⟩ }

def boundary_setoid {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    (X Y : C.Obj) : Setoid (C.CycleHom X Y) where
  r := C.boundary_rel
  iseqv :=
    ⟨target.boundary_rel_refl, target.boundary_rel_symm, target.boundary_rel_trans⟩

abbrev Hom {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    (X Y : C.Obj) : Type v :=
  Quotient (target.boundary_setoid X Y)

def quotient_map {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} :
    C.CycleHom X Y → target.Hom X Y :=
  Quotient.mk (target.boundary_setoid X Y)

def identity {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    (X : C.Obj) : target.Hom X X :=
  target.quotient_map ⟨C.id X, target.dgData.laws.id_closed X⟩

def compose_cycle {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y Z : C.Obj} :
    C.CycleHom X Y → C.CycleHom Y Z → C.CycleHom X Z :=
  fun f g => ⟨C.comp f.1 g.1, target.dgData.laws.closed_comp f g⟩

def compose {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y Z : C.Obj} :
    target.Hom X Y → target.Hom Y Z → target.Hom X Z := by
  intro left right
  refine Quotient.liftOn₂ left right
    (fun f g => target.quotient_map (target.compose_cycle f g)) ?_
  intro f g f' g' hff' hgg'
  have hLeft := target.comp_respects_boundary_left g hff'
  have hRight := target.comp_respects_boundary_right f' hgg'
  exact Quotient.sound (target.boundary_rel_trans hLeft hRight)

def zero_cycle {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} : C.CycleHom X Y :=
  ⟨C.zero 0, by
    simpa using target.dgData.laws.differential_zero (X := X) (Y := Y) 0⟩

def add_cycle {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} :
    C.CycleHom X Y → C.CycleHom X Y → C.CycleHom X Y
  | f, g => by
      refine ⟨C.add 0 f.1 g.1, ?_⟩
      calc
        C.differential 0 (C.add 0 f.1 g.1)
            = C.add 1 (C.differential 0 f.1) (C.differential 0 g.1) := by
                simpa using target.dgData.laws.differential_add 0 f.1 g.1
        _ = C.add 1 (C.zero 1) (C.zero 1) := by rw [f.2, g.2]
        _ = C.zero 1 := by exact target.dgData.laws.zero_add 1 (C.zero 1)

def neg_cycle {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} :
    C.CycleHom X Y → C.CycleHom X Y
  | f => by
      letI := GradedDGCategoryData.instAddCommGroupHom target.dgData X Y 1
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

theorem boundary_rel_add {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj}
    {f f' g g' : C.CycleHom X Y} :
    C.boundary_rel f f' → C.boundary_rel g g' →
      C.boundary_rel (target.add_cycle f g) (target.add_cycle f' g') := by
  intro hff' hgg'
  rcases hff' with ⟨leftWitness, hLeft⟩
  rcases hgg' with ⟨rightWitness, hRight⟩
  letI := GradedDGCategoryData.instAddCommGroupHom target.dgData X Y 0
  refine ⟨C.add (-1) leftWitness rightWitness, ?_⟩
  change C.differential (-1) (C.add (-1) leftWitness rightWitness) =
    C.sub 0 (target.add_cycle f g).1 (target.add_cycle f' g').1
  calc
    C.differential (-1) (C.add (-1) leftWitness rightWitness)
        = C.add 0 (C.differential (-1) leftWitness) (C.differential (-1) rightWitness) := by
            simpa using target.dgData.laws.differential_add (-1) leftWitness rightWitness
    _ = C.add 0 (C.sub 0 f.1 f'.1) (C.sub 0 g.1 g'.1) := by rw [hLeft, hRight]
    _ = C.sub 0 (C.add 0 f.1 g.1) (C.add 0 f'.1 g'.1) := by
          change (f.1 - f'.1) + (g.1 - g'.1) = (f.1 + g.1) - (f'.1 + g'.1)
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = C.sub 0 (target.add_cycle f g).1 (target.add_cycle f' g').1 := by rfl

theorem boundary_rel_neg {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj}
    {f f' : C.CycleHom X Y} :
    C.boundary_rel f f' → C.boundary_rel (target.neg_cycle f) (target.neg_cycle f') := by
  intro hff'
  rcases hff' with ⟨witness, hWitness⟩
  letI := GradedDGCategoryData.instAddCommGroupHom target.dgData X Y 0
  refine ⟨C.neg (-1) witness, ?_⟩
  change C.differential (-1) (C.neg (-1) witness) =
    C.sub 0 (target.neg_cycle f).1 (target.neg_cycle f').1
  calc
    C.differential (-1) (C.neg (-1) witness)
        = C.neg 0 (C.differential (-1) witness) := by
            simpa using target.dgData.laws.differential_neg (-1) witness
    _ = C.neg 0 (C.sub 0 f.1 f'.1) := by rw [hWitness]
    _ = C.sub 0 (C.neg 0 f.1) (C.neg 0 f'.1) := by
          change -(f.1 - f'.1) = (-f.1) - (-f'.1)
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = C.sub 0 (target.neg_cycle f).1 (target.neg_cycle f').1 := by rfl

instance {C : GradedDGCategory.{u, v}} (target : H0Category C)
    {X Y : C.Obj} : Zero (target.Hom X Y) where
  zero := target.quotient_map target.zero_cycle

instance {C : GradedDGCategory.{u, v}} (target : H0Category C)
    {X Y : C.Obj} : Add (target.Hom X Y) where
  add left right := by
    refine Quotient.liftOn₂ left right
      (fun f g => target.quotient_map (target.add_cycle f g)) ?_
    intro f g f' g' hff' hgg'
    exact Quotient.sound (target.boundary_rel_add hff' hgg')

instance {C : GradedDGCategory.{u, v}} (target : H0Category C)
    {X Y : C.Obj} : Neg (target.Hom X Y) where
  neg morphism := by
    refine Quotient.liftOn morphism (fun f => target.quotient_map (target.neg_cycle f)) ?_
    intro f g hfg
    exact Quotient.sound (target.boundary_rel_neg hfg)

instance {C : GradedDGCategory.{u, v}} (target : H0Category C)
    {X Y : C.Obj} : AddCommGroup (target.Hom X Y) := by
  letI : AddGroup (target.Hom X Y) :=
    AddGroup.ofLeftAxioms
      (by
        intro a b c
        refine Quotient.inductionOn₃ a b c ?_
        intro f g h
        let rightRep : C.CycleHom X Y := target.add_cycle f (target.add_cycle g h)
        have hleft : target.add_cycle (target.add_cycle f g) h = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.add 0 f.1 g.1) h.1 = rightRep.1
          simpa [rightRep, H0Category.add_cycle] using
            target.dgData.laws.add_assoc 0 f.1 g.1 h.1
        exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep))
      (by
        intro a
        refine Quotient.inductionOn a ?_
        intro f
        let rightRep : C.CycleHom X Y := f
        have hleft : target.add_cycle target.zero_cycle f = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.zero 0) f.1 = rightRep.1
          simpa [rightRep] using target.dgData.laws.zero_add 0 f.1
        exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep))
      (by
        intro a
        refine Quotient.inductionOn a ?_
        intro f
        let rightRep : C.CycleHom X Y := target.zero_cycle (X := X) (Y := Y)
        have hleft : target.add_cycle (target.neg_cycle f) f = rightRep := by
          apply Subtype.ext
          change C.add 0 (C.neg 0 f.1) f.1 = rightRep.1
          simpa [rightRep, H0Category.zero_cycle] using
            target.dgData.laws.add_left_neg 0 f.1
        exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep))
  let addGroupInst : AddGroup (target.Hom X Y) := inferInstance
  exact
    { addGroupInst with
      add_comm := by
        intro a b
        refine Quotient.inductionOn₂ a b ?_
        intro f g
        let rightRep : C.CycleHom X Y := target.add_cycle g f
        have hleft : target.add_cycle f g = rightRep := by
          apply Subtype.ext
          change C.add 0 f.1 g.1 = rightRep.1
          simpa [rightRep, H0Category.add_cycle] using
            target.dgData.laws.add_comm 0 f.1 g.1
        exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep) }

theorem identity_comp {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} (f : target.Hom X Y) :
    target.compose (target.identity X) f = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change target.quotient_map
      ⟨C.comp (C.id X) representative.1,
        target.dgData.laws.closed_comp ⟨C.id X, target.dgData.laws.id_closed X⟩ representative⟩ =
    target.quotient_map representative
  apply Quotient.sound
  change C.boundary_rel
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
  simpa [hleft] using target.boundary_rel_refl rightRep

theorem comp_identity {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {X Y : C.Obj} (f : target.Hom X Y) :
    target.compose f (target.identity Y) = f := by
  refine Quotient.inductionOn f ?_
  intro representative
  change target.quotient_map
      ⟨C.comp representative.1 (C.id Y),
        target.dgData.laws.closed_comp representative ⟨C.id Y, target.dgData.laws.id_closed Y⟩⟩ =
    target.quotient_map representative
  apply Quotient.sound
  change C.boundary_rel
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
  simpa [hleft] using target.boundary_rel_refl rightRep

theorem composition_assoc {C : GradedDGCategory.{u, v}}
    (target : H0Category C)
    {W X Y Z : C.Obj}
    (f : target.Hom W X)
    (g : target.Hom X Y)
    (h : target.Hom Y Z) :
    target.compose (target.compose f g) h =
      target.compose f (target.compose g h) := by
  refine Quotient.inductionOn₃ f g h ?_
  intro fRep gRep hRep
  change target.quotient_map
      ⟨C.comp (C.comp fRep.1 gRep.1) hRep.1,
        target.dgData.laws.closed_comp
          ⟨C.comp fRep.1 gRep.1, target.dgData.laws.closed_comp fRep gRep⟩ hRep⟩ =
    target.quotient_map
      ⟨C.comp fRep.1 (C.comp gRep.1 hRep.1),
        target.dgData.laws.closed_comp fRep
          ⟨C.comp gRep.1 hRep.1, target.dgData.laws.closed_comp gRep hRep⟩⟩
  apply Quotient.sound
  change C.boundary_rel
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
  simpa [hleft] using target.boundary_rel_refl rightRep

/-- Wrapper exposing the canonical `H0` quotient as a mathlib category. -/
structure QuotientCategory {C : GradedDGCategory.{u, v}}
    (target : H0Category C) where
  obj : C.Obj

namespace QuotientCategory

instance {C : GradedDGCategory.{u, v}} (target : H0Category C) :
    CategoryTheory.Category (QuotientCategory target) where
  Hom X Y := target.Hom X.obj Y.obj
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

instance {C : GradedDGCategory.{u, v}} (target : H0Category C) :
    CategoryTheory.Preadditive (QuotientCategory target) where
  homGroup X Y := inferInstanceAs (AddCommGroup (target.Hom X.obj Y.obj))
  add_comp P Q R f f' g := by
    letI : AddCommGroup (P ⟶ Q) := inferInstanceAs (AddCommGroup (target.Hom P.obj Q.obj))
    letI : AddCommGroup (P ⟶ R) := inferInstanceAs (AddCommGroup (target.Hom P.obj R.obj))
    refine Quotient.inductionOn₃ f f' g ?_
    intro fRep fRep' gRep
    change target.quotient_map (target.compose_cycle (target.add_cycle fRep fRep') gRep) =
      target.quotient_map
        (target.add_cycle (target.compose_cycle fRep gRep) (target.compose_cycle fRep' gRep))
    let rightRep : C.CycleHom P.obj R.obj :=
      target.add_cycle (target.compose_cycle fRep gRep) (target.compose_cycle fRep' gRep)
    letI := GradedDGCategoryData.instAddCommGroupHom target.dgData P.obj Q.obj 0
    letI := GradedDGCategoryData.instAddCommGroupHom target.dgData P.obj R.obj 0
    have hleft : target.compose_cycle (target.add_cycle fRep fRep') gRep = rightRep := by
      apply Subtype.ext
      change (target.compose_cycle (target.add_cycle fRep fRep') gRep).1 = rightRep.1
      simpa [rightRep, H0Category.add_cycle, H0Category.compose_cycle] using
        target.dgData.laws.comp_add_left fRep.1 fRep'.1 gRep.1
    exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep)
  comp_add P Q R f g g' := by
    letI : AddCommGroup (Q ⟶ R) := inferInstanceAs (AddCommGroup (target.Hom Q.obj R.obj))
    letI : AddCommGroup (P ⟶ R) := inferInstanceAs (AddCommGroup (target.Hom P.obj R.obj))
    refine Quotient.inductionOn₃ f g g' ?_
    intro fRep gRep gRep'
    change target.quotient_map (target.compose_cycle fRep (target.add_cycle gRep gRep')) =
      target.quotient_map
        (target.add_cycle (target.compose_cycle fRep gRep) (target.compose_cycle fRep gRep'))
    let rightRep : C.CycleHom P.obj R.obj :=
      target.add_cycle (target.compose_cycle fRep gRep) (target.compose_cycle fRep gRep')
    letI := GradedDGCategoryData.instAddCommGroupHom target.dgData Q.obj R.obj 0
    letI := GradedDGCategoryData.instAddCommGroupHom target.dgData P.obj R.obj 0
    have hleft : target.compose_cycle fRep (target.add_cycle gRep gRep') = rightRep := by
      apply Subtype.ext
      change (target.compose_cycle fRep (target.add_cycle gRep gRep')).1 = rightRep.1
      simpa [rightRep, H0Category.add_cycle, H0Category.compose_cycle] using
        target.dgData.laws.comp_add_right fRep.1 gRep.1 gRep'.1
    exact Quotient.sound (by simpa [hleft] using target.boundary_rel_refl rightRep)

@[simp] def of_object {C : GradedDGCategory.{u, v}}
    (target : H0Category C) (X : C.Obj) : QuotientCategory target :=
  ⟨X⟩

@[simp] theorem of_object_obj {C : GradedDGCategory.{u, v}}
    (target : H0Category C) (X : C.Obj) :
  (of_object target X).obj = X :=
  rfl

/-- Mathlib Karoubi completion of the canonical `H0` category. -/
abbrev KaroubiCompletion {C : GradedDGCategory.{u, v}}
    (target : H0Category C) : Type _ :=
  CategoryTheory.Idempotents.Karoubi (QuotientCategory target)

/-- The standard embedding of the canonical `H0` category into its Karoubi completion. -/
abbrev toKaroubi {C : GradedDGCategory.{u, v}}
    (target : H0Category C) :
    CategoryTheory.Functor (QuotientCategory target) (KaroubiCompletion target) :=
  CategoryTheory.Idempotents.toKaroubi (QuotientCategory target)

@[simp] def karoubi_of_object {C : GradedDGCategory.{u, v}}
    (target : H0Category C) (X : C.Obj) : KaroubiCompletion target :=
  ((of_object target X : QuotientCategory target) :
    CategoryTheory.Idempotents.Karoubi (QuotientCategory target))

@[simp] def karoubi_carrier {C : GradedDGCategory.{u, v}}
    (target : H0Category C) (P : KaroubiCompletion target) : C.Obj :=
  P.X.obj

@[simp] theorem karoubi_carrier_of_object {C : GradedDGCategory.{u, v}}
    (target : H0Category C) (X : C.Obj) :
  karoubi_carrier target (karoubi_of_object target X) = X :=
  rfl

theorem karoubi_idempotent_complete {C : GradedDGCategory.{u, v}}
    (target : H0Category C) :
    CategoryTheory.IsIdempotentComplete (KaroubiCompletion target) :=
  inferInstance

end QuotientCategory

end H0Category

end Foundation.DG

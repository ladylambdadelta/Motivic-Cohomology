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

/-!
# DG Functors

This module provides the minimal graded dg-functor interface needed to transport
cycle classes and boundary relations.
-/

universe u1 v1 u2 v2

namespace Foundation.DG

/-- A graded dg-functor between graded dg categories. -/
structure GradedDGFunctor
    (C : GradedDGCategory.{u1, v1})
    (D : GradedDGCategory.{u2, v2}) where
  obj : C.Obj → D.Obj
  map : ∀ {X Y : C.Obj} (n : Int), C.Hom X Y n → D.Hom (obj X) (obj Y) n

/-- Compatibility laws for a graded dg-functor. -/
structure GradedDGFunctorLaws
    {C : GradedDGCategory.{u1, v1}}
    {D : GradedDGCategory.{u2, v2}}
    (F : GradedDGFunctor C D) where
  map_zero :
    ∀ {X Y : C.Obj} (n : Int),
      F.map n (C.zero (X := X) (Y := Y) n) =
        D.zero (X := F.obj X) (Y := F.obj Y) n
  map_add :
    ∀ {X Y : C.Obj} (n : Int)
      (f g : C.Hom X Y n),
        F.map n (C.add n f g) = D.add n (F.map n f) (F.map n g)
  map_neg :
    ∀ {X Y : C.Obj} (n : Int)
      (f : C.Hom X Y n),
        F.map n (C.neg n f) = D.neg n (F.map n f)
  map_id :
    ∀ (X : C.Obj),
      F.map 0 (C.id X) = D.id (F.obj X)
  map_comp :
    ∀ {X Y Z : C.Obj} {i j : Int}
      (f : C.Hom X Y i)
      (g : C.Hom Y Z j),
        F.map (i + j) (C.comp f g) = D.comp (F.map i f) (F.map j g)
  map_differential :
    ∀ {X Y : C.Obj} (n : Int)
      (f : C.Hom X Y n),
        F.map (n + 1) (C.differential n f) = D.differential n (F.map n f)

structure GradedDGFunctorData
    {C : GradedDGCategory.{u1, v1}}
    {D : GradedDGCategory.{u2, v2}}
    (F : GradedDGFunctor C D) where
  laws : GradedDGFunctorLaws (F := F)

namespace GradedDGFunctor

/-- A dg-functor sends cycles to cycles. -/
def mapCycle
    {C : GradedDGCategory.{u1, v1}}
    {D : GradedDGCategory.{u2, v2}}
    {F : GradedDGFunctor C D}
    (data : GradedDGFunctorData F)
    {X Y : C.Obj} :
    C.CycleHom X Y → D.CycleHom (F.obj X) (F.obj Y)
  | f => by
      refine ⟨F.map 0 f.1, ?_⟩
      calc
        D.differential 0 (F.map 0 f.1)
            = F.map 1 (C.differential 0 f.1) := by
                simpa [Int.zero_add] using
                  (data.laws.map_differential (X := X) (Y := Y) 0 f.1).symm
        _ = F.map 1 (C.zero 1) := by rw [f.2]
        _ = D.zero 1 := by
              simpa using data.laws.map_zero (X := X) (Y := Y) 1

/-- A dg-functor preserves the canonical boundary relation on cycles. -/
theorem map_boundary_rel
    {C : GradedDGCategory.{u1, v1}}
    {D : GradedDGCategory.{u2, v2}}
    {F : GradedDGFunctor C D}
    (data : GradedDGFunctorData F)
    {X Y : C.Obj}
    {f g : C.CycleHom X Y} :
    C.boundary_rel f g →
      D.boundary_rel (mapCycle data f) (mapCycle data g) := by
  intro hfg
  rcases hfg with ⟨witness, hWitness⟩
  refine ⟨F.map (-1) witness, ?_⟩
  change D.differential (-1) (F.map (-1) witness) =
    D.sub 0 (mapCycle data f).1 (mapCycle data g).1
  calc
    D.differential (-1) (F.map (-1) witness)
        = F.map 0 (C.differential (-1) witness) := by
            simpa using (data.laws.map_differential (-1) witness).symm
    _ = F.map 0 (C.sub 0 f.1 g.1) := by rw [hWitness]
    _ = F.map 0 (C.add 0 f.1 (C.neg 0 g.1)) := rfl
    _ = D.add 0 (F.map 0 f.1) (F.map 0 (C.neg 0 g.1)) := by
          simpa using data.laws.map_add 0 f.1 (C.neg 0 g.1)
    _ = D.add 0 (F.map 0 f.1) (D.neg 0 (F.map 0 g.1)) := by
          rw [data.laws.map_neg (X := X) (Y := Y) 0 g.1]
    _ = D.sub 0 (mapCycle data f).1 (mapCycle data g).1 := rfl

end GradedDGFunctor

end Foundation.DG

import Boundary.SmOver
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Pullbacks in `Sm/k`

Given morphisms `f : SmOverHom X W` and `g : SmOverHom Y W` in
`Geometry.SmSchemeOver k`, where `f.hom` is smooth, separated, and of finite
type, the scheme-level fiber product `Limits.pullback f.hom g.hom` carries the
structure of a smooth `k`-scheme.  The construction uses base-change stability
of smooth, separated, quasi-compact, and locally-of-finite-type morphisms.

## Main declarations

- `SmSchemeOver.pullbackObject` — the fiber product `X ×_W Y` as an
  `SmSchemeOver k` object, with structure map
  `pullback.snd f.hom g.hom ≫ Y.structMap`.
- `SmSchemeOver.pullbackFst` — first projection `X ×_W Y ⟶ X`.
- `SmSchemeOver.pullbackSnd` — second projection `X ×_W Y ⟶ Y`.
- `SmSchemeOver.isPullback` — the universal property as a
  `CategoryTheory.IsPullback`.

## Hypotheses

All four results require that `f.hom` is smooth, separated, and of finite type.
Both `IsOpenImmersion f.hom` and `IsEtale f.hom` imply these conditions, so this
covers the two Nisnevich-square cases needed for
`NisnevichDistinguishedSquareDataQ.pullback_geometry`.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

noncomputable section

variable {W X Y : Geometry.SmSchemeOver k}
  (f : SmOverHom X W) (g : SmOverHom Y W)
  (hf_smooth : IsSmooth f.hom)
  (hf_sep    : IsSeparated f.hom)
  (hf_ft     : Geometry.IsOfFiniteType f.hom)

/-- The fiber product `X ×_W Y` as an object of `SmSchemeOver k`.

The structure map `X ×_W Y ⟶ Spec k` is the composite
`pullback.snd f.hom g.hom ≫ Y.structMap`.  Smoothness of that composite follows
from base-change stability of smooth morphisms (`isSmooth_isStableUnderBaseChange`)
applied to `f.hom`, which gives `IsSmooth (pullback.snd f.hom g.hom)`.  Separated
and finite-type properties are handled analogously. -/
def SmSchemeOver.pullbackObject : Geometry.SmSchemeOver k where
  scheme    := pullback f.hom g.hom
  structMap := pullback.snd f.hom g.hom ≫ Y.structMap
  smooth := by
    letI : MorphismProperty.IsStableUnderBaseChange @IsSmooth :=
      AlgebraicGeometry.isSmooth_isStableUnderBaseChange
    letI : IsSmooth (pullback.snd f.hom g.hom) :=
      MorphismProperty.pullback_snd f.hom g.hom hf_smooth
    letI : IsSmooth Y.structMap := Y.smooth
    infer_instance
  separated := by
    letI : IsSeparated (pullback.snd f.hom g.hom) :=
      MorphismProperty.pullback_snd f.hom g.hom hf_sep
    letI : IsSeparated Y.structMap := Y.separated
    infer_instance
  finiteType := ⟨by
      letI : QuasiCompact (pullback.snd f.hom g.hom) :=
        MorphismProperty.pullback_snd f.hom g.hom hf_ft.1
      letI : QuasiCompact Y.structMap := Y.quasiCompact_structMap
      infer_instance,
    by
      letI : LocallyOfFiniteType (pullback.snd f.hom g.hom) :=
        MorphismProperty.pullback_snd f.hom g.hom hf_ft.2
      letI : LocallyOfFiniteType Y.structMap := Y.locallyOfFiniteType_structMap
      infer_instance⟩

/-- The first projection `X ×_W Y ⟶ X` in `SmSchemeOver k`.

Compatibility with structure maps: `pullback.fst ≫ X.structMap = structMap_of_pullbackObject`
follows from the chain
`fst ≫ X.structMap = fst ≫ f.hom ≫ W.structMap = snd ≫ g.hom ≫ W.structMap = snd ≫ Y.structMap`. -/
def SmSchemeOver.pullbackFst :
    SmOverHom (SmSchemeOver.pullbackObject f g hf_smooth hf_sep hf_ft) X where
  hom  := pullback.fst f.hom g.hom
  over := by
    have hDef : (SmSchemeOver.pullbackObject f g hf_smooth hf_sep hf_ft).structMap =
        pullback.snd f.hom g.hom ≫ Y.structMap := rfl
    rw [hDef, ← f.over, ← Category.assoc, pullback.condition, Category.assoc, g.over]

/-- The second projection `X ×_W Y ⟶ Y` in `SmSchemeOver k`. -/
def SmSchemeOver.pullbackSnd :
    SmOverHom (SmSchemeOver.pullbackObject f g hf_smooth hf_sep hf_ft) Y where
  hom  := pullback.snd f.hom g.hom
  over := rfl

/-- The commutativity witness in `SmSchemeOver k`, lifting `pullback.condition` from `Scheme`.

Stated via `SmOverHom.comp` rather than `≫` to avoid stuck category metavariables:
`SmOverHom A B` is definitionally but not syntactically `A ⟶ B` in `Geometry.SmSchemeOver k`,
and Lean's instance search for `≫` requires syntactic matches on the morphism type. -/
theorem SmSchemeOver.pullbackFst_comp_eq :
    SmOverHom.comp (SmSchemeOver.pullbackFst f g hf_smooth hf_sep hf_ft) f =
    SmOverHom.comp (SmSchemeOver.pullbackSnd f g hf_smooth hf_sep hf_ft) g :=
  SmOverHom.ext _ _ pullback.condition

/-- The universal property of the fiber product in `SmSchemeOver k`.

The `@IsPullback (Geometry.SmSchemeOver k) _` spelling is required to give Lean an explicit
category argument; without it the `Category (SmSchemeOver k)` instance is not found when the
morphism arguments are typed as `SmOverHom A B` rather than `A ⟶ B`. -/
theorem SmSchemeOver.isPullback :
    @CategoryTheory.IsPullback (Geometry.SmSchemeOver k) _
      (SmSchemeOver.pullbackObject f g hf_smooth hf_sep hf_ft) X Y W
      (SmSchemeOver.pullbackFst f g hf_smooth hf_sep hf_ft)
      (SmSchemeOver.pullbackSnd f g hf_smooth hf_sep hf_ft)
      f g :=
  -- Term-mode: avoids `apply PullbackCone.isLimitAux` leaving a `Category` metavar.
  -- We use `PullbackCone.IsLimit.mk` which directly builds
  -- `IsLimit (PullbackCone.mk pullbackFst pullbackSnd eq)`.
  { toCommSq := ⟨SmSchemeOver.pullbackFst_comp_eq f g hf_smooth hf_sep hf_ft⟩
    isLimit' := ⟨PullbackCone.IsLimit.mk
        (SmSchemeOver.pullbackFst_comp_eq f g hf_smooth hf_sep hf_ft)
        -- Lift: scheme-level pullback.lift, wrapped with the `over` field proof.
        (fun s =>
          { hom := pullback.lift s.fst.hom s.snd.hom
                     (congrArg SmOverHom.hom (PullbackCone.condition s))
            over := by
              -- Goal: pullback.lift _ _ _ ≫ (pullbackObject ...).structMap = s.pt.structMap
              -- (pullbackObject ...).structMap = pullback.snd ≫ Y.structMap  (by rfl)
              change pullback.lift _ _ _ ≫ (pullback.snd f.hom g.hom ≫ Y.structMap) =
                     s.pt.structMap
              rw [← Category.assoc, pullback.lift_snd]
              exact s.snd.over })
        -- First factorization: lift ≫ pullbackFst = s.fst
        (fun s => SmOverHom.ext _ _ (pullback.lift_fst _ _ _))
        -- Second factorization: lift ≫ pullbackSnd = s.snd
        (fun s => SmOverHom.ext _ _ (pullback.lift_snd _ _ _))
        -- Uniqueness: any morphism satisfying both factorizations equals the lift
        (fun s m hm1 hm2 =>
          SmOverHom.ext _ _ (pullback.hom_ext
            (congrArg SmOverHom.hom hm1 |>.trans (pullback.lift_fst _ _ _).symm)
            (congrArg SmOverHom.hom hm2 |>.trans (pullback.lift_snd _ _ _).symm)))⟩ }

end -- noncomputable section

end Boundary

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Basic

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace TraceCalc
namespace ClassicalPeriods
namespace Wall10A

abbrev AGScheme := AlgebraicGeometry.Scheme

abbrev SpecQ : AGScheme :=
  AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of ℚ))

structure SchemeOverQ where
  X : AGScheme
  structureMap : X ⟶ SpecQ

namespace SchemeOverQ

private abbrev pullbackObj (X Y : SchemeOverQ) : AGScheme :=
  pullback X.structureMap Y.structureMap

private abbrev pullbackFst (X Y : SchemeOverQ) : pullbackObj X Y ⟶ X.X :=
  pullback.fst X.structureMap Y.structureMap

private abbrev pullbackSnd (X Y : SchemeOverQ) : pullbackObj X Y ⟶ Y.X :=
  pullback.snd X.structureMap Y.structureMap

structure Hom (X Y : SchemeOverQ) where
  f : X.X ⟶ Y.X
  over_base : f ≫ Y.structureMap = X.structureMap

instance (X Y : SchemeOverQ) : CoeFun (Hom X Y) (fun _ => X.X ⟶ Y.X) where
  coe f := f.f

@[ext]
theorem Hom.ext {X Y : SchemeOverQ} {f g : Hom X Y} (h : f.f = g.f) : f = g := by
  cases f
  cases g
  simp only at h
  subst h
  rfl

def id (X : SchemeOverQ) : Hom X X where
  f := 𝟙 X.X
  over_base := by simp

def comp {X Y Z : SchemeOverQ} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f
  over_base := by
    rw [Category.assoc, g.over_base, f.over_base]

structure ProductData (X Y : SchemeOverQ) where
  product : SchemeOverQ
  fst : Hom product X
  snd : Hom product Y
  lift : {T : SchemeOverQ} → Hom T X → Hom T Y → Hom T product
  lift_fst : ∀ {T : SchemeOverQ} (f : Hom T X) (g : Hom T Y),
    comp (lift f g) fst = f
  lift_snd : ∀ {T : SchemeOverQ} (f : Hom T X) (g : Hom T Y),
    comp (lift f g) snd = g
  mathlibProductObject : AGScheme
  mathlibProductObject_eq : mathlibProductObject = pullback X.structureMap Y.structureMap

def prod (X Y : SchemeOverQ) : SchemeOverQ where
  X := pullbackObj X Y
  structureMap := pullbackSnd X Y ≫ Y.structureMap

def prod_fst (X Y : SchemeOverQ) : Hom (prod X Y) X where
  f := pullbackFst X Y
  over_base := by
    change pullbackFst X Y ≫ X.structureMap = pullbackSnd X Y ≫ Y.structureMap
    exact (pullback.condition :
      pullbackFst X Y ≫ X.structureMap = pullbackSnd X Y ≫ Y.structureMap)

def prod_snd (X Y : SchemeOverQ) : Hom (prod X Y) Y where
  f := pullbackSnd X Y
  over_base := rfl

def prod_universal {T X Y : SchemeOverQ} (f : Hom T X) (g : Hom T Y) : Hom T (prod X Y) where
  f := pullback.lift f.f g.f (by rw [f.over_base, g.over_base])
  over_base := by
    dsimp [prod]
    simp
    exact g.over_base

def tripleProduct (X Y Z : SchemeOverQ) : SchemeOverQ :=
  prod (prod X Y) Z

def p12 (X Y Z : SchemeOverQ) : Hom (tripleProduct X Y Z) (prod X Y) :=
  prod_fst (prod X Y) Z

def p13 (X Y Z : SchemeOverQ) : Hom (tripleProduct X Y Z) (prod X Z) :=
  prod_universal
    (comp (p12 X Y Z) (prod_fst X Y))
    (prod_snd (prod X Y) Z)

def p23 (X Y Z : SchemeOverQ) : Hom (tripleProduct X Y Z) (prod Y Z) :=
  prod_universal
    (comp (p12 X Y Z) (prod_snd X Y))
    (prod_snd (prod X Y) Z)

end SchemeOverQ
end Wall10A
end ClassicalPeriods
end TraceCalc

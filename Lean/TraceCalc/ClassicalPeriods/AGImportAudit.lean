import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Algebra

open Opposite

/-!
# Wall 10A mathlib import audit

| Mathlib thing wanted | Actual available name | Import file | Usable now? | If no: local wrapper needed |
|---|---|---|---|---|
| Schemes | `AlgebraicGeometry.Scheme` | `Mathlib.AlgebraicGeometry.Scheme` | yes | no |
| Scheme morphisms | `AlgebraicGeometry.Scheme.Hom`, notation `X ⟶ Y` | `Mathlib.AlgebraicGeometry.Scheme` | yes | no |
| Affine base `Spec Q` | `AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of ℚ))` | `Mathlib.AlgebraicGeometry.Scheme`, `Mathlib.Algebra.Category.Ring.Basic` | yes | no |
| Pullback object | `CategoryTheory.Limits.pullback` | `Mathlib.AlgebraicGeometry.Pullbacks` | yes | wrap as `SchemeOverQ.prod` |
| Pullback projections | `CategoryTheory.Limits.pullback.fst`, `CategoryTheory.Limits.pullback.snd` | `Mathlib.AlgebraicGeometry.Pullbacks` | yes | wrap as over-`Q` projections |
| Binary product object | `CategoryTheory.Limits.prod` | `Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts` | yes | not used for over-`Q` product |
| Open immersion | `AlgebraicGeometry.IsOpenImmersion` | `Mathlib.AlgebraicGeometry.OpenImmersion` | yes | no |
| Closed immersion | `AlgebraicGeometry.IsClosedImmersion` | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` | yes | no |
| Proper morphism | `AlgebraicGeometry.IsProper` | `Mathlib.AlgebraicGeometry.Morphisms.Proper` | yes | no |
| Finite morphism | `AlgebraicGeometry.IsFinite` | `Mathlib.AlgebraicGeometry.Morphisms.Finite` | yes | no |
| Smooth morphism | `AlgebraicGeometry.IsSmooth` | `Mathlib.AlgebraicGeometry.Morphisms.Smooth` | yes | wrap for over-`Q` |
| Flat algebra/ring input | `Module.Flat`, `Algebra.Flat`, `RingHom.Flat` | `Mathlib.RingTheory.Flat.Basic`, `Mathlib.RingTheory.Flat.Algebra` | yes at algebra/ring level | local scheme-level wrapper needed |
| Finite support cycles | `Finsupp` notation `α →₀ ℤ` | `Mathlib.Data.Finsupp.Basic` | yes | no |
| Requested morphism properties import | no file at `Mathlib.AlgebraicGeometry.Morphisms.Properties` | individual morphism files | no | import concrete morphism files |
| Requested pullback import | no file at `Mathlib.CategoryTheory.Limits.Shapes.Pullbacks` | `Mathlib.AlgebraicGeometry.Pullbacks` imports pullback API | no | use available import |
| Requested free abelian import | no file at `Mathlib.Algebra.Group.FreeAbelianGroup` | `Mathlib.GroupTheory.FreeAbelianGroup` | no | use available import |
| Free abelian group alternative | `FreeAbelianGroup` | `Mathlib.GroupTheory.FreeAbelianGroup` | yes | optional |
-/

#check AlgebraicGeometry.Scheme
#check AlgebraicGeometry.Scheme.Hom
#check AlgebraicGeometry.Scheme.Spec
#check CategoryTheory.Limits.pullback
#check CategoryTheory.Limits.pullback.fst
#check CategoryTheory.Limits.pullback.snd
#check CategoryTheory.Limits.prod
#check CommRingCat.of
#check (AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of ℚ)))
#check AlgebraicGeometry.IsOpenImmersion
#check AlgebraicGeometry.IsClosedImmersion
#check AlgebraicGeometry.IsProper
#check AlgebraicGeometry.IsFinite
#check AlgebraicGeometry.IsSmooth
#check Module.Flat
#check Algebra.Flat
#check RingHom.Flat
#check Finsupp
#check FreeAbelianGroup

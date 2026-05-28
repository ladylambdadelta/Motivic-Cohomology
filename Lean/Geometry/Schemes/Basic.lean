import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.FiniteType
import Mathlib.CategoryTheory.Category.Basic

/-!
# Smooth schemes over a perfect field

Defines the object layer for `Sm/k`: smooth separated schemes of finite type over
a perfect field `k`.

Mathlib currently exposes `QuasiCompact` and `LocallyOfFiniteType` as separate
scheme-morphism predicates, so this file packages finite type as their conjunction.
This file does not define `SmCor(k)`: that category will reuse these objects but
replace ordinary morphisms with finite correspondences.

Every field is treated as a `CommRingCat` via `CommRingCat.of k`; the base scheme
is `Spec (CommRingCat.of k)`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace Geometry

/-- A scheme morphism is of finite type if it is quasi-compact and locally of finite type. -/
abbrev IsOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  QuasiCompact f ∧ LocallyOfFiniteType f

/-- The object layer of `Sm/k`: smooth separated schemes of finite type over a
    perfect field `k`. -/
structure SmSchemeOver (k : Type u) [Field k] [PerfectField k] where
  /-- The underlying scheme. -/
  scheme    : Scheme.{u}
  /-- The structure morphism X → Spec k. -/
  structMap : scheme ⟶ Spec (CommRingCat.of k)
  /-- The morphism is smooth over k. -/
  smooth    : IsSmooth structMap
  /-- The morphism is separated over k. -/
  separated : IsSeparated structMap
  /-- The morphism is of finite type over k. -/
  finiteType : IsOfFiniteType structMap

namespace SmSchemeOver

variable {k : Type u} [Field k] [PerfectField k]

/-- The structure morphism of an object of `Sm/k` is quasi-compact. -/
theorem quasiCompact_structMap (X : SmSchemeOver k) : QuasiCompact X.structMap :=
  X.finiteType.1

/-- The structure morphism of an object of `Sm/k` is locally of finite type. -/
theorem locallyOfFiniteType_structMap (X : SmSchemeOver k) :
    LocallyOfFiniteType X.structMap :=
  X.finiteType.2

instance isNoetherian_scheme (X : SmSchemeOver k) : AlgebraicGeometry.IsNoetherian X.scheme := by
  classical
  letI : AlgebraicGeometry.IsLocallyNoetherian X.scheme := by
    refine AlgebraicGeometry.isLocallyNoetherian_of_affine_cover
      (S := fun U : X.scheme.affineOpens => U)
      (AlgebraicGeometry.iSup_affineOpens_eq_top X.scheme) ?_
    intro U
    let f : Γ(Spec (CommRingCat.of k), ⊤) ⟶ Γ(X.scheme, (U : X.scheme.Opens)) :=
      X.structMap.appLE ⊤ U (by simp)
    letI : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X.scheme, U) := f.toAlgebra
    letI : Algebra.FiniteType Γ(Spec (CommRingCat.of k), ⊤) Γ(X.scheme, U) :=
      (locallyOfFiniteType_structMap X).finiteType_of_affine_subset
        ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ U (by simp)
    have hBase : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) := by
      apply isNoetherianRing_of_ringEquiv k
      exact (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    letI : IsNoetherianRing Γ(Spec (CommRingCat.of k), ⊤) := hBase
    simpa using
      (Algebra.FiniteType.isNoetherianRing
        Γ(Spec (CommRingCat.of k), ⊤)
        Γ(X.scheme, (U : X.scheme.Opens)))
  letI : CompactSpace X.scheme :=
    (AlgebraicGeometry.quasiCompact_over_affine_iff X.structMap).mp
      (quasiCompact_structMap X)
  exact
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := inferInstance }

/-- If an open subscheme is also closed in the ambient topological space, then
its inclusion is a closed immersion of schemes. -/
theorem isClosedImmersion_ι_of_isClosed (X : SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) : IsClosedImmersion U.ι := by
  constructor
  · simpa using hU.isClosedEmbedding_subtypeVal
  · intro x
    exact Scheme.Hom.stalkMap_surjective U.ι x

/-- An open subscheme whose inclusion is also a closed immersion inherits the
`Sm/k` structure from the ambient smooth scheme. -/
def ofOpen (X : SmSchemeOver k) (U : X.scheme.Opens) [IsClosedImmersion U.ι] :
    SmSchemeOver k where
  scheme := U.toScheme
  structMap := U.ι ≫ X.structMap
  smooth := by
    letI : IsSmooth X.structMap := X.smooth
    letI : IsSmooth U.ι := inferInstance
    infer_instance
  separated := by
    letI : IsSeparated X.structMap := X.separated
    letI : IsSeparated U.ι := inferInstance
    infer_instance
  finiteType := by
    letI : QuasiCompact X.structMap := quasiCompact_structMap X
    letI : LocallyOfFiniteType X.structMap := locallyOfFiniteType_structMap X
    letI : QuasiCompact U.ι := inferInstance
    letI : LocallyOfFiniteType U.ι := inferInstance
    constructor
    · infer_instance
    · infer_instance

/-- A clopen subscheme inherits the `Sm/k` structure from the ambient smooth
scheme. -/
def ofClopen (X : SmSchemeOver k) (U : X.scheme.Opens)
    (hU : IsClosed (U : Set X.scheme)) : SmSchemeOver k := by
  letI : IsClosedImmersion U.ι := isClosedImmersion_ι_of_isClosed X U hU
  exact ofOpen X U

end SmSchemeOver

/-- The rational-base object layer used by the project target `DM_gm(Q)`. -/
abbrev SmQ := SmSchemeOver ℚ

end Geometry

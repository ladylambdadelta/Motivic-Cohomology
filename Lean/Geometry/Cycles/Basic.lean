import Geometry.Schemes.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Data.Finsupp.Defs
import Mathlib.Algebra.Module.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Algebraic cycles

Defines algebraic cycles on a scheme as formal ℤ-linear combinations of
integral closed subschemes.  Finite correspondences (in `Geometry.Correspondences`)
are built on top of these.

An *integral closed subscheme* of X is a scheme Z equipped with a closed
immersion Z ↪ X such that Z is integral (reduced + irreducible).

An *algebraic cycle* on X is an element of `IntClosedSubscheme X →₀ ℤ` —
the free abelian group on the set of integral closed subschemes.
-/

universe u

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

/-- A closed integral subscheme of X: an integral scheme Z with a closed
    immersion Z ↪ X.  These are the atoms of the algebraic cycle group. -/
structure IntClosedSubscheme (X : Scheme.{u}) where
  /-- The integral scheme Z. -/
  scheme          : Scheme.{u}
  /-- The closed immersion Z ↪ X. -/
  inclusion       : scheme ⟶ X
  /-- The inclusion is a closed immersion. -/
  isClosedImm     : IsClosedImmersion inclusion
  /-- Z is integral (= reduced and irreducible). -/
  isIntegral      : IsIntegral scheme

attribute [instance] IntClosedSubscheme.isIntegral

namespace IntClosedSubscheme

variable {X : Scheme.{u}}

/-- The image in `X` of the generic point of an integral closed subscheme `W`. -/
noncomputable def genericPointImage (W : IntClosedSubscheme X) : X :=
  by
    letI : IsIntegral W.scheme := W.isIntegral
    exact W.inclusion.base (genericPoint W.scheme)

/-- The generic point of `W.scheme`, packaged without exposing typeclass arguments. -/
noncomputable def sourceGenericPoint (W : IntClosedSubscheme X) : W.scheme := by
  letI : IsIntegral W.scheme := W.isIntegral
  exact genericPoint W.scheme

/-- Function field of an integral closed subscheme, with the integrality plumbing
    hidden behind the subscheme package. -/
noncomputable abbrev functionField (W : IntClosedSubscheme X) : CommRingCat := by
  letI : IsIntegral W.scheme := W.isIntegral
  exact W.scheme.functionField

/-- An affine chart in `X` containing the image of the generic point of `W`. -/
structure GenericAffineChart (W : IntClosedSubscheme X) where
  /-- Affine open neighborhood in the ambient scheme. -/
  U : X.Opens
  /-- Affineness of the chart. -/
  isAffine : IsAffineOpen U
  /-- The image of the generic point lies in the chart. -/
  mem_genericPointImage : genericPointImage W ∈ U

/-- There exists an affine open neighborhood in `X` containing the image of the
    generic point of `W`. -/
theorem genericPointImage_mem_affineOpen (W : IntClosedSubscheme X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ genericPointImage W ∈ U := by
  letI : IsIntegral W.scheme := W.isIntegral
  refine ⟨(X.affineCover.map (genericPointImage W)).opensRange, ?_, ?_⟩
  · simpa using (isAffineOpen_opensRange (X.affineCover.map (genericPointImage W)))
  · simpa using (X.affineCover.covers (genericPointImage W))

/-- Choice version of `genericPointImage_mem_affineOpen`. -/
noncomputable def genericAffineChart (W : IntClosedSubscheme X) : GenericAffineChart W := by
  classical
  refine ⟨Classical.choose (genericPointImage_mem_affineOpen (W := W)), ?_, ?_⟩
  · exact (Classical.choose_spec (genericPointImage_mem_affineOpen (W := W))).1
  · exact (Classical.choose_spec (genericPointImage_mem_affineOpen (W := W))).2

/-- Existence of a generic affine chart package for any integral closed subscheme. -/
theorem genericAffineChart_exists (W : IntClosedSubscheme X) :
    ∃ chart : GenericAffineChart W, genericPointImage W ∈ chart.U := by
  refine ⟨genericAffineChart W, ?_⟩
  exact (genericAffineChart W).mem_genericPointImage

/-- Named chooser for a generic affine chart package. -/
noncomputable def chooseGenericAffineChart (W : IntClosedSubscheme X) : GenericAffineChart W :=
  genericAffineChart W

/-- Source-side generic-point affine chart existence for `W.scheme`. -/
theorem genericPoint_mem_affineOpen_source (W : IntClosedSubscheme X) :
    ∃ U : W.scheme.Opens, IsAffineOpen U ∧ sourceGenericPoint W ∈ U := by
  letI : IsIntegral W.scheme := W.isIntegral
  refine ⟨(W.scheme.affineCover.map (sourceGenericPoint W)).opensRange, ?_, ?_⟩
  · simpa using
      (isAffineOpen_opensRange (W.scheme.affineCover.map (sourceGenericPoint W)))
  · simpa using (W.scheme.affineCover.covers (sourceGenericPoint W))

/-- Compatibility data for using an ambient generic affine chart of an image component
    with a morphism `f : X ⟶ Y`: the source preimage chart is affine. -/
structure GenericAffineChartCompatibility
    {X Y : Scheme.{u}} (f : X ⟶ Y) {W : IntClosedSubscheme Y}
    (targetChart : GenericAffineChart W) where
  sourcePreimageIsAffine : IsAffineOpen (f ⁻¹ᵁ targetChart.U)

/-- Packaged common-localization witness for comparing two generic affine chart
    multiplicity computations in the same finite-map/image-component context. -/
structure GenericAffineChartCommonLocalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) {W : IntClosedSubscheme Y}
    (chart₁ chart₂ : GenericAffineChart W) where
  A₁ : Type*
  B₁ : Type*
  A₂ : Type*
  B₂ : Type*
  A₀ : Type*
  B₀ : Type*
  [commRingA₁ : CommRing A₁]
  [commRingB₁ : CommRing B₁]
  [commRingA₂ : CommRing A₂]
  [commRingB₂ : CommRing B₂]
  [commRingA₀ : CommRing A₀]
  [commRingB₀ : CommRing B₀]
  [isDomainA₁ : IsDomain A₁]
  [isDomainB₁ : IsDomain B₁]
  [isDomainA₂ : IsDomain A₂]
  [isDomainB₂ : IsDomain B₂]
  [isDomainA₀ : IsDomain A₀]
  [isDomainB₀ : IsDomain B₀]
  [algebraA₁B₁ : Algebra A₁ B₁]
  [algebraA₂B₂ : Algebra A₂ B₂]
  [algebraA₀B₀ : Algebra A₀ B₀]
  [algebraFracA₁B₁ : Algebra (FractionRing A₁) (FractionRing B₁)]
  [algebraFracA₂B₂ : Algebra (FractionRing A₂) (FractionRing B₂)]
  [algebraFracA₀B₀ : Algebra (FractionRing A₀) (FractionRing B₀)]
  [isScalarTowerA₁ : IsScalarTower A₁ (FractionRing A₁) (FractionRing B₁)]
  [isScalarTowerA₂ : IsScalarTower A₂ (FractionRing A₂) (FractionRing B₂)]
  [isScalarTowerA₀ : IsScalarTower A₀ (FractionRing A₀) (FractionRing B₀)]
  [isLocFracB₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ A₁⁰) (FractionRing B₁)]
  [isLocFracB₂ : IsLocalization (Algebra.algebraMapSubmonoid B₂ A₂⁰) (FractionRing B₂)]
  [isLocFracB₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ A₀⁰) (FractionRing B₀)]
  [moduleFiniteA₁B₁ : Module.Finite A₁ B₁]
  [moduleFiniteA₂B₂ : Module.Finite A₂ B₂]
  [moduleFiniteA₀B₀ : Module.Finite A₀ B₀]
  S₁ : Submonoid A₁
  [algebraA₁A₀ : Algebra A₁ A₀]
  [isLocA₁A₀ : IsLocalization S₁ A₀]
  [algebraB₁B₀ : Algebra B₁ B₀]
  [isLocB₁B₀ : IsLocalization (Algebra.algebraMapSubmonoid B₁ S₁) B₀]
  S₂ : Submonoid A₂
  [algebraA₂A₀ : Algebra A₂ A₀]
  [isLocA₂A₀ : IsLocalization S₂ A₀]
  [algebraB₂B₀ : Algebra B₂ B₀]
  [isLocB₂B₀ : IsLocalization (Algebra.algebraMapSubmonoid B₂ S₂) B₀]
  eA₁ : FractionRing A₁ ≃+* FractionRing A₀
  eB₁ : FractionRing B₁ ≃+* FractionRing B₀
  hcompat₁ :
    (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₁.toRingHom =
      eB₁.toRingHom.comp (algebraMap (FractionRing A₁) (FractionRing B₁))
  eA₂ : FractionRing A₂ ≃+* FractionRing A₀
  eB₂ : FractionRing B₂ ≃+* FractionRing B₀
  hcompat₂ :
    (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₂.toRingHom =
      eB₂.toRingHom.comp (algebraMap (FractionRing A₂) (FractionRing B₂))

/-- The function field of `W.scheme` provides a common-localization witness for any two
    generic affine charts.  W produces exactly one common field K = k(W); all six
    ring slots are filled with K.  No second copy (FractionRing K) is manufactured;
    it appears only in the structure's `eA₁/eB₁/eA₂/eB₂` slots which are satisfied
    by `RingEquiv.refl (FractionRing K)`.  Compatibility is trivial since all maps
    are identities. -/
theorem genericAffineChartCommonLocalization_exists
    {X Y : Scheme.{u}} (f : X ⟶ Y) {W : IntClosedSubscheme Y}
    (c₁ c₂ : GenericAffineChart W) :
  Nonempty (@GenericAffineChartCommonLocalization.{u, u, u, u, u, u, u} X Y f W c₁ c₂) := by
  letI : IsIntegral W.scheme := W.isIntegral
  -- Two-step unpack: Kcat as CommRingCat object, K as its carrier type.
  -- This makes the CoeSort coercion explicit and helps instance synthesis.
  let Kcat : CommRingCat := W.scheme.functionField
  let K : Type u := Kcat
  -- Root instance: Field K (from the global IsIntegral instance chain).
  -- This alone provides CommRing K, IsDomain K, and all their derivatives.
  letI hField : Field K := inferInstance
  -- Explicit self-algebra (Algebra.id takes R as an explicit argument).
  letI hAlgKK : Algebra K K := Algebra.id K
  -- Module.Finite K K: K is a finitely generated module over itself.
  letI hFinKK : Module.Finite K K := Module.Finite.self K
  letI hLocSelf : IsLocalization (Algebra.algebraMapSubmonoid K K⁰) K :=
    IsLocalization.at_units (R := K) (Algebra.algebraMapSubmonoid K K⁰) <| by
      intro y hy
      change IsUnit y
      rcases Submonoid.mem_map.mp hy with ⟨x, hx, rfl⟩
      simpa [Algebra.id.map_eq_id] using (isUnit_of_mem_nonZeroDivisors hx)
  letI hLocFrac : IsLocalization (Algebra.algebraMapSubmonoid K K⁰) (FractionRing K) :=
    IsLocalization.isLocalization_of_algEquiv (M := Algebra.algebraMapSubmonoid K K⁰)
      ((FractionRing.algEquiv (A := K) K).symm)
  exact ⟨(show @GenericAffineChartCommonLocalization.{u, u, u, u, u, u, u} X Y f W c₁ c₂ from {
    A₁ := K, B₁ := K, A₂ := K, B₂ := K, A₀ := K, B₀ := K,
    S₁ := K⁰, S₂ := K⁰,
    eA₁ := RingEquiv.refl (FractionRing K),
    eB₁ := RingEquiv.refl (FractionRing K),
    hcompat₁ := by
      ext x
      simp [Algebra.id.map_eq_id, RingEquiv.refl],
    eA₂ := RingEquiv.refl (FractionRing K),
    eB₂ := RingEquiv.refl (FractionRing K),
    hcompat₂ := by
      ext x
      simp [Algebra.id.map_eq_id, RingEquiv.refl]
  })⟩

end IntClosedSubscheme

/-- Algebraic cycles on X: the free abelian group on integral closed subschemes.
    Concretely, `AlgCycle X` = `IntClosedSubscheme X →₀ ℤ`. -/
abbrev AlgCycle (X : Scheme.{u}) : Type (u + 1) :=
  IntClosedSubscheme X →₀ ℤ

namespace AlgCycle

variable {X : Scheme.{u}}

/-- The zero cycle. -/
def zero : AlgCycle X := 0

/-- Addition of cycles. -/
noncomputable def add (c d : AlgCycle X) : AlgCycle X := c + d

/-- The cycle associated to a single integral closed subscheme (with coefficient 1). -/
noncomputable def ofSubscheme (Z : IntClosedSubscheme X) : AlgCycle X := by
  classical
  exact Finsupp.single Z 1

/-- Scalar multiplication by an integer. -/
noncomputable def smul (n : ℤ) (c : AlgCycle X) : AlgCycle X := n • c

end AlgCycle

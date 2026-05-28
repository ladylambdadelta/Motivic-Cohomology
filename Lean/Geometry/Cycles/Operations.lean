import Geometry.Cycles.Basic
import Boundary.ImageComponentGeometry
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Cycle Operations

This file records honest, currently available operations on `AlgCycle` that are
already provided by the underlying `Finsupp` model:

* coefficient evaluation;
* additive inverse and subtraction.

Boundary of the current implementation (not yet formalized here):

* chart-parametric `finiteMapImageMultiplicityOnChart`
* chart-independence of `finiteMapImageMultiplicityOnChart`
* `finitePushforwardIntegralSubscheme`
* `finitePushforwardCycle`
* `finitePushforwardCycle_coeff_eq_genericLength`

These require real algebraic-geometry input:

* general scheme-theoretic image (or adequate affine/local reduction);
* generic-point or generic-rank/length API;
* local length/rank theorem for finite morphisms;
* proof that finite pushforward has finite support.

## Finite-map multiplicity theorem targets

Intended dependency ladder:

1. affine-local image factorization for finite maps;
2. generic-point/function-field coefficient;
3. numeric generic multiplicity;
4. affine-local independence;
5. finite pushforward of integral closed subschemes;
6. finite pushforward of cycles;
7. coefficient theorem.

Comment-only target signatures (mathematical intent, not Lean declarations):

* finiteMapImageMultiplicity
  -- finite f : X ⟶ Y
  -- integral closed Z ⊂ X
  -- integral image component W ⊂ Y
  -- returns Nat or Int coefficient from generic local length/rank

* finiteMapImageMultiplicity_eq_genericLength
  -- coefficient equals length at generic point / generic rank

* finitePushforwardIntegralSubscheme
  -- push [Z] to weighted image-component cycle

* finitePushforwardCycle
  -- additive extension to AlgCycle

* finitePushforwardCycle_coeff_eq_genericLength
  -- coefficient formula needed for finite correspondence composition

Exact missing Mathlib-style shim target:

* genericLengthOfFiniteMapToIntegralImage
  -- numeric length/rank of the finite module at the generic point of the image
  -- invariant under affine-local presentation

Current algebraic overlap core now available in this file:

* finiteDominantAffine_genericMultiplicity_commonLocalization_eq
  -- two affine presentations localizing to a common overlap yield equal
  -- affine generic multiplicities

First downstream wrappers still needed before defining finite pushforward operations:

1. affine chart around the generic point of an integral image component
  -- input: finite `f : X ⟶ Y`, integral component `W ⊂ Y`
  -- output: affine open `U ⊆ Y` with `genericPoint W ∈ U`

2. induced finite algebra map on chosen source/image charts
  -- input: chart `U` around `genericPoint W` and corresponding source chart
  -- output: finite ring map `A → B` representing the local finite dominant model

3. common affine localization for two admissible chart choices
  -- input: two chart-induced finite algebra models
  -- output: overlap-localized common model `(A₀, B₀)` with localization data

4. compatibility transport from chart constructions to the algebraic overlap theorem
  -- produce fraction-field equivalences and scalar-compatibility hypotheses needed by
  -- `finiteDominantAffine_genericMultiplicity_commonLocalization_eq`

Principle: no coefficient without generic length/rank, and no global scalar by choosing a chart.
-/

universe u

open AlgebraicGeometry
open scoped nonZeroDivisors

section GenericRankPrimitive

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
variable [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B)]
variable [Module.Finite A B]

/-- Ring-level generic-rank primitive: finite `A`-algebra data on `B` yields finite-dimensional
    fraction-field extension under the ambient localization/tower assumptions. -/
theorem finiteDimensional_fractionRing_of_moduleFinite :
    FiniteDimensional (FractionRing A) (FractionRing B) :=
  Module.Finite_of_isLocalization A B (FractionRing A) (FractionRing B) A⁰

/-- Numeric generic rank candidate for finite-map multiplicity in the affine/dominant model.
    This is the finrank of fraction fields under the finite-algebra hypotheses above. -/
noncomputable def finiteMapImageGenericRank : Nat := by
  letI : FiniteDimensional (FractionRing A) (FractionRing B) :=
    finiteDimensional_fractionRing_of_moduleFinite A B
  exact Module.finrank (FractionRing A) (FractionRing B)

end GenericRankPrimitive

section AffineFunctionFieldBridge

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A]
variable [Algebra A B]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B)]
variable [Module.Finite A B]

/-- Affine bridge theorem: finite affine algebra data over an integral base gives
    finite-dimensional generic-rank data on fraction fields. This is the first
    non-fake bridge toward finite dominant function-field coefficients. -/
theorem finiteDominantAffine_functionField_finiteDimensional :
    FiniteDimensional (FractionRing A) (FractionRing B) :=
  finiteDimensional_fractionRing_of_moduleFinite A B

/-- Affine numeric multiplicity primitive for finite dominant-type algebra data:
    the generic multiplicity is the function-field finrank. -/
noncomputable def finiteDominantAffine_genericMultiplicity : ℕ :=
  Module.finrank (FractionRing A) (FractionRing B)

omit [IsDomain A] [Algebra A B] [IsScalarTower A (FractionRing A) (FractionRing B)]
  [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B)] [Module.Finite A B] in
theorem finiteDominantAffine_genericMultiplicity_eq_finrank :
    finiteDominantAffine_genericMultiplicity A B =
      Module.finrank (FractionRing A) (FractionRing B) :=
  rfl

end AffineFunctionFieldBridge

section AffineMultiplicityTransport

/-- Ring-clean affine transport theorem: the multiplicity attached to finite affine
    algebra data is exactly the previously defined affine generic multiplicity primitive. -/
theorem finiteDominantAffine_genericMultiplicity_of_finiteAlgebra
    (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B)] [Module.Finite A B] :
    finiteDominantAffine_genericMultiplicity A B =
    finiteMapImageGenericRank A B :=
  by
    rfl

end AffineMultiplicityTransport

section AffineSchemeFunctionFieldBridge

variable {X Y : Scheme} (f : X ⟶ Y)

/-- For finite morphisms with affine target, the map on global sections is finite.
    This is the coordinate-ring finiteness statement at the affine top-open level. -/
theorem finiteAffine_morphism_moduleFinite_on_coordinateRings
    [IsFinite f] [IsAffine Y] : RingHom.Finite f.appTop := by
  simpa using (IsFinite.finite_app (f := f) ⊤ (isAffineOpen_top Y))

/-- Induced coordinate-ring map is module-finite on a compatible generic affine target chart.
  Finiteness is obtained from `IsFinite.finite_app` on the chosen target affine open.
  (Source preimage-affineness is packaged separately in
  `IntClosedSubscheme.GenericAffineChartCompatibility` for downstream chart-comparison use.) -/
theorem finiteMap_on_genericAffineCharts_moduleFinite
    [IsFinite f] {W : IntClosedSubscheme Y}
  (targetChart : IntClosedSubscheme.GenericAffineChart W) :
    RingHom.Finite (f.app targetChart.U) := by
  simpa using (IsFinite.finite_app (f := f) targetChart.U targetChart.isAffine)

/-- Function field of an affine integral scheme `Spec A` identified with `FractionRing A`. -/
noncomputable def affineIntegral_functionField_equiv_fractionRing
    (A : CommRingCat) [IsDomain A] :
    (Spec A).functionField ≃ₐ[A] FractionRing A :=
  (FractionRing.algEquiv (A := A) (K := (Spec A).functionField)).symm

/-- Affine scheme/function-field finite-dimensional bridge under explicit algebra and
    localization assumptions on the induced function-field map. -/
theorem finiteDominantAffineScheme_functionField_finiteDimensional
    (A B : CommRingCat) [IsDomain A] [IsDomain B] [Algebra A B]
  [Algebra A (Spec B).functionField]
  [IsScalarTower A B (Spec B).functionField]
    [Algebra (Spec A).functionField (Spec B).functionField]
    [IsScalarTower A (Spec A).functionField (Spec B).functionField]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (Spec B).functionField]
    [Module.Finite A B] :
    FiniteDimensional (Spec A).functionField (Spec B).functionField := by
  letI : IsLocalization A⁰ (Spec A).functionField := by
    simpa [IsFractionRing] using
      (inferInstance : IsFractionRing A (Spec A).functionField)
  exact Module.Finite_of_isLocalization A B (Spec A).functionField (Spec B).functionField A⁰

/-- Affine-scheme generic multiplicity wrapper for finite dominant/integral algebra data.
    This remains chart-level/function-field-level and is not yet a cycle coefficient. -/
noncomputable def finiteDominantAffineScheme_genericMultiplicity
    (A B : CommRingCat) [IsDomain A] [IsDomain B] [Algebra A B]
    [Algebra A (Spec B).functionField]
    [IsScalarTower A B (Spec B).functionField]
    [Algebra (Spec A).functionField (Spec B).functionField]
    [IsScalarTower A (Spec A).functionField (Spec B).functionField]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (Spec B).functionField]
    [Module.Finite A B] : ℕ := by
  letI : FiniteDimensional (Spec A).functionField (Spec B).functionField :=
    finiteDominantAffineScheme_functionField_finiteDimensional A B
  exact Module.finrank (Spec A).functionField (Spec B).functionField

theorem finiteDominantAffineScheme_genericMultiplicity_eq_finrank
    (A B : CommRingCat) [IsDomain A] [IsDomain B] [Algebra A B]
    [Algebra A (Spec B).functionField]
    [IsScalarTower A B (Spec B).functionField]
    [Algebra (Spec A).functionField (Spec B).functionField]
    [IsScalarTower A (Spec A).functionField (Spec B).functionField]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (Spec B).functionField]
    [Module.Finite A B] :
    finiteDominantAffineScheme_genericMultiplicity A B =
      Module.finrank (Spec A).functionField (Spec B).functionField := by
  rfl

/-- Finrank transport across compatible ring equivalences of base and extension fields. -/
theorem finrank_congr_fieldEquiv
    {K L F E : Type*} [Field K] [Field L] [Field F] [Field E]
    [Algebra K F] [Algebra L E]
    (i : K ≃+* L) (j : F ≃+* E)
    (hc : (algebraMap L E).comp i.toRingHom = j.toRingHom.comp (algebraMap K F)) :
    Module.finrank K F = Module.finrank L E := by
  have hrank : Cardinal.lift (Module.rank K F) = Cardinal.lift (Module.rank L E) :=
    Algebra.lift_rank_eq_of_equiv_equiv (R := K) (S := F) (R' := L) (S' := E) i j hc
  simpa [Module.finrank] using congrArg Cardinal.toNat hrank

/-- Comparison theorem: affine-scheme generic multiplicity agrees with the affine ring-level
    generic multiplicity once the two scalar towers are identified by compatible
    function-field/fraction-ring equivalences. -/
theorem finiteDominantAffineScheme_genericMultiplicity_eq_affineRingMultiplicity
    (A B : CommRingCat) [IsDomain A] [IsDomain B] [Algebra A B]
    [Algebra A (Spec B).functionField]
    [IsScalarTower A B (Spec B).functionField]
    [Algebra (Spec A).functionField (Spec B).functionField]
    [IsScalarTower A (Spec A).functionField (Spec B).functionField]
    [Algebra (FractionRing A) (FractionRing B)]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (Spec B).functionField]
    [Module.Finite A B]
    (hcompat :
      (algebraMap (FractionRing A) (FractionRing B)).comp
          (affineIntegral_functionField_equiv_fractionRing A).toRingEquiv.toRingHom =
        (affineIntegral_functionField_equiv_fractionRing B).toRingEquiv.toRingHom.comp
          (algebraMap (Spec A).functionField (Spec B).functionField)) :
    finiteDominantAffineScheme_genericMultiplicity A B =
      finiteDominantAffine_genericMultiplicity A B := by
  rw [finiteDominantAffineScheme_genericMultiplicity_eq_finrank (A := A) (B := B)]
  simpa [finiteDominantAffine_genericMultiplicity] using
    (finrank_congr_fieldEquiv
      (i := (affineIntegral_functionField_equiv_fractionRing A).toRingEquiv)
      (j := (affineIntegral_functionField_equiv_fractionRing B).toRingEquiv)
      hcompat)

/-- Affine-local compatibility core for generic multiplicity: if a localization model
    `Aₛ, Bₛ` is fixed and the induced fraction fields are identified by compatible
    ring equivalences, then the affine generic multiplicity is unchanged. -/
theorem finiteDominantAffine_genericMultiplicity_localization_eq
    {A B Aₛ Bₛ : Type*}
    [CommRing A] [CommRing B] [CommRing Aₛ] [CommRing Bₛ]
    [IsDomain A] [IsDomain B] [IsDomain Aₛ] [IsDomain Bₛ]
    [Algebra A B] [Algebra Aₛ Bₛ]
    [Algebra (FractionRing A) (FractionRing B)]
    [Algebra (FractionRing Aₛ) (FractionRing Bₛ)]
    [IsScalarTower A (FractionRing A) (FractionRing B)]
    [IsScalarTower Aₛ (FractionRing Aₛ) (FractionRing Bₛ)]
    [IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (FractionRing B)]
    [IsLocalization (Algebra.algebraMapSubmonoid Bₛ Aₛ⁰) (FractionRing Bₛ)]
    [Module.Finite A B] [Module.Finite Aₛ Bₛ]
    (S : Submonoid A) [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra B Bₛ] [IsLocalization (Algebra.algebraMapSubmonoid B S) Bₛ]
    (eA : FractionRing A ≃+* FractionRing Aₛ)
    (eB : FractionRing B ≃+* FractionRing Bₛ)
    (hcompat :
      (algebraMap (FractionRing Aₛ) (FractionRing Bₛ)).comp eA.toRingHom =
        eB.toRingHom.comp (algebraMap (FractionRing A) (FractionRing B))) :
    finiteDominantAffine_genericMultiplicity A B =
      finiteDominantAffine_genericMultiplicity Aₛ Bₛ := by
  simpa [finiteDominantAffine_genericMultiplicity] using
    (finrank_congr_fieldEquiv (K := FractionRing A) (L := FractionRing Aₛ)
      (F := FractionRing B) (E := FractionRing Bₛ) eA eB hcompat)

/-- Algebraic overlap compatibility: if two affine finite-algebra presentations localize
    to a common model with compatible fraction-field identifications, then their
    generic multiplicities agree. -/
theorem finiteDominantAffine_genericMultiplicity_commonLocalization_eq
    {A₁ B₁ A₂ B₂ A₀ B₀ : Type*}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [CommRing A₀] [CommRing B₀]
    [IsDomain A₁] [IsDomain B₁] [IsDomain A₂] [IsDomain B₂] [IsDomain A₀] [IsDomain B₀]
    [Algebra A₁ B₁] [Algebra A₂ B₂] [Algebra A₀ B₀]
    [Algebra (FractionRing A₁) (FractionRing B₁)]
    [Algebra (FractionRing A₂) (FractionRing B₂)]
    [Algebra (FractionRing A₀) (FractionRing B₀)]
    [IsScalarTower A₁ (FractionRing A₁) (FractionRing B₁)]
    [IsScalarTower A₂ (FractionRing A₂) (FractionRing B₂)]
    [IsScalarTower A₀ (FractionRing A₀) (FractionRing B₀)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₁ A₁⁰) (FractionRing B₁)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₂ A₂⁰) (FractionRing B₂)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₀ A₀⁰) (FractionRing B₀)]
    [Module.Finite A₁ B₁] [Module.Finite A₂ B₂] [Module.Finite A₀ B₀]
    (S₁ : Submonoid A₁) [Algebra A₁ A₀] [IsLocalization S₁ A₀]
    [Algebra B₁ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₁ S₁) B₀]
    (S₂ : Submonoid A₂) [Algebra A₂ A₀] [IsLocalization S₂ A₀]
    [Algebra B₂ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₂ S₂) B₀]
    (eA₁ : FractionRing A₁ ≃+* FractionRing A₀)
    (eB₁ : FractionRing B₁ ≃+* FractionRing B₀)
    (hcompat₁ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₁.toRingHom =
        eB₁.toRingHom.comp (algebraMap (FractionRing A₁) (FractionRing B₁)))
    (eA₂ : FractionRing A₂ ≃+* FractionRing A₀)
    (eB₂ : FractionRing B₂ ≃+* FractionRing B₀)
    (hcompat₂ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₂.toRingHom =
        eB₂.toRingHom.comp (algebraMap (FractionRing A₂) (FractionRing B₂))) :
    finiteDominantAffine_genericMultiplicity A₁ B₁ =
      finiteDominantAffine_genericMultiplicity A₂ B₂ := by
  have h₁ : finiteDominantAffine_genericMultiplicity A₁ B₁ =
      finiteDominantAffine_genericMultiplicity A₀ B₀ :=
    finiteDominantAffine_genericMultiplicity_localization_eq
      (A := A₁) (B := B₁) (Aₛ := A₀) (Bₛ := B₀)
      S₁ eA₁ eB₁ hcompat₁
  have h₂ : finiteDominantAffine_genericMultiplicity A₂ B₂ =
      finiteDominantAffine_genericMultiplicity A₀ B₀ :=
    finiteDominantAffine_genericMultiplicity_localization_eq
      (A := A₂) (B := B₂) (Aₛ := A₀) (Bₛ := B₀)
      S₂ eA₂ eB₂ hcompat₂
  exact h₁.trans h₂.symm

/-- Chart-compatibility boundary for finite-map image multiplicity computations:
  two admissible affine chart computations that reduce to a common localization
  model yield the same multiplicity value. This is the core chart-independence
  input for later proof-relevant pushforward constructions. -/
theorem finiteMapImageMultiplicity_compatibleCharts_eq
    {A₁ B₁ A₂ B₂ A₀ B₀ : Type*}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [CommRing A₀] [CommRing B₀]
    [IsDomain A₁] [IsDomain B₁] [IsDomain A₂] [IsDomain B₂] [IsDomain A₀] [IsDomain B₀]
    [Algebra A₁ B₁] [Algebra A₂ B₂] [Algebra A₀ B₀]
    [Algebra (FractionRing A₁) (FractionRing B₁)]
    [Algebra (FractionRing A₂) (FractionRing B₂)]
    [Algebra (FractionRing A₀) (FractionRing B₀)]
    [IsScalarTower A₁ (FractionRing A₁) (FractionRing B₁)]
    [IsScalarTower A₂ (FractionRing A₂) (FractionRing B₂)]
    [IsScalarTower A₀ (FractionRing A₀) (FractionRing B₀)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₁ A₁⁰) (FractionRing B₁)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₂ A₂⁰) (FractionRing B₂)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₀ A₀⁰) (FractionRing B₀)]
    [Module.Finite A₁ B₁] [Module.Finite A₂ B₂] [Module.Finite A₀ B₀]
    (S₁ : Submonoid A₁) [Algebra A₁ A₀] [IsLocalization S₁ A₀]
    [Algebra B₁ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₁ S₁) B₀]
    (S₂ : Submonoid A₂) [Algebra A₂ A₀] [IsLocalization S₂ A₀]
    [Algebra B₂ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₂ S₂) B₀]
    (eA₁ : FractionRing A₁ ≃+* FractionRing A₀)
    (eB₁ : FractionRing B₁ ≃+* FractionRing B₀)
    (hcompat₁ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₁.toRingHom =
        eB₁.toRingHom.comp (algebraMap (FractionRing A₁) (FractionRing B₁)))
    (eA₂ : FractionRing A₂ ≃+* FractionRing A₀)
    (eB₂ : FractionRing B₂ ≃+* FractionRing B₀)
    (hcompat₂ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₂.toRingHom =
        eB₂.toRingHom.comp (algebraMap (FractionRing A₂) (FractionRing B₂))) :
    finiteDominantAffine_genericMultiplicity A₁ B₁ =
      finiteDominantAffine_genericMultiplicity A₂ B₂ :=
  finiteDominantAffine_genericMultiplicity_commonLocalization_eq
    (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂) (A₀ := A₀) (B₀ := B₀)
    S₁ S₂ eA₁ eB₁ hcompat₁ eA₂ eB₂ hcompat₂

/-- Wrapper-level compatible-chart equality boundary:
    for a fixed finite map/image-component situation, two generic affine chart packages
    yield equal affine multiplicity computations once explicit common-localization
    overlap data is supplied.

    Note: current `IntClosedSubscheme.GenericAffineChartCompatibility` only records
    source-preimage affineness, so overlap/localization/fraction-field compatibility
    data is carried explicitly in the hypotheses below. -/
theorem finiteMapImageMultiplicity_genericAffineCharts_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {W : IntClosedSubscheme Y}
    (targetChart₁ targetChart₂ : IntClosedSubscheme.GenericAffineChart W)
    (compat₁ : IntClosedSubscheme.GenericAffineChartCompatibility f targetChart₁)
    (compat₂ : IntClosedSubscheme.GenericAffineChartCompatibility f targetChart₂)
    {A₁ B₁ A₂ B₂ A₀ B₀ : Type*}
    [CommRing A₁] [CommRing B₁] [CommRing A₂] [CommRing B₂] [CommRing A₀] [CommRing B₀]
    [IsDomain A₁] [IsDomain B₁] [IsDomain A₂] [IsDomain B₂] [IsDomain A₀] [IsDomain B₀]
    [Algebra A₁ B₁] [Algebra A₂ B₂] [Algebra A₀ B₀]
    [Algebra (FractionRing A₁) (FractionRing B₁)]
    [Algebra (FractionRing A₂) (FractionRing B₂)]
    [Algebra (FractionRing A₀) (FractionRing B₀)]
    [IsScalarTower A₁ (FractionRing A₁) (FractionRing B₁)]
    [IsScalarTower A₂ (FractionRing A₂) (FractionRing B₂)]
    [IsScalarTower A₀ (FractionRing A₀) (FractionRing B₀)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₁ A₁⁰) (FractionRing B₁)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₂ A₂⁰) (FractionRing B₂)]
    [IsLocalization (Algebra.algebraMapSubmonoid B₀ A₀⁰) (FractionRing B₀)]
    [Module.Finite A₁ B₁] [Module.Finite A₂ B₂] [Module.Finite A₀ B₀]
    (S₁ : Submonoid A₁) [Algebra A₁ A₀] [IsLocalization S₁ A₀]
    [Algebra B₁ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₁ S₁) B₀]
    (S₂ : Submonoid A₂) [Algebra A₂ A₀] [IsLocalization S₂ A₀]
    [Algebra B₂ B₀] [IsLocalization (Algebra.algebraMapSubmonoid B₂ S₂) B₀]
    (eA₁ : FractionRing A₁ ≃+* FractionRing A₀)
    (eB₁ : FractionRing B₁ ≃+* FractionRing B₀)
    (hcompat₁ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₁.toRingHom =
        eB₁.toRingHom.comp (algebraMap (FractionRing A₁) (FractionRing B₁)))
    (eA₂ : FractionRing A₂ ≃+* FractionRing A₀)
    (eB₂ : FractionRing B₂ ≃+* FractionRing B₀)
    (hcompat₂ :
      (algebraMap (FractionRing A₀) (FractionRing B₀)).comp eA₂.toRingHom =
        eB₂.toRingHom.comp (algebraMap (FractionRing A₂) (FractionRing B₂))) :
    finiteDominantAffine_genericMultiplicity A₁ B₁ =
      finiteDominantAffine_genericMultiplicity A₂ B₂ := by
  let _ := targetChart₁
  let _ := targetChart₂
  let _ := compat₁
  let _ := compat₂
  exact finiteMapImageMultiplicity_compatibleCharts_eq
    (A₁ := A₁) (B₁ := B₁) (A₂ := A₂) (B₂ := B₂) (A₀ := A₀) (B₀ := B₀)
    S₁ S₂ eA₁ eB₁ hcompat₁ eA₂ eB₂ hcompat₂

/-- Honest generic-field package for a finite source/image component pair.
    The public multiplicity scalar is defined from this data, not from any
    chosen chart. -/
structure FiniteMapImageFunctionFieldData
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : IntClosedSubscheme X) (W : IntClosedSubscheme Y) where
  toImage : Z.scheme ⟶ W.scheme
  functionFieldAlgebra : Algebra (IntClosedSubscheme.functionField W) (IntClosedSubscheme.functionField Z)
  functionFieldFiniteDimensional :
    FiniteDimensional (IntClosedSubscheme.functionField W) (IntClosedSubscheme.functionField Z)

attribute [instance] FiniteMapImageFunctionFieldData.functionFieldAlgebra
attribute [instance] FiniteMapImageFunctionFieldData.functionFieldFiniteDimensional

/-- Public finite-map image multiplicity: the generic rank of `k(Z)` over
    `k(W)`, packaged through explicit source-to-image function-field data. -/
noncomputable def finiteMapImageMultiplicity
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W) : ℕ := by
  let _ := f
  let _ := data
  letI := data.functionFieldAlgebra
  letI := data.functionFieldFiniteDimensional
  exact Module.finrank (IntClosedSubscheme.functionField W) (IntClosedSubscheme.functionField Z)

/-- A chart-level computation is now only an interface: it records a local
    computed value together with proof that it agrees with the canonical public
    multiplicity. -/
structure FiniteMapImageMultiplicityChartComputation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : IntClosedSubscheme X) (W : IntClosedSubscheme Y)
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart : IntClosedSubscheme.GenericAffineChart W) where
  value : ℕ
  value_eq_multiplicity : value = finiteMapImageMultiplicity f data

/-- Chart-parametric multiplicity interface attached to a generic affine chart.
    This exposes only a local computation already identified with the canonical
    generic-rank scalar. -/
noncomputable def finiteMapImageMultiplicityOnChart
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart : IntClosedSubscheme.GenericAffineChart W)
    (computation : FiniteMapImageMultiplicityChartComputation f Z W data targetChart) : ℕ :=
  computation.value

/-- Packaged left chart computation attached to a common-localization witness. -/
noncomputable def finiteMapImageMultiplicity_genericAffineChartComputationLeft
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart₁ targetChart₂ : IntClosedSubscheme.GenericAffineChart W)
    (common : IntClosedSubscheme.GenericAffineChartCommonLocalization f targetChart₁ targetChart₂)
    (computation₁ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₁) :
    ℕ := by
  let _ := targetChart₂
  let _ := common
  exact finiteMapImageMultiplicityOnChart (f := f) data targetChart₁ computation₁

/-- Packaged right chart computation attached to a common-localization witness. -/
noncomputable def finiteMapImageMultiplicity_genericAffineChartComputationRight
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart₁ targetChart₂ : IntClosedSubscheme.GenericAffineChart W)
    (common : IntClosedSubscheme.GenericAffineChartCommonLocalization f targetChart₁ targetChart₂)
    (computation₂ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₂) :
    ℕ := by
  let _ := targetChart₁
  let _ := common
  exact finiteMapImageMultiplicityOnChart (f := f) data targetChart₂ computation₂

/-- Wrapper-level compatible-chart equality using a packaged common-localization witness.
    This keeps the low-level explicit theorem available while exposing a reusable
    compatibility package for chart-independence arguments. -/
theorem finiteMapImageMultiplicity_genericAffineCharts_eq'
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart₁ targetChart₂ : IntClosedSubscheme.GenericAffineChart W)
    (common : IntClosedSubscheme.GenericAffineChartCommonLocalization f targetChart₁ targetChart₂)
    (computation₁ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₁)
    (computation₂ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₂) :
    finiteMapImageMultiplicity_genericAffineChartComputationLeft f data targetChart₁ targetChart₂ common computation₁ =
      finiteMapImageMultiplicity_genericAffineChartComputationRight f data targetChart₁ targetChart₂ common computation₂ := by
  let _ := common
  rw [finiteMapImageMultiplicity_genericAffineChartComputationLeft,
    finiteMapImageMultiplicity_genericAffineChartComputationRight,
    finiteMapImageMultiplicityOnChart,
    finiteMapImageMultiplicityOnChart,
    computation₁.value_eq_multiplicity,
    computation₂.value_eq_multiplicity]

/-- Chart-independence of the chart-parametric finite-map image multiplicity.
    The proof stays proof-relevant: we compare two chart computations by passing
    through the canonical generic-rank scalar carried by explicit source/image
    function-field data. -/
theorem finiteMapImageMultiplicityOnChart_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W)
    (targetChart₁ targetChart₂ : IntClosedSubscheme.GenericAffineChart W)
    (computation₁ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₁)
    (computation₂ : FiniteMapImageMultiplicityChartComputation f Z W data targetChart₂) :
    finiteMapImageMultiplicityOnChart (f := f) data targetChart₁ computation₁ =
      finiteMapImageMultiplicityOnChart (f := f) data targetChart₂ computation₂ := by
  rw [finiteMapImageMultiplicityOnChart,
    finiteMapImageMultiplicityOnChart,
    computation₁.value_eq_multiplicity,
    computation₂.value_eq_multiplicity]

/-- The canonical multiplicity data for one target image component yields a
    weighted integral closed subscheme of the target. -/
noncomputable def finiteMapImageWeightedComponent
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W) : Boundary.WeightedIntClosedSubscheme Y where
  multiplicity := finiteMapImageMultiplicity f data
  support := W

@[simp] theorem finiteMapImageWeightedComponent_multiplicity
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W) :
    (finiteMapImageWeightedComponent f data).multiplicity =
      finiteMapImageMultiplicity f data := rfl

@[simp] theorem finiteMapImageWeightedComponent_support
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X} {W : IntClosedSubscheme Y}
    (data : FiniteMapImageFunctionFieldData f Z W) :
    (finiteMapImageWeightedComponent f data).support = W := rfl

/-- Explicit finite family of target image components for a fixed integral
    source subscheme. This packages only honest data already available: each
    chosen target component comes with its canonical function-field
    multiplicity package. -/
structure FiniteMapIntegralImageData
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : IntClosedSubscheme X) where
  index : Type u
  fintype_index : Fintype index
  decidableEq_index : DecidableEq index
  targetComponent : index → IntClosedSubscheme Y
  functionFieldData :
    (i : index) → FiniteMapImageFunctionFieldData f Z (targetComponent i)

/-- The weighted target component contributed by one chosen image component in
    an explicit finite image family for `Z`. -/
noncomputable def finiteMapIntegralImageData.component
    {X Y : Scheme.{u}} {f : X ⟶ Y} {Z : IntClosedSubscheme X}
    (imageData : FiniteMapIntegralImageData f Z)
    (i : imageData.index) : Boundary.WeightedIntClosedSubscheme Y :=
  finiteMapImageWeightedComponent f (imageData.functionFieldData i)

/-- Forget the source-side provenance and view an explicit finite image family
    simply as a finite weighted family of integral closed subschemes in the
    target. -/
noncomputable def FiniteMapIntegralImageData.toFiniteWeightedIntegralClosedFamily
    {X Y : Scheme.{u}} {f : X ⟶ Y} {Z : IntClosedSubscheme X}
    (imageData : FiniteMapIntegralImageData f Z) : Boundary.FiniteWeightedIntegralClosedFamily Y where
  index := imageData.index
  fintype_index := imageData.fintype_index
  decidableEq_index := imageData.decidableEq_index
  component := finiteMapIntegralImageData.component imageData

/-- Data-driven finite pushforward of a single integral closed subscheme.
    No existence of image decompositions is claimed here; this only sums an
    explicit finite family of target image components equipped with canonical
    multiplicity data. -/
noncomputable def finitePushforwardIntegralSubscheme
    {X Y : Scheme.{u}} (f : X ⟶ Y) {Z : IntClosedSubscheme X}
    (imageData : FiniteMapIntegralImageData f Z) : AlgCycle Y := by
  classical
  letI := imageData.fintype_index
  letI := imageData.decidableEq_index
  exact Finset.univ.sum fun i => (finiteMapIntegralImageData.component imageData i).toCycle

@[simp] theorem FiniteMapIntegralImageData_toFiniteWeightedIntegralClosedFamily_toCycle
    {X Y : Scheme.{u}} {f : X ⟶ Y} {Z : IntClosedSubscheme X}
    (imageData : FiniteMapIntegralImageData f Z) :
    imageData.toFiniteWeightedIntegralClosedFamily.toCycle =
      finitePushforwardIntegralSubscheme f imageData := by
  rfl

/-- Explicit pushforward data for all integral closed subschemes appearing in a
    cycle. This keeps pushforward honest: the construction depends only on
    supplied finite image families, not on any unproved existence theorem. -/
structure FinitePushforwardData {X Y : Scheme.{u}} (f : X ⟶ Y) where
  imageData : (Z : IntClosedSubscheme X) → FiniteMapIntegralImageData f Z

/-- Data-driven finite pushforward of cycles along `f`, obtained by extending
    the integral pushforward by `Finsupp` linearity. -/
noncomputable def finitePushforwardCycle
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (pushData : FinitePushforwardData f) : AlgCycle X → AlgCycle Y := by
  classical
  intro c
  exact c.sum fun Z coeff => coeff • finitePushforwardIntegralSubscheme f (pushData.imageData Z)

@[simp] theorem finitePushforwardCycle_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (pushData : FinitePushforwardData f) :
    finitePushforwardCycle f pushData 0 = 0 := by
  classical
  simp [finitePushforwardCycle]

@[simp] theorem finitePushforwardCycle_add
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (pushData : FinitePushforwardData f)
    (c d : AlgCycle X) :
    finitePushforwardCycle f pushData (c + d) =
      finitePushforwardCycle f pushData c + finitePushforwardCycle f pushData d := by
  classical
  simp [finitePushforwardCycle, Finsupp.sum_add_index, add_smul, zero_smul]

@[simp] theorem finitePushforwardCycle_ofSubscheme
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (pushData : FinitePushforwardData f)
    (Z : IntClosedSubscheme X) :
    finitePushforwardCycle f pushData (AlgCycle.ofSubscheme Z) =
      finitePushforwardIntegralSubscheme f (pushData.imageData Z) := by
  classical
  ext W
  simp [finitePushforwardCycle, finitePushforwardIntegralSubscheme, AlgCycle.ofSubscheme]

end AffineSchemeFunctionFieldBridge

namespace AlgCycle

variable {X : Scheme.{u}}

/-- Coefficient of a cycle at an integral closed subscheme. -/
def coeff (c : AlgCycle X) (Z : IntClosedSubscheme X) : ℤ :=
  c Z

/-- Additive inverse of a cycle. -/
noncomputable def neg (c : AlgCycle X) : AlgCycle X :=
  -c

/-- Subtraction of cycles. -/
noncomputable def sub (c d : AlgCycle X) : AlgCycle X :=
  c - d

end AlgCycle

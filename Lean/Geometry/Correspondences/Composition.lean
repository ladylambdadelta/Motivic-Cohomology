import Geometry.Correspondences.Graph
import Boundary.CompositionGeometry
import Boundary.RepresentedPrimeComposition

/-! # Graph Correspondence Composition

This file proves that the composition of two rational graph correspondences
`Γ(f, D_X)` and `Γ(g, D_Y)` in a `SmCorQ` category is the rational graph
correspondence `Γ(SmOverHom.comp f g, D_X)` of the composite morphism.

## Main axiom

`GraphFunctoriality` — the graph-functoriality axiom for a
`FiniteCorrespondenceCompositionData`.  It states that, for any source component
`C` of `X`, the integral composition of the componentwise graph correspondence
`Γ_C(f)` with the full graph correspondence `Γ(g, D_Y)` equals `Γ_C(SmOverHom.comp f g)`.

## Main theorem

`ordinaryMorphismGraph_comp` — given the `GraphFunctoriality` hypothesis on the
category's composition data, the composition of two rational graph
correspondences is the rational graph correspondence of the composite:
  `[Γ_f] ∘ [Γ_g] = [Γ_{SmOverHom.comp f g}]`.

## AG lemma (proved)

`graph_component_pullback_fst_isIso` — when `D.toAmbient` is an open
immersion (hence a monomorphism) and `C.toAmbient ≫ f.hom` factors through
`D.toAmbient` via `h`, the pullback projection
  `pullback.fst (C.toAmbient ≫ f.hom) D.toAmbient : pullback ⟶ C.carrier.scheme`
is an isomorphism.  This expresses that the fiber product of the component
graph of `f` over `C` with the open inclusion of `D` into `Y` is canonically
isomorphic to `C.carrier.scheme`.

Proof: rewrite using the factorization `h ≫ D.toAmbient = C.toAmbient ≫ f.hom`,
then apply Mathlib's `pullback_snd_iso_of_left_factors_mono`, which says
`IsIso (pullback.fst (h ≫ i) i)` for any monomorphism `i`.

## What remains for full `GraphFunctoriality` instantiation

To replace `GraphFunctoriality` with a proved theorem for a concrete fiber-product
`SmCor`, the remaining steps are:
  (1) Define a concrete `FiniteCorrespondenceCompositionData` whose `compPrime`
      is computed by the fiber-product intersection formula.
  (2) Show that for graph prime supports, `compPrime (Γ_C(f)) (Γ_D(g))` equals
      `Finsupp.single (ordinaryMorphismGraphPrimeGeom C (SmOverHom.comp f g)) 1`
      using `graph_component_pullback_fst_isIso` when the factorization exists,
      and `0` otherwise (using integrality of `C.carrier.scheme` to ensure the
      image lands in a unique component `D`).
  (3) Combine with `FiniteCorrespondenceCompositionData.comp_single_single` to
      sum over `D_Y.components` and recover the `GraphFunctoriality` condition.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Geometry

/-- A `FiniteCorrespondenceCompositionData` is **graph-functorial** if, for every
source component `C` of a smooth `k`-scheme `X`, every pair of ordinary `Sm/k`
morphisms `f : X → Y` and `g : Y → Z`, and every source decomposition `D_Y` of
`Y`, the integral composition of the componentwise graph correspondence `Γ_C(f)`
with the full graph correspondence `Γ(g, D_Y)` equals the componentwise graph
correspondence `Γ_C(SmOverHom.comp f g)`.

This is the axiom encoding `[Γ_f] ∘ [Γ_g] = [Γ_{SmOverHom.comp f g}]` at the componentwise
level.  For concrete fiber-product `SmCor` instances this follows from the fact
that the composition fiber product of two graph prime supports is isomorphic to
the source component (see module docstring for the exact missing AG lemma). -/
structure GraphFunctoriality
    (data : Boundary.FiniteCorrespondenceCompositionData (k := k)) where
  /-- `Γ_C(f)` composed (integrally) with `Γ(g, D_Y)` equals `Γ_C(SmOverHom.comp f g)`. -/
  graph_comp_component :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (C : Boundary.SourceIrreducibleComponent X)
      (f : Boundary.SmOverHom X Y)
      (g : Boundary.SmOverHom Y Z)
      (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y),
      Boundary.FiniteCorrespondenceCompositionData.comp data
        (ordinaryMorphismGraph_componentCorrespondence C f)
        (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y)
      = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g)

/-- **Graph functoriality**: the composition of two rational graph
correspondences `Γ(f, D_X)` and `Γ(g, D_Y)` in a `SmCorQ` category equals the
rational graph correspondence `Γ(SmOverHom.comp f g, D_X)` of the composite morphism.

Mathematically: `[Γ_f] ∘ [Γ_g] = [Γ_{SmOverHom.comp f g}]`.

The proof reduces via `comp_eq_toRational_comp` and bilinearity of integral
composition to the `GraphFunctoriality.graph_comp_component` axiom applied
componentwise over the source decomposition `D_X`. -/
theorem ordinaryMorphismGraph_comp
    {X Y Z : Geometry.SmSchemeOver k}
    (category : Boundary.SmCorQ (k := k))
    (hGF : GraphFunctoriality category.integral.composition)
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_X : Boundary.FiniteIrreducibleComponentDecomposition X)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    category.comp
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D_X)
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category g D_Y)
    = ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category (Boundary.SmOverHom.comp f g) D_X := by
  -- Unfold rational graph correspondences to `toRational (finiteCorr ...)`.
  simp only [ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition]
  -- Rewrite the rational composition as rationalization of integral composition.
  rw [category.comp_eq_toRational_comp]
  -- It suffices to show equality before applying `toRational`.
  apply congrArg Boundary.FiniteCorrespondence.toRational
  -- Normalize `category.integral.comp` to `FiniteCorrespondenceCompositionData.comp`.
  simp only [Boundary.SmCor.comp]
  -- Unfold integral graph correspondences as Finset sums over D_X.components.
  simp only [ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition]
  -- Auxiliary: integral composition distributes over Finset.sum on the left.
  -- We use map_sum applied to an AddMonoidHom to avoid DecidableEq requirements.
  have h_distrib :
      ∀ (right : Boundary.FiniteCorrespondence Y Z)
        (s : Finset (Boundary.SourceIrreducibleComponent X))
        (φ : Boundary.SourceIrreducibleComponent X → Boundary.FiniteCorrespondence X Y),
        Boundary.FiniteCorrespondenceCompositionData.comp category.integral.composition
            (s.sum φ) right =
          s.sum fun C =>
            Boundary.FiniteCorrespondenceCompositionData.comp category.integral.composition
              (φ C) right := by
    intro right s φ
    let compHom : Boundary.FiniteCorrespondence X Y →+ Boundary.FiniteCorrespondence X Z :=
      { toFun := fun l =>
          Boundary.FiniteCorrespondenceCompositionData.comp category.integral.composition l right
        map_zero' := Boundary.FiniteCorrespondenceCompositionData.comp_zero_left
                       category.integral.composition right
        map_add' := fun a b =>
          Boundary.FiniteCorrespondenceCompositionData.comp_add_left
            category.integral.composition a b right }
    exact map_sum compHom φ s
  -- Apply the distribution lemma to D_X.components.
  rw [h_distrib
        (∑ component in D_Y.components,
          ordinaryMorphismGraph_componentCorrespondence component g)
        D_X.components
        (fun C => ordinaryMorphismGraph_componentCorrespondence C f)]
  -- For each source component C, apply the graph-functoriality axiom.
  apply Finset.sum_congr rfl
  intro C _
  exact hGF.graph_comp_component C f g D_Y

/-- Componentwise graph functoriality in the exact shape required by
`GraphFunctoriality`: composing the graph singleton on a source component with
the full graph decomposition of `g` yields the graph singleton of the composite
`f ≫ g`. -/
theorem ordinaryMorphismGraph_component_comp
    {X Y Z : Geometry.SmSchemeOver k}
    (category : Boundary.SmCorQ (k := k))
    (hGF : GraphFunctoriality category.integral.composition)
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    Boundary.FiniteCorrespondenceCompositionData.comp category.integral.composition
        (ordinaryMorphismGraph_componentCorrespondence C f)
        (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y)
      = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) := by
  exact hGF.graph_comp_component C f g D_Y

/-- Componentwise graph functoriality specialized to the canonical/package-family
integral composition datum attached to `CanonicalCompositionPackageData`. -/
theorem ordinaryMorphismGraph_component_comp_canonical
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData (k := k))
    (hGF : GraphFunctoriality
      (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition).toFiniteCorrespondenceCompositionData)
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    let data :=
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition
    Boundary.FiniteCorrespondenceCompositionData.comp
        data.toFiniteCorrespondenceCompositionData
        (ordinaryMorphismGraph_componentCorrespondence C f)
        (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y)
      = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) := by
  let data :=
    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
      composition
  exact hGF.graph_comp_component C f g D_Y

/-- Integral graph functoriality specialized to the canonical/package-family
composition datum attached to `CanonicalCompositionPackageData`. -/
theorem ordinaryMorphismGraph_comp_canonical
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData (k := k))
    (hGF : GraphFunctoriality
      (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition).toFiniteCorrespondenceCompositionData)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_X : Boundary.FiniteIrreducibleComponentDecomposition X)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    let data :=
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition
    Boundary.FiniteCorrespondenceCompositionData.comp
      data.toFiniteCorrespondenceCompositionData
      (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f D_X)
      (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y)
    = ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (Boundary.SmOverHom.comp f g) D_X := by
  let data :=
    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
      composition
  simp only [ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition]
  have h_distrib :
      ∀ (right : Boundary.FiniteCorrespondence Y Z)
        (s : Finset (Boundary.SourceIrreducibleComponent X))
        (φ : Boundary.SourceIrreducibleComponent X → Boundary.FiniteCorrespondence X Y),
        Boundary.FiniteCorrespondenceCompositionData.comp
            data.toFiniteCorrespondenceCompositionData
            (s.sum φ) right =
          s.sum fun C =>
            Boundary.FiniteCorrespondenceCompositionData.comp
              data.toFiniteCorrespondenceCompositionData
              (φ C) right := by
    intro right s φ
    let compHom : Boundary.FiniteCorrespondence X Y →+ Boundary.FiniteCorrespondence X Z :=
      { toFun := fun left =>
          Boundary.FiniteCorrespondenceCompositionData.comp
            data.toFiniteCorrespondenceCompositionData
            left right
        map_zero' :=
          Boundary.FiniteCorrespondenceCompositionData.comp_zero_left
            data.toFiniteCorrespondenceCompositionData
            right
        map_add' := fun left₁ left₂ =>
          Boundary.FiniteCorrespondenceCompositionData.comp_add_left
            data.toFiniteCorrespondenceCompositionData
            left₁ left₂ right }
    exact map_sum compHom φ s
  rw [h_distrib
        (∑ component in D_Y.components,
          ordinaryMorphismGraph_componentCorrespondence component g)
        D_X.components
        (fun C => ordinaryMorphismGraph_componentCorrespondence C f)]
  apply Finset.sum_congr rfl
  intro C _
  exact ordinaryMorphismGraph_component_comp_canonical composition hGF C f g D_Y

/-- **Graph component fiber product isomorphism (AG lemma)**:
When `D.toAmbient : D.carrier.scheme ⟶ Y.scheme` is an open immersion
(hence a monomorphism) and `C.toAmbient ≫ f.hom` factors through `D.toAmbient`
via `h : C.carrier.scheme ⟶ D.carrier.scheme`, the first pullback projection
  `pullback.fst (C.toAmbient ≫ f.hom) D.toAmbient`
is an isomorphism.

Geometrically: the fiber product of the graph prime of `f` restricted to the
source component `C` with the open inclusion of `D` into `Y` is isomorphic
(via the first projection) to `C.carrier.scheme`.

Proof: rewrite the left leg using `h ≫ D.toAmbient = C.toAmbient ≫ f.hom`
to expose the syntactic form `h ≫ D.toAmbient`, then apply Mathlib's
`pullback_snd_iso_of_left_factors_mono : IsIso (pullback.fst (h ≫ i) i)`
which holds for any monomorphism `i`.  `D.toAmbient` is mono because it is
an open immersion (`AlgebraicGeometry.IsOpenImmersion.mono`). -/
theorem graph_component_pullback_fst_isIso
    {X Y : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    IsIso (pullback.fst (C.toAmbient ≫ f.hom) D.toAmbient) := by
  -- D.toAmbient is an open immersion, hence a monomorphism.
  haveI : IsOpenImmersion D.toAmbient := D.isOpenImmersion
  -- Rewrite to expose the factored form h ≫ D.toAmbient.
  rw [← hh]
  -- Now apply Mathlib: IsIso (pullback.fst (h ≫ i) i) for any Mono i.
  infer_instance

/-- API-upgrade of `graph_component_pullback_fst_isIso` to graph prime supports:
for graph primes `P = Γ_C(f)` and `Q = Γ_D(g)` with factorization data
`h ≫ D.toAmbient = C.toAmbient ≫ f.hom`, the canonical first projection
`compositionFiberFst P Q` is an isomorphism. -/
theorem graphPrime_compositionFiberFst_isIso
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    IsIso (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D g)) := by
  have hQ := ordinaryMorphismGraphPrimeSupport_toAmbientSource D g
  change IsIso (pullback.fst
      (ordinaryMorphismGraphPrimeSupport C f).toTargetScheme
      (ordinaryMorphismGraphPrimeSupport D g).toAmbientSource)
  rw [hQ]
  exact graph_component_pullback_fst_isIso C f D h hh

/-- Support-factorization step for graph-prime composition:
for graph primes `P = Γ_C(f)` and `Q = Γ_D(g)` with factorization data
`h ≫ D.toAmbient = C.toAmbient ≫ f.hom`, package the canonical map
`P.support ×_Y Q.support ⟶ source(C) ×_k Z` through the graph image of
`SmOverHom.comp f g` on `C`. -/
noncomputable def graphPrimeSupportFiberProductImageFactorization
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    Boundary.SupportFiberProductImageFactorization
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D g) where
  image := C.carrier.scheme
  toImage := Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
    (ordinaryMorphismGraphPrimeSupport C f)
    (ordinaryMorphismGraphPrimeSupport D g)
  imageToAmbientProduct :=
    ordinaryMorphismGraphMap
      (ordinaryMorphismOnSourceComponent C (Boundary.SmOverHom.comp f g))
  factorization := by
    let _ := graphPrime_compositionFiberFst_isIso C f D g h hh
    apply Limits.pullback.hom_ext
    · rw [Boundary.PrimeFiniteCorrespondenceSupport.compositionToAmbientProduct_fst]
      simp [ordinaryMorphismGraphPrimeSupport_toSourceComponent, Category.assoc]
      exact (Category.comp_id
        (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
          (ordinaryMorphismGraphPrimeSupport C f)
          (ordinaryMorphismGraphPrimeSupport D g))).symm
    · have hQsrc := ordinaryMorphismGraphPrimeSupport_toAmbientSource D g
      have hcond :=
        Boundary.PrimeFiniteCorrespondenceSupport.compositionFiber_condition
          (ordinaryMorphismGraphPrimeSupport C f)
          (ordinaryMorphismGraphPrimeSupport D g)
      rw [hQsrc] at hcond
      have hcond' :
          Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g) ≫
            C.toAmbient ≫ f.hom
            = Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
                (ordinaryMorphismGraphPrimeSupport C f)
                (ordinaryMorphismGraphPrimeSupport D g) ≫
              D.toAmbient := by
        simpa [Boundary.PrimeFiniteCorrespondenceSupport.toTargetScheme,
          ordinaryMorphismGraphPrimeSupport, Category.assoc] using hcond
      rw [Boundary.PrimeFiniteCorrespondenceSupport.compositionToAmbientProduct_snd]
      calc
        Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g) ≫
            ordinaryMorphismGraphMap
              (ordinaryMorphismOnSourceComponent C (Boundary.SmOverHom.comp f g)) ≫
            Boundary.overBaseProduct.snd C.carrier Z
            = (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
                (ordinaryMorphismGraphPrimeSupport C f)
                (ordinaryMorphismGraphPrimeSupport D g) ≫
                C.toAmbient ≫ f.hom) ≫ g.hom := by
                  simp [ordinaryMorphismGraphMap_snd,
                    ordinaryMorphismOnSourceComponent,
                    Boundary.SmOverHom.comp, Category.assoc]
        _ = (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
                (ordinaryMorphismGraphPrimeSupport C f)
                (ordinaryMorphismGraphPrimeSupport D g) ≫
                D.toAmbient) ≫ g.hom := by
                  rw [hcond']
        _ = Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g) ≫
              (ordinaryMorphismGraphPrimeSupport D g).toTargetScheme := by
                simp [Boundary.PrimeFiniteCorrespondenceSupport.toTargetScheme,
                  ordinaryMorphismGraphPrimeSupport, Category.assoc]
  imageClosedImmersion :=
    ordinaryMorphismGraphMap_isClosedImmersion
      (ordinaryMorphismOnSourceComponent C (Boundary.SmOverHom.comp f g))

/-- The unique integral image component for graph-prime composition, obtained
from the graph support of the composite `SmOverHom.comp f g`. -/
noncomputable def graphPrimeSupportFiberProductImageComponent
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    Boundary.SupportFiberProductImageComponent
      (graphPrimeSupportFiberProductImageFactorization C f D g h hh) where
  lengthCoeff := 1
  support := C.carrier.scheme
  isIntegral := C.isIntegral
  toImage := 𝟙 C.carrier.scheme
  toImageClosedImmersion := by infer_instance
  toCompositionFiberProduct := by
    haveI := graphPrime_compositionFiberFst_isIso C f D g h hh
    exact inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D g))
  toImage_factorization := by
    haveI := graphPrime_compositionFiberFst_isIso C f D g h hh
    simp [graphPrimeSupportFiberProductImageFactorization]
  finiteOverSourceComponent :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).finiteOverSourceComponent
  finite_toSourceComponent :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).finite_toSourceComponent
  surjective_toSourceComponent :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).surjective_toSourceComponent
  toTarget :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).toTarget
  inclusion :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).inclusion
  inclusion_factorization := by
    simp [graphPrimeSupportFiberProductImageFactorization,
      ordinaryMorphismGraphPrimeSupport, ordinaryMorphismOnSourceComponent]
  inclusion_fst :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).inclusion_fst
  inclusion_snd :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).inclusion_snd
  isClosedImmersion :=
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).isClosedImmersion
  toCompositionFiberProduct_fst := by
    haveI := graphPrime_compositionFiberFst_isIso C f D g h hh
    change
      inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
          (ordinaryMorphismGraphPrimeSupport C f)
          (ordinaryMorphismGraphPrimeSupport D g)) ≫
        Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
          (ordinaryMorphismGraphPrimeSupport C f)
          (ordinaryMorphismGraphPrimeSupport D g) ≫
        (ordinaryMorphismGraphPrimeSupport C f).toSourceComponent
      = (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).finiteOverSourceComponent
    simp [Boundary.PrimeFiniteCorrespondenceSupport.toSourceComponent,
      ordinaryMorphismGraphPrimeSupport_toSourceImage,
      ordinaryMorphismGraphPrimeSupport_toSourceComponent,
      ordinaryMorphismOnSourceComponent,
      ordinaryMorphismGraphMap_sourceOverBaseProduct_fst,
      Boundary.SmOverHom.comp, Category.assoc]
  toCompositionFiberProduct_snd := by
    haveI := graphPrime_compositionFiberFst_isIso C f D g h hh
    have hQsrc := ordinaryMorphismGraphPrimeSupport_toAmbientSource D g
    have hcond :=
      Boundary.PrimeFiniteCorrespondenceSupport.compositionFiber_condition
        (ordinaryMorphismGraphPrimeSupport C f)
        (ordinaryMorphismGraphPrimeSupport D g)
    rw [hQsrc] at hcond
    have hcond' :
        Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g) ≫
          C.toAmbient ≫ f.hom
          = Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g) ≫
            D.toAmbient := by
      simpa [Boundary.PrimeFiniteCorrespondenceSupport.toTargetScheme,
        ordinaryMorphismGraphPrimeSupport, Category.assoc] using hcond
    calc
      inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g)) ≫
          Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g) ≫
          (ordinaryMorphismGraphPrimeSupport D g).toTargetScheme
          = inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g)) ≫
            Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberSnd
              (ordinaryMorphismGraphPrimeSupport C f)
              (ordinaryMorphismGraphPrimeSupport D g) ≫
            D.toAmbient ≫ g.hom := by
                simp [Boundary.PrimeFiniteCorrespondenceSupport.toTargetScheme,
                  ordinaryMorphismGraphPrimeSupport, ordinaryMorphismOnSourceComponent,
                  Category.assoc]
      _ = inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g)) ≫
          (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g) ≫
          C.toAmbient ≫ f.hom) ≫ g.hom := by
            simpa [Category.assoc] using congrArg
              (fun m => inv (Boundary.PrimeFiniteCorrespondenceSupport.compositionFiberFst
                (ordinaryMorphismGraphPrimeSupport C f)
                (ordinaryMorphismGraphPrimeSupport D g)) ≫ m ≫ g.hom)
              hcond'.symm
      _ = C.toAmbient ≫ f.hom ≫ g.hom := by
            simp [Category.assoc]
      _ = (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)).toTarget := by
            simp [Boundary.SmOverHom.comp, ordinaryMorphismGraphPrimeSupport,
              ordinaryMorphismOnSourceComponent, Category.assoc]

/-- The one-component image decomposition for graph-prime composition. -/
noncomputable def graphPrimeSupportFiberProductImageDecomposition
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    Boundary.SupportFiberProductImageDecomposition
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D g) where
  imageData := graphPrimeSupportFiberProductImageFactorization C f D g h hh
  index := PUnit
  fintype_index := inferInstance
  decidableEq_index := inferInstance
  component := fun _ => graphPrimeSupportFiberProductImageComponent C f D g h hh

/-- The singleton graph-prime image decomposition presents exactly the singleton
prime support of the composite graph on `C`. -/
theorem graphPrimeSupportFiberProductImageDecomposition_toPresentation_toGeom
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z)
    (h : C.carrier.scheme ⟶ D.carrier.scheme)
    (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom) :
    Boundary.FiniteCorrespondencePresentation.toGeom
        ((Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (graphPrimeSupportFiberProductImageDecomposition C f D g h hh)).toPresentation) =
      Finsupp.single
        (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented
          (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g))) 1 := by
  have hpres :
      (Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (graphPrimeSupportFiberProductImageDecomposition C f D g h hh)).toPresentation =
        Boundary.FiniteCorrespondencePresentation.ofPrimeSupport
          (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g)) := by
    cases C
    simp [graphPrimeSupportFiberProductImageDecomposition,
      graphPrimeSupportFiberProductImageComponent,
      Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition,
      Boundary.SupportFiberProductImageDecomposition.toRepresentedPrimeCompositionDatum,
      Boundary.RepresentedPrimeCompositionDatum.toPresentation,
      Boundary.FiniteCorrespondencePresentation.ofPrimeSupport,
      Boundary.FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
      Boundary.SupportFiberProductImageComponent.toRepresentedPrimeCompositionPiece,
      Boundary.RepresentedPrimeCompositionPiece.toWeightedPrimeFiniteCorrespondenceSupport,
      Boundary.RepresentedPrimeCompositionPiece.toRepresentedPrimeSupport,
      ordinaryMorphismGraphPrimeSupport, ordinaryMorphismOnSourceComponent,
      ordinaryMorphismGraphMap_fst, ordinaryMorphismGraphMap_snd,
      Boundary.SmOverHom.comp, Category.assoc]
  rw [hpres]
  exact Boundary.FiniteCorrespondencePresentation.toGeom_single
    (ordinaryMorphismGraphPrimeSupport C (Boundary.SmOverHom.comp f g))

/-- Package-family level compatibility obligation for graph-prime pairs.
It records the exact finite correspondence computed by the chosen canonical
package family on each graph singleton pair, before any summation over a target
decomposition is performed. This is an internal obligation on abstract package
data, not the canonical public graph theorem. -/
def CanonicalGraphPackageCompatibilityObligation
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
        (k := k)) : Prop := by
  classical
  exact
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (C : Boundary.SourceIrreducibleComponent X)
      (f : Boundary.SmOverHom X Y)
      (D : Boundary.SourceIrreducibleComponent Y)
      (g : Boundary.SmOverHom Y Z),
        Boundary.FiniteCorrespondencePresentation.toGeom
            (Boundary.SupportFiberProductImageDecomposition.toPresentation
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                composition.packages
                (ordinaryMorphismGraphPrimeSupport C f)
                (ordinaryMorphismGraphPrimeSupport D g))) =
          if hfac : Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }
          then ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g)
          else 0

private abbrev ConcreteLiftedPackages :=
  {X Y Z : Geometry.SmSchemeOver k} →
  Boundary.PrimeFiniteCorrespondenceGeom X Y →
  Boundary.PrimeFiniteCorrespondenceGeom Y Z →
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage (k := k)

private abbrev ConcreteLiftedIdentityPackages :=
  {X Y : Geometry.SmSchemeOver k} →
  Boundary.PrimeFiniteCorrespondenceGeom X Y →
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage (k := k)

private def concreteLiftedCanonicalComposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceComponent.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceComponent.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                  (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
      (k := k) :=
  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.ofConcreteLiftedDecompositionFamily
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright

private noncomputable def concreteLiftedGraphPairDecomposition
    (packages : ConcreteLiftedPackages (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y)
    (D : Boundary.SourceIrreducibleComponent Y)
    (g : Boundary.SmOverHom Y Z) :
    Boundary.SupportFiberProductImageDecomposition
      (ordinaryMorphismGraphPrimeSupport C f)
      (ordinaryMorphismGraphPrimeSupport D g) :=
  ((packages
      (ordinaryMorphismGraphPrimeGeom C f)
      (ordinaryMorphismGraphPrimeGeom D g)).liftedDecomposition
        (ordinaryMorphismGraphPrimeSupport C f)
        (ordinaryMorphismGraphPrimeSupport D g)).toSupportFiberProductImageDecomposition

/-- The canonical package family built from a concrete lifted-decomposition
family satisfies the graph-pair compatibility obligation as soon as the lifted
packages compute the graph-pair decomposition on the nose and become empty when
no middle-component factorization exists. -/
theorem canonicalGraphPackageCompatibility_ofConcreteLiftedDecompositionFamily
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceComponent.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceComponent.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                  (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    (graphPair_yes :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z)
        (h : C.carrier.scheme ⟶ D.carrier.scheme)
        (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom),
          concreteLiftedGraphPairDecomposition packages C f D g =
            graphPrimeSupportFiberProductImageDecomposition C f D g h hh)
    (graphPair_no :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z),
          (¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }) →
            IsEmpty (concreteLiftedGraphPairDecomposition packages C f D g).index) :
    CanonicalGraphPackageCompatibilityObligation
      (concreteLiftedCanonicalComposition
        diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
        rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
        leftPresentation rightPresentation hpresentation hleft hright) := by
  classical
  intro X Y Z C f D g
  change Boundary.FiniteCorrespondencePresentation.toGeom
      (Boundary.SupportFiberProductImageDecomposition.toPresentation
        (concreteLiftedGraphPairDecomposition packages C f D g)) =
    if hfac : Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
        h ≫ D.toAmbient = C.toAmbient ≫ f.hom }
    then ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g)
    else 0
  by_cases hfac : Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
      h ≫ D.toAmbient = C.toAmbient ≫ f.hom }
  · rcases hfac with ⟨⟨h, hh⟩⟩
    have hfac' : Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
        h ≫ D.toAmbient = C.toAmbient ≫ f.hom } := ⟨⟨h, hh⟩⟩
    rw [graphPair_yes C f D g h hh]
    have hgeom :=
      graphPrimeSupportFiberProductImageDecomposition_toPresentation_toGeom C f D g h hh
    simpa [ordinaryMorphismGraph_componentCorrespondence,
      Boundary.FiniteCorrespondence.ofPrimeSupport, hfac'] using hgeom
  · let dec := concreteLiftedGraphPairDecomposition packages C f D g
    letI : IsEmpty dec.index := graphPair_no C f D g hfac
    have hdatum_zero :
        (Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          dec).toPresentation = 0 := by
      simpa using
        Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition_toPresentation_eq_zero_of_isEmpty dec
    have hpres_zero : dec.toPresentation = 0 := by
      simpa using
        (Boundary.RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition_toPresentation dec).symm.trans hdatum_zero
    have hzero :
        Boundary.FiniteCorrespondencePresentation.toGeom
          (Boundary.SupportFiberProductImageDecomposition.toPresentation dec) = 0 := by
      rw [hpres_zero, Boundary.FiniteCorrespondencePresentation.toGeom_zero]
    simpa [hfac, dec] using hzero

/-- A canonical package family satisfying the graph-pair compatibility
obligation is already graph-functorial at the finite-correspondence composition
level. -/
private theorem graphFunctoriality_ofCompatibilityObligation
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
        (k := k))
    (hgraph : CanonicalGraphPackageCompatibilityObligation composition) :
    GraphFunctoriality
      (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition).toFiniteCorrespondenceCompositionData := by
  classical
  let data :=
    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
      composition
  refine ⟨?_⟩
  intro X Y Z C f g D_Y
  have h_distrib :
      ∀ (right : Boundary.FiniteCorrespondence Y Z)
        (s : Finset (Boundary.SourceIrreducibleComponent Y))
        (φ : Boundary.SourceIrreducibleComponent Y → Boundary.FiniteCorrespondence Y Z),
        Boundary.FiniteCorrespondenceCompositionData.comp
            data.toFiniteCorrespondenceCompositionData
            (ordinaryMorphismGraph_componentCorrespondence C f)
            (s.sum φ) =
          s.sum fun D =>
            Boundary.FiniteCorrespondenceCompositionData.comp
              data.toFiniteCorrespondenceCompositionData
              (ordinaryMorphismGraph_componentCorrespondence C f)
              (φ D) := by
    intro right s φ
    let compHom : Boundary.FiniteCorrespondence Y Z →+ Boundary.FiniteCorrespondence X Z :=
      { toFun := fun corr =>
          Boundary.FiniteCorrespondenceCompositionData.comp
            data.toFiniteCorrespondenceCompositionData
            (ordinaryMorphismGraph_componentCorrespondence C f)
            corr
        map_zero' :=
          Boundary.FiniteCorrespondenceCompositionData.comp_zero_right
            data.toFiniteCorrespondenceCompositionData
            (ordinaryMorphismGraph_componentCorrespondence C f)
        map_add' := fun corr₁ corr₂ =>
          Boundary.FiniteCorrespondenceCompositionData.comp_add_right
            data.toFiniteCorrespondenceCompositionData
            (ordinaryMorphismGraph_componentCorrespondence C f)
            corr₁ corr₂ }
    exact map_sum compHom φ s
  have hterm (D : Boundary.SourceIrreducibleComponent Y) :
      Boundary.FiniteCorrespondenceCompositionData.comp
        data.toFiniteCorrespondenceCompositionData
        (ordinaryMorphismGraph_componentCorrespondence C f)
        (ordinaryMorphismGraph_componentCorrespondence D g) =
          if hfac : Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }
          then ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g)
          else 0 := by
    simp only [ordinaryMorphismGraph_componentCorrespondence,
      Boundary.FiniteCorrespondence.ofPrimeSupport,
      Boundary.FiniteCorrespondenceCompositionData.comp_single_single,
      one_mul, one_zsmul]
    change data.compPrime
        (ordinaryMorphismGraphPrimeGeom C f)
        (ordinaryMorphismGraphPrimeGeom D g) = _
    change Boundary.FiniteCorrespondencePresentation.toGeom
        (Boundary.SupportFiberProductImageDecomposition.toPresentation
          (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
            composition.packages
            (ordinaryMorphismGraphPrimeSupport C f)
            (ordinaryMorphismGraphPrimeSupport D g))) = _
    simpa [CanonicalGraphPackageCompatibilityObligation, ordinaryMorphismGraphPrimeGeom] using hgraph C f D g
  let term := fun D : Boundary.SourceIrreducibleComponent Y =>
    Boundary.FiniteCorrespondenceCompositionData.comp
      data.toFiniteCorrespondenceCompositionData
      (ordinaryMorphismGraph_componentCorrespondence C f)
      (ordinaryMorphismGraph_componentCorrespondence D g)
  have hsum :
      Boundary.FiniteCorrespondenceCompositionData.comp
        data.toFiniteCorrespondenceCompositionData
        (ordinaryMorphismGraph_componentCorrespondence C f)
        (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y) =
      D_Y.components.sum term := by
    simpa [ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition, term] using
      (h_distrib
        (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y)
        D_Y.components
        (fun D => ordinaryMorphismGraph_componentCorrespondence D g))
  rw [hsum]
  let landing :=
    Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
      D_Y
      (ordinaryMorphismGraphPrimeSupport C f)
  let listed : Boundary.SourceIrreducibleComponent Y := landing.1.1
  have hlisted_mem : listed ∈ D_Y.components := landing.1.2
  have hlanding_term :
      term listed = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) := by
    have hfac : Nonempty { h : C.carrier.scheme ⟶ listed.carrier.scheme //
        h ≫ listed.toAmbient = C.toAmbient ≫ f.hom } := ⟨⟨landing.2.1, landing.2.2⟩⟩
    calc
      term listed =
        if hfac' : Nonempty { h : C.carrier.scheme ⟶ listed.carrier.scheme //
          h ≫ listed.toAmbient = C.toAmbient ≫ f.hom }
        then ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g)
        else 0 := by
        simpa [term] using hterm listed
      _ = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) := by
        simp [hfac]
  have hoffsum :
      (D_Y.components.erase listed).sum term = 0 := by
    have haux :
        ∀ t : Finset (Boundary.SourceIrreducibleComponent Y),
          t ⊆ D_Y.components.erase listed → t.sum term = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro D t hnotin hIH hsub
        have hmemErase : D ∈ D_Y.components.erase listed := hsub (by simp)
        have hmem : D ∈ D_Y.components := (Finset.mem_erase.mp hmemErase).2
        have hneq : D ≠ listed := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D_Y.components.erase listed := by
          intro x hx
          exact hsub (by simp [hx])
        have hno :
            ¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
                h ≫ D.toAmbient = C.toAmbient ≫ f.hom } := by
          intro hfac
          rcases hfac with ⟨⟨h, hh⟩⟩
          exact hneq
            (Boundary.FiniteIrreducibleComponentDecomposition.eq_landingComponent_of_target_factorization
              D_Y
              (ordinaryMorphismGraphPrimeSupport C f)
              D
              hmem
              h
              hh)
        rw [Finset.sum_insert hnotin, hterm D, hIH hsub_t]
        simp [hno]
    exact haux (D_Y.components.erase listed) (by
      intro x hx
      exact hx)
  have hsplit :
      D_Y.components.sum term = term listed + (D_Y.components.erase listed).sum term := by
    simpa [term, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D_Y.components) (f := term) hlisted_mem).symm
  calc
    D_Y.components.sum term = term listed + (D_Y.components.erase listed).sum term := by
      rw [hsplit]
    _ = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) + 0 := by
      rw [hlanding_term, hoffsum]
    _ = ordinaryMorphismGraph_componentCorrespondence C (Boundary.SmOverHom.comp f g) := by
      simp

private theorem ordinaryMorphismGraph_comp_canonical_ofCompatibilityObligation
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
        (k := k))
    (hgraph : CanonicalGraphPackageCompatibilityObligation composition)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_X : Boundary.FiniteIrreducibleComponentDecomposition X)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    let data :=
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData.data
        composition
    Boundary.FiniteCorrespondenceCompositionData.comp
      data.toFiniteCorrespondenceCompositionData
      (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition f D_X)
      (ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition g D_Y) =
      ordinaryMorphismGraph_finiteCorrespondenceOfDecomposition
        (Boundary.SmOverHom.comp f g) D_X := by
  exact ordinaryMorphismGraph_comp_canonical
    composition
    (graphFunctoriality_ofCompatibilityObligation composition hgraph)
    f g D_X D_Y

/-- Concrete-lifted entry point for canonical graph functoriality.
This is the public canonical route: the theorem is stated directly in the raw
inputs of `CanonicalCompositionPackageData.ofConcreteLiftedDecompositionFamily`,
not via a free-standing graph-compatibility hypothesis on abstract package data. -/
theorem canonicalGraphFunctoriality_ofConcreteLiftedDecompositionFamily
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceComponent.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceComponent.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                  (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    (graphPair_yes :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z)
        (h : C.carrier.scheme ⟶ D.carrier.scheme)
        (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom),
          concreteLiftedGraphPairDecomposition packages C f D g =
            graphPrimeSupportFiberProductImageDecomposition C f D g h hh)
    (graphPair_no :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z),
          (¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }) →
            IsEmpty (concreteLiftedGraphPairDecomposition packages C f D g).index) :
    let composition :=
      concreteLiftedCanonicalComposition
        diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
        rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
        leftPresentation rightPresentation hpresentation hleft hright
    GraphFunctoriality composition.data.toFiniteCorrespondenceCompositionData := by
  let composition := concreteLiftedCanonicalComposition
    diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
    rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
    leftPresentation rightPresentation hpresentation hleft hright
  exact graphFunctoriality_ofCompatibilityObligation composition
    (canonicalGraphPackageCompatibility_ofConcreteLiftedDecompositionFamily
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright
      graphPair_yes graphPair_no)

/-- Rational graph functoriality for an abstract canonical package-family
composition, transported from the validated integral theorem through
`canonicalSmCorQ` and the rationalization map. This remains available only as an
obligation-suffixed internal route. -/
theorem ordinaryMorphismGraph_comp_canonical_Q_ofCompatibilityObligation
    (composition :
      Boundary.RepresentedPrimeFiniteCorrespondenceComposition.CanonicalCompositionPackageData
        (k := k))
    (hgraph : CanonicalGraphPackageCompatibilityObligation composition)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_X : Boundary.FiniteIrreducibleComponentDecomposition X)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    let category :=
      ({ integral := composition.toSmCor } : Boundary.SmCorQ (k := k))
    category.comp
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D_X)
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category g D_Y)
      = ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
          (Boundary.SmOverHom.comp f g) D_X := by
  let category :=
    ({ integral := composition.toSmCor } : Boundary.SmCorQ (k := k))
  have hGF : GraphFunctoriality category.integral.composition := by
    simpa [category] using
      graphFunctoriality_ofCompatibilityObligation composition hgraph
  exact ordinaryMorphismGraph_comp category hGF f g D_X D_Y

/-- Rational graph functoriality for the canonical concrete lifted-decomposition
family, transported from the validated integral theorem through `canonicalSmCorQ`
and the rationalization map. -/
theorem ordinaryMorphismGraph_comp_canonical_Q
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → Boundary.FiniteIrreducibleComponentDecomposition X)
    (packages : ConcreteLiftedPackages (k := k))
    (leftIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y)
        (component : Boundary.SourceIrreducibleComponent X)
        (toComponent : P.sourceComponent.carrier.scheme ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.sourceComponent.toAmbient),
          packages (Boundary.SourceIrreducibleComponent.diagonalPrimeGeom component)
              (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) =
            leftIdentityPackage (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P))
    (rightIdentityPackage : ConcreteLiftedIdentityPackages (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : Boundary.PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : Boundary.PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport X Y),
          Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
              (fun {X} {Y} {Z} x y =>
                Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                  (packages (X := X) (Y := Y) (Z := Z) x y))
              P
              (Boundary.SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            Boundary.RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((Boundary.FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        Boundary.RepresentedPrimeSupport W X →
        Boundary.RepresentedPrimeSupport X Y →
        Boundary.RepresentedPrimeSupport Y Z →
          Boundary.FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  P Q)))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              Boundary.FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : Boundary.RepresentedPrimeSupport W X)
        (Q : Boundary.RepresentedPrimeSupport X Y)
        (R : Boundary.RepresentedPrimeSupport Y Z),
          Boundary.FiniteCorrespondenceCompositionData.comp
            (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
              (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.data
                diagonalDecomposition
                (fun {X} {Y} {Z} x y =>
                  Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                    (packages (X := X) (Y := Y) (Z := Z) x y))))
            (Finsupp.single (Boundary.PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (Boundary.FiniteCorrespondencePresentation.toGeom
              (Boundary.SupportFiberProductImageDecomposition.toPresentation
                (Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductImageCompositionPackageFamily.decomposition
                  (fun {X} {Y} {Z} x y =>
                    Boundary.RepresentedPrimeFiniteCorrespondenceComposition.SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
                      (packages (X := X) (Y := Y) (Z := Z) x y))
                  Q R))) =
              Boundary.FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    (graphPair_yes :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z)
        (h : C.carrier.scheme ⟶ D.carrier.scheme)
        (hh : h ≫ D.toAmbient = C.toAmbient ≫ f.hom),
          concreteLiftedGraphPairDecomposition packages C f D g =
            graphPrimeSupportFiberProductImageDecomposition C f D g h hh)
    (graphPair_no :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (C : Boundary.SourceIrreducibleComponent X)
        (f : Boundary.SmOverHom X Y)
        (D : Boundary.SourceIrreducibleComponent Y)
        (g : Boundary.SmOverHom Y Z),
          (¬ Nonempty { h : C.carrier.scheme ⟶ D.carrier.scheme //
              h ≫ D.toAmbient = C.toAmbient ≫ f.hom }) →
            IsEmpty (concreteLiftedGraphPairDecomposition packages C f D g).index)
    {X Y Z : Geometry.SmSchemeOver k}
    (f : Boundary.SmOverHom X Y)
    (g : Boundary.SmOverHom Y Z)
    (D_X : Boundary.FiniteIrreducibleComponentDecomposition X)
    (D_Y : Boundary.FiniteIrreducibleComponentDecomposition Y) :
    let composition := concreteLiftedCanonicalComposition
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright
    let category := ({ integral := composition.toSmCor } : Boundary.SmCorQ (k := k))
    category.comp
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category f D_X)
      (ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category g D_Y)
      = ordinaryMorphismGraph_rationalCorrespondenceOfDecomposition category
          (Boundary.SmOverHom.comp f g) D_X := by
  let composition := concreteLiftedCanonicalComposition
    diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
    rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
    leftPresentation rightPresentation hpresentation hleft hright
  exact ordinaryMorphismGraph_comp_canonical_Q_ofCompatibilityObligation
    composition
    (canonicalGraphPackageCompatibility_ofConcreteLiftedDecompositionFamily
      diagonalDecomposition packages leftIdentityPackage leftIdentity_constant
      rightIdentityPackage rightIdentity_constant landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright
      graphPair_yes graphPair_no)
    f g D_X D_Y

end Geometry

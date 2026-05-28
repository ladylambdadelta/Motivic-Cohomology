import Geometry.Correspondences.Graph
import Boundary.CompositionGeometry

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

/-- The `toAmbientSource` of a graph prime support is the source component's
ambient immersion. -/
private theorem ordinaryMorphismGraphPrimeSupport_toAmbientSource
    {X Y : Geometry.SmSchemeOver k}
    (C : Boundary.SourceIrreducibleComponent X)
    (f : Boundary.SmOverHom X Y) :
    (ordinaryMorphismGraphPrimeSupport C f).toAmbientSource = C.toAmbient := by
  simp [Boundary.PrimeFiniteCorrespondenceSupport.toAmbientSource,
        ordinaryMorphismGraphPrimeSupport, ordinaryMorphismGraphMap_fst]

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
    · simp [Boundary.PrimeFiniteCorrespondenceSupport.compositionToAmbientProduct_fst,
        Boundary.PrimeFiniteCorrespondenceSupport.toSourceComponent,
        ordinaryMorphismGraphPrimeSupport, ordinaryMorphismGraphMap_fst]
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
      ordinaryMorphismGraphPrimeSupport, ordinaryMorphismOnSourceComponent,
      ordinaryMorphismGraphMap_fst, Boundary.SmOverHom.comp, Category.assoc]
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

end Geometry

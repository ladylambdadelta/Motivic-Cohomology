import Boundary.Diagonal
import Mathlib.Topology.Irreducible

/-!
# Diagonal Decomposition Data

This file packages the diagonal prime classes and identity correspondence
attached to a finite irreducible-component decomposition.
-/

universe u v

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open SourceIrreducibleComponent

noncomputable section

namespace FiniteIrreducibleComponentDecomposition

/-- For an integral represented prime support, choose a listed target component
whose image contains the irreducible image of the target morphism, together
with the induced factorization through that open immersion. -/
def landingComponent_of_finite
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y) :
    Σ listed : { listed : SourceIrreducibleComponent Y // listed ∈ D.components },
        { toComponent : P.support ⟶ listed.1.carrier.scheme //
            toComponent ≫ listed.1.toAmbient = P.toTarget } := by
  classical
  letI : IsIntegral P.support := P.isIntegral
  let image : Set Y.scheme.carrier := Set.range P.toTarget.base
  have hImageIrreducible : IsIrreducible image := by
    rw [show image = P.toTarget.base '' Set.univ by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨x, Set.mem_univ x, rfl⟩
      · intro hy
        rcases hy with ⟨x, _hx, rfl⟩
        exact ⟨x, rfl⟩]
    exact (IrreducibleSpace.isIrreducible_univ P.support).image
      P.toTarget.base P.toTarget.base.continuous.continuousOn
  let y : Y.scheme.carrier := Classical.choose hImageIrreducible.nonempty
  have hy : y ∈ image := Classical.choose_spec hImageIrreducible.nonempty
  let component : SourceIrreducibleComponent Y := Classical.choose (D.covers y)
  letI : IsOpenImmersion component.toAmbient := component.isOpenImmersion
  have hcomponent : component ∈ D.components := (Classical.choose_spec (D.covers y)).1
  have hycomponent : y ∈ Set.range component.toAmbient.base :=
    (Classical.choose_spec (D.covers y)).2
  have hcomponentClopen : IsClopen (Set.range component.toAmbient.base) :=
    ⟨component.isClosedImmersion.base_closed.isClosed_range,
      IsOpenImmersion.isOpen_range component.toAmbient⟩
  have himage_subset : image ⊆ Set.range component.toAmbient.base := by
    exact hImageIrreducible.isConnected.isPreconnected.subset_isClopen
      hcomponentClopen ⟨y, hy, hycomponent⟩
  let listed : { listed : SourceIrreducibleComponent Y // listed ∈ D.components } :=
    ⟨component, hcomponent⟩
  let toComponent : P.support ⟶ component.carrier.scheme :=
    IsOpenImmersion.lift component.toAmbient P.toTarget himage_subset
  refine ⟨listed, ⟨toComponent, ?_⟩⟩
  exact IsOpenImmersion.lift_fac component.toAmbient P.toTarget himage_subset

/-- Any listed component of the chosen finite decomposition through which the
target morphism of `P` factors must coincide with the canonical landing
component selected by `landingComponent_of_finite`. -/
theorem eq_landingComponent_of_target_factorization
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y)
    (listed : SourceIrreducibleComponent Y)
    (hlisted : listed ∈ D.components)
    (toComponent : P.support ⟶ listed.carrier.scheme)
    (htoComponent : toComponent ≫ listed.toAmbient = P.toTarget) :
    listed = (landingComponent_of_finite D P).1.1 := by
  classical
  let landing := landingComponent_of_finite D P
  let landingListed : SourceIrreducibleComponent Y := landing.1.1
  let landingToComponent : P.support ⟶ landingListed.carrier.scheme := landing.2.1
  have hlanding_mem : landingListed ∈ D.components := landing.1.2
  by_contra hne
  have hdisj := D.pairwise_disjoint hlisted hlanding_mem hne
  have hsource_nonempty : (Set.range P.sourceImage.toAmbient.base).Nonempty := by
    exact P.sourceImage.range_nonempty
  rcases hsource_nonempty with ⟨xAmbient, xSource, rfl⟩
  let x : P.support.carrier := Classical.choose (P.surjective_toSourceComponent xSource)
  have hx_listed : P.toTarget.base x ∈ Set.range listed.toAmbient.base := by
    refine ⟨toComponent.base x, ?_⟩
    exact congrArg (fun f => f.base x) htoComponent
  have hx_landing : P.toTarget.base x ∈ Set.range landingListed.toAmbient.base := by
    refine ⟨landingToComponent.base x, ?_⟩
    exact congrArg (fun f => f.base x) landing.2.2
  exact Set.disjoint_left.mp hdisj hx_listed hx_landing

/-- The diagonal class of any listed component through which `P.toTarget`
factors is the canonical landing diagonal class attached to the chosen finite
decomposition. -/
theorem diagonalPrimeGeom_eq_landingComponent_of_target_factorization
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y)
    (listed : SourceIrreducibleComponent Y)
    (hlisted : listed ∈ D.components)
    (toComponent : P.support ⟶ listed.carrier.scheme)
    (htoComponent : toComponent ≫ listed.toAmbient = P.toTarget) :
    SourceIrreducibleComponent.diagonalPrimeGeom listed =
      SourceIrreducibleComponent.diagonalPrimeGeom ((landingComponent_of_finite D P).1.1) := by
  rw [eq_landingComponent_of_target_factorization D P listed hlisted toComponent htoComponent]

/-- If a listed source component already belongs to the chosen finite
decomposition, then the canonical landing component of its diagonal support is
that same listed component. -/
theorem landingComponent_of_finite_diagonalRepresentedPrimeSupport
    {X : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X)
    (hcomponent : component ∈ D.components) :
    (landingComponent_of_finite D
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)).1.1 = component := by
  symm
  refine eq_landingComponent_of_target_factorization D
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)
    component hcomponent (𝟙 component.carrier.scheme) ?_
  change 𝟙 component.carrier.scheme ≫ component.toAmbient =
    component.toSourceImageSubscheme.diagonalRepresentedPrimeSupport.toTarget
  change component.toAmbient =
    component.toSourceImageSubscheme.diagonalRepresentedPrimeSupport.toTarget
  rfl

/-- A point of the support pullback `P.support ×_Y Δ_component` forces the
target map of `P` to factor through `component`. -/
theorem target_factorization_of_nonempty_compositionFiberProduct_diagonal
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (x : PrimeFiniteCorrespondenceSupport.compositionFiberProduct P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) :
    ∃ toComponent : P.support ⟶ component.carrier.scheme,
      toComponent ≫ component.toAmbient = P.toTarget := by
  classical
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
  letI : IsIntegral P.support := P.isIntegral
  let image : Set Y.scheme.carrier := Set.range P.toTarget.base
  have hImageIrreducible : IsIrreducible image := by
    rw [show image = P.toTarget.base '' Set.univ by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, rfl⟩
        exact ⟨x, Set.mem_univ x, rfl⟩
      · intro hy
        rcases hy with ⟨x, _hx, rfl⟩
        exact ⟨x, rfl⟩]
    exact (IrreducibleSpace.isIrreducible_univ P.support).image
      P.toTarget.base P.toTarget.base.continuous.continuousOn
  have hy :
      P.toTarget.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x) ∈ image := by
    exact ⟨(PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x, rfl⟩
  have hycomponent :
      P.toTarget.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x) ∈
        Set.range component.toAmbient.base := by
    refine ⟨(PrimeFiniteCorrespondenceSupport.compositionFiberSnd P diag).base x, ?_⟩
    have hcond := congrArg (fun f => f.base x)
      (PrimeFiniteCorrespondenceSupport.compositionFiber_condition P diag)
    change component.toAmbient.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd P diag).base x) =
      P.toTarget.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x)
    change diag.toAmbientSource.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd P diag).base x) =
      P.toTarget.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x)
    exact hcond.symm
  letI : IsOpenImmersion component.toAmbient := component.isOpenImmersion
  have hcomponentClopen : IsClopen (Set.range component.toAmbient.base) := by
    exact ⟨component.isClosedImmersion.base_closed.isClosed_range,
      IsOpenImmersion.isOpen_range component.toAmbient⟩
  have himage_subset : image ⊆ Set.range component.toAmbient.base := by
    exact hImageIrreducible.isConnected.isPreconnected.subset_isClopen
      hcomponentClopen ⟨_, hy, hycomponent⟩
  let toComponent : P.support ⟶ component.carrier.scheme :=
    IsOpenImmersion.lift component.toAmbient P.toTarget himage_subset
  refine ⟨toComponent, ?_⟩
  exact IsOpenImmersion.lift_fac component.toAmbient P.toTarget himage_subset

/-- If a listed component of a certified finite decomposition is not the
canonical landing component of `P`, then the pullback of `P` with the diagonal
over that component is empty. -/
theorem isEmpty_compositionFiberProduct_diagonal_of_ne_landingComponent
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (hcomponent : component ∈ D.components)
    (hne : component ≠ (landingComponent_of_finite D P).1.1) :
    IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) := by
  refine ⟨?_⟩
  intro x
  rcases target_factorization_of_nonempty_compositionFiberProduct_diagonal P component x with
    ⟨toComponent, htoComponent⟩
  exact hne (eq_landingComponent_of_target_factorization D P component hcomponent toComponent htoComponent)

/-- Distinct listed diagonal components in a certified finite decomposition have
empty support fiber product. -/
theorem isEmpty_compositionFiberProduct_diagonal_of_ne_component
    {X : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition X)
    (left right : SourceIrreducibleComponent X)
    (hleft : left ∈ D.components)
    (hright : right ∈ D.components)
    (hne : right ≠ left) :
    IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport right)) := by
  have hlanding :
      (landingComponent_of_finite D
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)).1.1 = left :=
    landingComponent_of_finite_diagonalRepresentedPrimeSupport D left hleft
  exact isEmpty_compositionFiberProduct_diagonal_of_ne_landingComponent D
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
    right hright (fun h => hne (h.trans hlanding))

/-- The finite set of diagonal geometric classes represented by a certified
finite irreducible-component decomposition. -/
def diagonalPrimeClasses {X : Geometry.SmSchemeOver k}
  (decomposition : FiniteIrreducibleComponentDecomposition X) :
  Finset (PrimeFiniteCorrespondenceGeom X X) := by
  classical
  exact decomposition.components.image SourceIrreducibleComponent.diagonalPrimeGeom

/-- The component-sum identity correspondence attached to a certified finite
irreducible-component decomposition. -/
def identityFiniteCorrespondence {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X) :
    FiniteCorrespondence X X :=
  decomposition.diagonalPrimeClasses.sum (fun diagonalClass =>
    Finsupp.single diagonalClass 1)

/-- The rational diagonal identity correspondence is the honest coefficient
cast of the integral component-sum identity correspondence. -/
def identityFiniteCorrespondenceQ {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X) :
    RationalFiniteCorrespondence X X :=
  FiniteCorrespondence.toRational decomposition.identityFiniteCorrespondence

/-- The identity correspondence attached to a certified decomposition is the
formal sum of the diagonal singleton correspondences of its listed source
components. -/
theorem identityFiniteCorrespondence_eq_sum_components {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X) :
    decomposition.identityFiniteCorrespondence =
      decomposition.components.sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
  classical
  rw [identityFiniteCorrespondence, diagonalPrimeClasses]
  refine Finset.sum_image ?_
  intro C hC D hD hCD
  have hiso : SourceIrreducibleComponent.IsoOverAmbient C D :=
    isoOverAmbient_of_diagonalPrimeGeom_eq hCD
  exact decomposition.no_equivalent_duplicates hC hD hiso

/-- Formal comparison between an indexed diagonal component sum and the
canonical identity correspondence of a certified finite irreducible-component
decomposition.

This is the coefficient-level endpoint needed by external-product identity
proofs: once the geometric construction identifies its indexed diagonal pieces
bijectively with the certified listed components, the finite correspondence is
the canonical identity. -/
theorem sum_diagonal_eq_identityFiniteCorrespondence_of_equiv_components
    {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    {ι : Type v} [Fintype ι]
    (sourceImage : ι → SourceImageSubscheme (k := k) X)
    (listedEquiv : ι ≃ { listed : SourceIrreducibleComponent X //
      listed ∈ decomposition.components })
    (hcomponent :
      ∀ i,
        SourceImageSubscheme.diagonalFiniteCorrespondence (sourceImage i) =
          SourceIrreducibleComponent.diagonalFiniteCorrespondence (listedEquiv i).1) :
    (∑ i : ι, SourceImageSubscheme.diagonalFiniteCorrespondence (sourceImage i)) =
      decomposition.identityFiniteCorrespondence := by
  classical
  rw [identityFiniteCorrespondence_eq_sum_components decomposition]
  calc
    (∑ i : ι, SourceImageSubscheme.diagonalFiniteCorrespondence (sourceImage i)) =
        ∑ i : ι,
          SourceIrreducibleComponent.diagonalFiniteCorrespondence ((listedEquiv i).1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hcomponent i
    _ =
        ∑ listed : { listed : SourceIrreducibleComponent X //
          listed ∈ decomposition.components },
          SourceIrreducibleComponent.diagonalFiniteCorrespondence listed.1 := by
        exact Fintype.sum_equiv listedEquiv
          (fun i =>
            SourceIrreducibleComponent.diagonalFiniteCorrespondence ((listedEquiv i).1))
          (fun listed =>
            SourceIrreducibleComponent.diagonalFiniteCorrespondence listed.1)
          (fun _ => rfl)
    _ =
        decomposition.components.sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
        exact Finset.sum_attach decomposition.components
          SourceIrreducibleComponent.diagonalFiniteCorrespondence

theorem identityFiniteCorrespondence_apply_of_mem {X : Geometry.SmSchemeOver k}
  (decomposition : FiniteIrreducibleComponentDecomposition X)
  {diagonalClass : PrimeFiniteCorrespondenceGeom X X}
  (hmem : diagonalClass ∈ decomposition.diagonalPrimeClasses) :
  decomposition.identityFiniteCorrespondence diagonalClass = 1 := by
  classical
  rw [identityFiniteCorrespondence]
  rw [show
    (∑ c ∈ decomposition.diagonalPrimeClasses,
      (Finsupp.single c 1 : FiniteCorrespondence X X)) diagonalClass =
        ∑ c ∈ decomposition.diagonalPrimeClasses,
          (Finsupp.single c 1 : FiniteCorrespondence X X) diagonalClass by
    exact map_sum (Finsupp.applyAddHom diagonalClass)
      (fun c => (Finsupp.single c 1 : FiniteCorrespondence X X))
      decomposition.diagonalPrimeClasses]
  rw [Finset.sum_eq_single diagonalClass]
  · rw [Finsupp.single_eq_same]
  · intro other hother hne
    exact Finsupp.single_eq_of_ne hne
  · intro hnot
    exact False.elim (hnot hmem)

theorem identityFiniteCorrespondence_apply_of_not_mem {X : Geometry.SmSchemeOver k}
  (decomposition : FiniteIrreducibleComponentDecomposition X)
  {diagonalClass : PrimeFiniteCorrespondenceGeom X X}
  (hmem : diagonalClass ∉ decomposition.diagonalPrimeClasses) :
  decomposition.identityFiniteCorrespondence diagonalClass = 0 := by
  classical
  rw [identityFiniteCorrespondence]
  rw [show
    (∑ c ∈ decomposition.diagonalPrimeClasses,
      (Finsupp.single c 1 : FiniteCorrespondence X X)) diagonalClass =
        ∑ c ∈ decomposition.diagonalPrimeClasses,
          (Finsupp.single c 1 : FiniteCorrespondence X X) diagonalClass by
    exact map_sum (Finsupp.applyAddHom diagonalClass)
      (fun c => (Finsupp.single c 1 : FiniteCorrespondence X X))
      decomposition.diagonalPrimeClasses]
  rw [Finset.sum_eq_zero]
  intro other hother
  exact Finsupp.single_eq_of_ne (fun h => hmem (h ▸ hother))

theorem mem_identityFiniteCorrespondence_support_iff {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    (diagonalClass : PrimeFiniteCorrespondenceGeom X X) :
    diagonalClass ∈ (decomposition.identityFiniteCorrespondence.support : Finset (PrimeFiniteCorrespondenceGeom X X)) ↔
      diagonalClass ∈ decomposition.diagonalPrimeClasses := by
  classical
  by_cases hmem : diagonalClass ∈ decomposition.diagonalPrimeClasses
  · rw [Finsupp.mem_support_iff]
    rw [decomposition.identityFiniteCorrespondence_apply_of_mem hmem]
    constructor
    · intro _hne
      exact hmem
    · intro _hmem
      exact one_ne_zero
  · rw [Finsupp.mem_support_iff]
    rw [decomposition.identityFiniteCorrespondence_apply_of_not_mem hmem]
    constructor
    · intro hzero
      exact False.elim (hzero rfl)
    · intro hmem'
      exact False.elim (hmem hmem')

theorem identityFiniteCorrespondence_apply_eq_indicator {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    [DecidableEq (PrimeFiniteCorrespondenceGeom X X)]
    (diagonalClass : PrimeFiniteCorrespondenceGeom X X) :
    decomposition.identityFiniteCorrespondence diagonalClass =
      if diagonalClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
  classical
  by_cases hmem : diagonalClass ∈ decomposition.diagonalPrimeClasses
  · rw [decomposition.identityFiniteCorrespondence_apply_of_mem hmem]
    rw [if_pos hmem]
  · rw [decomposition.identityFiniteCorrespondence_apply_of_not_mem hmem]
    rw [if_neg hmem]

theorem identityFiniteCorrespondenceQ_apply_eq_indicator {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    [DecidableEq (PrimeFiniteCorrespondenceGeom X X)]
    (diagonalClass : PrimeFiniteCorrespondenceGeom X X) :
    decomposition.identityFiniteCorrespondenceQ diagonalClass =
      if diagonalClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 := by
  classical
  by_cases hmem : diagonalClass ∈ decomposition.diagonalPrimeClasses
  · rw [if_pos hmem]
    change ((decomposition.identityFiniteCorrespondence diagonalClass : ℤ) : ℚ) = 1
    rw [decomposition.identityFiniteCorrespondence_apply_of_mem hmem]
    norm_num
  · rw [if_neg hmem]
    change ((decomposition.identityFiniteCorrespondence diagonalClass : ℤ) : ℚ) = 0
    rw [decomposition.identityFiniteCorrespondence_apply_of_not_mem hmem]
    norm_num

@[simp] theorem mem_diagonalPrimeClasses_iff {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    (diagonalClass : PrimeFiniteCorrespondenceGeom X X) :
    diagonalClass ∈ decomposition.diagonalPrimeClasses ↔
      ∃ component ∈ decomposition.components,
        SourceIrreducibleComponent.diagonalPrimeGeom component = diagonalClass := by
  classical
  rw [diagonalPrimeClasses]
  exact Finset.mem_image

/-- Any two certified decompositions of `X` determine the same set of diagonal
geometric classes. -/
theorem diagonalPrimeClasses_eq {X : Geometry.SmSchemeOver k}
  (D : FiniteIrreducibleComponentDecomposition X) (D' : FiniteIrreducibleComponentDecomposition X) :
  D.diagonalPrimeClasses = D'.diagonalPrimeClasses := by
  classical
  apply Finset.ext
  intro diagonalClass
  constructor
  · intro hmem
    rcases (mem_diagonalPrimeClasses_iff D diagonalClass).mp hmem with
      ⟨component, hcomponent, hdiag⟩
    rcases D'.exhaustive component with ⟨listed, hiso⟩
    refine (mem_diagonalPrimeClasses_iff D' diagonalClass).mpr ?_
    refine ⟨listed.1, listed.2, ?_⟩
    rw [← SourceIrreducibleComponent.diagonalPrimeGeom_eq_of_isoOverAmbient hiso]
    exact hdiag
  · intro hmem
    rcases (mem_diagonalPrimeClasses_iff D' diagonalClass).mp hmem with
      ⟨component, hcomponent, hdiag⟩
    rcases D.exhaustive component with ⟨listed, hiso⟩
    refine (mem_diagonalPrimeClasses_iff D diagonalClass).mpr ?_
    refine ⟨listed.1, listed.2, ?_⟩
    rw [← SourceIrreducibleComponent.diagonalPrimeGeom_eq_of_isoOverAmbient hiso]
    exact hdiag

/-- The component-sum identity correspondence is independent of the certified
finite irreducible-component decomposition used to build it. -/
theorem identityFiniteCorrespondence_independent {X : Geometry.SmSchemeOver k}
  (D : FiniteIrreducibleComponentDecomposition X) (D' : FiniteIrreducibleComponentDecomposition X) :
  D.identityFiniteCorrespondence = D'.identityFiniteCorrespondence := by
  classical
  rw [identityFiniteCorrespondence, identityFiniteCorrespondence,
    diagonalPrimeClasses_eq D D']

/-- If a certified decomposition is represented by a singleton source
component, its identity correspondence specializes to the corresponding
diagonal singleton class. -/
theorem identityFiniteCorrespondence_singleton {X : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X)
    (hcomponents : D.components = {component}) :
    D.identityFiniteCorrespondence =
      SourceIrreducibleComponent.diagonalFiniteCorrespondence component := by
  classical
  have hclasses : D.diagonalPrimeClasses =
      {SourceIrreducibleComponent.diagonalPrimeGeom component} := by
    rw [diagonalPrimeClasses, hcomponents]
    ext diagonalClass
    rw [Finset.mem_image]
    constructor
    · intro h
      rcases h with ⟨listed, hlisted, hdiag⟩
      rw [Finset.mem_singleton] at hlisted
      rw [← hdiag, hlisted]
      exact Finset.mem_singleton_self _
    · intro h
      rw [Finset.mem_singleton] at h
      refine ⟨component, Finset.mem_singleton_self component, ?_⟩
      exact h.symm
  rw [identityFiniteCorrespondence, hclasses,
    SourceIrreducibleComponent.diagonalFiniteCorrespondence]
  rw [Finset.sum_singleton]
  change Finsupp.single (SourceIrreducibleComponent.diagonalPrimeGeom component) (1 : ℤ) =
    Finsupp.single (SourceIrreducibleComponent.diagonalPrimeGeom component) (1 : ℤ)
  rfl

end FiniteIrreducibleComponentDecomposition

/-- Backward-compatible top-level notation for the rational diagonal identity.
The owner is `FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondenceQ`. -/
abbrev identityFiniteCorrespondenceQ {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X) :
    RationalFiniteCorrespondence X X :=
  decomposition.identityFiniteCorrespondenceQ

theorem identityFiniteCorrespondenceQ_apply_eq_indicator {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X)
    [DecidableEq (PrimeFiniteCorrespondenceGeom X X)]
    (diagonalClass : PrimeFiniteCorrespondenceGeom X X) :
    identityFiniteCorrespondenceQ decomposition diagonalClass =
      if diagonalClass ∈ decomposition.diagonalPrimeClasses then 1 else 0 :=
  decomposition.identityFiniteCorrespondenceQ_apply_eq_indicator diagonalClass

end

end Boundary

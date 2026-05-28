import Boundary.CompositionGeometry
import Boundary.CompositionCategory

/-!
# Represented-Prime Composition Package

This file packages descended composition on geometric prime-support classes and
the canonical builders from represented-prime composition geometry.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory Limits

namespace Boundary

open PrimeFiniteCorrespondenceSupport

noncomputable section

private theorem localTargetFactorizationOfNonemptyCompositionFiberProductDiagonal
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (x : PrimeFiniteCorrespondenceSupport.compositionFiberProduct P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) :
    ∃ toComponent : P.support ⟶ component.carrier.scheme,
      toComponent ≫ component.toAmbient = P.toTargetScheme := by
  classical
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
  letI : IsIntegral P.support := P.isIntegral
  let image : Set Y.scheme.carrier := Set.range P.toTargetScheme.base
  have hImageIrreducible : IsIrreducible image := by
    simpa [image] using
      (IrreducibleSpace.isIrreducible_univ P.support).image
        P.toTargetScheme.base P.toTargetScheme.base.continuous.continuousOn
  have hy :
      P.toTargetScheme.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x) ∈ image := by
    exact ⟨(PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x, rfl⟩
  have hycomponent :
      P.toTargetScheme.base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberFst P diag).base x) ∈
        Set.range component.toAmbient.base := by
    refine ⟨(PrimeFiniteCorrespondenceSupport.compositionFiberSnd P diag).base x, ?_⟩
    have hcond := congrArg (fun f => f.base x)
      (PrimeFiniteCorrespondenceSupport.compositionFiber_condition P diag)
    change (PrimeFiniteCorrespondenceSupport.toAmbientSource diag).base
        ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd P diag).base x) =
      P.toTargetScheme.base
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
    IsOpenImmersion.lift component.toAmbient P.toTargetScheme himage_subset
  refine ⟨toComponent, ?_⟩
  exact IsOpenImmersion.lift_fac component.toAmbient P.toTargetScheme himage_subset

private theorem localEqLandingComponentOfTargetFactorization
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y)
    (listed : SourceIrreducibleComponent Y)
    (hlisted : listed ∈ D.components)
    (toComponent : P.support ⟶ listed.carrier.scheme)
    (htoComponent : toComponent ≫ listed.toAmbient = P.toTargetScheme) :
    listed = (FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D P).1.1 := by
  classical
  let landing := FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D P
  let landingListed : SourceIrreducibleComponent Y := landing.1.1
  let landingToComponent : P.support ⟶ landingListed.carrier.scheme := landing.2.1
  have hlanding_mem : landingListed ∈ D.components := landing.1.2
  by_contra hne
  have hdisj := D.pairwise_disjoint hlisted hlanding_mem hne
  have hsource_nonempty : (Set.range P.sourceComponent.toAmbient.base).Nonempty := by
    exact P.sourceComponent.range_mem_irreducibleComponents.1.nonempty
  rcases hsource_nonempty with ⟨xAmbient, xSource, rfl⟩
  let x : P.support.carrier := Classical.choose (P.surjective_toSourceComponent xSource)
  have hx_listed : P.toTargetScheme.base x ∈ Set.range listed.toAmbient.base := by
    refine ⟨toComponent.base x, ?_⟩
    exact congrArg (fun f => f.base x) htoComponent
  have hx_landing : P.toTargetScheme.base x ∈ Set.range landingListed.toAmbient.base := by
    refine ⟨landingToComponent.base x, ?_⟩
    exact congrArg (fun f => f.base x) landing.2.2
  exact Set.disjoint_left.mp hdisj hx_listed hx_landing

private theorem localLandingComponentOfFiniteDiagonalRepresentedPrimeSupport
    {X : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition X)
    (component : SourceIrreducibleComponent X)
    (hcomponent : component ∈ D.components) :
    (FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)).1.1 = component := by
  symm
  refine localEqLandingComponentOfTargetFactorization D
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)
    component hcomponent (𝟙 component.carrier.scheme) ?_
  simp [SourceIrreducibleComponent.diagonalRepresentedPrimeSupport,
    PrimeFiniteCorrespondenceSupport.toTargetScheme]

private theorem localCompAddLeft (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left₁ left₂ : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (left₁ + left₂) right =
      FiniteCorrespondenceCompositionData.comp data left₁ right +
        FiniteCorrespondenceCompositionData.comp data left₂ right := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

private theorem localCompAddRight (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : FiniteCorrespondence X Y)
    (right₁ right₂ : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data left (right₁ + right₂) =
      FiniteCorrespondenceCompositionData.comp data left right₁ +
        FiniteCorrespondenceCompositionData.comp data left right₂ := by
  classical
  rw [FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    FiniteCorrespondenceCompositionData.comp,
    ← Finsupp.sum_add]
  congr
  ext leftPrime leftCoeff
  rw [Finsupp.sum_add_index'] <;>
    simp [mul_add, add_smul, zero_mul]

private theorem localCompSmulLeft (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data (coeff • left) right =
      coeff • FiniteCorrespondenceCompositionData.comp data left right := by
  apply Finsupp.induction_linear left
  · simp
  · intro left₁ left₂ ih₁ ih₂
    rw [smul_add, localCompAddLeft, ih₁, ih₂, ← smul_add, localCompAddLeft]
  · intro prime primeCoeff
    simp [FiniteCorrespondenceCompositionData.comp_single_left]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro rightPrime _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

private theorem localCompSmulRight (data : FiniteCorrespondenceCompositionData (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (coeff : ℤ)
    (left : FiniteCorrespondence X Y)
    (right : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp data left (coeff • right) =
      coeff • FiniteCorrespondenceCompositionData.comp data left right := by
  apply Finsupp.induction_linear right
  · simp
  · intro right₁ right₂ ih₁ ih₂
    rw [smul_add, localCompAddRight, ih₁, ih₂, ← smul_add, localCompAddRight]
  · intro prime primeCoeff
    simp [FiniteCorrespondenceCompositionData.comp_single_right]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro leftPrime _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

private def localIsoOverAmbientOfDiagonalPrimeSupportEquivalent
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D)) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  have h' :
      ∃ (compatibleSourceComponent :
          SourceIrreducibleComponent.IsoOverAmbient.CompatibleOverBaseProductIso
            (Y := X) C D)
        (_iso : C.carrier.scheme ≅ D.carrier.scheme),
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport C).inclusion ≫
            compatibleSourceComponent.iso.hom =
          _iso.hom ≫
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport D).inclusion := by
    simpa [PrimeFiniteCorrespondenceSupport.PrimeSupportEquivalent,
      PrimeFiniteCorrespondenceSupport.SupportIsoOverProduct,
      SourceIrreducibleComponent.diagonalRepresentedPrimeSupport] using h
  let compatibleSourceComponent := Classical.choose h'
  exact compatibleSourceComponent.sourceIso

private def localIsoOverAmbientOfDiagonalPrimeGeomEq
    {X : Geometry.SmSchemeOver k} {C D : SourceIrreducibleComponent X}
    (h : SourceIrreducibleComponent.diagonalPrimeGeom C =
      SourceIrreducibleComponent.diagonalPrimeGeom D) :
    SourceIrreducibleComponent.IsoOverAmbient C D := by
  exact localIsoOverAmbientOfDiagonalPrimeSupportEquivalent (Quotient.exact h)

private theorem localIsEmptyCompositionFiberProductDiagonalOfNeLandingComponent
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition Y)
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (hcomponent : component ∈ D.components)
    (hne : component ≠
      (FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D P).1.1) :
    IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) := by
  refine ⟨?_⟩
  intro x
  rcases localTargetFactorizationOfNonemptyCompositionFiberProductDiagonal P component x with
    ⟨toComponent, htoComponent⟩
  exact hne
    (localEqLandingComponentOfTargetFactorization D P component hcomponent toComponent htoComponent)

private theorem localIsEmptyCompositionFiberProductDiagonalOfNeComponent
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
      (FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)).1.1 = left :=
    localLandingComponentOfFiniteDiagonalRepresentedPrimeSupport D left hleft
  exact localIsEmptyCompositionFiberProductDiagonalOfNeLandingComponent D
    (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
    right hright (by simpa [hlanding] using hne)

private theorem localAssocScaledPrimeOfPrimeAssoc
    (data : FiniteCorrespondenceCompositionData (k := k))
    (assoc_prime :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (f : PrimeFiniteCorrespondenceGeom W X)
        (g : PrimeFiniteCorrespondenceGeom X Y)
        (h : PrimeFiniteCorrespondenceGeom Y Z),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.compPrime data f g)
            (Finsupp.single h 1) =
              FiniteCorrespondenceCompositionData.comp data
                (Finsupp.single f 1)
                (FiniteCorrespondenceCompositionData.compPrime data g h)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data
          ((fCoeff * gCoeff) • FiniteCorrespondenceCompositionData.compPrime data f g)
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f fCoeff)
              ((gCoeff * hCoeff) • FiniteCorrespondenceCompositionData.compPrime data g h) := by
  intro W X Y Z f fCoeff g gCoeff h hCoeff
  calc
    FiniteCorrespondenceCompositionData.comp data
        ((fCoeff * gCoeff) • FiniteCorrespondenceCompositionData.compPrime data f g)
        (Finsupp.single h hCoeff)
        = FiniteCorrespondenceCompositionData.comp data
            ((fCoeff * gCoeff) • FiniteCorrespondenceCompositionData.compPrime data f g)
            (hCoeff • Finsupp.single h 1) := by
              simp
    _ = hCoeff •
          FiniteCorrespondenceCompositionData.comp data
            ((fCoeff * gCoeff) • FiniteCorrespondenceCompositionData.compPrime data f g)
            (Finsupp.single h 1) := by
              rw [localCompSmulRight]
    _ = hCoeff •
          ((fCoeff * gCoeff) •
            FiniteCorrespondenceCompositionData.comp data
              (FiniteCorrespondenceCompositionData.compPrime data f g)
              (Finsupp.single h 1)) := by
                rw [localCompSmulLeft]
    _ = (fCoeff * (gCoeff * hCoeff)) •
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.compPrime data f g)
            (Finsupp.single h 1) := by
              simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = (fCoeff * (gCoeff * hCoeff)) •
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single f 1)
            (FiniteCorrespondenceCompositionData.compPrime data g h) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                congrArg (fun corr => (fCoeff * (gCoeff * hCoeff)) • corr)
                  (assoc_prime f g h)
    _ = fCoeff •
          ((gCoeff * hCoeff) •
            FiniteCorrespondenceCompositionData.comp data
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime data g h)) := by
                simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = fCoeff •
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single f 1)
            ((gCoeff * hCoeff) • FiniteCorrespondenceCompositionData.compPrime data g h) := by
                rw [← localCompSmulRight]
    _ = FiniteCorrespondenceCompositionData.comp data
          (fCoeff • Finsupp.single f 1)
          ((gCoeff * hCoeff) • FiniteCorrespondenceCompositionData.compPrime data g h) := by
              rw [← localCompSmulLeft]
    _ = FiniteCorrespondenceCompositionData.comp data
          (Finsupp.single f fCoeff)
          ((gCoeff * hCoeff) • FiniteCorrespondenceCompositionData.compPrime data g h) := by
              simp

private theorem localIdCompOfSingletonIdentities
    (data : FiniteCorrespondenceCompositionData (k := k))
    (id_comp_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (FiniteCorrespondenceCompositionData.id data X)
            (Finsupp.single prime coeff) = Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp data
      (FiniteCorrespondenceCompositionData.id data X) f = f := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    rw [localCompAddRight, hf₁, hf₂]
  · intro prime coeff
    exact id_comp_single prime coeff

private theorem localCompIdOfSingletonIdentities
    (data : FiniteCorrespondenceCompositionData (k := k))
    (comp_id_single :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
          FiniteCorrespondenceCompositionData.comp data
            (Finsupp.single prime coeff)
            (FiniteCorrespondenceCompositionData.id data Y) = Finsupp.single prime coeff)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp data
      f (FiniteCorrespondenceCompositionData.id data Y) = f := by
  apply Finsupp.induction_linear f
  · simp
  · intro f₁ f₂ hf₁ hf₂
    rw [localCompAddLeft, hf₁, hf₂]
  · intro prime coeff
    exact comp_id_single prime coeff

private theorem localIsEmptyIndexOfIsEmptyCompositionFiberProduct
    {X Y Z : Geometry.SmSchemeOver k}
    {P : RepresentedPrimeSupport X Y} {Q : RepresentedPrimeSupport Y Z}
    (decomposition : SupportFiberProductImageDecomposition P Q)
    [IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct P Q)] :
    IsEmpty decomposition.index := by
  refine ⟨fun i => ?_⟩
  let component := decomposition.component i
  have hsource_nonempty : (Set.range P.sourceComponent.toAmbient.base).Nonempty := by
    exact P.sourceComponent.range_mem_irreducibleComponents.1.nonempty
  rcases hsource_nonempty with ⟨_, xSource, rfl⟩
  let x : component.support := Classical.choose (component.surjective_toSourceComponent xSource)
  exact isEmptyElim (component.toCompositionFiberProduct.base x)

private theorem localIdentityFiniteCorrespondenceEqSumComponents
    {X : Geometry.SmSchemeOver k}
    (decomposition : FiniteIrreducibleComponentDecomposition X) :
    decomposition.identityFiniteCorrespondence =
      decomposition.components.sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
  classical
  rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
    FiniteIrreducibleComponentDecomposition.diagonalPrimeClasses]
  refine Finset.sum_image ?_
  intro C hC D hD hCD
  have hiso : SourceIrreducibleComponent.IsoOverAmbient C D := by
    exact localIsoOverAmbientOfDiagonalPrimeGeomEq hCD
  exact decomposition.no_equivalent_duplicates hC hD hiso

/-- Ground-up geometric input for finite-correspondence composition.

For represented prime supports `P : X ⟶ Y` and `Q : Y ⟶ Z`, the field
`compRepresented P Q` is a raw finite correspondence presentation on `X ×_k Z`.
Compatibility with `PrimeSupportEquivalent` ensures that this descends to a
well-defined composition on geometric prime-support classes. -/
structure RepresentedPrimeFiniteCorrespondenceComposition where
  diagonalDecomposition :
    (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X
  compRepresented :
    {X Y Z : Geometry.SmSchemeOver k} →
    RepresentedPrimeSupport X Y →
    RepresentedPrimeSupport Y Z →
    FiniteCorrespondencePresentation X Z
  respects_left :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      {P P' : RepresentedPrimeSupport X Y}
      (_h : PrimeSupportEquivalent P P')
      (Q : RepresentedPrimeSupport Y Z),
        FiniteCorrespondencePresentation.toGeom (compRepresented P Q) =
          FiniteCorrespondencePresentation.toGeom (compRepresented P' Q)
  respects_right :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y)
      {Q Q' : RepresentedPrimeSupport Y Z}
      (_h : PrimeSupportEquivalent Q Q'),
        FiniteCorrespondencePresentation.toGeom (compRepresented P Q) =
          FiniteCorrespondencePresentation.toGeom (compRepresented P Q')

namespace RepresentedPrimeFiniteCorrespondenceComposition

/-- Descended composition on geometric prime-support classes. -/
def compPrime (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (left : PrimeFiniteCorrespondenceGeom X Y)
    (right : PrimeFiniteCorrespondenceGeom Y Z) :
    FiniteCorrespondence X Z := by
  classical
  refine Quotient.liftOn left
    (fun P =>
      Quotient.liftOn right
        (fun Q => FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q))
        (by
          intro Q Q' hQQ'
          exact data.respects_right P hQQ')) ?_
  intro P P' hPP'
  refine Quotient.inductionOn right ?_
  intro Q
  exact data.respects_left hPP' Q

@[simp] theorem compPrime_ofRepresented
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z) :
    data.compPrime (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
      FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q) :=
  rfl

/-- If the represented-prime composition model uses the canonical left-identity
presentation on diagonal inputs, then composing the diagonal prime over the
source component of `P` with `P` gives back the singleton class of `P`. -/
theorem singleton_left_identity_of_diagonalFiberIso
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        data.compRepresented
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) :
    data.compPrime
        (SourceIrreducibleComponent.diagonalPrimeGeom P.sourceComponent)
        (PrimeFiniteCorrespondenceGeom.ofRepresented P) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  change data.compPrime
      (PrimeFiniteCorrespondenceGeom.ofRepresented
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent))
      (PrimeFiniteCorrespondenceGeom.ofRepresented P) =
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1
  rw [compPrime_ofRepresented, hleft P]
  exact RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition_toGeomSingle P

/-- If the represented-prime composition model uses the canonical right-identity
presentation on diagonal inputs after factoring `P.toTargetScheme` through a
chosen source component of `Y`, then composing `P` with that diagonal prime
gives back the singleton class of `P`. -/
theorem singleton_right_identity_of_diagonalFiberIso
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme) :
    data.compPrime (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (SourceIrreducibleComponent.diagonalPrimeGeom component) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1 := by
  change data.compPrime (PrimeFiniteCorrespondenceGeom.ofRepresented P)
      (PrimeFiniteCorrespondenceGeom.ofRepresented
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) =
    Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1
  rw [compPrime_ofRepresented, hright P component toComponent htoComponent]
  exact RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition_toGeomSingle
    P component toComponent htoComponent

/-- The class-level composition data induced by represented-prime composition
geometry. -/
def toFiniteCorrespondenceCompositionData
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k)) :
  FiniteCorrespondenceCompositionData (k := k) where
  diagonalDecomposition := data.diagonalDecomposition
  compPrime := data.compPrime

/-- The diagonal singleton over the source component of `P` acts by left
identity on the singleton correspondence supported on `P`, provided the
represented-prime composition model uses the canonical left-identity image
decomposition on diagonal inputs. -/
theorem comp_singleton_left_identity_of_diagonalFiberIso
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        data.compRepresented
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence P.sourceComponent)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  simp [RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData,
    SourceIrreducibleComponent.diagonalFiniteCorrespondence,
    FiniteCorrespondenceCompositionData.comp_single_single,
    singleton_left_identity_of_diagonalFiberIso data hleft P]

/-- The canonical left-identity image decomposition already computes the
singleton composition `Δ_sourceComponent(P) ∘ P = P` at the class level, with
no additional composition-law hypothesis. -/
theorem id_comp_single_of_diagonalLeftIdentityImageDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    (1 * coeff) •
        FiniteCorrespondencePresentation.toGeom
          ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition
              P)).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  rw [RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition_toGeomSingle]
  simp

/-- The diagonal singleton over a chosen source component of `Y` acts by right
identity on the singleton correspondence supported on `P`, once
`P.toTargetScheme` is factored through that component and the represented-prime
composition model uses the canonical right-identity image decomposition. -/
theorem comp_singleton_right_identity_of_diagonalFiberIso
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence component) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  simp [RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData,
    SourceIrreducibleComponent.diagonalFiniteCorrespondence,
    FiniteCorrespondenceCompositionData.comp_single_single,
    singleton_right_identity_of_diagonalFiberIso data hright P component toComponent htoComponent]

/-- The canonical diagonal-right image decomposition already computes the
singleton composition `P ∘ Δ_component = P` at the class level, with no
additional composition-law hypothesis. -/
theorem comp_id_single_of_diagonalRightIdentityImageDecomposition
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (component : SourceIrreducibleComponent Y)
    (toComponent : P.support ⟶ component.carrier.scheme)
    (htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme)
    (coeff : ℤ) :
    (coeff * 1) •
        FiniteCorrespondencePresentation.toGeom
          ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P component toComponent htoComponent)).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  rw [RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition_toGeomSingle]
  simp

/-- If one can choose a listed target component through which `P.toTargetScheme`
factors, and all other diagonal summands act by zero, then composition with the
full identity correspondence on the right acts by identity on the singleton
class of `P`. -/
theorem comp_id_single_of_component_selection_ofRepresented
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (landingComponent :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        Σ listed : { listed : SourceIrreducibleComponent Y //
            listed ∈ (data.diagonalDecomposition Y).components },
          { toComponent : P.support ⟶ listed.1.carrier.scheme //
              toComponent ≫ listed.1.toAmbient = P.toTargetScheme })
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom ((landingComponent P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  classical
  let D := data.diagonalDecomposition Y
  let landing := landingComponent P
  let listed : SourceIrreducibleComponent Y := landing.1.1
  let landingClass : PrimeFiniteCorrespondenceGeom Y Y :=
    SourceIrreducibleComponent.diagonalPrimeGeom listed
  let toComponent : P.support ⟶ listed.carrier.scheme := landing.2.1
  let htoComponent : toComponent ≫ listed.toAmbient = P.toTargetScheme := landing.2.2
  have hlisted_mem : listed ∈ D.components := landing.1.2
  have hlanding_mem : landingClass ∈ D.diagonalPrimeClasses := by
    exact (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D landingClass).2
      ⟨listed, hlisted_mem, rfl⟩
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
          Finsupp.single diagClass 1) = 0 := by
    let f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y =>
      Finsupp.single diagClass (1 : ℤ)
    have haux :
        ∀ t : Finset (PrimeFiniteCorrespondenceGeom Y Y),
          t ⊆ D.diagonalPrimeClasses.erase landingClass →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (t.sum f) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro diagClass t hnotin hIH hsub
        have hmemErase : diagClass ∈ D.diagonalPrimeClasses.erase landingClass := hsub (by simp)
        have hmem : diagClass ∈ D.diagonalPrimeClasses := (Finset.mem_erase.mp hmemErase).2
        have hneq : diagClass ≠ landingClass := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.diagonalPrimeClasses.erase landingClass := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_right,
          offComponentZero P coeff hmem hneq, hIH hsub_t]
        simp
    exact haux (D.diagonalPrimeClasses.erase landingClass) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
          (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1 := by
    simpa [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence, landingClass,
      add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D.diagonalPrimeClasses)
        (f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y => Finsupp.single diagClass (1 : ℤ))
        hlanding_mem).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
            D.identityFiniteCorrespondence := by
              rfl
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
            (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
              Finsupp.single diagClass 1) := by
                rw [hsplit]
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed) +
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1) := by
              rw [FiniteCorrespondenceCompositionData.comp_add_right]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff + 0 := by
          rw [comp_singleton_right_identity_of_diagonalFiberIso
            data hright P listed toComponent htoComponent, hoffsum]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by simp

/-- Right singleton identity using any listed target-component factorization,
while requiring off-component vanishing only with respect to the canonical
finite landing class. The landing-class uniqueness is supplied by
`DiagonalDecomposition.eq_landingComponent_of_target_factorization`. -/
theorem comp_id_single_of_component_selection_against_finite_landing_ofRepresented
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (_landingComponent :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        Σ listed : { listed : SourceIrreducibleComponent Y //
            listed ∈ (data.diagonalDecomposition Y).components },
          { toComponent : P.support ⟶ listed.1.carrier.scheme //
              toComponent ≫ listed.1.toAmbient = P.toTargetScheme })
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (data.diagonalDecomposition Y) P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  let canonicalLandingComponent :=
    fun {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) =>
      FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
        (data.diagonalDecomposition Y) P
  exact comp_id_single_of_component_selection_ofRepresented
    data canonicalLandingComponent
      (fun {X Y} P coeff {diagClass} hmem hneq => offComponentZero P coeff hmem hneq)
      hright P coeff

/-- Right singleton identity using the canonical landing-component choice
provided by the selected finite irreducible-component decomposition. -/
theorem comp_id_single_of_finite_landingComponent_ofRepresented
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (data.diagonalDecomposition Y) P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  exact comp_id_single_of_component_selection_ofRepresented
    data
    (fun {X Y} P =>
      FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
        (data.diagonalDecomposition Y) P)
    offComponentZero hright P coeff

/-- Quotient-level right singleton identity derived from a choice of landing
component for each represented prime support together with off-component
vanishing. This matches the `comp_id_single` hypothesis required by
`FiniteCorrespondenceCategoryLaws.ofSingletonLaws`. -/
theorem comp_id_single_of_component_selection
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (landingComponent :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        Σ listed : { listed : SourceIrreducibleComponent Y //
            listed ∈ (data.diagonalDecomposition Y).components },
          { toComponent : P.support ⟶ listed.1.carrier.scheme //
              toComponent ≫ listed.1.toAmbient = P.toTargetScheme })
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom ((landingComponent P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  classical
  refine Quotient.inductionOn prime ?_
  intro P
  exact comp_id_single_of_component_selection_ofRepresented
    data landingComponent offComponentZero hright P coeff

/-- Quotient-level right singleton identity using any listed target-component
factorization, with off-component vanishing stated only against the canonical
finite landing class. -/
theorem comp_id_single_of_component_selection_against_finite_landing
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (landingComponent :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y),
        Σ listed : { listed : SourceIrreducibleComponent Y //
            listed ∈ (data.diagonalDecomposition Y).components },
          { toComponent : P.support ⟶ listed.1.carrier.scheme //
              toComponent ≫ listed.1.toAmbient = P.toTargetScheme })
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (data.diagonalDecomposition Y) P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact comp_id_single_of_component_selection_against_finite_landing_ofRepresented
    data landingComponent offComponentZero hright P coeff

/-- Quotient-level right singleton identity using the canonical landing
component constructed from the chosen finite irreducible-component
decomposition. -/
theorem comp_id_single_of_finite_landingComponent
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (offComponentZero :
      ∀ {X Y : Geometry.SmSchemeOver k} (P : RepresentedPrimeSupport X Y) (coeff : ℤ)
        {diagClass : PrimeFiniteCorrespondenceGeom Y Y},
          diagClass ∈ (data.diagonalDecomposition Y).diagonalPrimeClasses →
          diagClass ≠
            SourceIrreducibleComponent.diagonalPrimeGeom
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (data.diagonalDecomposition Y) P).1.1) →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (Finsupp.single diagClass 1) = 0)
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          data.compRepresented P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact comp_id_single_of_finite_landingComponent_ofRepresented
    data offComponentZero hright P coeff

/-- If a chosen left-associated triple image decomposition computes the two
nested singleton compositions on represented supports, then the coefficient-free
prime associativity statement follows for those represented inputs. -/
theorem assoc_prime_of_tripleImagePresentation_ofRepresented
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom (data.compRepresented Q R)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R))
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X)
    (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.compPrime data.toFiniteCorrespondenceCompositionData
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q))
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondenceCompositionData.compPrime data.toFiniteCorrespondenceCompositionData
            (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
            (PrimeFiniteCorrespondenceGeom.ofRepresented R)) := by
  have hcompPQ :
      FiniteCorrespondenceCompositionData.compPrime data.toFiniteCorrespondenceCompositionData
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
          FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q) := by
    change data.compPrime (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q) =
      FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q)
    exact compPrime_ofRepresented data P Q
  have hcompQR :
      FiniteCorrespondenceCompositionData.compPrime data.toFiniteCorrespondenceCompositionData
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
        (PrimeFiniteCorrespondenceGeom.ofRepresented R) =
          FiniteCorrespondencePresentation.toGeom (data.compRepresented Q R) := by
    change data.compPrime (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
        (PrimeFiniteCorrespondenceGeom.ofRepresented R) =
      FiniteCorrespondencePresentation.toGeom (data.compRepresented Q R)
    exact compPrime_ofRepresented data Q R
  rw [hcompPQ, hcompQR]
  rw [hleft P Q R, hright P Q R]
  exact
    (congrArg FiniteCorrespondencePresentation.toGeom
      (hpresentation P Q R)).symm

/-- Quotient-level coefficient-free prime associativity follows once the two
nested singleton compositions are computed by the left and right presentations
of a chosen triple image decomposition. -/
theorem assoc_prime_of_tripleImagePresentation
    (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom (data.compRepresented Q R)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X)
      (g : PrimeFiniteCorrespondenceGeom X Y)
      (h : PrimeFiniteCorrespondenceGeom Y Z),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            data.toFiniteCorrespondenceCompositionData f g)
          (Finsupp.single h 1) =
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime
                data.toFiniteCorrespondenceCompositionData g h) := by
  intro W X Y Z f g h
  refine Quotient.inductionOn f ?_
  intro P
  refine Quotient.inductionOn g ?_
  intro Q
  refine Quotient.inductionOn h ?_
  intro R
  simpa [FiniteCorrespondenceCompositionData.comp_single_single,
    PrimeFiniteCorrespondenceGeom.ofRepresented] using
    assoc_prime_of_tripleImagePresentation_ofRepresented
      data leftPresentation rightPresentation hpresentation hleft hright P Q R

/-- Bundle a represented-prime composition law package into `SmCor(k)` once the
singleton identity and associativity laws are available at class level. -/
def toSmCorOfSingletonLaws
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
  (id_comp_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
          (Finsupp.single prime coeff) =
            Finsupp.single prime coeff)
  (comp_id_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single prime coeff)
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
            Finsupp.single prime coeff)
  (assoc_single :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single f fCoeff) (Finsupp.single g gCoeff))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single f fCoeff)
              (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
                (Finsupp.single g gCoeff) (Finsupp.single h hCoeff))) :
  SmCor (k := k) :=
    ⟨data.toFiniteCorrespondenceCompositionData,
      FiniteCorrespondenceCategoryLaws.ofSingletonLaws
        data.toFiniteCorrespondenceCompositionData
        id_comp_single comp_id_single assoc_single⟩

/-- A represented-prime composition package yields `SmCor(k)` once the
singleton identity laws are known and the geometric associativity problem is
solved in the scaled prime-level form from
`FiniteCorrespondenceCompositionData.assoc_single_of_scaled_prime_assoc`. -/
def toSmCorOfScaledPrimeAssoc
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
  (id_comp_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
          (Finsupp.single prime coeff) =
            Finsupp.single prime coeff)
  (comp_id_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single prime coeff)
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
            Finsupp.single prime coeff)
  (assoc_scaled_prime :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          ((fCoeff * gCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime
              data.toFiniteCorrespondenceCompositionData f g))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single f fCoeff)
              ((gCoeff * hCoeff) •
                (FiniteCorrespondenceCompositionData.compPrime
                  data.toFiniteCorrespondenceCompositionData g h))) :
  SmCor (k := k) :=
    toSmCorOfSingletonLaws data id_comp_single comp_id_single
      (by
        intro W X Y Z f fCoeff g gCoeff h hCoeff
        simpa [FiniteCorrespondenceCompositionData.comp_single_single] using
          assoc_scaled_prime f fCoeff g gCoeff h hCoeff)

/-- A represented-prime composition package yields `SmCor(k)` once the
singleton identity laws are known and the geometric associativity problem is
solved in the coefficient-free prime-level form. Bilinearity upgrades that
statement to the scaled prime-level bridge automatically. -/
def toSmCorOfPrimeAssoc
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
  (id_comp_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
          (Finsupp.single prime coeff) =
            Finsupp.single prime coeff)
  (comp_id_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single prime coeff)
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
            Finsupp.single prime coeff)
  (assoc_prime :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X)
      (g : PrimeFiniteCorrespondenceGeom X Y)
      (h : PrimeFiniteCorrespondenceGeom Y Z),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            data.toFiniteCorrespondenceCompositionData f g)
          (Finsupp.single h 1) =
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime
                data.toFiniteCorrespondenceCompositionData g h)) :
  SmCor (k := k) :=
    toSmCorOfScaledPrimeAssoc data id_comp_single comp_id_single
      (localAssocScaledPrimeOfPrimeAssoc
        data.toFiniteCorrespondenceCompositionData assoc_prime)

/-- A represented-prime composition package yields `SmCor(k)` once singleton
identity laws are known and both nested singleton compositions are computed by
the left and right presentations of a chosen left-associated triple image
decomposition. The geometric associativity bridge is supplied by
`assoc_prime_of_tripleImagePresentation`. -/
def toSmCorOfTripleImagePresentation
  (data : RepresentedPrimeFiniteCorrespondenceComposition (k := k))
  (id_comp_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
          (Finsupp.single prime coeff) =
            Finsupp.single prime coeff)
  (comp_id_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single prime coeff)
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
            Finsupp.single prime coeff)
  (leftPresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k},
      RepresentedPrimeSupport W X →
      RepresentedPrimeSupport X Y →
      RepresentedPrimeSupport Y Z →
        FiniteCorrespondencePresentation W Z)
  (rightPresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k},
      RepresentedPrimeSupport W X →
      RepresentedPrimeSupport X Y →
      RepresentedPrimeSupport Y Z →
        FiniteCorrespondencePresentation W Z)
  (hpresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        rightPresentation P Q R = leftPresentation P Q R)
  (hleft :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondencePresentation.toGeom (data.compRepresented P Q))
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
            FiniteCorrespondencePresentation.toGeom
              (leftPresentation P Q R))
  (hright :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondencePresentation.toGeom (data.compRepresented Q R)) =
            FiniteCorrespondencePresentation.toGeom
              (rightPresentation P Q R)) :
  SmCor (k := k) :=
    toSmCorOfPrimeAssoc data id_comp_single comp_id_single
      (assoc_prime_of_tripleImagePresentation
        data leftPresentation rightPresentation hpresentation hleft hright)

end RepresentedPrimeFiniteCorrespondenceComposition

/-- Build represented-prime composition from support-level geometric
composition data. For each pair `P, Q`, the datum is a finite family of
integral pieces over `P.support ×_Y Q.support`; `compRepresented` is the sum of
their weighted prime-support contributions on `X ×_k Z`. -/
def RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (datum :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      RepresentedPrimeCompositionDatum P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom ((datum P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((datum P' Q).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom ((datum P Q).toPresentation) =
            FiniteCorrespondencePresentation.toGeom ((datum P Q').toPresentation)) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) := by
  refine
    { diagonalDecomposition := diagonalDecomposition
      compRepresented := fun P Q => (datum P Q).toPresentation
      respects_left := ?_
      respects_right := ?_ }
  · intro X Y Z P P' h Q
    exact respects_left h Q
  · intro X Y Z P Q Q' h
    exact respects_right P h

/-- Build represented-prime composition directly from finite integral
decompositions of the scheme-theoretic images of the canonical support fiber
product maps `P.support ×_Y Q.support → sourceComponent(P) ×_k Z`. -/
def RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation)) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) :=
  RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum
    diagonalDecomposition
    (fun P Q =>
      RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (decomposition P Q))
    respects_left respects_right

/-- Build represented-prime composition directly from support-fiber-product
image decompositions, with the compatibility hypotheses stated on the honest
geometric presentations `decomposition P Q |>.toPresentation` rather than on
the intermediate composition-datum wrapper. -/
def RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q'))) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) :=
  RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
    diagonalDecomposition decomposition
    (fun {X Y Z} {P P'} h Q => by
      simpa using respects_left h Q)
    (fun {X Y Z} P {Q Q'} h => by
      simpa using respects_right P h)

namespace RepresentedPrimeFiniteCorrespondenceComposition

/-- For a support-fiber-product image-decomposition builder, it is enough to
know that the chosen decomposition agrees with the canonical diagonal-left
singleton decomposition on diagonal-left inputs; no global `hleft` hypothesis
is needed in that case. -/
theorem id_comp_single_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence P.sourceComponent)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact comp_singleton_left_identity_of_diagonalFiberIso
    data
    (fun {X Y} P => by
      simpa [data,
        RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition,
        RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum] using
        congrArg
          (fun dec =>
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              dec).toPresentation)
          (source_eq_diagonalLeftIdentity P))
    P coeff

/-- Quotient-level left singleton identity for the concrete
support-fiber-product image-decomposition builder, assuming only that the
chosen left-diagonal decomposition has the canonical presentation. -/
theorem id_comp_single_ofSupportFiberProductImageDecomposition_ofRepresented
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
              P)).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence P.sourceComponent)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact comp_singleton_left_identity_of_diagonalFiberIso
    data
    (fun {X Y} P => by
      simpa [data,
        RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition,
        RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum] using
        hleft P)
    P coeff

/-- For the concrete composition model built from support-fiber-product image
decompositions, if the chosen decomposition for `(P, Q)` has empty index then
the corresponding singleton composition is zero. This variant fixes the left
coefficient to `1` and leaves the right coefficient arbitrary. -/
theorem comp_singleton_left_eq_zero_of_isEmpty_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z)
    (coeff : ℤ)
    [IsEmpty (decomposition P Q).index] :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Q) coeff) = 0 := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  rw [FiniteCorrespondenceCompositionData.comp_single_single]
  change (1 * coeff) • FiniteCorrespondencePresentation.toGeom
      ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (decomposition P Q)).toPresentation) = 0
  rw [RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition_toPresentation_eq_zero_of_isEmpty]
  simp

/-- Concrete left off-component vanishing for the composition model built from
support-fiber-product image decompositions: if a diagonal class of the chosen
source decomposition is not the listed source component attached to `P`, then
the corresponding singleton composition vanishes. -/
theorem offSourceComponentZero_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ)
    {diagClass : PrimeFiniteCorrespondenceGeom X X}
    (hmem : diagClass ∈ (diagonalDecomposition X).diagonalPrimeClasses)
    (hneq :
      diagClass ≠
        SourceIrreducibleComponent.diagonalPrimeGeom
          ((diagonalDecomposition X).exhaustive P.sourceComponent).1.1) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single diagClass 1)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) = 0 := by
  classical
  let D := diagonalDecomposition X
  let listed : SourceIrreducibleComponent X := (D.exhaustive P.sourceComponent).1.1
  let hiso : SourceIrreducibleComponent.IsoOverAmbient P.sourceComponent listed :=
    (D.exhaustive P.sourceComponent).2
  have hlisted_mem : listed ∈ D.components := (D.exhaustive P.sourceComponent).1.2
  rcases (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D diagClass).mp hmem with
    ⟨component, hcomponent, hdiag⟩
  have hcomponent_ne : component ≠ listed := by
    intro hcomp
    apply hneq
    calc
      diagClass = SourceIrreducibleComponent.diagonalPrimeGeom component := hdiag.symm
      _ = SourceIrreducibleComponent.diagonalPrimeGeom listed := by simp [hcomp]
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
  haveI : IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct diag P) := by
    refine ⟨?_⟩
    intro x
    have hdisj := D.pairwise_disjoint hcomponent hlisted_mem hcomponent_ne
    have hy_component :
        P.toAmbientSource.base
            ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x) ∈
          Set.range component.toAmbient.base := by
      refine ⟨(PrimeFiniteCorrespondenceSupport.compositionFiberFst diag P).base x, ?_⟩
      change diag.toTargetScheme.base
          ((PrimeFiniteCorrespondenceSupport.compositionFiberFst diag P).base x) =
        P.toAmbientSource.base
          ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x)
      exact congrArg (fun f => f.base x)
        (PrimeFiniteCorrespondenceSupport.compositionFiber_condition diag P)
    have hy_listed :
        P.toAmbientSource.base
            ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x) ∈
          Set.range listed.toAmbient.base := by
      refine ⟨hiso.iso.hom.base
          (P.toSourceComponent.base
            ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x)), ?_⟩
      have hambient := congrArg
        (fun f =>
          f.base
            (P.toSourceComponent.base
              ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x)))
        hiso.hom_toAmbient
      calc
        listed.toAmbient.base
            (hiso.iso.hom.base
              (P.toSourceComponent.base
                ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x)))
            = P.sourceComponent.toAmbient.base
                (P.toSourceComponent.base
                  ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x)) := by
                    simpa [Category.assoc] using hambient
        _ = P.toAmbientSource.base
              ((PrimeFiniteCorrespondenceSupport.compositionFiberSnd diag P).base x) := by
              simp [PrimeFiniteCorrespondenceSupport.toAmbientSource, Category.assoc]
    exact Set.disjoint_left.mp hdisj hy_component hy_listed
  haveI : IsEmpty (decomposition diag P).index :=
    localIsEmptyIndexOfIsEmptyCompositionFiberProduct
      (decomposition diag P)
  rw [← hdiag]
  simpa [SourceIrreducibleComponent.diagonalFiniteCorrespondence,
    SourceIrreducibleComponent.diagonalRepresentedPrimeSupport] using
    comp_singleton_left_eq_zero_of_isEmpty_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right diag P coeff

/-- Quotient-level left singleton identity for the concrete
support-fiber-product image-decomposition builder, assuming only the canonical
diagonal left-identity presentation on diagonal inputs. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  classical
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  let D := diagonalDecomposition X
  let listed : SourceIrreducibleComponent X := (D.exhaustive P.sourceComponent).1.1
  let hiso : SourceIrreducibleComponent.IsoOverAmbient P.sourceComponent listed :=
    (D.exhaustive P.sourceComponent).2
  let sourceClass : PrimeFiniteCorrespondenceGeom X X :=
    SourceIrreducibleComponent.diagonalPrimeGeom listed
  have hlisted_mem : listed ∈ D.components := (D.exhaustive P.sourceComponent).1.2
  have hsource_singleton :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
          Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
    rw [← SourceIrreducibleComponent.diagonalFiniteCorrespondence_eq_of_isoOverAmbient hiso]
    exact id_comp_single_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition respects_left respects_right
      source_eq_diagonalLeftIdentity P coeff
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        ((D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
          Finsupp.single diagClass 1)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) = 0 := by
    let f := fun diagClass : PrimeFiniteCorrespondenceGeom X X =>
      Finsupp.single diagClass (1 : ℤ)
    have haux :
        ∀ t : Finset (PrimeFiniteCorrespondenceGeom X X),
          t ⊆ D.diagonalPrimeClasses.erase sourceClass →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (t.sum f)
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro diagClass t hnotin hIH hsub
        have hmemErase : diagClass ∈ D.diagonalPrimeClasses.erase sourceClass := hsub (by simp)
        have hmem : diagClass ∈ D.diagonalPrimeClasses := (Finset.mem_erase.mp hmemErase).2
        have hneq : diagClass ≠ sourceClass := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.diagonalPrimeClasses.erase sourceClass := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_left,
          offSourceComponentZero_ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right
            P coeff hmem hneq, hIH hsub_t]
        simp
    exact haux (D.diagonalPrimeClasses.erase sourceClass) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
          (D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
            Finsupp.single diagClass 1 := by
    have hsource_mem : sourceClass ∈ D.diagonalPrimeClasses := by
      exact (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D sourceClass).2
        ⟨listed, hlisted_mem, rfl⟩
    simpa [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence, sourceClass,
      add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D.diagonalPrimeClasses)
        (f := fun diagClass : PrimeFiniteCorrespondenceGeom X X => Finsupp.single diagClass (1 : ℤ))
        hsource_mem).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            D.identityFiniteCorrespondence
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
              rfl
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
            (D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
              Finsupp.single diagClass 1)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
            rw [hsplit]
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) +
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          ((D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
            Finsupp.single diagClass 1)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
            rw [FiniteCorrespondenceCompositionData.comp_add_left]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff + 0 := by
          rw [hsource_singleton, hoffsum]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by simp

/-- Quotient-level left singleton identity for the concrete
support-fiber-product image-decomposition builder on represented supports,
assuming only the canonical diagonal left-identity presentation on diagonal
inputs. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_ofRepresented
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
              P)).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  classical
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  let D := diagonalDecomposition X
  let listed : SourceIrreducibleComponent X := (D.exhaustive P.sourceComponent).1.1
  let hiso : SourceIrreducibleComponent.IsoOverAmbient P.sourceComponent listed :=
    (D.exhaustive P.sourceComponent).2
  let sourceClass : PrimeFiniteCorrespondenceGeom X X :=
    SourceIrreducibleComponent.diagonalPrimeGeom listed
  have hlisted_mem : listed ∈ D.components := (D.exhaustive P.sourceComponent).1.2
  have hsource_singleton :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) =
          Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
    rw [← SourceIrreducibleComponent.diagonalFiniteCorrespondence_eq_of_isoOverAmbient hiso]
    exact id_comp_single_ofSupportFiberProductImageDecomposition_ofRepresented
      diagonalDecomposition decomposition respects_left respects_right
      hleft P coeff
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        ((D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
          Finsupp.single diagClass 1)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) = 0 := by
    let f := fun diagClass : PrimeFiniteCorrespondenceGeom X X =>
      Finsupp.single diagClass (1 : ℤ)
    have haux :
        ∀ t : Finset (PrimeFiniteCorrespondenceGeom X X),
          t ⊆ D.diagonalPrimeClasses.erase sourceClass →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (t.sum f)
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro diagClass t hnotin hIH hsub
        have hmemErase : diagClass ∈ D.diagonalPrimeClasses.erase sourceClass := hsub (by simp)
        have hmem : diagClass ∈ D.diagonalPrimeClasses := (Finset.mem_erase.mp hmemErase).2
        have hneq : diagClass ≠ sourceClass := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.diagonalPrimeClasses.erase sourceClass := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_left,
          offSourceComponentZero_ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right
            P coeff hmem hneq, hIH hsub_t]
        simp
    exact haux (D.diagonalPrimeClasses.erase sourceClass) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
          (D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
            Finsupp.single diagClass 1 := by
    have hsource_mem : sourceClass ∈ D.diagonalPrimeClasses := by
      exact (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D sourceClass).2
        ⟨listed, hlisted_mem, rfl⟩
    simpa [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence, sourceClass,
      add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D.diagonalPrimeClasses)
        (f := fun diagClass : PrimeFiniteCorrespondenceGeom X X => Finsupp.single diagClass (1 : ℤ))
        hsource_mem).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            D.identityFiniteCorrespondence
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
              rfl
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
            (D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
              Finsupp.single diagClass 1)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
            rw [hsplit]
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) +
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          ((D.diagonalPrimeClasses.erase sourceClass).sum fun diagClass =>
            Finsupp.single diagClass 1)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff) := by
            rw [FiniteCorrespondenceCompositionData.comp_add_left]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff + 0 := by
          rw [hsource_singleton, hoffsum]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by simp

/-- Quotient-level left singleton identity for the concrete
support-fiber-product image-decomposition builder, assuming only the canonical
diagonal left-identity presentation on diagonal inputs. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
              P)).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single prime coeff) = Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_ofRepresented
    diagonalDecomposition decomposition respects_left respects_right
    hleft
    P coeff

/-- Quotient-level left singleton identity for the concrete builder, with all
compatibility hypotheses stated directly on
`SupportFiberProductImageDecomposition.toPresentation`. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImagePresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          SupportFiberProductImageDecomposition.toPresentation
              (decomposition
                (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P) =
            FiniteCorrespondencePresentation.ofPrimeSupport P)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single prime coeff) = Finsupp.single prime coeff := by
  simpa using
    (id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      (fun P => by
        simpa using hleft P)
      prime coeff)

/-- Left diagonal identity for arbitrary finite correspondences, provided the
chosen builder uses the canonical diagonal-left presentation on represented
prime inputs. This is the formal-sum extension of the represented-prime left
identity theorem. -/
theorem id_comp_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hleft :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
              P)).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      f = f := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact localIdCompOfSingletonIdentities
    data.toFiniteCorrespondenceCompositionData
    (fun {X Y} prime coeff => by
      simpa [data] using
        id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right
          hleft prime coeff)
    f

/-- Quotient-level left singleton identity for any builder whose chosen
source-side diagonal decomposition agrees with the canonical
`diagonalLeftIdentityImageDecomposition`. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single prime coeff) = Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalLeftIdentity
    diagonalDecomposition decomposition respects_left respects_right
    source_eq_diagonalLeftIdentity P coeff

/-- Quotient-level left singleton identity for the concrete builder, with
compatibility hypotheses stated directly on
`SupportFiberProductImageDecomposition.toPresentation`. -/
theorem id_comp_single_of_exhaustive_source_ofSupportFiberProductImagePresentation_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      (Finsupp.single prime coeff) = Finsupp.single prime coeff := by
  simpa using
    (id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      source_eq_diagonalLeftIdentity prime coeff)

/-- Left diagonal identity for arbitrary finite correspondences, provided the
chosen builder uses the canonical diagonal-left decomposition on represented
prime inputs. This is the formal-sum extension of the represented-prime left
identity theorem. -/
theorem id_comp_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      f = f := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact localIdCompOfSingletonIdentities
    data.toFiniteCorrespondenceCompositionData
    (fun {X Y} prime coeff => by
      simpa [data] using
        id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
          diagonalDecomposition decomposition respects_left respects_right
          source_eq_diagonalLeftIdentity prime coeff)
    f

/-- Left diagonal identity for arbitrary finite correspondences, with
compatibility hypotheses stated directly on the honest geometric
presentations `SupportFiberProductImageDecomposition.toPresentation`. -/
theorem id_comp_ofSupportFiberProductImagePresentation_of_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData X)
      f = f := by
  simpa using
    (id_comp_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      source_eq_diagonalLeftIdentity f)

/-- For the concrete composition model built from support-fiber-product image
decompositions, if the chosen decomposition for `(P, Q)` has empty index then
the corresponding singleton composition is zero. -/
theorem comp_singleton_right_eq_zero_of_isEmpty_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z)
    (coeff : ℤ)
    [IsEmpty (decomposition P Q).index] :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented Q) 1) = 0 := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  rw [FiniteCorrespondenceCompositionData.comp_single_single]
  change (coeff * 1) • FiniteCorrespondencePresentation.toGeom
      ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (decomposition P Q)).toPresentation) = 0
  rw [RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition_toPresentation_eq_zero_of_isEmpty]
  simp

/-- Distinct listed diagonal singleton correspondences compose to zero for the
concrete support-fiber-product image-decomposition builder. This is the
orthogonal-projector vanishing relation at the singleton level. -/
theorem comp_diagonalFiniteCorrespondence_eq_zero_of_ne_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    {X : Geometry.SmSchemeOver k}
    (left right : SourceIrreducibleComponent X)
    (hleft : left ∈ (diagonalDecomposition X).components)
    (hright : right ∈ (diagonalDecomposition X).components)
    (hne : right ≠ left) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence left)
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence right) = 0 := by
  haveI : IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport right)) :=
    localIsEmptyCompositionFiberProductDiagonalOfNeComponent
      (diagonalDecomposition X) left right hleft hright hne
  haveI : IsEmpty
      (decomposition
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport right)).index :=
    localIsEmptyIndexOfIsEmptyCompositionFiberProduct
      (decomposition
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport right))
  simpa [SourceIrreducibleComponent.diagonalFiniteCorrespondence] using
    comp_singleton_right_eq_zero_of_isEmpty_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport left)
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport right)
      (1 : ℤ)



/-- Concrete off-component vanishing for the composition model built from
support-fiber-product image decompositions: if a diagonal class is not the
canonical finite landing class of `P`, then the corresponding singleton
composition vanishes. -/
theorem offComponentZero_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ)
    {diagClass : PrimeFiniteCorrespondenceGeom Y Y}
    (hmem : diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses)
    (hneq :
      diagClass ≠
        SourceIrreducibleComponent.diagonalPrimeGeom
          ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
            (diagonalDecomposition Y) P).1.1)) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (Finsupp.single diagClass 1) = 0 := by
  classical
  rcases (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff
      (diagonalDecomposition Y) diagClass).mp hmem with ⟨component, hcomponent, hdiag⟩
  have hcomponent_ne :
      component ≠
        (FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
          (diagonalDecomposition Y) P).1.1 := by
    intro hcomp
    apply hneq
    rw [← hdiag, hcomp]
  haveI : IsEmpty (PrimeFiniteCorrespondenceSupport.compositionFiberProduct P
      (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)) :=
    localIsEmptyCompositionFiberProductDiagonalOfNeLandingComponent
      (diagonalDecomposition Y) P component hcomponent hcomponent_ne
  haveI : IsEmpty
      (decomposition P (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component)).index :=
    localIsEmptyIndexOfIsEmptyCompositionFiberProduct
      (decomposition P (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component))
  rw [← hdiag]
  simpa [SourceIrreducibleComponent.diagonalFiniteCorrespondence] using
    comp_singleton_right_eq_zero_of_isEmpty_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
      P (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component) coeff

/-- For the concrete composition model built from support-fiber-product image
decompositions, right singleton identity follows from the canonical diagonal
right-identity presentation on diagonal inputs; off-component vanishing is
derived automatically from pullback emptiness. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component))).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact comp_id_single_of_finite_landingComponent_ofRepresented
    data
    (offComponentZero_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right)
    (fun {X Y} P component toComponent htoComponent => by
      simpa [data,
        RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition,
        RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum] using
        hright P component toComponent htoComponent)
    P coeff

/-- For a support-fiber-product image-decomposition builder, it is enough to
know that the chosen decomposition agrees with the canonical diagonal-right
singleton decomposition on the finite landing component of each `P`; no global
`hright` hypothesis is needed in that case. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  classical
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  let D := diagonalDecomposition Y
  let landing :=
    FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D P
  let listed : SourceIrreducibleComponent Y := landing.1.1
  let landingClass : PrimeFiniteCorrespondenceGeom Y Y :=
    SourceIrreducibleComponent.diagonalPrimeGeom listed
  let toComponent : P.support ⟶ listed.carrier.scheme := landing.2.1
  let htoComponent : toComponent ≫ listed.toAmbient = P.toTargetScheme := landing.2.2
  have hlisted_mem : listed ∈ D.components := landing.1.2
  have hlanding_mem : landingClass ∈ D.diagonalPrimeClasses := by
    exact (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D landingClass).2
      ⟨listed, hlisted_mem, rfl⟩
  have hdiag_presentation :
      (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (decomposition P
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport listed))).toPresentation =
        (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
            P listed toComponent htoComponent)).toPresentation := by
    simpa [D, landing, listed, toComponent, htoComponent] using congrArg
      (fun dec =>
        (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition dec).toPresentation)
      (landing_eq_diagonalRightIdentity P)
  have hlanding_singleton :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed) =
          Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
    simp [RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence,
      FiniteCorrespondenceCompositionData.comp_single_single]
    change coeff •
        FiniteCorrespondencePresentation.toGeom
          ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport listed))).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff
    rw [hdiag_presentation]
    simpa using comp_id_single_of_diagonalRightIdentityImageDecomposition
      P listed toComponent htoComponent coeff
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
          Finsupp.single diagClass 1) = 0 := by
    let f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y =>
      Finsupp.single diagClass (1 : ℤ)
    have haux :
        ∀ t : Finset (PrimeFiniteCorrespondenceGeom Y Y),
          t ⊆ D.diagonalPrimeClasses.erase landingClass →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (t.sum f) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro diagClass t hnotin hIH hsub
        have hmemErase : diagClass ∈ D.diagonalPrimeClasses.erase landingClass := hsub (by simp)
        have hmem : diagClass ∈ D.diagonalPrimeClasses := (Finset.mem_erase.mp hmemErase).2
        have hneq : diagClass ≠ landingClass := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.diagonalPrimeClasses.erase landingClass := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_right,
          offComponentZero_ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right
            P coeff hmem hneq, hIH hsub_t]
        simp
    exact haux (D.diagonalPrimeClasses.erase landingClass) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
          (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1 := by
    simpa [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence, landingClass,
      add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D.diagonalPrimeClasses)
        (f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y => Finsupp.single diagClass (1 : ℤ))
        hlanding_mem).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
            D.identityFiniteCorrespondence := by
              rfl
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
            (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
              Finsupp.single diagClass 1) := by
                rw [hsplit]
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed) +
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1) := by
              rw [FiniteCorrespondenceCompositionData.comp_add_right]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff + 0 := by
          rw [hlanding_singleton, hoffsum]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by simp

/-- Represented-prime right singleton identity for the concrete
support-fiber-product image-decomposition builder, assuming only the canonical
diagonal right-identity presentation on the finite landing component. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented_of_diagonalRightPresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_presentation :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)))).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.2))).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
  classical
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  let D := diagonalDecomposition Y
  let landing :=
    FiniteIrreducibleComponentDecomposition.landingComponent_of_finite D P
  let listed : SourceIrreducibleComponent Y := landing.1.1
  let landingClass : PrimeFiniteCorrespondenceGeom Y Y :=
    SourceIrreducibleComponent.diagonalPrimeGeom listed
  let toComponent : P.support ⟶ listed.carrier.scheme := landing.2.1
  let htoComponent : toComponent ≫ listed.toAmbient = P.toTargetScheme := landing.2.2
  have hlisted_mem : listed ∈ D.components := landing.1.2
  have hlanding_mem : landingClass ∈ D.diagonalPrimeClasses := by
    exact (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D landingClass).2
      ⟨listed, hlisted_mem, rfl⟩
  have hdiag_presentation :
      (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
        (decomposition P
          (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport listed))).toPresentation =
        (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
          (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
            P listed toComponent htoComponent)).toPresentation := by
    simpa [D, landing, listed, toComponent, htoComponent] using landing_presentation P
  have hlanding_singleton :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed) =
          Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by
    simp [RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence,
      FiniteCorrespondenceCompositionData.comp_single_single]
    change coeff •
        FiniteCorrespondencePresentation.toGeom
          ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport listed))).toPresentation) =
      Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff
    rw [hdiag_presentation]
    simpa using comp_id_single_of_diagonalRightIdentityImageDecomposition
      P listed toComponent htoComponent coeff
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
          Finsupp.single diagClass 1) = 0 := by
    let f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y =>
      Finsupp.single diagClass (1 : ℤ)
    have haux :
        ∀ t : Finset (PrimeFiniteCorrespondenceGeom Y Y),
          t ⊆ D.diagonalPrimeClasses.erase landingClass →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
              (t.sum f) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro diagClass t hnotin hIH hsub
        have hmemErase : diagClass ∈ D.diagonalPrimeClasses.erase landingClass := hsub (by simp)
        have hmem : diagClass ∈ D.diagonalPrimeClasses := (Finset.mem_erase.mp hmemErase).2
        have hneq : diagClass ≠ landingClass := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.diagonalPrimeClasses.erase landingClass := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_right,
          offComponentZero_ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right
            P coeff hmem hneq, hIH hsub_t]
        simp
    exact haux (D.diagonalPrimeClasses.erase landingClass) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
          (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1 := by
    simpa [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence,
      SourceIrreducibleComponent.diagonalFiniteCorrespondence, landingClass,
      add_comm, add_left_comm, add_assoc] using
      (Finset.sum_erase_add (s := D.diagonalPrimeClasses)
        (f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y => Finsupp.single diagClass (1 : ℤ))
        hlanding_mem).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
            D.identityFiniteCorrespondence := by
              rfl
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed +
            (D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
              Finsupp.single diagClass 1) := by
                rw [hsplit]
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          (SourceIrreducibleComponent.diagonalFiniteCorrespondence listed) +
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff)
          ((D.diagonalPrimeClasses.erase landingClass).sum fun diagClass =>
            Finsupp.single diagClass 1) := by
              rw [FiniteCorrespondenceCompositionData.comp_add_right]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff + 0 := by
          rw [hlanding_singleton, hoffsum]
    _ = Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) coeff := by simp

/-- Quotient-level right singleton identity for the concrete
support-fiber-product image-decomposition builder, assuming only the canonical
diagonal right-identity presentation on diagonal inputs. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (hright :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        (component : SourceIrreducibleComponent Y)
        (toComponent : P.support ⟶ component.carrier.scheme)
        (_htoComponent : toComponent ≫ component.toAmbient = P.toTargetScheme),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component))).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P component toComponent _htoComponent)).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact comp_id_single_of_finite_landingComponent
    data
    (offComponentZero_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right)
    (fun {X Y} P component toComponent htoComponent => by
      simpa [data,
        RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition,
        RepresentedPrimeFiniteCorrespondenceComposition.ofCompositionDatum] using
        hright P component toComponent htoComponent)
    prime coeff

/-- Quotient-level right singleton identity for any builder whose chosen
landing-component diagonal decomposition agrees with the canonical
`diagonalRightIdentityImageDecomposition`. This specialized route avoids a
global `hright` hypothesis while keeping the fully generic theorem unchanged. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalRightIdentity
    diagonalDecomposition decomposition respects_left respects_right
    landing_eq_diagonalRightIdentity P coeff

/-- Quotient-level right singleton identity for the concrete builder, with
compatibility hypotheses stated directly on
`SupportFiberProductImageDecomposition.toPresentation`. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImagePresentation_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  simpa using
    (comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      landing_eq_diagonalRightIdentity prime coeff)

/-- Quotient-level right singleton identity for the concrete support-fiber-
product image-decomposition builder, assuming only the canonical diagonal
right-identity presentation on the finite landing component. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_diagonalRightPresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_presentation :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)))).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.2))).toPresentation)
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  refine Quotient.inductionOn prime ?_
  intro P
  exact comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented_of_diagonalRightPresentation
    diagonalDecomposition decomposition respects_left respects_right
    landing_presentation P coeff

/-- Quotient-level right singleton identity for the concrete builder, with all
compatibility hypotheses stated directly on
`SupportFiberProductImageDecomposition.toPresentation`. -/
theorem comp_id_single_of_finite_landing_ofSupportFiberProductImagePresentation_of_diagonalRightPresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (landing_presentation :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          SupportFiberProductImageDecomposition.toPresentation
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1))) =
            SupportFiberProductImageDecomposition.toPresentation
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.2)))
    {X Y : Geometry.SmSchemeOver k}
    (prime : PrimeFiniteCorrespondenceGeom X Y)
    (coeff : ℤ) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (Finsupp.single prime coeff)
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) =
        Finsupp.single prime coeff := by
  simpa using
    (comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_diagonalRightPresentation
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      (fun {X Y} P => by
        change
          (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
            (decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)))).toPresentation =
            (RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
                P
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.1)
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).2.2))).toPresentation
        exact landing_presentation P)
      prime coeff)

/-- Each listed diagonal singleton correspondence is idempotent for the
concrete support-fiber-product image-decomposition builder, provided the chosen
decomposition agrees with the canonical diagonal-right singleton decomposition
on finite landing components. -/
theorem comp_diagonalFiniteCorrespondence_eq_self_of_mem_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X : Geometry.SmSchemeOver k}
    (component : SourceIrreducibleComponent X)
    (hcomponent : component ∈ (diagonalDecomposition X).components) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence component) =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence component := by
  classical
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  let D := diagonalDecomposition X
  let diag := SourceIrreducibleComponent.diagonalRepresentedPrimeSupport component
  have hfull :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
        (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X) =
          SourceIrreducibleComponent.diagonalFiniteCorrespondence component := by
    simpa [data, diag, SourceIrreducibleComponent.diagonalFiniteCorrespondence] using
      comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_ofRepresented_of_eq_diagonalRightIdentity
        diagonalDecomposition decomposition respects_left respects_right
        landing_eq_diagonalRightIdentity diag (1 : ℤ)
  have hoffsum :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
        ((D.components.erase component).sum SourceIrreducibleComponent.diagonalFiniteCorrespondence) = 0 := by
    have haux :
        ∀ t : Finset (SourceIrreducibleComponent X),
          t ⊆ D.components.erase component →
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
              (t.sum SourceIrreducibleComponent.diagonalFiniteCorrespondence) = 0 := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro _
        simp
      · intro other t hnotin hIH hsub
        have hmemErase : other ∈ D.components.erase component := hsub (by simp)
        have hmem : other ∈ D.components := (Finset.mem_erase.mp hmemErase).2
        have hneq : other ≠ component := (Finset.mem_erase.mp hmemErase).1
        have hsub_t : t ⊆ D.components.erase component := by
          intro x hx
          exact hsub (by simp [hx])
        rw [Finset.sum_insert hnotin, FiniteCorrespondenceCompositionData.comp_add_right,
          comp_diagonalFiniteCorrespondence_eq_zero_of_ne_ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right
            component other hcomponent hmem hneq, hIH hsub_t]
        simp
    exact haux (D.components.erase component) (by
      intro x hx
      exact hx)
  have hsplit :
      D.identityFiniteCorrespondence =
        SourceIrreducibleComponent.diagonalFiniteCorrespondence component +
          (D.components.erase component).sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
    calc
      D.identityFiniteCorrespondence =
          D.components.sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
            exact localIdentityFiniteCorrespondenceEqSumComponents D
      _ = SourceIrreducibleComponent.diagonalFiniteCorrespondence component +
            (D.components.erase component).sum SourceIrreducibleComponent.diagonalFiniteCorrespondence := by
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_erase_add (s := D.components)
                  (f := SourceIrreducibleComponent.diagonalFiniteCorrespondence) hcomponent).symm
  calc
    FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
        (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
        = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            (SourceIrreducibleComponent.diagonalFiniteCorrespondence component)
            (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X) := by
              rw [show FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X =
                    D.identityFiniteCorrespondence by rfl,
                hsplit, FiniteCorrespondenceCompositionData.comp_add_right, hoffsum]
              simp
    _ = SourceIrreducibleComponent.diagonalFiniteCorrespondence component := hfull

/-- Coefficient-free prime associativity for the concrete support-fiber-product
image-decomposition builder, once a chosen left-associated triple image
decomposition computes the two nested singleton compositions. -/
theorem assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition_ofRepresented
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R))
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X)
    (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.compPrime
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q))
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondenceCompositionData.compPrime
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
            (PrimeFiniteCorrespondenceGeom.ofRepresented R)) := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  simpa [data] using
    (assoc_prime_of_tripleImagePresentation_ofRepresented
      data leftPresentation rightPresentation hpresentation hleft hright P Q R)

/-- Represented-point coefficient-free prime associativity for the concrete
support-fiber-product image-decomposition builder, with compatibility and
nested-singleton hypotheses stated directly on the honest geometric
presentations `SupportFiberProductImageDecomposition.toPresentation`. -/
theorem assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImagePresentation_ofRepresented
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition Q R))) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R))
    {W X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport W X)
    (Q : RepresentedPrimeSupport X Y)
    (R : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (FiniteCorrespondenceCompositionData.compPrime
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q))
      (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondenceCompositionData.compPrime
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
            (PrimeFiniteCorrespondenceGeom.ofRepresented R)) := by
  simpa using
    (assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition_ofRepresented
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      leftPresentation rightPresentation hpresentation
      (fun P Q R => by
        simpa using hleft P Q R)
      (fun P Q R => by
        simpa using hright P Q R)
      P Q R)

/-- Coefficient-free prime associativity for the concrete support-fiber-product
image-decomposition builder, once a chosen left-associated triple image
decomposition computes the two nested singleton compositions. -/
theorem assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X)
      (g : PrimeFiniteCorrespondenceGeom X Y)
      (h : PrimeFiniteCorrespondenceGeom Y Z),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            f g)
          (Finsupp.single h 1) =
            FiniteCorrespondenceCompositionData.comp
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime
                (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
                  diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
                g h) := by
  intro W X Y Z f g h
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  simpa [data] using
    (assoc_prime_of_tripleImagePresentation
      data leftPresentation rightPresentation hpresentation hleft hright f g h)

/-- Coefficient-free prime associativity for the concrete support-fiber-product
image-decomposition builder, with compatibility and nested-singleton
hypotheses stated directly on the honest geometric presentations
`SupportFiberProductImageDecomposition.toPresentation`. -/
theorem assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImagePresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition Q R))) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X)
      (g : PrimeFiniteCorrespondenceGeom X Y)
      (h : PrimeFiniteCorrespondenceGeom Y Z),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            f g)
          (Finsupp.single h 1) =
            FiniteCorrespondenceCompositionData.comp
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime
                (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
                  diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
                g h) := by
  intro W X Y Z f g h
  simpa using
    (assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      leftPresentation rightPresentation hpresentation
      (fun P Q R => by
        simpa using hleft P Q R)
      (fun P Q R => by
        simpa using hright P Q R)
      f g h)

/-- Scaled prime associativity for the concrete support-fiber-product image-
decomposition builder follows formally from the coefficient-free prime
associativity surface proved above. -/
theorem assoc_scaled_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          ((fCoeff * gCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              f g))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              (Finsupp.single f fCoeff)
              ((gCoeff * hCoeff) •
                (FiniteCorrespondenceCompositionData.compPrime
                  (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
                    diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
                  g h)) := by
  intro W X Y Z f fCoeff g gCoeff h hCoeff
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  simpa [data] using
    (localAssocScaledPrimeOfPrimeAssoc
      data.toFiniteCorrespondenceCompositionData
      (assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right
        leftPresentation rightPresentation hpresentation hleft hright)
      f fCoeff g gCoeff h hCoeff)

/-- Scaled prime associativity for the concrete support-fiber-product image-
decomposition builder, with compatibility and nested-singleton hypotheses
stated directly on `SupportFiberProductImageDecomposition.toPresentation`. -/
theorem assoc_scaled_prime_of_tripleImagePresentation_ofSupportFiberProductImagePresentation
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition Q R))) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X) (fCoeff : ℤ)
      (g : PrimeFiniteCorrespondenceGeom X Y) (gCoeff : ℤ)
      (h : PrimeFiniteCorrespondenceGeom Y Z) (hCoeff : ℤ),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          ((fCoeff * gCoeff) •
            (FiniteCorrespondenceCompositionData.compPrime
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              f g))
          (Finsupp.single h hCoeff) =
            FiniteCorrespondenceCompositionData.comp
              (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
                diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
              (Finsupp.single f fCoeff)
              ((gCoeff * hCoeff) •
                (FiniteCorrespondenceCompositionData.compPrime
                  (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
                    diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
                  g h)) := by
  intro W X Y Z f fCoeff g gCoeff h hCoeff
  simpa using
    (assoc_scaled_prime_of_tripleImagePresentation_ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      leftPresentation rightPresentation hpresentation
      (fun P Q R => by
        simpa using hleft P Q R)
      (fun P Q R => by
        simpa using hright P Q R)
      f fCoeff g gCoeff h hCoeff)

/-- Bundle the concrete support-fiber-product image-decomposition composition
model into `SmCor(k)` once diagonal inputs agree with the canonical left/right
identity decompositions and a chosen triple image decomposition computes the
two nested singleton compositions. -/
def toSmCorOfTripleImagePresentation_ofSupportFiberProductImageDecomposition_of_eq_diagonalIdentities
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    SmCor (k := k) := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact data.toSmCorOfTripleImagePresentation
    (id_comp_single_of_exhaustive_source_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition respects_left respects_right
      source_eq_diagonalLeftIdentity)
    (comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
      diagonalDecomposition decomposition respects_left respects_right
      landing_eq_diagonalRightIdentity)
    leftPresentation
    rightPresentation
    hpresentation
    hleft
    hright

/-- A version of
`toSmCorOfTripleImagePresentation_ofSupportFiberProductImageDecomposition_of_eq_diagonalIdentities`
whose compatibility and nested-singleton hypotheses are stated directly on the
honest geometric presentations `SupportFiberProductImageDecomposition.toPresentation`. -/
def toSmCorOfTripleImagePresentation_ofSupportFiberProductImagePresentation_of_eq_diagonalIdentities
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition Q R))) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    SmCor (k := k) := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
      diagonalDecomposition decomposition respects_left respects_right
  exact data.toSmCorOfTripleImagePresentation
    (id_comp_single_of_exhaustive_source_ofSupportFiberProductImagePresentation_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition respects_left respects_right
      source_eq_diagonalLeftIdentity)
    (comp_id_single_of_finite_landing_ofSupportFiberProductImagePresentation_of_eq_diagonalRightIdentity
      diagonalDecomposition decomposition respects_left respects_right
      landing_eq_diagonalRightIdentity)
    leftPresentation
    rightPresentation
    hpresentation
    hleft
    hright

/-- Bundled concrete geometric input still needed to obtain the final
`SmCor(k)` from support-fiber-product image decompositions. The cycle layer can
feed multiplicities into such decompositions, but the remaining geometric task
is to instantiate this package honestly. -/
structure SupportFiberProductImageCompositionPackage where
  diagonalDecomposition :
    (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X
  decomposition :
    {X Y Z : Geometry.SmSchemeOver k} →
    (P : RepresentedPrimeSupport X Y) →
    (Q : RepresentedPrimeSupport Y Z) →
    SupportFiberProductImageDecomposition P Q
  respects_left :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      {P P' : RepresentedPrimeSupport X Y}
      (_h : PrimeSupportEquivalent P P')
      (Q : RepresentedPrimeSupport Y Z),
        FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition P Q)).toPresentation) =
          FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition P' Q)).toPresentation)
  respects_right :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y)
      {Q Q' : RepresentedPrimeSupport Y Z}
      (_h : PrimeSupportEquivalent Q Q'),
        FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition P Q)).toPresentation) =
          FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition P Q')).toPresentation)
  source_eq_diagonalLeftIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        decomposition
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
          RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P
  landing_eq_diagonalRightIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        decomposition P
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)) =
          RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
            P
            ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
              (diagonalDecomposition Y) P).1.1)
            ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
              (diagonalDecomposition Y) P).2.1)
            ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
              (diagonalDecomposition Y) P).2.2)
  leftPresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k},
      RepresentedPrimeSupport W X →
      RepresentedPrimeSupport X Y →
      RepresentedPrimeSupport Y Z →
        FiniteCorrespondencePresentation W Z
  rightPresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k},
      RepresentedPrimeSupport W X →
      RepresentedPrimeSupport X Y →
      RepresentedPrimeSupport Y Z →
        FiniteCorrespondencePresentation W Z
  hpresentation :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        rightPresentation P Q R = leftPresentation P Q R
  hleft :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition P Q)).toPresentation))
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
            FiniteCorrespondencePresentation.toGeom
              (leftPresentation P Q R)
  hright :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              (decomposition Q R)).toPresentation)) =
            FiniteCorrespondencePresentation.toGeom
              (rightPresentation P Q R)

/-- Forget the source-lifted refinement of a binary image-decomposition builder
and extract the ordinary `SupportFiberProductImageDecomposition` expected by the
existing composition package. -/
def supportFiberProductLiftedDecomposition
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
        SupportFiberProductLiftedImageDecompositionData P Q) :
    {X Y Z : Geometry.SmSchemeOver k} →
    (P : RepresentedPrimeSupport X Y) →
    (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q :=
  fun {X} {Y} {Z} P Q =>
    (decomposition (X := X) (Y := Y) (Z := Z) P Q).toSupportFiberProductImageDecomposition

namespace SupportFiberProductImageCompositionPackage

/-- The bundled support-fiber-product image composition package produces the
final correspondence category `SmCor(k)`. -/
def toSmCor (pkg : SupportFiberProductImageCompositionPackage (k := k)) : SmCor (k := k) :=
  toSmCorOfTripleImagePresentation_ofSupportFiberProductImageDecomposition_of_eq_diagonalIdentities
    pkg.diagonalDecomposition
    pkg.decomposition
    pkg.respects_left
    pkg.respects_right
    pkg.source_eq_diagonalLeftIdentity
    pkg.landing_eq_diagonalRightIdentity
    pkg.leftPresentation
    pkg.rightPresentation
    pkg.hpresentation
    pkg.hleft
    pkg.hright

end SupportFiberProductImageCompositionPackage

/-- The concrete diagonal projectors form the expected orthogonal family: two
listed diagonal singleton correspondences compose to the shared projector when
the listed components agree, and to zero otherwise. -/
theorem comp_diagonalFiniteCorrespondence_eq_ite_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X : Geometry.SmSchemeOver k}
    [DecidableEq (SourceIrreducibleComponent X)]
    (left right : SourceIrreducibleComponent X)
    (hleft : left ∈ (diagonalDecomposition X).components)
    (hright : right ∈ (diagonalDecomposition X).components) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence left)
      (SourceIrreducibleComponent.diagonalFiniteCorrespondence right) =
        if right = left then SourceIrreducibleComponent.diagonalFiniteCorrespondence left else 0 := by
  classical
  by_cases h : right = left
  · subst h
    simpa using
      comp_diagonalFiniteCorrespondence_eq_self_of_mem_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
        diagonalDecomposition decomposition respects_left respects_right
        landing_eq_diagonalRightIdentity right hright
  · simpa [h] using
      comp_diagonalFiniteCorrespondence_eq_zero_of_ne_ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right
        left right hleft hright h

/-- Right diagonal identity for arbitrary finite correspondences, provided the
chosen builder uses the canonical diagonal-right decomposition on the finite
landing component of each represented prime support. This is the formal-sum
extension of the represented-prime right identity theorem. -/
theorem comp_id_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                (decomposition P Q')).toPresentation))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      f
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) = f := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      diagonalDecomposition decomposition respects_left respects_right
  exact localCompIdOfSingletonIdentities
    data.toFiniteCorrespondenceCompositionData
    (fun {X Y} prime coeff =>
      comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
        diagonalDecomposition decomposition respects_left respects_right
        landing_eq_diagonalRightIdentity prime coeff)
    f

/-- Right diagonal identity for arbitrary finite correspondences, with
compatibility hypotheses stated directly on the honest geometric
presentations `SupportFiberProductImageDecomposition.toPresentation`. -/
theorem comp_id_of_finite_landing_ofSupportFiberProductImagePresentation_of_eq_diagonalRightIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    {X Y : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence X Y) :
    FiniteCorrespondenceCompositionData.comp
      (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
        diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
      f
      (FiniteCorrespondenceCompositionData.id
        (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
          diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData Y) = f := by
  simpa using
    (comp_id_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
      diagonalDecomposition decomposition
      (fun {X Y Z} {P P'} h Q => by
        simpa using respects_left h Q)
      (fun {X Y Z} P {Q Q'} h => by
        simpa using respects_right P h)
      landing_eq_diagonalRightIdentity f)

/-- Literature-shaped package for finite-correspondence composition on smooth
`k`-schemes.

The public interface exposes only the descended prime-level composition law and
the singleton identity and prime associativity bridges needed to extend it to
`SmCor(k)`. Concrete support-fiber-product image decompositions may be used by
constructors, but they do not appear in the exported API. -/
structure GeometricFiniteCorrespondenceComposition where
  data : RepresentedPrimeFiniteCorrespondenceComposition (k := k)
  id_comp_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData X)
          (Finsupp.single prime coeff) =
            Finsupp.single prime coeff
  comp_id_single :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y) (coeff : ℤ),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single prime coeff)
          (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) =
            Finsupp.single prime coeff
  assoc_prime :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (f : PrimeFiniteCorrespondenceGeom W X)
      (g : PrimeFiniteCorrespondenceGeom X Y)
      (h : PrimeFiniteCorrespondenceGeom Y Z),
        FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            data.toFiniteCorrespondenceCompositionData f g)
          (Finsupp.single h 1) =
            FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
              (Finsupp.single f 1)
              (FiniteCorrespondenceCompositionData.compPrime
                data.toFiniteCorrespondenceCompositionData g h)

namespace GeometricFiniteCorrespondenceComposition

/-- Build the literature-shaped composition package from an honest
support-fiber-product image-decomposition model, with all compatibility
hypotheses stated directly on the honest geometric presentations. -/
def ofSupportFiberProductImagePresentation_of_eq_diagonalIdentities
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (decomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductImageDecomposition P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P' Q)))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)) =
            FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q')))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          decomposition P
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport
                ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                  (diagonalDecomposition Y) P).1.1)) =
            RepresentedPrimeCompositionDatum.diagonalRightIdentityImageDecomposition
              P
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).1.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.1)
              ((FiniteIrreducibleComponentDecomposition.landingComponent_of_finite
                (diagonalDecomposition Y) P).2.2))
    (leftPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (rightPresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k},
        RepresentedPrimeSupport W X →
        RepresentedPrimeSupport X Y →
        RepresentedPrimeSupport Y Z →
          FiniteCorrespondencePresentation W Z)
    (hpresentation :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          rightPresentation P Q R = leftPresentation P Q R)
    (hleft :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom
                (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
              diagonalDecomposition decomposition respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation (decomposition Q R))) =
              FiniteCorrespondencePresentation.toGeom
                (rightPresentation P Q R)) :
    GeometricFiniteCorrespondenceComposition (k := k) where
  data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
      diagonalDecomposition decomposition respects_left respects_right
  id_comp_single :=
    id_comp_single_of_exhaustive_source_ofSupportFiberProductImagePresentation_of_eq_diagonalLeftIdentity
      diagonalDecomposition decomposition respects_left respects_right
      source_eq_diagonalLeftIdentity
  comp_id_single :=
    comp_id_single_of_finite_landing_ofSupportFiberProductImagePresentation_of_eq_diagonalRightIdentity
      diagonalDecomposition decomposition respects_left respects_right
      landing_eq_diagonalRightIdentity
  assoc_prime :=
    assoc_prime_of_tripleImagePresentation_ofSupportFiberProductImagePresentation
      diagonalDecomposition decomposition respects_left respects_right
      leftPresentation rightPresentation hpresentation hleft hright

/-- Build the correspondence category `SmCor(k)` from a literature-shaped
finite-correspondence composition package. -/
def toSmCor (composition : GeometricFiniteCorrespondenceComposition (k := k)) :
    SmCor (k := k) :=
  composition.data.toSmCorOfPrimeAssoc
    composition.id_comp_single
    composition.comp_id_single
    composition.assoc_prime

end GeometricFiniteCorrespondenceComposition

end RepresentedPrimeFiniteCorrespondenceComposition

end

end Boundary

import Boundary.CompositionGeometry
import Boundary.CompositionCategory
import Boundary.RationalCompositionCategory

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

/-- Bundled concrete composition input whose binary packages are still defined
via honest lifted support-fiber-product image decompositions. This keeps the
package-family layer computational: later graph compatibility can be proved by
showing that a chosen lifted builder specializes to the graph decomposition on
graph-prime pairs. -/
structure SupportFiberProductLiftedImageCompositionPackage where
  diagonalDecomposition :
    (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X
  liftedDecomposition :
    {X Y Z : Geometry.SmSchemeOver k} →
    (P : RepresentedPrimeSupport X Y) →
    (Q : RepresentedPrimeSupport Y Z) →
      SupportFiberProductLiftedImageDecompositionData P Q
  respects_left :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      {P P' : RepresentedPrimeSupport X Y}
      (_h : PrimeSupportEquivalent P P')
      (Q : RepresentedPrimeSupport Y Z),
        FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
          FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) P' Q)).toPresentation)
  respects_right :
    ∀ {X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y)
      {Q Q' : RepresentedPrimeSupport Y Z}
      (_h : PrimeSupportEquivalent Q Q'),
        FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
          FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q')).toPresentation)
  source_eq_diagonalLeftIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        (supportFiberProductLiftedDecomposition liftedDecomposition)
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
          RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P
  landing_eq_diagonalRightIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        (supportFiberProductLiftedDecomposition liftedDecomposition) P
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
            diagonalDecomposition
            (supportFiberProductLiftedDecomposition liftedDecomposition)
            respects_left respects_right).toFiniteCorrespondenceCompositionData
          (FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation))
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
            FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R)
  hright :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp
          (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
            diagonalDecomposition
            (supportFiberProductLiftedDecomposition liftedDecomposition)
            respects_left respects_right).toFiniteCorrespondenceCompositionData
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondencePresentation.toGeom
            ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
              ((supportFiberProductLiftedDecomposition liftedDecomposition) Q R)).toPresentation)) =
            FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)

namespace SupportFiberProductLiftedImageCompositionPackage

/-- Forget the lifted refinement of a concrete package while keeping the fact
that it came from an honest lifted decomposition builder available upstream. -/
def toSupportFiberProductImageCompositionPackage
    (pkg : SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    SupportFiberProductImageCompositionPackage (k := k) :=
  { diagonalDecomposition := pkg.diagonalDecomposition
    decomposition := supportFiberProductLiftedDecomposition pkg.liftedDecomposition
    respects_left := pkg.respects_left
    respects_right := pkg.respects_right
    source_eq_diagonalLeftIdentity := pkg.source_eq_diagonalLeftIdentity
    landing_eq_diagonalRightIdentity := pkg.landing_eq_diagonalRightIdentity
    leftPresentation := pkg.leftPresentation
    rightPresentation := pkg.rightPresentation
    hpresentation := pkg.hpresentation
    hleft := pkg.hleft
    hright := pkg.hright }

end SupportFiberProductLiftedImageCompositionPackage

namespace SupportFiberProductImageCompositionPackage

/-- Build the ordinary support-fiber-product image composition package directly
from a real lifted-decomposition builder by forgetting the source-lifted
refinement. -/
def ofSupportFiberProductLiftedDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (liftedDecomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
        SupportFiberProductLiftedImageDecompositionData P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition) P
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
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    SupportFiberProductImageCompositionPackage (k := k) where
  diagonalDecomposition := diagonalDecomposition
  decomposition := supportFiberProductLiftedDecomposition liftedDecomposition
  respects_left := respects_left
  respects_right := respects_right
  source_eq_diagonalLeftIdentity := source_eq_diagonalLeftIdentity
  landing_eq_diagonalRightIdentity := landing_eq_diagonalRightIdentity
  leftPresentation := leftPresentation
  rightPresentation := rightPresentation
  hpresentation := hpresentation
  hleft := hleft
  hright := hright

/-- Existence form of `ofSupportFiberProductLiftedDecomposition`: once the real
lifted decomposition and its presentation compatibilities are available, the
ordinary support-fiber-product image composition package exists. -/
theorem exists_ofSupportFiberProductLiftedDecomposition
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (liftedDecomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
        SupportFiberProductLiftedImageDecompositionData P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition) P
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
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    Nonempty (SupportFiberProductImageCompositionPackage (k := k)) :=
  ⟨ofSupportFiberProductLiftedDecomposition
      diagonalDecomposition liftedDecomposition respects_left respects_right
      source_eq_diagonalLeftIdentity landing_eq_diagonalRightIdentity
      leftPresentation rightPresentation hpresentation hleft hright⟩

/-- The package-parametric prime composition presentation produced by the
honest support-fiber-product image decomposition attached to `pkg`. -/
def canonicalCompPresentation
    (pkg : SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondencePresentation X Z :=
  (pkg.decomposition P Q).toPresentation

/-- The package-parametric prime composition descended to geometric prime
classes. -/
def canonicalComp
    (pkg : SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondence X Z :=
  FiniteCorrespondencePresentation.toGeom (pkg.canonicalCompPresentation P Q)

@[simp] theorem canonicalComp_eq_toGeom_canonicalCompPresentation
    (pkg : SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    (Q : RepresentedPrimeSupport Y Z) :
    pkg.canonicalComp P Q =
      FiniteCorrespondencePresentation.toGeom (pkg.canonicalCompPresentation P Q) :=
  rfl

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

namespace PrimeFiniteCorrespondenceSupport

/-- The canonical prime-composition presentation produced by a chosen honest
support-fiber-product image composition package. -/
def canonicalCompPresentation
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z)
    (pkg : SupportFiberProductImageCompositionPackage (k := k)) :
    FiniteCorrespondencePresentation X Z :=
  pkg.canonicalCompPresentation P Q

/-- The canonical prime composition on geometric prime-support classes produced
by a chosen honest support-fiber-product image composition package. -/
def canonicalComp
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z)
    (pkg : SupportFiberProductImageCompositionPackage (k := k)) :
    FiniteCorrespondence X Z :=
  pkg.canonicalComp P Q

@[simp] theorem canonicalComp_eq_toGeom_canonicalCompPresentation
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z)
    (pkg : SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalComp P Q pkg =
      FiniteCorrespondencePresentation.toGeom (canonicalCompPresentation P Q pkg) :=
  rfl

private def liftedCanonicalCompGenericLengthPresentation
    (liftedDecomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
        SupportFiberProductLiftedImageDecompositionData P Q)
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z) :
    FiniteCorrespondencePresentation X Z := by
  classical
  let lifted := liftedDecomposition P Q
  let decomposition := lifted.toSupportFiberProductImageDecomposition
  letI := decomposition.fintype_index
  letI := decomposition.decidableEq_index
  exact Finset.univ.sum fun i : decomposition.index =>
    let component := decomposition.component i
    ((_root_.finiteMapImageMultiplicity (compositionToAmbientProduct P Q)
        (lifted.component i).genericLengthData : ℤ)) •
      Finsupp.single component.toWeightedPrimeFiniteCorrespondenceSupport.prime 1

/-- For a package obtained from a real lifted decomposition, the canonical
prime-composition presentation is the sum of singleton represented-prime
supports weighted by the corresponding generic-length multiplicities. -/
theorem canonicalComp_coeff_eq_genericLength
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (liftedDecomposition :
      {X Y Z : Geometry.SmSchemeOver k} →
      (P : RepresentedPrimeSupport X Y) →
      (Q : RepresentedPrimeSupport Y Z) →
        SupportFiberProductLiftedImageDecompositionData P Q)
    (respects_left :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        {P P' : RepresentedPrimeSupport X Y}
        (_h : PrimeSupportEquivalent P P')
        (Q : RepresentedPrimeSupport Y Z),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P' Q)).toPresentation))
    (respects_right :
      ∀ {X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y)
        {Q Q' : RepresentedPrimeSupport Y Z}
        (_h : PrimeSupportEquivalent Q Q'),
          FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation) =
            FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q')).toPresentation))
    (source_eq_diagonalLeftIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition)
              (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent) P =
            RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          (supportFiberProductLiftedDecomposition liftedDecomposition) P
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
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) P Q)).toPresentation))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
              diagonalDecomposition
              (supportFiberProductLiftedDecomposition liftedDecomposition)
              respects_left respects_right).toFiniteCorrespondenceCompositionData
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              ((RepresentedPrimeCompositionDatum.ofSupportFiberProductImageDecomposition
                ((supportFiberProductLiftedDecomposition liftedDecomposition) Q R)).toPresentation)) =
              FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z) :
    canonicalCompPresentation P Q
        (SupportFiberProductImageCompositionPackage.ofSupportFiberProductLiftedDecomposition
          diagonalDecomposition liftedDecomposition respects_left respects_right
          source_eq_diagonalLeftIdentity landing_eq_diagonalRightIdentity
          leftPresentation rightPresentation hpresentation hleft hright) =
      liftedCanonicalCompGenericLengthPresentation liftedDecomposition P Q := by
  classical
  simp [canonicalCompPresentation,
    liftedCanonicalCompGenericLengthPresentation,
    SupportFiberProductImageCompositionPackage.canonicalCompPresentation,
    SupportFiberProductImageCompositionPackage.ofSupportFiberProductLiftedDecomposition,
    supportFiberProductLiftedDecomposition,
    SupportFiberProductLiftedImageDecompositionData.toSupportFiberProductImageDecomposition,
    SupportFiberProductLiftedImageComponentData.toSupportFiberProductImageComponent,
    SupportFiberProductImageDecomposition.toPresentation,
    SupportFiberProductImageComponent.toWeightedPrimeFiniteCorrespondenceSupport,
    SupportFiberProductImageComponent.toRepresentedPrimeSupport,
    FiniteCorrespondencePresentation.ofWeightedPrimeSupport,
    SupportFiberProductLiftedImageComponentData.multiplicity_eq_finiteMapImageMultiplicity]

end PrimeFiniteCorrespondenceSupport

namespace PrimeFiniteCorrespondenceGeom

/-- Package-parametric prime composition on geometric prime-support classes. The
package input is indexed explicitly by the two geometric prime classes being
composed, so no representative is chosen by hidden choice. -/
def canonicalCompWithPackages
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceGeom X Y)
    (Q : PrimeFiniteCorrespondenceGeom Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    FiniteCorrespondence X Z := by
  let pkg := packages P Q
  exact
    (RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      pkg.diagonalDecomposition
      pkg.decomposition
      pkg.respects_left
      pkg.respects_right).compPrime P Q

@[simp] theorem canonicalCompWithPackages_ofRepresented
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceSupport X Y)
    (Q : PrimeFiniteCorrespondenceSupport Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages
        (PrimeFiniteCorrespondenceGeom.ofRepresented P)
        (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
        packages =
      PrimeFiniteCorrespondenceSupport.canonicalComp P Q
        (packages
          (PrimeFiniteCorrespondenceGeom.ofRepresented P)
          (PrimeFiniteCorrespondenceGeom.ofRepresented Q)) :=
  rfl

end PrimeFiniteCorrespondenceGeom

namespace FiniteCorrespondence

/-- Package-parametric bilinear composition on finite correspondences. The
package data is supplied explicitly for each pair of geometric prime classes in
the supports of the two inputs. -/
def canonicalCompWithPackages
    {X Y Z : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y)
    (β : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    FiniteCorrespondence X Z :=
  α.sum fun P a =>
    β.sum fun Q b =>
      (a * b) • PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages P Q packages

@[simp] theorem canonicalCompWithPackages_zero_left
    {X Y Z : Geometry.SmSchemeOver k}
    (β : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages (0 : FiniteCorrespondence X Y) β packages = 0 := by
  simp [canonicalCompWithPackages]

@[simp] theorem canonicalCompWithPackages_zero_right
    {X Y Z : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages α (0 : FiniteCorrespondence Y Z) packages = 0 := by
  simp [canonicalCompWithPackages]

@[simp] theorem canonicalCompWithPackages_add_left
    {X Y Z : Geometry.SmSchemeOver k}
    (α₁ α₂ : FiniteCorrespondence X Y)
    (β : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages (α₁ + α₂) β packages =
      canonicalCompWithPackages α₁ β packages +
        canonicalCompWithPackages α₂ β packages := by
  classical
  rw [canonicalCompWithPackages,
    canonicalCompWithPackages,
    canonicalCompWithPackages,
    Finsupp.sum_add_index'] <;>
    simp [add_mul, add_smul, zero_mul]

@[simp] theorem canonicalCompWithPackages_add_right
    {X Y Z : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y)
    (β₁ β₂ : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages α (β₁ + β₂) packages =
      canonicalCompWithPackages α β₁ packages +
        canonicalCompWithPackages α β₂ packages := by
  classical
  rw [canonicalCompWithPackages,
    canonicalCompWithPackages,
    canonicalCompWithPackages,
    ← Finsupp.sum_add]
  congr
  ext P a
  rw [Finsupp.sum_add_index'] <;> simp [mul_add, add_smul, zero_mul]

@[simp] theorem canonicalCompWithPackages_zsmul_left
    {X Y Z : Geometry.SmSchemeOver k}
    (n : ℤ)
    (α : FiniteCorrespondence X Y)
    (β : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages (n • α) β packages =
      n • canonicalCompWithPackages α β packages := by
  apply Finsupp.induction_linear α
  · simp
  · intro α₁ α₂ ih₁ ih₂
    rw [smul_add, canonicalCompWithPackages_add_left, ih₁, ih₂,
      ← smul_add, canonicalCompWithPackages_add_left]
  · intro P a
    simp [canonicalCompWithPackages]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro Q _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

@[simp] theorem canonicalCompWithPackages_zsmul_right
    {X Y Z : Geometry.SmSchemeOver k}
    (n : ℤ)
    (α : FiniteCorrespondence X Y)
    (β : FiniteCorrespondence Y Z)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    canonicalCompWithPackages α (n • β) packages =
      n • canonicalCompWithPackages α β packages := by
  apply Finsupp.induction_linear β
  · simp
  · intro β₁ β₂ ih₁ ih₂
    rw [smul_add, canonicalCompWithPackages_add_right, ih₁, ih₂,
      ← smul_add, canonicalCompWithPackages_add_right]
  · intro Q b
    simp [canonicalCompWithPackages]
    rw [Finsupp.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro P _
    simp [smul_smul, mul_assoc, mul_left_comm, mul_comm]

private theorem canonicalCompWithPackages_const_id_left
    (pkg : SupportFiberProductImageCompositionPackage (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y) :
    canonicalCompWithPackages
      ((pkg.diagonalDecomposition X).identityFiniteCorrespondence)
      α
      (fun _ _ => pkg) = α := by
  change FiniteCorrespondenceCompositionData.comp
      ((RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
        pkg.diagonalDecomposition
        pkg.decomposition
        pkg.respects_left
        pkg.respects_right).toFiniteCorrespondenceCompositionData)
      ((pkg.diagonalDecomposition X).identityFiniteCorrespondence)
      α = α
  exact id_comp_ofSupportFiberProductImageDecomposition_of_eq_diagonalLeftIdentity
    pkg.diagonalDecomposition
    pkg.decomposition
    pkg.respects_left
    pkg.respects_right
    pkg.source_eq_diagonalLeftIdentity
    α

private theorem canonicalCompWithPackages_const_id_right
    (pkg : SupportFiberProductImageCompositionPackage (k := k))
    {X Y : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y) :
    canonicalCompWithPackages
      α
      ((pkg.diagonalDecomposition Y).identityFiniteCorrespondence)
      (fun _ _ => pkg) = α := by
  let data :=
    RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImageDecomposition
      pkg.diagonalDecomposition
      pkg.decomposition
      pkg.respects_left
      pkg.respects_right
  change FiniteCorrespondenceCompositionData.comp
      data.toFiniteCorrespondenceCompositionData
      α
      (FiniteCorrespondenceCompositionData.id data.toFiniteCorrespondenceCompositionData Y) = α
  exact FiniteCorrespondenceCompositionData.comp_id_of_singleton_identities
    data.toFiniteCorrespondenceCompositionData
    (fun {X Y} prime coeff =>
      comp_id_single_of_finite_landing_ofSupportFiberProductImageDecomposition_of_eq_diagonalRightIdentity
        pkg.diagonalDecomposition
        pkg.decomposition
        pkg.respects_left
        pkg.respects_right
        pkg.landing_eq_diagonalRightIdentity
        prime coeff)
    α

@[simp] theorem canonicalCompWithPackages_id_left
    {X Y : Geometry.SmSchemeOver k}
    (D : FiniteIrreducibleComponentDecomposition X)
    (α : FiniteCorrespondence X Y)
    (packages :
      PrimeFiniteCorrespondenceGeom X X →
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductImageCompositionPackage (k := k))
    (leftPackage :
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductImageCompositionPackage (k := k))
    (hpackages :
      ∀ (diagClass : PrimeFiniteCorrespondenceGeom X X)
        (prime : PrimeFiniteCorrespondenceGeom X Y),
          diagClass ∈ D.diagonalPrimeClasses →
            packages diagClass prime = leftPackage prime) :
    canonicalCompWithPackages D.identityFiniteCorrespondence α packages = α := by
  classical
  apply Finsupp.induction_linear α
  · simp
  · intro α₁ α₂ ih₁ ih₂
    rw [canonicalCompWithPackages_add_right, ih₁, ih₂]
  · intro prime coeff
    let pkg := leftPackage prime
    have hconst :
        canonicalCompWithPackages D.identityFiniteCorrespondence
          (Finsupp.single prime coeff)
          packages =
          canonicalCompWithPackages D.identityFiniteCorrespondence
            (Finsupp.single prime coeff)
            (fun _ _ => pkg) := by
      rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence]
      let f := fun diagClass : PrimeFiniteCorrespondenceGeom X X => Finsupp.single diagClass (1 : ℤ)
      have haux :
          ∀ t : Finset (PrimeFiniteCorrespondenceGeom X X),
            t ⊆ D.diagonalPrimeClasses →
              canonicalCompWithPackages (t.sum f) (Finsupp.single prime coeff) packages =
                canonicalCompWithPackages (t.sum f) (Finsupp.single prime coeff) (fun _ _ => pkg) := by
        intro t
        refine Finset.induction_on t ?_ ?_
        · intro _
          simp [canonicalCompWithPackages, f]
        · intro diagClass s hnotin ih hsub
          have hdiag_mem : diagClass ∈ D.diagonalPrimeClasses := hsub (by simp)
          have hsub_s : s ⊆ D.diagonalPrimeClasses := by
            intro x hx
            exact hsub (by simp [hx])
          rw [Finset.sum_insert hnotin, canonicalCompWithPackages_add_left,
            canonicalCompWithPackages_add_left, ih hsub_s]
          have hfirst :
              canonicalCompWithPackages
                (Finsupp.single diagClass 1)
                (Finsupp.single prime coeff)
                packages =
                canonicalCompWithPackages
                  (Finsupp.single diagClass 1)
                  (Finsupp.single prime coeff)
                  (fun _ _ => pkg) := by
            simpa [canonicalCompWithPackages,
              mul_comm, mul_left_comm, mul_assoc] using
              (show coeff • PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages
                    diagClass
                    prime
                    packages =
                  coeff • PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages
                    diagClass
                    prime
                    (fun _ _ => pkg) by
                dsimp [PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages, pkg]
                rw [hpackages diagClass prime hdiag_mem])
          exact congrArg (fun t =>
            t + canonicalCompWithPackages (s.sum f) (Finsupp.single prime coeff) (fun _ _ => pkg)) hfirst
      exact haux D.diagonalPrimeClasses (by intro x hx; exact hx)
    have hid :
        D.identityFiniteCorrespondence =
          (pkg.diagonalDecomposition X).identityFiniteCorrespondence :=
      FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_independent
        D (pkg.diagonalDecomposition X)
    calc
      canonicalCompWithPackages D.identityFiniteCorrespondence
          (Finsupp.single prime coeff)
          packages =
        canonicalCompWithPackages D.identityFiniteCorrespondence
          (Finsupp.single prime coeff)
          (fun _ _ => pkg) := hconst
      _ = canonicalCompWithPackages
            ((pkg.diagonalDecomposition X).identityFiniteCorrespondence)
            (Finsupp.single prime coeff)
            (fun _ _ => pkg) := by
              rw [hid]
      _ = Finsupp.single prime coeff :=
        canonicalCompWithPackages_const_id_left pkg (Finsupp.single prime coeff)

@[simp] theorem canonicalCompWithPackages_id_right
    {X Y : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y)
    (D : FiniteIrreducibleComponentDecomposition Y)
    (packages :
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Y →
      SupportFiberProductImageCompositionPackage (k := k))
    (rightPackage :
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductImageCompositionPackage (k := k))
    (hpackages :
      ∀ (prime : PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ D.diagonalPrimeClasses →
            packages prime diagClass = rightPackage prime) :
    canonicalCompWithPackages α D.identityFiniteCorrespondence packages = α := by
  classical
  apply Finsupp.induction_linear α
  · simp
  · intro α₁ α₂ ih₁ ih₂
    rw [canonicalCompWithPackages_add_left, ih₁, ih₂]
  · intro prime coeff
    let pkg := rightPackage prime
    have hconst :
        canonicalCompWithPackages
          (Finsupp.single prime coeff)
          D.identityFiniteCorrespondence
          packages =
          canonicalCompWithPackages
            (Finsupp.single prime coeff)
            D.identityFiniteCorrespondence
            (fun _ _ => pkg) := by
      rw [FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence]
      let f := fun diagClass : PrimeFiniteCorrespondenceGeom Y Y => Finsupp.single diagClass (1 : ℤ)
      have haux :
          ∀ t : Finset (PrimeFiniteCorrespondenceGeom Y Y),
            t ⊆ D.diagonalPrimeClasses →
              canonicalCompWithPackages (Finsupp.single prime coeff) (t.sum f) packages =
                canonicalCompWithPackages (Finsupp.single prime coeff) (t.sum f) (fun _ _ => pkg) := by
        intro t
        refine Finset.induction_on t ?_ ?_
        · intro _
          simp [canonicalCompWithPackages, f]
        · intro diagClass s hnotin ih hsub
          have hdiag_mem : diagClass ∈ D.diagonalPrimeClasses := hsub (by simp)
          have hsub_s : s ⊆ D.diagonalPrimeClasses := by
            intro x hx
            exact hsub (by simp [hx])
          rw [Finset.sum_insert hnotin, canonicalCompWithPackages_add_right,
            canonicalCompWithPackages_add_right, ih hsub_s]
          have hfirst :
              canonicalCompWithPackages
                (Finsupp.single prime coeff)
                (Finsupp.single diagClass 1)
                packages =
                canonicalCompWithPackages
                  (Finsupp.single prime coeff)
                  (Finsupp.single diagClass 1)
                  (fun _ _ => pkg) := by
            simpa [canonicalCompWithPackages,
              mul_comm, mul_left_comm, mul_assoc] using
              (show coeff • PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages
                    prime
                    diagClass
                    packages =
                  coeff • PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages
                    prime
                    diagClass
                    (fun _ _ => pkg) by
                dsimp [PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages, pkg]
                rw [hpackages prime diagClass hdiag_mem])
          exact congrArg (fun t =>
            t + canonicalCompWithPackages (Finsupp.single prime coeff) (s.sum f) (fun _ _ => pkg)) hfirst
      exact haux D.diagonalPrimeClasses (by intro x hx; exact hx)
    have hid :
        D.identityFiniteCorrespondence =
          (pkg.diagonalDecomposition Y).identityFiniteCorrespondence :=
      FiniteIrreducibleComponentDecomposition.identityFiniteCorrespondence_independent
        D (pkg.diagonalDecomposition Y)
    calc
      canonicalCompWithPackages
          (Finsupp.single prime coeff)
          D.identityFiniteCorrespondence
          packages =
        canonicalCompWithPackages
          (Finsupp.single prime coeff)
          D.identityFiniteCorrespondence
          (fun _ _ => pkg) := hconst
      _ = canonicalCompWithPackages
            (Finsupp.single prime coeff)
            ((pkg.diagonalDecomposition Y).identityFiniteCorrespondence)
            (fun _ _ => pkg) := by
              rw [hid]
      _ = Finsupp.single prime coeff :=
        canonicalCompWithPackages_const_id_right pkg (Finsupp.single prime coeff)

end FiniteCorrespondence

namespace SupportFiberProductImageCompositionPackageFamily

/-- The honest represented-level decomposition builder obtained by freezing a
package family on quotient geometric prime classes and evaluating it on
represented inputs. -/
def decomposition
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    {X Y Z : Geometry.SmSchemeOver k} →
    (P : RepresentedPrimeSupport X Y) →
    (Q : RepresentedPrimeSupport Y Z) →
    SupportFiberProductImageDecomposition P Q :=
  fun {_} {_} {_} P Q =>
    (packages (PrimeFiniteCorrespondenceGeom.ofRepresented P)
      (PrimeFiniteCorrespondenceGeom.ofRepresented Q)).decomposition P Q

/-- Left-compatibility for the decomposition builder induced by a package
family follows from the bundled left-compatibility of the frozen package. -/
theorem respects_left
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    {P P' : RepresentedPrimeSupport X Y}
    (h : PrimeSupportEquivalent P P')
    (Q : RepresentedPrimeSupport Y Z) :
    FiniteCorrespondencePresentation.toGeom
        (SupportFiberProductImageDecomposition.toPresentation
          (decomposition packages P Q)) =
      FiniteCorrespondencePresentation.toGeom
        (SupportFiberProductImageDecomposition.toPresentation
          (decomposition packages P' Q)) := by
  let pkg :=
    packages (PrimeFiniteCorrespondenceGeom.ofRepresented P)
      (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
  have hclass : PrimeFiniteCorrespondenceGeom.ofRepresented P =
      PrimeFiniteCorrespondenceGeom.ofRepresented P' := Quot.sound h
  simpa [decomposition, pkg, hclass] using pkg.respects_left h Q

/-- Right-compatibility for the decomposition builder induced by a package
family follows from the bundled right-compatibility of the frozen package. -/
theorem respects_right
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y)
    {Q Q' : RepresentedPrimeSupport Y Z}
    (h : PrimeSupportEquivalent Q Q') :
    FiniteCorrespondencePresentation.toGeom
        (SupportFiberProductImageDecomposition.toPresentation
          (decomposition packages P Q)) =
      FiniteCorrespondencePresentation.toGeom
        (SupportFiberProductImageDecomposition.toPresentation
          (decomposition packages P Q')) := by
  let pkg :=
    packages (PrimeFiniteCorrespondenceGeom.ofRepresented P)
      (PrimeFiniteCorrespondenceGeom.ofRepresented Q)
  have hclass : PrimeFiniteCorrespondenceGeom.ofRepresented Q =
      PrimeFiniteCorrespondenceGeom.ofRepresented Q' := Quot.sound h
  simpa [decomposition, pkg, hclass] using pkg.respects_right P h

/-- The represented-prime composition package induced by a global family of
binary support-fiber-product image composition packages. -/
def data
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k)) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) :=
  RepresentedPrimeFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation
    diagonalDecomposition
    (decomposition packages)
    (respects_left packages)
    (respects_right packages)

@[simp] theorem compPrime_eq_canonicalCompWithPackages
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (P : PrimeFiniteCorrespondenceGeom X Y)
    (Q : PrimeFiniteCorrespondenceGeom Y Z) :
    (data diagonalDecomposition packages).compPrime P Q =
      PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages P Q (fun x y => packages x y) := by
  refine Quotient.inductionOn P ?_
  intro PRep
  refine Quotient.inductionOn Q ?_
  intro QRep
  rfl

@[simp] theorem comp_eq_canonicalCompWithPackages
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k))
    {X Y Z : Geometry.SmSchemeOver k}
    (α : FiniteCorrespondence X Y)
    (β : FiniteCorrespondence Y Z) :
    FiniteCorrespondenceCompositionData.comp
      (data diagonalDecomposition packages).toFiniteCorrespondenceCompositionData
      α β =
        FiniteCorrespondence.canonicalCompWithPackages α β (fun x y => packages x y) := by
  classical
  apply Finsupp.induction_linear α
  · simp [FiniteCorrespondenceCompositionData.comp,
      FiniteCorrespondence.canonicalCompWithPackages]
  · intro α₁ α₂ ih₁ ih₂
    rw [FiniteCorrespondenceCompositionData.comp_add_left,
      FiniteCorrespondence.canonicalCompWithPackages_add_left, ih₁, ih₂]
  · intro prime coeff
    simp [FiniteCorrespondenceCompositionData.comp_single_left,
      FiniteCorrespondence.canonicalCompWithPackages]
    refine Finset.sum_congr rfl ?_
    intro Q _
    exact congrArg (fun t => (coeff * β Q) • t)
      (compPrime_eq_canonicalCompWithPackages
        (diagonalDecomposition := diagonalDecomposition)
        (packages := packages)
        (P := prime) (Q := Q))

/-- If the package family is constant on source-side diagonal classes with
respect to a chosen decomposition, the induced represented-level decomposition
builder uses the canonical left-identity decomposition on diagonal inputs. -/
theorem source_eq_diagonalLeftIdentity
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductImageCompositionPackage (k := k))
    (leftIdentityPackage :
      {X Y : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductImageCompositionPackage (k := k))
    (hleftpkg :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (diagClass : PrimeFiniteCorrespondenceGeom X X)
        (prime : PrimeFiniteCorrespondenceGeom X Y),
          diagClass ∈ (diagonalDecomposition X).diagonalPrimeClasses →
            packages diagClass prime = leftIdentityPackage prime)
    {X Y : Geometry.SmSchemeOver k}
    (P : RepresentedPrimeSupport X Y) :
    decomposition packages
        (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
        P =
      RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P := by
  let D := diagonalDecomposition X
  let diagClass : PrimeFiniteCorrespondenceGeom X X :=
    SourceIrreducibleComponent.diagonalPrimeGeom P.sourceComponent
  have hdiag_mem : diagClass ∈ D.diagonalPrimeClasses := by
    rcases D.exhaustive P.sourceComponent with ⟨listed, hiso⟩
    refine (FiniteIrreducibleComponentDecomposition.mem_diagonalPrimeClasses_iff D diagClass).2 ?_
    refine ⟨listed.1, listed.2, ?_⟩
    rw [← SourceIrreducibleComponent.diagonalPrimeGeom_eq_of_isoOverAmbient hiso]
  change (packages diagClass (PrimeFiniteCorrespondenceGeom.ofRepresented P)).decomposition _ _ = _
  rw [hleftpkg diagClass (PrimeFiniteCorrespondenceGeom.ofRepresented P) hdiag_mem]
  exact (leftIdentityPackage (PrimeFiniteCorrespondenceGeom.ofRepresented P)).source_eq_diagonalLeftIdentity P

end SupportFiberProductImageCompositionPackageFamily

/-- Canonical composition data built from a global family of honest binary
support-fiber-product image composition packages, together with the exact
identity and triple-coherence hypotheses needed to recover `SmCor(k)`. -/
structure CanonicalCompositionPackageData where
  diagonalDecomposition :
    (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X
  packages :
    {X Y Z : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    PrimeFiniteCorrespondenceGeom Y Z →
    SupportFiberProductImageCompositionPackage (k := k)
  leftIdentityPackage :
    {X Y : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    SupportFiberProductImageCompositionPackage (k := k)
  leftIdentity_constant :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (diagClass : PrimeFiniteCorrespondenceGeom X X)
      (prime : PrimeFiniteCorrespondenceGeom X Y),
        diagClass ∈ (diagonalDecomposition X).diagonalPrimeClasses →
          packages diagClass prime = leftIdentityPackage prime
  rightIdentityPackage :
    {X Y : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    SupportFiberProductImageCompositionPackage (k := k)
  rightIdentity_constant :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (prime : PrimeFiniteCorrespondenceGeom X Y)
      (diagClass : PrimeFiniteCorrespondenceGeom Y Y),
        diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
          packages prime diagClass = rightIdentityPackage prime
  source_eq_diagonalLeftIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        SupportFiberProductImageCompositionPackageFamily.decomposition packages
            (SourceIrreducibleComponent.diagonalRepresentedPrimeSupport P.sourceComponent)
            P =
          RepresentedPrimeCompositionDatum.diagonalLeftIdentityImageDecomposition P
  landing_eq_diagonalRightIdentity :
    ∀ {X Y : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport X Y),
        SupportFiberProductImageCompositionPackageFamily.decomposition packages P
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
          ((SupportFiberProductImageCompositionPackageFamily.data
            diagonalDecomposition packages).toFiniteCorrespondenceCompositionData)
          (FiniteCorrespondencePresentation.toGeom
            (SupportFiberProductImageDecomposition.toPresentation
              (SupportFiberProductImageCompositionPackageFamily.decomposition packages P Q)))
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
            FiniteCorrespondencePresentation.toGeom
              (leftPresentation P Q R)
  hright :
    ∀ {W X Y Z : Geometry.SmSchemeOver k}
      (P : RepresentedPrimeSupport W X)
      (Q : RepresentedPrimeSupport X Y)
      (R : RepresentedPrimeSupport Y Z),
        FiniteCorrespondenceCompositionData.comp
          ((SupportFiberProductImageCompositionPackageFamily.data
            diagonalDecomposition packages).toFiniteCorrespondenceCompositionData)
          (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
          (FiniteCorrespondencePresentation.toGeom
            (SupportFiberProductImageDecomposition.toPresentation
              (SupportFiberProductImageCompositionPackageFamily.decomposition packages Q R))) =
            FiniteCorrespondencePresentation.toGeom
              (rightPresentation P Q R)

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

namespace CanonicalCompositionPackageData

private def concreteLiftedPackageToImagePackage
    (pkg : SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    SupportFiberProductImageCompositionPackage (k := k) :=
  SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage pkg

private def concreteLiftedPackagesFamily
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    {X Y Z : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    PrimeFiniteCorrespondenceGeom Y Z →
    SupportFiberProductImageCompositionPackage (k := k) :=
  fun {X} {Y} {Z} x y =>
    concreteLiftedPackageToImagePackage
      (packages (X := X) (Y := Y) (Z := Z) x y)

private def concreteLiftedIdentityFamily
    (packages :
      {X Y : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    {X Y : Geometry.SmSchemeOver k} →
    PrimeFiniteCorrespondenceGeom X Y →
    SupportFiberProductImageCompositionPackage (k := k) :=
  fun {X} {Y} prime =>
    concreteLiftedPackageToImagePackage (packages (X := X) (Y := Y) prime)

private def concreteLiftedFamilyData
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) :=
  SupportFiberProductImageCompositionPackageFamily.data
    diagonalDecomposition
    (concreteLiftedPackagesFamily packages)

private def concreteLiftedFamilyCompositionData
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductLiftedImageCompositionPackage (k := k)) :
    FiniteCorrespondenceCompositionData (k := k) :=
  RepresentedPrimeFiniteCorrespondenceComposition.toFiniteCorrespondenceCompositionData
    (SupportFiberProductImageCompositionPackageFamily.data
      diagonalDecomposition
      (concreteLiftedPackagesFamily packages))

/-- Build canonical package-family data from a family of concrete lifted
packages. The resulting `packages` field is still computed by honest lifted
decomposition builders rather than supplied as an arbitrary abstract family. -/
def ofConcreteLiftedDecompositionFamily
    (diagonalDecomposition :
      (X : Geometry.SmSchemeOver k) → FiniteIrreducibleComponentDecomposition X)
    (packages :
      {X Y Z : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      PrimeFiniteCorrespondenceGeom Y Z →
      SupportFiberProductLiftedImageCompositionPackage (k := k))
    (leftIdentityPackage :
      {X Y : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductLiftedImageCompositionPackage (k := k))
    (leftIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (diagClass : PrimeFiniteCorrespondenceGeom X X)
        (prime : PrimeFiniteCorrespondenceGeom X Y),
          diagClass ∈ (diagonalDecomposition X).diagonalPrimeClasses →
            packages diagClass prime = leftIdentityPackage prime)
    (rightIdentityPackage :
      {X Y : Geometry.SmSchemeOver k} →
      PrimeFiniteCorrespondenceGeom X Y →
      SupportFiberProductLiftedImageCompositionPackage (k := k))
    (rightIdentity_constant :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (prime : PrimeFiniteCorrespondenceGeom X Y)
        (diagClass : PrimeFiniteCorrespondenceGeom Y Y),
          diagClass ∈ (diagonalDecomposition Y).diagonalPrimeClasses →
            packages prime diagClass = rightIdentityPackage prime)
    (landing_eq_diagonalRightIdentity :
      ∀ {X Y : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport X Y),
          SupportFiberProductImageCompositionPackageFamily.decomposition
              (concreteLiftedPackagesFamily packages)
              P
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
            (concreteLiftedFamilyCompositionData diagonalDecomposition packages)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (concreteLiftedPackagesFamily packages)
                  P Q)))
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented R) 1) =
              FiniteCorrespondencePresentation.toGeom (leftPresentation P Q R))
    (hright :
      ∀ {W X Y Z : Geometry.SmSchemeOver k}
        (P : RepresentedPrimeSupport W X)
        (Q : RepresentedPrimeSupport X Y)
        (R : RepresentedPrimeSupport Y Z),
          FiniteCorrespondenceCompositionData.comp
            (concreteLiftedFamilyCompositionData diagonalDecomposition packages)
            (Finsupp.single (PrimeFiniteCorrespondenceGeom.ofRepresented P) 1)
            (FiniteCorrespondencePresentation.toGeom
              (SupportFiberProductImageDecomposition.toPresentation
                (SupportFiberProductImageCompositionPackageFamily.decomposition
                  (concreteLiftedPackagesFamily packages)
                  Q R))) =
              FiniteCorrespondencePresentation.toGeom (rightPresentation P Q R)) :
    CanonicalCompositionPackageData (k := k) where
  diagonalDecomposition := diagonalDecomposition
  packages := concreteLiftedPackagesFamily packages
  leftIdentityPackage := concreteLiftedIdentityFamily leftIdentityPackage
  leftIdentity_constant := by
    intro X Y diagClass prime hdiag
    exact congrArg
      SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
      (leftIdentity_constant diagClass prime hdiag)
  rightIdentityPackage := concreteLiftedIdentityFamily rightIdentityPackage
  rightIdentity_constant := by
    intro X Y prime diagClass hdiag
    exact congrArg
      SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
      (rightIdentity_constant prime diagClass hdiag)
  source_eq_diagonalLeftIdentity := by
    intro X Y P
    exact SupportFiberProductImageCompositionPackageFamily.source_eq_diagonalLeftIdentity
      diagonalDecomposition
      (concreteLiftedPackagesFamily packages)
      (concreteLiftedIdentityFamily leftIdentityPackage)
      (fun diagClass prime hdiag =>
        congrArg
          SupportFiberProductLiftedImageCompositionPackage.toSupportFiberProductImageCompositionPackage
          (leftIdentity_constant diagClass prime hdiag))
      P
  landing_eq_diagonalRightIdentity := landing_eq_diagonalRightIdentity
  leftPresentation := leftPresentation
  rightPresentation := rightPresentation
  hpresentation := hpresentation
  hleft := hleft
  hright := hright

/-- The represented-prime composition model induced by the package family. -/
def data (composition : CanonicalCompositionPackageData (k := k)) :
    RepresentedPrimeFiniteCorrespondenceComposition (k := k) :=
  SupportFiberProductImageCompositionPackageFamily.data
    composition.diagonalDecomposition
    composition.packages

/-- The literature-shaped finite-correspondence composition package induced by
the canonical package family data. -/
def toGeometricFiniteCorrespondenceComposition
    (composition : CanonicalCompositionPackageData (k := k)) :
    GeometricFiniteCorrespondenceComposition (k := k) :=
  GeometricFiniteCorrespondenceComposition.ofSupportFiberProductImagePresentation_of_eq_diagonalIdentities
    composition.diagonalDecomposition
    (SupportFiberProductImageCompositionPackageFamily.decomposition composition.packages)
    (SupportFiberProductImageCompositionPackageFamily.respects_left composition.packages)
    (SupportFiberProductImageCompositionPackageFamily.respects_right composition.packages)
    composition.source_eq_diagonalLeftIdentity
    composition.landing_eq_diagonalRightIdentity
    composition.leftPresentation
    composition.rightPresentation
    composition.hpresentation
    composition.hleft
    composition.hright

/-- The induced prime-level associativity bridge for the canonical package
family data. -/
theorem assoc_prime
    (composition : CanonicalCompositionPackageData (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : PrimeFiniteCorrespondenceGeom W X)
    (g : PrimeFiniteCorrespondenceGeom X Y)
    (h : PrimeFiniteCorrespondenceGeom Y Z) :
    FiniteCorrespondence.canonicalCompWithPackages
      (PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages f g
        (fun x y => composition.packages x y))
      (Finsupp.single h 1)
      (fun x y => composition.packages x y) =
        FiniteCorrespondence.canonicalCompWithPackages
          (Finsupp.single f 1)
          (PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages g h
            (fun x y => composition.packages x y))
          (fun x y => composition.packages x y) := by
  let data := composition.data
  have hfg :
      FiniteCorrespondenceCompositionData.compPrime
        data.toFiniteCorrespondenceCompositionData f g =
      PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages f g
        (fun x y => composition.packages x y) := by
    change (SupportFiberProductImageCompositionPackageFamily.data
        composition.diagonalDecomposition
        (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData.compPrime
        f g = _
    exact SupportFiberProductImageCompositionPackageFamily.compPrime_eq_canonicalCompWithPackages
      composition.diagonalDecomposition (fun x y => composition.packages x y) f g
  have hgh :
      FiniteCorrespondenceCompositionData.compPrime
        data.toFiniteCorrespondenceCompositionData g h =
      PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages g h
        (fun x y => composition.packages x y) := by
    change (SupportFiberProductImageCompositionPackageFamily.data
        composition.diagonalDecomposition
        (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData.compPrime
        g h = _
    exact SupportFiberProductImageCompositionPackageFamily.compPrime_eq_canonicalCompWithPackages
      composition.diagonalDecomposition (fun x y => composition.packages x y) g h
  have hAssoc :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData f g)
        (Finsupp.single h 1) =
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single f 1)
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData g h) := by
    simpa [CanonicalCompositionPackageData.toGeometricFiniteCorrespondenceComposition,
      CanonicalCompositionPackageData.data, data] using
      (composition.toGeometricFiniteCorrespondenceComposition).assoc_prime f g h
  have hOuterLeft :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData f g)
        (Finsupp.single h 1) =
      FiniteCorrespondence.canonicalCompWithPackages
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData f g)
        (Finsupp.single h 1)
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData f g)
        (Finsupp.single h 1) = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition
      (fun x y => composition.packages x y)
      (FiniteCorrespondenceCompositionData.compPrime
        data.toFiniteCorrespondenceCompositionData f g)
      (Finsupp.single h 1)
  have hOuterRight :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (Finsupp.single f 1)
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData g h) =
      FiniteCorrespondence.canonicalCompWithPackages
        (Finsupp.single f 1)
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData g h)
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        (Finsupp.single f 1)
        (FiniteCorrespondenceCompositionData.compPrime
          data.toFiniteCorrespondenceCompositionData g h) = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition
      (fun x y => composition.packages x y)
      (Finsupp.single f 1)
      (FiniteCorrespondenceCompositionData.compPrime
        data.toFiniteCorrespondenceCompositionData g h)
  calc
    FiniteCorrespondence.canonicalCompWithPackages
        (PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages f g
          (fun x y => composition.packages x y))
        (Finsupp.single h 1)
        (fun x y => composition.packages x y)
      = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.compPrime
            data.toFiniteCorrespondenceCompositionData f g)
          (Finsupp.single h 1) := by
            rw [← hfg]
            exact hOuterLeft.symm
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (Finsupp.single f 1)
          (FiniteCorrespondenceCompositionData.compPrime
            data.toFiniteCorrespondenceCompositionData g h) := hAssoc
    _ = FiniteCorrespondence.canonicalCompWithPackages
          (Finsupp.single f 1)
          (PrimeFiniteCorrespondenceGeom.canonicalCompWithPackages g h
            (fun x y => composition.packages x y))
          (fun x y => composition.packages x y) := by
            rw [← hgh]
            exact hOuterRight

/-- The correspondence category induced by the canonical package family data. -/
def toSmCor (composition : CanonicalCompositionPackageData (k := k)) :
    SmCor (k := k) :=
  (composition.toGeometricFiniteCorrespondenceComposition).toSmCor

/-- The rationalized correspondence category induced by the canonical package
family data. This is the Q-linearization of `CanonicalCompositionPackageData.toSmCor`. -/
def canonicalSmCorQ (composition : CanonicalCompositionPackageData (k := k)) :
    SmCorQ (k := k) where
  integral := composition.toSmCor

/-- Bilinear associativity for the finite-correspondence composition induced by
the canonical package family data. -/
theorem assoc
    (composition : CanonicalCompositionPackageData (k := k))
    {W X Y Z : Geometry.SmSchemeOver k}
    (f : FiniteCorrespondence W X)
    (g : FiniteCorrespondence X Y)
    (h : FiniteCorrespondence Y Z) :
    FiniteCorrespondence.canonicalCompWithPackages
      (FiniteCorrespondence.canonicalCompWithPackages f g
        (fun x y => composition.packages x y))
      h
      (fun x y => composition.packages x y) =
        FiniteCorrespondence.canonicalCompWithPackages
          f
          (FiniteCorrespondence.canonicalCompWithPackages g h
            (fun x y => composition.packages x y))
          (fun x y => composition.packages x y) := by
  let data := composition.data
  have hfg :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        f g =
      FiniteCorrespondence.canonicalCompWithPackages f g
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        f g = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition (fun x y => composition.packages x y) f g
  have hgh :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        g h =
      FiniteCorrespondence.canonicalCompWithPackages g h
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        g h = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition (fun x y => composition.packages x y) g h
  have hAssoc :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f g)
        h =
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        f
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          g h) := by
    have hAssoc' := (composition.toSmCor).laws.assoc f g h
    change FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f g)
        h =
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        f
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          g h) at hAssoc'
    exact hAssoc'
  have hOuterLeft :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f g)
        h =
      FiniteCorrespondence.canonicalCompWithPackages
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f g)
        h
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f g)
        h = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition
      (fun x y => composition.packages x y)
      (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        f g)
      h
  have hOuterRight :
      FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        f
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          g h) =
      FiniteCorrespondence.canonicalCompWithPackages
        f
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          g h)
        (fun x y => composition.packages x y) := by
    change FiniteCorrespondenceCompositionData.comp
        (SupportFiberProductImageCompositionPackageFamily.data
          composition.diagonalDecomposition
          (fun x y => composition.packages x y)).toFiniteCorrespondenceCompositionData
        f
        (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          g h) = _
    exact SupportFiberProductImageCompositionPackageFamily.comp_eq_canonicalCompWithPackages
      composition.diagonalDecomposition
      (fun x y => composition.packages x y)
      f
      (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
        g h)
  calc
    FiniteCorrespondence.canonicalCompWithPackages
        (FiniteCorrespondence.canonicalCompWithPackages f g
          (fun x y => composition.packages x y))
        h
        (fun x y => composition.packages x y)
      = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            f g)
          h := by
            rw [← hfg]
            exact hOuterLeft.symm
    _ = FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
          f
          (FiniteCorrespondenceCompositionData.comp data.toFiniteCorrespondenceCompositionData
            g h) := hAssoc
    _ = FiniteCorrespondence.canonicalCompWithPackages
          f
          (FiniteCorrespondence.canonicalCompWithPackages g h
            (fun x y => composition.packages x y))
          (fun x y => composition.packages x y) := by
            rw [← hgh]
            exact hOuterRight

end CanonicalCompositionPackageData

end RepresentedPrimeFiniteCorrespondenceComposition

end

end Boundary

import Boundary.PolynomialSmoothness.StandardSmoothDimensionZero.FieldLocalizationAtPrime
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Jacobson
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.LocalizationLocalization

universe u

namespace Boundary

noncomputable section

variable {k : Type u} [Field k]

namespace _root_.Algebra

/-- After localizing a relative-dimension-zero standard smooth ring map at a
prime of the target and its comap on the base, the induced local map is
formally étale. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_formallyEtale_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    let q : Ideal R := Ideal.comap φ p
    @Algebra.FormallyEtale (Localization.AtPrime q) (Localization.AtPrime p) _ _
      (Localization.localRingHom q p φ rfl).toAlgebra := by
  let hloc :
      let q : Ideal R := Ideal.comap φ p
      RingHom.IsStandardSmoothOfRelativeDimension 0
        (Localization.localRingHom q p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_localizationAtPrime φ hφ p
  dsimp at hloc ⊢
  rw [RingHom.IsStandardSmoothOfRelativeDimension] at hloc
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      (Localization.AtPrime (Ideal.comap φ p)) (Localization.AtPrime p) := hloc
  exact Algebra.IsStandardSmoothOfRelativeDimension.formallyEtale

/-- After localizing a relative-dimension-zero standard smooth ring map at a
prime of the target and its comap on the base, the induced local map is
étale. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_etale_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    let q : Ideal R := Ideal.comap φ p
    @Algebra.Etale (Localization.AtPrime q) (Localization.AtPrime p) _ _
      (Localization.localRingHom q p φ rfl).toAlgebra := by
  let hloc :
      let q : Ideal R := Ideal.comap φ p
      RingHom.IsStandardSmoothOfRelativeDimension 0
        (Localization.localRingHom q p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_localizationAtPrime φ hφ p
  dsimp at hloc ⊢
  rw [RingHom.IsStandardSmoothOfRelativeDimension] at hloc
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      (Localization.AtPrime (Ideal.comap φ p)) (Localization.AtPrime p) := hloc
  exact Algebra.IsStandardSmoothOfRelativeDimension.etale

/-- After localizing a relative-dimension-zero standard smooth ring map at a
prime of the target and its comap on the base, the induced local map is flat.
This is the canonical local flatness theorem needed for the remaining
domain/local-irreducibility route. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_flat_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    RingHom.Flat (Localization.localRingHom (Ideal.comap φ p) p φ rfl) := by
  letI : Algebra.Etale
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) :=
    ringHom_standardSmoothOfRelativeDimensionZero_etale_localizationAtPrime φ hφ p
  infer_instance

/-- If the localized relative-dimension-zero standard-smooth map is flat, then
its target algebra is free over the localized base local ring. This is the
canonical local-freeness support theorem needed before the local-domain
argument. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_free_localizationAtPrime_of_flat
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime]
    [RingHom.Flat (Localization.localRingHom (Ideal.comap φ p) p φ rfl)] :
    let q : Ideal R := Ideal.comap φ p
    @Module.Free (Localization.AtPrime q) (Localization.AtPrime p) _ _ _ := by
  let hloc :
      let q : Ideal R := Ideal.comap φ p
      RingHom.IsStandardSmoothOfRelativeDimension 0
        (Localization.localRingHom q p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_localizationAtPrime φ hφ p
  dsimp at hloc ⊢
  have hlocStd :
      RingHom.IsStandardSmooth
        (Localization.localRingHom (Ideal.comap φ p) p φ rfl) := by
    rw [RingHom.IsStandardSmooth]
    rw [RingHom.IsStandardSmoothOfRelativeDimension] at hloc
    letI : Algebra.IsStandardSmoothOfRelativeDimension 0
        (Localization.AtPrime (Ideal.comap φ p)) (Localization.AtPrime p) := hloc
    exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth
      (n := 0) (R := Localization.AtPrime (Ideal.comap φ p))
      (S := Localization.AtPrime p)
  letI : @Algebra.FinitePresentation
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) _ _ _
      (Localization.localRingHom (Ideal.comap φ p) p φ rfl).toAlgebra :=
    by
      rw [RingHom.IsStandardSmooth] at hlocStd
      letI : Algebra.IsStandardSmooth
          (Localization.AtPrime (Ideal.comap φ p))
          (Localization.AtPrime p) := hlocStd
      exact standardSmooth_finitePresentation
  exact Module.free_of_flat_of_isLocalRing

/-- If the localized relative-dimension-zero standard-smooth map is flat, then
its target algebra is finite over the localized base local ring. This packages
the free + formally-unramified consequence under the exact local hypotheses
used by the remaining domain proof. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_finite_localizationAtPrime_of_flat
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime]
    [RingHom.Flat (Localization.localRingHom (Ideal.comap φ p) p φ rfl)] :
    let q : Ideal R := Ideal.comap φ p
    @Module.Finite (Localization.AtPrime q) (Localization.AtPrime p) _ _ _ := by
  letI : @Module.Free
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) _ _ _ :=
    ringHom_standardSmoothOfRelativeDimensionZero_free_localizationAtPrime_of_flat φ hφ p
  letI : @Algebra.FormallyUnramified
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) _ _
      (Localization.localRingHom (Ideal.comap φ p) p φ rfl).toAlgebra := by
    letI : @Algebra.FormallyEtale
        (Localization.AtPrime (Ideal.comap φ p))
        (Localization.AtPrime p) _ _
        (Localization.localRingHom (Ideal.comap φ p) p φ rfl).toAlgebra :=
      ringHom_standardSmoothOfRelativeDimensionZero_formallyEtale_localizationAtPrime φ hφ p
    infer_instance
  exact Algebra.FormallyUnramified.finite_of_free

/-- The target of a relative-dimension-zero standard-smooth ring map localized
at a prime is free over the localized base local ring. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_free_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    let q : Ideal R := Ideal.comap φ p
    @Module.Free (Localization.AtPrime q) (Localization.AtPrime p) _ _ _ := by
  letI : RingHom.Flat (Localization.localRingHom (Ideal.comap φ p) p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_flat_localizationAtPrime φ hφ p
  exact ringHom_standardSmoothOfRelativeDimensionZero_free_localizationAtPrime_of_flat φ hφ p

/-- The target of a relative-dimension-zero standard-smooth ring map localized
at a prime is finite over the localized base local ring. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_finite_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    let q : Ideal R := Ideal.comap φ p
    @Module.Finite (Localization.AtPrime q) (Localization.AtPrime p) _ _ _ := by
  letI : RingHom.Flat (Localization.localRingHom (Ideal.comap φ p) p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_flat_localizationAtPrime φ hφ p
  exact ringHom_standardSmoothOfRelativeDimensionZero_finite_localizationAtPrime_of_flat φ hφ p

/-- The localized target of a relative-dimension-zero standard-smooth map is
integral over the localized base. This is the canonical finiteness-to-integral
upgrade needed before the remaining prime-contraction argument. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_isIntegral_localizationAtPrime
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime] :
    Algebra.IsIntegral
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) := by
  letI : Module.Finite
      (Localization.AtPrime (Ideal.comap φ p))
      (Localization.AtPrime p) :=
    ringHom_standardSmoothOfRelativeDimensionZero_finite_localizationAtPrime φ hφ p
  exact Algebra.IsIntegral.of_finite

/-- Let `R → A` be relative-dimension-zero standard smooth, `p` a prime of `A`,
and `P` a prime of `A_p`. If `P` lies over the generic point of the localized
base `R_q`, then the local ring `(A_p)_P` is a field. This is the prime-local
generic-point theorem needed before proving the full local-domain statement over
an arbitrary local domain. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_isField_localizationAtPrime_of_comap_bot
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime]
    (P : Ideal (Localization.AtPrime p)) [P.IsPrime]
    (hP :
      Ideal.comap
        (algebraMap (Localization.AtPrime (Ideal.comap φ p)) (Localization.AtPrime p))
        P = ⊥) :
    IsField (Localization.AtPrime P) := by
  let q : Ideal R := Ideal.comap φ p
  have hloc :
      RingHom.IsStandardSmoothOfRelativeDimension 0
        (Localization.localRingHom q p φ rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_localizationAtPrime φ hφ p
  have hlocP :
      RingHom.IsStandardSmoothOfRelativeDimension 0
        (Localization.localRingHom
          (Ideal.comap (Localization.localRingHom q p φ rfl) P)
          P
          (Localization.localRingHom q p φ rfl)
          rfl) :=
    ringHom_standardSmoothOfRelativeDimensionZero_localizationAtPrime
      (Localization.localRingHom q p φ rfl) hloc P
  rw [RingHom.IsStandardSmoothOfRelativeDimension] at hlocP
  dsimp at hlocP
  letI : IsDomain (Localization.AtPrime q) := inferInstance
  letI : Field (Localization.AtPrime (⊥ : Ideal (Localization.AtPrime q))) :=
    IsFractionRing.toField
      (Localization.AtPrime q)
      (Localization.AtPrime (⊥ : Ideal (Localization.AtPrime q)))
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0
      (Localization.AtPrime (⊥ : Ideal (Localization.AtPrime q)))
      (Localization.AtPrime P) := by
    simpa [hP] using hlocP
  exact
    standardSmoothOfRelativeDimensionZero_isField_of_isLocalRing
      (k := Localization.AtPrime (⊥ : Ideal (Localization.AtPrime q)))

/-- If a relative-dimension-zero standard-smooth prime `p` lies over the
generic point of the base, then the local ring `A_p` is already a field. This
is the arbitrary-base generic-point analogue of the field-base theorem
`standardSmoothOfRelativeDimensionZero_isField_atPrime`. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_isField_atPrime_of_comap_bot
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime]
    (hp : Ideal.comap φ p = ⊥) :
    IsField (Localization.AtPrime p) := by
  let q : Ideal R := Ideal.comap φ p
  have hbotPrime : (⊥ : Ideal R).IsPrime := by
    rw [← hp]
    exact Ideal.comap_isPrime φ p
  letI : (⊥ : Ideal R).IsPrime := hbotPrime
  have hq : q = ⊥ := hp
  letI : IsDomain (R ⧸ (⊥ : Ideal R)) := Ideal.Quotient.isDomain (I := (⊥ : Ideal R))
  letI : IsDomain R := (RingEquiv.quotientBot (R := R)).symm.isDomain
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) :=
    IsFractionRing.toField R (Localization.AtPrime (⊥ : Ideal R))
  have hMax :
      Ideal.comap
        (algebraMap (Localization.AtPrime (⊥ : Ideal R)) (Localization.AtPrime p))
        (IsLocalRing.maximalIdeal (Localization.AtPrime p)) = ⊥ := by
    have hComap :
        Ideal.comap
          (algebraMap (Localization.AtPrime (⊥ : Ideal R)) (Localization.AtPrime p))
          (IsLocalRing.maximalIdeal (Localization.AtPrime p)) =
            IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal R)) := by
      exact ((IsLocalRing.local_hom_TFAE
        (algebraMap (Localization.AtPrime (⊥ : Ideal R)) (Localization.AtPrime p))).out 0 4 inferInstance)
    simpa using hComap
  exact
    ringHom_standardSmoothOfRelativeDimensionZero_isField_localizationAtPrime_of_comap_bot
      φ hφ p (IsLocalRing.maximalIdeal (Localization.AtPrime p)) (by simpa using hMax)

/-- Minimal primes of a localized relative-dimension-zero standard-smooth
target that lie over the generic point of the localized base have field
localizations. This is the exact generic-point statement used when attacking
the remaining local-domain theorem via minimal primes. -/
theorem ringHom_standardSmoothOfRelativeDimensionZero_isField_atMinimalPrime_of_comap_bot
    {R A : Type u} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (hφ : RingHom.IsStandardSmoothOfRelativeDimension 0 φ)
    (p : Ideal A) [p.IsPrime]
    (P : Ideal (Localization.AtPrime p)) [P.IsPrime]
    (hPmin : P ∈ minimalPrimes (Localization.AtPrime p))
    (hP :
      Ideal.comap
        (algebraMap (Localization.AtPrime (Ideal.comap φ p)) (Localization.AtPrime p))
        P = ⊥) :
    IsField (Localization.AtPrime P) :=
  ringHom_standardSmoothOfRelativeDimensionZero_isField_localizationAtPrime_of_comap_bot
    φ hφ p P hP

/-- An integral domain has a unique minimal prime, namely `⊥`. This is the
base-side minimal-prime theorem used in the remaining local-domain proof after
localizing the polynomial base at a prime. -/
theorem minimalPrimes_eq_subsingleton_bot_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R] :
    minimalPrimes R = ({⊥} : Set (Ideal R)) := by
  rw [minimalPrimes]
  exact Ideal.minimalPrimes_eq_subsingleton_self (I := (⊥ : Ideal R))

/-- After localizing a domain at a prime, the localized base still has the
unique minimal prime `⊥`. -/
theorem localizationAtPrime_minimalPrimes_eq_subsingleton_bot_of_isDomain
    {R : Type u} [CommRing R] [IsDomain R]
    (q : Ideal R) [q.IsPrime] :
    minimalPrimes (Localization.AtPrime q) =
      ({⊥} : Set (Ideal (Localization.AtPrime q))) := by
  letI : IsDomain (Localization.AtPrime q) := inferInstance
  exact minimalPrimes_eq_subsingleton_bot_of_isDomain

/-- Relative-dimension-zero standard smoothness over a field is preserved by
localization at a prime of the target algebra. -/
theorem standardSmoothOfRelativeDimensionZero_localizationAtPrime
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A]
    (p : Ideal A) [p.IsPrime] :
    Algebra.IsStandardSmoothOfRelativeDimension 0 k (Localization.AtPrime p) := by
  exact standardSmoothOfRelativeDimensionZero_localizationAtPrime (k := k) (A := A) p

/-- Every prime localization of a relative-dimension-zero standard smooth
algebra over a field is a field. -/
theorem standardSmoothOfRelativeDimensionZero_isField_atPrime
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A]
    (p : Ideal A) [p.IsPrime] :
    IsField (Localization.AtPrime p) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 k (Localization.AtPrime p) :=
    standardSmoothOfRelativeDimensionZero_localizationAtPrime (k := k) p
  letI : Algebra.IsStandardSmooth k (Localization.AtPrime p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth
      (n := 0) (R := k) (S := Localization.AtPrime p)
  letI : Algebra.FinitePresentation k (Localization.AtPrime p) :=
    standardSmooth_finitePresentation
  letI : Algebra.FiniteType k (Localization.AtPrime p) := by
    infer_instance
  letI : Algebra.FormallyEtale k (Localization.AtPrime p) :=
    Algebra.IsStandardSmoothOfRelativeDimension.formallyEtale
  exact formallyEtale_isField_of_field_of_isLocalRing (k := k) (A := Localization.AtPrime p)

/-- A surjective ring homomorphism from a field has field target. -/
theorem isField_of_surjective
    {K R : Type u} [Field K] [CommRing R] [Nontrivial R]
    (f : K →+* R) (hf : Function.Surjective f) :
    IsField R := by
  have hker : RingHom.ker f = ⊥ := by
    rcases Ideal.eq_bot_or_top (RingHom.ker f) with hbot | htop
    · exact hbot
    · exfalso
      have h1 : (1 : K) ∈ RingHom.ker f := by
        simpa [htop]
      have : (1 : R) = 0 := by
        simpa [RingHom.mem_ker] using h1
      exact one_ne_zero this
  let e : K ⧸ RingHom.ker f ≃+* R := RingHom.quotientKerEquivOfSurjective hf
  letI : Field (K ⧸ RingHom.ker f) := by
    simpa [hker] using (inferInstance : Field (K ⧸ (⊥ : Ideal K)))
  exact e.isField _

/-- In a relative-dimension-zero standard smooth algebra over a field, every
prime ideal is minimal. Equivalently, every chain of primes below `p` is
trivial because the localization at `p` is a field. -/
theorem standardSmoothOfRelativeDimensionZero_prime_isMinimal
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A]
    (p q : Ideal A) [p.IsPrime] [q.IsPrime] (hqp : q ≤ p) :
    q = p := by
  let e :=
    IsLocalization.AtPrime.orderIsoOfPrime
      (S := Localization.AtPrime p) p
  have hs :
      e.symm ⟨q, inferInstance, hqp⟩ =
        e.symm ⟨p, inferInstance, le_rfl⟩ := by
    apply Subtype.ext
    exact (Ideal.eq_bot_of_prime : (e.symm ⟨q, inferInstance, hqp⟩).1 = ⊥).trans
      (Ideal.eq_bot_of_prime : (e.symm ⟨p, inferInstance, le_rfl⟩).1 = ⊥).symm
  exact Subtype.ext_iff.mp (e.symm.injective hs)

/-- In a relative-dimension-zero standard smooth algebra over a field, every
prime ideal is maximal. The proof passes to the quotient by `p`, localizes at
an arbitrary maximal ideal there, and uses the fact that the localized quotient
is a surjective image of the field `A_q`. -/
theorem standardSmoothOfRelativeDimensionZero_prime_isMaximal
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A]
    (p : Ideal A) [p.IsPrime] :
    p.IsMaximal := by
  let B := A ⧸ p
  let π : A →+* B := Ideal.Quotient.mk p
  have hBfield : IsField B := by
    letI : IsDomain B := Ideal.Quotient.isDomain p
    suffices hbotMax : (⊥ : Ideal B).IsMaximal by
      simpa using
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient (⊥ : Ideal B)).mp hbotMax)
    obtain ⟨m, hm⟩ := Ideal.exists_maximal B
    have hmzero : m = ⊥ := by
      let q : Ideal A := Ideal.comap π m
      have hqprime : q.IsPrime := Ideal.comap_isPrime π m
      letI : q.IsPrime := hqprime
      have hsurj :
          Function.Surjective
            (Localization.localRingHom q m π rfl) :=
        RingHom.surjective_localRingHom_of_surjective π Ideal.Quotient.mk_surjective m
      have hsourceField : IsField (Localization.AtPrime q) :=
        standardSmoothOfRelativeDimensionZero_isField_atPrime (k := k) q
      letI : Field (Localization.AtPrime q) := hsourceField.toField
      have htargetField : IsField (Localization.AtPrime m) :=
        isField_of_surjective
          (Localization.localRingHom q m π rfl) hsurj
      calc
        m = Ideal.comap (algebraMap B (Localization.AtPrime m))
              (IsLocalRing.maximalIdeal (Localization.AtPrime m)) := by
              symm
              exact Localization.AtPrime.comap_maximalIdeal (I := m)
        _ = Ideal.comap (algebraMap B (Localization.AtPrime m)) (⊥ : Ideal (Localization.AtPrime m)) := by
              rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp htargetField]
        _ = RingHom.ker (algebraMap B (Localization.AtPrime m)) := by
              rw [RingHom.ker_eq_comap_bot]
        _ = ⊥ := by
              rw [RingHom.injective_iff_ker_eq_bot]
              exact IsLocalization.injective (Localization.AtPrime m)
                m.primeCompl_le_nonZeroDivisors
    simpa [hmzero] using hm
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mpr hBfield

/-- The prime spectrum of a relative-dimension-zero standard smooth algebra
over a field is discrete. -/
theorem standardSmoothOfRelativeDimensionZero_discretePrimeSpectrum
    {A : Type u} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A] :
    DiscreteTopology (PrimeSpectrum A) := by
  letI : Algebra.IsStandardSmooth k A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 0) (R := k) (S := A)
  letI : Algebra.FinitePresentation k A := standardSmooth_finitePresentation
  letI : Algebra.FiniteType k A := by infer_instance
  letI : IsNoetherianRing A := by infer_instance
  letI : IsJacobsonRing A := by infer_instance
  refine (singletons_open_iff_discrete).2 ?_
  intro x
  have hClosed : IsClosed ({x} : Set (PrimeSpectrum A)) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr
      (standardSmoothOfRelativeDimensionZero_prime_isMaximal (k := k) x.asIdeal)
  have hStable : StableUnderGeneralization ({x} : Set (PrimeSpectrum A)) := by
    rw [PrimeSpectrum.stableUnderGeneralization_singleton, ← PrimeSpectrum.isMin_iff]
    intro y hy
    exact PrimeSpectrum.ext
      (standardSmoothOfRelativeDimensionZero_prime_isMinimal
        (k := k) x.asIdeal y.asIdeal hy)
  exact (PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing x).out 2 0
    ⟨hClosed, hStable⟩

/-- Zariski-lemma form needed for zero-dimensional étale chart rings: a
finitely generated domain over a field whose elements are algebraic over the
base is already a field. -/
theorem isField_of_finiteType_of_isDomain_of_isAlgebraic
    {A : Type u} [CommRing A] [Algebra k A] [IsDomain A]
    [Algebra.FiniteType k A]
    (hAlg : Algebra.IsAlgebraic k A) :
    IsField A := by
  letI : Algebra.IsIntegral k A := Algebra.IsAlgebraic.isIntegral (K := k) (A := A)
  let hFin : (algebraMap k A).Finite :=
    (show RingHom.IsIntegral (algebraMap k A) from inferInstance).to_finite inferInstance
  letI : Module.Finite k A := hFin.out
  refine ⟨⟨inferInstance⟩, ?_⟩
  intro x hx
  let μ : A →ₗ[k] A :=
    Algebra.lmul k A x
  have hμinj : Function.Injective μ := by
    intro y z hyz
    apply sub_eq_zero.mp
    apply mul_left_cancel₀ hx
    simpa [μ, sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hyz
  have hμsurj : Function.Surjective μ :=
    LinearMap.surjective_of_injective hμinj
  obtain ⟨y, hy⟩ := hμsurj 1
  exact ⟨y, hy⟩

/-- Localizing a relative-dimension-zero standard smooth algebra at a principal
open preserves formal étaleness. This is the algebra-owner localization step
needed for pointwise chart arguments. -/
theorem localizationAway_standardSmoothOfRelativeDimensionZero_formallyEtale
    {R A Aᵣ : Type u} [CommRing R] [CommRing A] [CommRing Aᵣ]
    [Algebra R A] [Algebra A Aᵣ] [Algebra R Aᵣ]
    [IsScalarTower R A Aᵣ]
    (r : A) [IsLocalization.Away r Aᵣ]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 R A] :
    Algebra.FormallyEtale R Aᵣ := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 A Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
  have h :
      Algebra.IsStandardSmoothOfRelativeDimension (0 + 0) R Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans
      (n := 0) (m := 0) (R := R) (S := A) (T := Aᵣ)
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R Aᵣ :=
    Nat.zero_add 0 ▸ h
  exact Algebra.IsStandardSmoothOfRelativeDimension.formallyEtale

/-- Localizing a relative-dimension-zero standard smooth algebra at a principal
open preserves étaleness. -/
theorem localizationAway_standardSmoothOfRelativeDimensionZero_etale
    {R A Aᵣ : Type u} [CommRing R] [CommRing A] [CommRing Aᵣ]
    [Algebra R A] [Algebra A Aᵣ] [Algebra R Aᵣ]
    [IsScalarTower R A Aᵣ]
    (r : A) [IsLocalization.Away r Aᵣ]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 R A] :
    Algebra.Etale R Aᵣ := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 A Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
  have h :
      Algebra.IsStandardSmoothOfRelativeDimension (0 + 0) R Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans
      (n := 0) (m := 0) (R := R) (S := A) (T := Aᵣ)
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 R Aᵣ :=
    Nat.zero_add 0 ▸ h
  exact Algebra.IsStandardSmoothOfRelativeDimension.etale

/-- Localizing a relative-dimension-zero standard smooth algebra at a principal
open preserves reducedness over a field. -/
theorem localizationAway_isReduced_of_standardSmoothOfRelativeDimensionZero
    {A Aᵣ : Type u} [CommRing A] [CommRing Aᵣ]
    [Algebra k A] [Algebra A Aᵣ] [Algebra k Aᵣ]
    [IsScalarTower k A Aᵣ]
    (r : A) [IsLocalization.Away r Aᵣ]
    [Algebra.IsStandardSmoothOfRelativeDimension 0 k A] :
    _root_.IsReduced Aᵣ := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 A Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away r
  have h :
      Algebra.IsStandardSmoothOfRelativeDimension (0 + 0) k Aᵣ :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans
      (n := 0) (m := 0) (R := k) (S := A) (T := Aᵣ)
  letI : Algebra.IsStandardSmoothOfRelativeDimension 0 k Aᵣ :=
    Nat.zero_add 0 ▸ h
  exact isReduced_of_standardSmoothOfRelativeDimensionZero (k := k) (A := Aᵣ)

end _root_.Algebra

end Boundary

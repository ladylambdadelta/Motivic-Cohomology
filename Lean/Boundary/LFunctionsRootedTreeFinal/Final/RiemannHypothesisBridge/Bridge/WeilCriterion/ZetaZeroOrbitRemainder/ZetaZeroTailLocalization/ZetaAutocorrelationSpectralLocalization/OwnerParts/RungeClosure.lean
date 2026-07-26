import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.ForcedDaggerTailParts.Reconstruction

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Completed zeros outside the excluded zero set avoid the dagger-closed constraints. -/
theorem autocorrelationSpectralEvalFiber_completedZero_daggerExclusion
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hdaggerExcluded :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∀ ρ : ℂ,
      ZetaCompletedZero ρ →
        ρ ∉ S →
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P :=
  hdaggerExcluded

/-- Noncircular zero-tail closure density for autocorrelation spectral fibers. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure
    (hRunge : AutocorrelationSpectralEvalFiberZeroTailSmallValuesRunge)
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSeparated :
      ∀ ρ : ℂ,
        ZetaCompletedZero ρ →
          ρ ∉ S →
            zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    (0 : ℝ) ∈ closure
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
    S P f₀
    (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRungeCore
      hRunge S P f₀ hSeparated)

variable
  (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
  (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
  (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
  (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
  (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
  (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
  (hZeroTailClosureOwnerRunge :
    AutocorrelationSpectralEvalFiberZeroTailClosureRunge)

include hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  hZeroTailClosureOwnerRunge

/-- Nonlinear finite autocorrelation-cone density in the zero-tail quotient. -/
theorem autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) :=
  let hConcreteClosure :
      (0 : ℝ) ∈
        closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
    hZeroTailClosureOwnerRunge
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀
  let hConcrete_eq_quotient :
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ =
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀ :=
    Eq.trans
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
        S P f₀).symm
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀)
  Eq.subst
    (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
    hConcrete_eq_quotient
    hConcreteClosure

/-- Positive-cone/GNS density at the quotient-level zero-tail functional. -/
theorem seedSpectralEvalFiniteSample_surjective_autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_radical
    (hSeedSurj :
      ∀ T : Finset ℂ,
        Function.Surjective (seedSpectralEvalFiniteSample T))
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) :=
  autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Positive-cone/GNS density at the quotient-level zero-tail functional. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) :=
  seedSpectralEvalFiniteSample_surjective_autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_radical
    hZeroTailClosureOwnerRunge
    (fun T => seedSpectralEvalFiniteSample_surjective_ownerPaleyWiener T)
    S P f₀

/-- Positive/autocorrelation cone density in the zero-tail ordered-heart quotient fiber. -/
theorem autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        ((completedBoundaryOrderedHeartZeroTailRealAbs S) ''
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀) :=
  Eq.subst
    (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
    (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_eq_image
      S P f₀)
    (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
      hZeroTailClosureOwnerRunge
      S P f₀)

/-- Positive-cone/GNS density recognition in the completed ordered-heart radical quotient. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_recognizes_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀) :=
  Eq.subst
    (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
    (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
      S P f₀).symm
    (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
      hZeroTailClosureOwnerRunge
      S P f₀)

/-- Positive/autocorrelation cone density in the completed ordered-heart radical quotient. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  Eq.subst
    (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
    (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
      S P f₀)
    (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_recognizes_zeroTail_mem_closure_radical
      hZeroTailClosureOwnerRunge
      S P f₀)

/-- Compatibility name for the positive/autocorrelation cone density theorem in the
completed ordered-heart radical quotient. -/
theorem autocorrelationConeSpectralFiber_zeroTailFunctional_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Autocorrelation cone Runge closure/radical condition for a fixed finite spectral fiber. -/
theorem autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationConeSpectralFiber_zeroTailFunctional_mem_closure_radical
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Compatibility name for the autocorrelation-cone Runge closure/radical condition. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
  autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Runge closure/radical condition gives arbitrarily small zero-tail values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
    S P f₀
    (hZeroTailClosureOwnerRunge S P f₀)

/-- Autocorrelation closure/density gives radical tail control inside a fixed finite fiber. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
    S P f₀
    (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀)

/-- Autocorrelation closure/density gives radical tail control in a realized finite fiber. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_fiberRealization_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ f₁ : ZetaAdmissibleFunction)
    (_hf₁ : f₁ ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Compatibility wrapper for the previous Paley-range-shaped Runge localization theorem. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_paleyRange_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (_hPaleyRange :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Runge density for the zero-tail absolute-value set in a finite autocorrelation fiber. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  fun ε hε =>
    match
        exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfFiber, hfTail⟩ =>
        ⟨autocorrelationZeroTailRealAbs S f,
          ⟨f, hfFiber, Eq.refl (autocorrelationZeroTailRealAbs S f)⟩,
          hfTail⟩

/-- Compatibility wrapper for the previous Paley-range-shaped Runge value-set theorem. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_paleyRange_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (_hPaleyRange :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Runge density for the zero-tail absolute-value set in a finite autocorrelation fiber. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
    hZeroTailClosureOwnerRunge
    S P f₀

/-- Runge localization inside the pointwise finite autocorrelation spectral-evaluation fiber. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  fun ε hε =>
    match
        exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨r, hrValues, hrSmall⟩ =>
        match
            (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
              S P f₀ r).mp hrValues with
        | ⟨f, hfFiber, hr⟩ =>
            ⟨f, hfFiber,
              Eq.subst
                (motive := fun x : ℝ => x < ε)
                hr
                hrSmall⟩

/-- Runge localization preserving pointwise finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  fun ε hε =>
    match
        exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfFiber, hfTail⟩ =>
        ⟨f,
          spectralEval_eq_on_finset_of_mem_autocorrelationSpectralEvalFiberOf
            P f₀ f hfFiber,
          hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  fun ε hε =>
    match
        exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfSample, hfTail⟩ =>
        ⟨f,
          autocorrelationSpectralFiniteSample_eq_of_spectralEval_eq_on_finset
            P f f₀ hfSample,
          hfTail⟩

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  fun ε hε =>
    match
        exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfSample, hfTail⟩ =>
        ⟨f,
          mem_autocorrelationSampleFiberOf_of_spectralFiniteSample_eq
            P f₀ f hfSample,
          hfTail⟩

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
  fun ε hε =>
    match
        exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfFiber, hfTail⟩ =>
        ⟨f, hfFiber,
          zeroTailRealAbs_lt_of_autocorrelationZeroTailRealAbs_lt
            S f ε hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
  fun ε hε =>
    match
        exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfFiber, hfTail⟩ =>
        ⟨f, hfFiber, hfTail⟩

omit hZeroTailClosureOwnerRunge

/-- The canonical unit autocorrelation sample vector on a finite spectral sample set. -/
def autocorrelationSpectralFiniteUnitTarget
    (P : Finset ℂ) : SpectralSampleVector P :=
  fun z : P => (fun value : ℂ => 1) z

/-- Membership in the unit autocorrelation sample fiber is exactly unit finite-sample
realization. -/
theorem mem_autocorrelationSampleFiber_unit_iff
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P :=
  Iff.intro
    (fun h => h)
    (fun h => h)

/-- The finite autocorrelation interpolation theorem realizes the unit sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_unitTarget
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P :=
  match exists_autocorrelation_spectralEval_one_on_finset P with
  | ⟨f, hf⟩ =>
      ⟨f, funext (fun z => hf (z : ℂ) z.property)⟩

/-- The unit finite autocorrelation spectral-sample fiber is nonempty. -/
theorem exists_mem_autocorrelationSampleFiber_unit
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) :=
  exists_autocorrelation_spectralFiniteSample_eq_unitTarget P

include hZeroTailClosureOwnerRunge

/-- Runge localization with the canonical unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteUnitTarget P ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
  match exists_mem_autocorrelationSampleFiber_unit P with
  | ⟨f₀, hf₀⟩ =>
      fun ε hε =>
        match
            exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
              hZeroTailClosureOwnerRunge
              S P f₀ ε hε with
        | ⟨f, hfSample, hfTail⟩ =>
            ⟨f, hfSample.trans hf₀, hfTail⟩

/-- Pointwise form of Runge localization with unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralEval_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z = 1) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
  fun ε hε =>
    match
        exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P ε hε with
    | ⟨f, hfSample, hfTail⟩ =>
        ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

/-- Autocorrelation spectral localization with zero-tail control. -/
theorem exists_autocorrelation_spectralEval_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε :=
  fun ε hε =>
    match
        exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
          hZeroTailClosureOwnerRunge
          S P f₀ ε hε with
    | ⟨f, hfSample, hfTail⟩ =>
        ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

/-- Construct a finite base window disjoint from the dagger-closed set. -/
theorem exists_autocorrelationSpectralEvalFiberSeparatedBaseWindow
    (P : Finset ℂ) :
    ∃ T₀ : Finset ℂ,
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P :=
  ⟨∅, fun ρ hρ => absurd hρ (Finset.mem_empty_iff_false ρ)⟩

/-- Completed zero counting satisfies polynomial growth via Jensen's formula. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_le_polynomial
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ C : ℝ, ∃ d : ℕ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d :=
  exists_completedZeroMultiplicityCounting_height_bound
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary

/-- Envelope constants exist using the completed-zero shell summability theorem. -/
theorem exists_autocorrelationSpectralEvalFiberSeparatedEnvelope
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 ≤ A ∧
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} ↦
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) :=
  match
      completedZeroMultiplicityCountingInCenteredHeightBall_le_polynomial
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary with
  | ⟨C, d, hC_pos, hcount⟩ =>
      let h_shell_decay :
          Summable (fun m : ℕ => completedZeroCenteredHeightShellDecayMass 0 3 m) :=
        summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
          C 0 3 hC_pos hcount
      ⟨1, 3, one_nonneg,
        summable_completedZero_centeredHeight_negativePower_of_shellMass
          0 3 h_shell_decay⟩

/-- Zero-side contributions are bounded by the envelope under separation. -/
theorem autocorrelationSpectralEvalFiber_separated_zeroSideContribution_bounded
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (S P : Finset ℂ) (f₀ : ZetaAdmissibleFunction)
    (T₀ : Finset ℂ)
    (hSeparated : ∀ ρ : ℂ,
      ZetaCompletedZero ρ → ρ ∉ S →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hT₀_disjoint : ∀ ρ ∈ T₀,
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∃ A : ℝ, ∃ k : ℕ,
      0 ≤ A ∧
      Summable (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} ↦
        A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) ∧
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          (∀ ρ : ℂ, ρ ∈ T₀ →
            zetaSpectralEval (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)
              (zetaCenteredZero ρ) = 0) →
            ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ ∧ ρ ∉ S ∧ ρ ∉ T₀},
              ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
  let h_envelope :=
    exists_zetaZeroMultiplicityTransformEnvelope_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  match h_envelope (convolutionAutocorrelation f₀) with
  | ⟨A, k, hA_pos, hEnv_summable, h_bound_universal⟩ =>
      ⟨A, k, le_of_lt hA_pos, hEnv_summable,
        fun f hf_fiber hf_annihilate ρ =>
          let h_norm :=
            norm_zetaZeroSideContribution_le_majorant
              (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩
          let h_majorant_eq :
              zetaZeroSideContributionMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ =
                zetaZeroMultiplicityTransformMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ :=
            zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant
              (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩
          let h_bound_f := h_bound_universal (convolutionAutocorrelation f)
          let h_centered_norm_eq_raw_norm :
              ‖zetaCenteredZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ =
                ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ :=
            congrArg norm
              (zetaCenteredZeroSideContribution_positiveModulation_eq_raw (ρ : ℂ) f)
          let h_raw_norm_le_majorant :
              ‖zetaZeroSideContribution (ρ : ℂ)
                  (convolutionAutocorrelation f)‖ ≤
                zetaZeroSideContributionMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ :=
            h_norm
          let h_majorant_le_transform_majorant :
              zetaZeroSideContributionMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ ≤
                zetaZeroMultiplicityTransformMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ :=
            le_of_eq h_majorant_eq
          let h_transform_majorant_le_envelope :
              zetaZeroMultiplicityTransformMajorant
                  (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ ≤
                A * zetaCompletedZeroCenteredHeight
                  (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^
                    (-(k + 3 : ℤ)) :=
            h_bound_f ⟨ρ.val, ρ.property.1⟩
          le_trans
            (le_of_eq h_centered_norm_eq_raw_norm)
            (le_trans
              h_raw_norm_le_majorant
              (le_trans
                h_majorant_le_transform_majorant
                h_transform_majorant_le_envelope))⟩

/-- Assemble the separated common-polynomial-envelope base theorem. -/
theorem autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase :=
  fun S P f₀ hSeparated =>
    match exists_autocorrelationSpectralEvalFiberSeparatedBaseWindow P with
    | ⟨T₀, hT₀_disjoint⟩ =>
        match
            autocorrelationSpectralEvalFiber_separated_zeroSideContribution_bounded
              hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
              S P f₀ T₀ hSeparated hT₀_disjoint with
        | ⟨A, k, hA_nonneg, hEnv_summable, hBound⟩ =>
            let hforced :
                ∀ f : ZetaAdmissibleFunction,
                  f ∈ AutocorrelationSpectralEvalFiberOfShifted
                    (translatedSpectralSampleFinset P (1 / 2 : ℝ))
                    (1 / 2 : ℝ) f₀ →
                    ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
                      zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
                        zetaCenteredZeroSideContribution ρ
                          (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 :=
              fun f hf ρ hρZero hρS hρDagger =>
                False.elim (hSeparated ρ hρZero hρS hρDagger)
            ⟨T₀, A, k,
              ⟨hT₀_disjoint, hA_nonneg, hEnv_summable, hforced, hBound⟩⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.ForcedDaggerTailParts.Reconstruction

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Completed zeros outside the excluded zero set are separated from the dagger-closed
finite spectral constraints.

This is the exact exclusion needed by the polynomial-envelope tail selector: forced
vanishing controls actual zero-side contributions at dagger-constrained zeros, but it
does not remove their positive envelope mass from a purely summable envelope tail. -/
theorem autocorrelationSpectralEvalFiber_completedZero_daggerExclusion_ownerGap
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
          zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P := by
  exact hdaggerExcluded

/-- Owner theorem: noncircular zero-tail closure density for autocorrelation spectral
fibers.

The proof surface is purely topological once the owner Runge/tomography theorem supplies
arbitrarily small attained zero-tail values in the fixed finite autocorrelation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerGap
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
      (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
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

/-- Nonlinear finite autocorrelation-cone density in the zero-tail quotient.

This is the actual Runge/GNS input for the positive cone.  The linear finite
sample surjectivity theorem supplies seed interpolation data, but the passage
to autocorrelation probes and then to the completed ordered-heart quotient is
nonlinear and is owned here rather than hidden in a downstream wrapper. -/
theorem autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) := by
  have hConcreteClosure :
      (0 : ℝ) ∈
        closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :=
    hZeroTailClosureOwnerRunge
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀
  have hConcrete_eq_quotient :
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ =
        autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀ :=
    Eq.trans
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq
        S P f₀).symm
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀)
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      hConcrete_eq_quotient
      hConcreteClosure

/-- Positive-cone/GNS density at the quotient-level zero-tail functional.

This is the nonlinear transport from finite seed spectral interpolation to the
positive/autocorrelation cone density statement in the completed zero-tail ordered-heart
quotient.

This is the nonlinear positive-cone transport primitive: it is a theorem about the
autocorrelation cone image in the fixed finite spectral fiber, not about the raw linear
Laplace-evaluation map.  The linear surjectivity argument is retained in the signature
for compatibility with older callers, while the proof delegates to the nonlinear owner
Runge theorem above. -/
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
          S P f₀) := by
  exact
    autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Positive-cone/GNS density at the quotient-level zero-tail functional.

This is the quotient-level finite spectral-fiber cone-density statement obtained by
transporting the finite seed spectral interpolation package through the nonlinear
autocorrelation/positive-cone map. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues
          S P f₀) := by
  exact
    seedSpectralEvalFiniteSample_surjective_autocorrelationConeSpectralFiber_positiveConeDensity_quotientZeroTail_mem_closure_radical
      hZeroTailClosureOwnerRunge
      (fun T => seedSpectralEvalFiniteSample_surjective_ownerPaleyWiener T)
      S P f₀

/-- Positive/autocorrelation cone density in the zero-tail ordered-heart quotient fiber.

Applying the quotient zero-tail functional to the positive/autocorrelation cone image of
the fixed finite spectral fiber has `0` in its closure. This is only the image-presentation
transport of the quotient-level nonlinear positive-cone density theorem. -/
theorem autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        ((completedBoundaryOrderedHeartZeroTailRealAbs S) ''
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀) := by
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      (autocorrelationConeSpectralFiberOrderedHeartQuotientZeroTailRealAbsValues_eq_image
        S P f₀)
      (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
        hZeroTailClosureOwnerRunge
        S P f₀)

/-- Positive-cone/GNS density recognition in the completed ordered-heart radical quotient.

This is the finite spectral-fiber cone-density input: the autocorrelation/positive cone
inside the fixed finite spectral presentation fiber has enough completed ordered-heart
representatives to put the zero-tail functional in the closure radical.  This statement is
intentionally nonlinear; it is not deduced from the raw affine kernel theorem for
`zetaSpectralEvalPresentationMap`. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_recognizes_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈
      closure
        (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues S P f₀) := by
  exact
    Eq.subst
      (motive := fun V : Set ℝ => (0 : ℝ) ∈ closure V)
      (autocorrelationConeSpectralFiberOrderedHeartZeroTailRealAbsValues_eq_quotient
        S P f₀).symm
      (autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_quotientZeroTail_mem_closure_radical
        hZeroTailClosureOwnerRunge
        S P f₀)

/-- Positive/autocorrelation cone density in the completed ordered-heart radical quotient.

This is the positive/autocorrelation-cone density input in quotient language: the
zero-tail functional belongs to the closure radical relative to the fixed finite spectral
presentation constraints. This is not a consequence of the raw affine kernel theorem. -/
theorem autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
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
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralFiber_completedOrderedHeart_positiveConeDensity_zeroTail_mem_closure_radical
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Autocorrelation cone Runge closure/radical condition for a fixed finite spectral
presentation fiber.

This is the closure-of-values form of the positive/autocorrelation-cone radical theorem. -/
theorem autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralFiber_zeroTailFunctional_mem_closure_radical
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Compatibility name for the autocorrelation-cone Runge closure/radical condition. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    autocorrelationConeSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Runge closure/radical condition gives arbitrarily small values of the zero-tail value
set of a fixed finite autocorrelation spectral-evaluation presentation fiber. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
      S P f₀
      (hZeroTailClosureOwnerRunge S P f₀)

/-- Autocorrelation closure/density gives radical tail control inside a fixed finite
spectral-evaluation presentation fiber.

The closure step keeps the finite autocorrelation spectral fiber fixed while shrinking
the named real zero-tail functional. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
      S P f₀
      (autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_ownerRunge
        hZeroTailClosureOwnerRunge
        S P f₀)

/-- Autocorrelation closure/density gives radical tail control inside an already realized
finite spectral-evaluation presentation fiber.

This wrapper records the realized-fiber form while the analytic Runge root is the fixed
fiber density theorem above. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_fiberRealization_autocorrelationClosure_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ f₁ : ZetaAdmissibleFunction)
    (_hf₁ : f₁ ∈ AutocorrelationSpectralEvalFiberOf P f₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Compatibility wrapper for the previous Paley-range-shaped Runge localization theorem.

The actual closure/density input is the fixed-fiber theorem above; the Paley range
argument is retained only for downstream statement shape. -/
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
          autocorrelationZeroTailRealAbs S f < ε := by
  exact
    exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Runge density/localization for the named zero-tail absolute-value set attained inside
the pointwise finite autocorrelation spectral-evaluation presentation fiber, obtained from
the fixed-fiber autocorrelation closure/density theorem. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_of_autocorrelationClosureDensity_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨autocorrelationZeroTailRealAbs S f,
    ⟨f, hfFiber, rfl⟩,
    hfTail⟩

/-- Compatibility wrapper for the previous Paley-range-shaped Runge value-set theorem.

The actual closure/density input is the fixed-fiber theorem above; the Paley range
argument is retained only for downstream statement shape. -/
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
          r < ε := by
  exact
    exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Runge density/localization for the named zero-tail absolute-value set attained inside
the pointwise finite autocorrelation spectral-evaluation fiber. -/
theorem exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε := by
  exact
    exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_of_autocorrelationClosureDensity_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀

/-- Runge localization inside the pointwise finite autocorrelation spectral-evaluation
fiber of a source, stated against the named real zero-tail functional. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelationSpectralEvalFiberZeroTailRealAbsValue_lt_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨r, hrValues, hrSmall⟩
  rcases
    (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
      S P f₀ r).mp hrValues with
    ⟨f, hfFiber, hr⟩
  exact ⟨f, hfFiber,
    Eq.subst
      (motive := fun x : ℝ => x < ε)
      hr
      hrSmall⟩

/-- Runge localization preserving pointwise finite autocorrelation spectral samples,
stated against the named real zero-tail functional. -/
theorem exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z =
            zetaSpectralEval (convolutionAutocorrelation f₀) z) ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f,
    spectralEval_eq_on_finset_of_mem_autocorrelationSpectralEvalFiberOf
      P f₀ f hfFiber,
    hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector,
stated against the named real zero-tail functional. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralEval_eq_zeroTailRealAbs_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f,
    autocorrelationSpectralFiniteSample_eq_of_spectralEval_eq_on_finset
      P f f₀ hfSample,
    hfTail⟩

/-- Runge localization inside the finite autocorrelation spectral-sample fiber of a source,
stated against the named real zero-tail functional.

This is the true analytic Runge root in this lane: it does not prescribe an arbitrary
autocorrelation target vector. It stays inside the already-realized finite sample fiber of
`f₀` while shrinking the complementary zero-tail functional. -/
theorem exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSampleFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_eq_zeroTailRealAbs_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f,
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
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTailRealAbs_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber,
    zeroTailRealAbs_lt_of_autocorrelationZeroTailRealAbs_lt
      S f ε hfTail⟩

/-- Runge localization preserving the finite autocorrelation spectral-sample vector of a
given source. -/
theorem exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        autocorrelationSpectralFiniteSample P f =
            autocorrelationSpectralFiniteSample P f₀ ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfFiber, hfTail⟩
  exact ⟨f, hfFiber, hfTail⟩

omit hZeroTailClosureOwnerRunge

/-- The canonical unit autocorrelation sample vector on a finite spectral sample set. -/
def autocorrelationSpectralFiniteUnitTarget
    (P : Finset ℂ) : SpectralSampleVector P :=
  fun _z : P => 1

/-- Membership in the unit autocorrelation sample fiber is exactly unit finite-sample
realization. -/
theorem mem_autocorrelationSampleFiber_unit_iff
    (P : Finset ℂ) (f : ZetaAdmissibleFunction) :
    f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) ↔
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  exact Iff.rfl

/-- The existing finite autocorrelation interpolation theorem realizes the unit finite
sample vector. -/
theorem exists_autocorrelation_spectralFiniteSample_eq_unitTarget
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      autocorrelationSpectralFiniteSample P f =
        autocorrelationSpectralFiniteUnitTarget P := by
  rcases exists_autocorrelation_spectralEval_one_on_finset P with
    ⟨f, hf⟩
  exact ⟨f, by
    funext z
    exact hf (z : ℂ) z.property⟩

/-- The unit finite autocorrelation spectral-sample fiber is nonempty. -/
theorem exists_mem_autocorrelationSampleFiber_unit
    (P : Finset ℂ) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSampleFiber P (autocorrelationSpectralFiniteUnitTarget P) := by
  exact exists_autocorrelation_spectralFiniteSample_eq_unitTarget P

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
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  rcases exists_mem_autocorrelationSampleFiber_unit P with
    ⟨f₀, hf₀⟩
  intro ε hε
  rcases exists_mem_autocorrelationSampleFiberOf_zeroTail_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, hfSample.trans hf₀, hfTail⟩

/-- Pointwise form of Runge localization with unit finite autocorrelation spectral samples. -/
theorem exists_autocorrelation_spectralEval_unit_zeroTail_small_ownerRunge
    (S : Finset ℂ)
    (P : Finset ℂ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        (∀ z : ℂ, z ∈ P →
          zetaSpectralEval (convolutionAutocorrelation f) z = 1) ∧
          |Complex.re
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_unit_zeroTail_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

/-- Autocorrelation spectral localization with zero-tail control.

This is the analytic Runge/Paley-Wiener localization input: while preserving a
finite set of completed autocorrelation spectral samples, one can drive the real
part of the complementary completed zero-tail functional below any positive
tolerance. -/
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
            (zetaZeroTail S (convolutionAutocorrelation f))| < ε := by
  intro ε hε
  rcases exists_autocorrelation_spectralFiniteSample_preserved_zeroTail_small_ownerRunge
      hZeroTailClosureOwnerRunge
      S P f₀ ε hε with
    ⟨f, hfSample, hfTail⟩
  exact ⟨f, fun z hz => congrFun hfSample ⟨z, hz⟩, hfTail⟩

/-! # Separated common-polynomial-envelope base theorem

This section proves the core Runge theorem: for any finite spectral constraint set P
and any separation hypothesis, there exist a finite base window T₀, envelope constant A ≥ 0,
and decay rate k such that completed autocorrelation spectral fibers with T₀-annihilated
zero-side contributions satisfy polynomial height-decay bounds.

The proof is split into:
1. T₀ selection: construct a finite window disjoint from dagger-closed spectral constraints
2. Envelope existence: show appropriate A, k exist using existing summability theory
3. Core bound: bind zero-side contributions using Paley-Wiener + analytical estimates
4. Assembly: package into the separated base theorem
-/

/-- Step 1: Construct finite base window T₀ disjoint from dagger-closed set.

For any finite spectral sample P, we can always choose some finite set T₀ of completed
zeros whose centered coordinates are outside daggerClosedSpectralSampleFinset P.

Construction: Since daggerClosedSpectralSampleFinset P is finite and the inverse image
under zetaCenteredZero is finite, we select T₀ as any finite subset of completed zeros
not in this finite inverse image. The simplest choice is the empty set, but any finite
disjoint set works.
-/
theorem exists_autocorrelationSpectralEvalFiberSeparatedBaseWindow
    (P : Finset ℂ) :
    ∃ T₀ : Finset ℂ,
      ∀ ρ : ℂ, ρ ∈ T₀ →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P := by
  -- Simplest construction: empty set is always disjoint
  use ∅
  intro ρ hρ
  exact absurd hρ (Finset.mem_empty_iff_false ρ)

/-- Completed zero counting satisfies polynomial growth (via Jensen's formula).

The number of completed zeros with centered height ≤ T grows at most polynomially.
This is proven via Jensen's formula relating zero count to the finite order of the
completed Riemann zeta function, which depends on boundary conditions of the analytic
continuation.

The theorem exists_completedZeroMultiplicityCounting_height_bound in
ZetaCompletedZeroJensen/HeightBall/Owner.lean (line 284) provides this with
the necessary analytical inputs.
-/
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

/-- Step 2: Envelope constants exist using existing summability theory.

For any k ≥ 0 and A > 0, the envelope A * height(ρ)^(-(k+3)) over all completed zeros
is summable. This follows from existing summability theorems via height-decay shell
decomposition.

We use A = 1 and k = 3, so the envelope is height(ρ)^(-6).

The summability depends on the polynomial bound from Jensen's formula, which requires
the analytical boundary conditions from the completed zeta function's properties.
-/
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
          A * zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  -- Get polynomial bound from Jensen's formula via boundary conditions
  obtain ⟨C, d, hC_pos, hcount⟩ := completedZeroMultiplicityCountingInCenteredHeightBall_le_polynomial
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
  -- Use shell decay mass summability theorem with the polynomial bound
  have h_shell_decay : Summable (fun m : ℕ => completedZeroCenteredHeightShellDecayMass 0 3 m) :=
    summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound C 0 3 hC_pos hcount
  -- Apply the existing summability theorem
  use 1, 3
  exact ⟨one_nonneg, summable_completedZero_centeredHeight_negativePower_of_shellMass 0 3 h_shell_decay⟩

/-- Step 3: Zero-side contributions are bounded by the envelope under separation.

This is the core analytical theorem. It derives from the envelope machinery:
- Envelope existence theorem produces A and k
- For any f in the spectral fiber, the bound follows from majorant decomposition

This theorem directly invokes exists_zetaZeroMultiplicityTransformEnvelope_bound,
which takes the boundary conditions and produces both existence and bound guarantee.
-/
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
                  (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) := by
  -- Invoke envelope existence theorem with boundary conditions
  -- This produces A, k such that ∀ φ, majorant(φ,ρ) ≤ A·height(ρ)^(-(k+3))
  have h_envelope := exists_zetaZeroMultiplicityTransformEnvelope_bound
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary

  -- Extract A, k and their properties from the first use (on an arbitrary function)
  -- We use them universally since they work for ANY admissible function
  obtain ⟨A, k, hA_pos, hEnv_summable, h_bound_universal⟩ :=
    h_envelope (convolutionAutocorrelation f₀)

  -- Now produce these as witnesses
  use A, k

  -- Prove the three components: A ≥ 0, summable, and the universal bound
  constructor
  · exact le_of_lt hA_pos
  constructor
  · exact hEnv_summable
  · -- The majorant is uniform, so it applies before and after modulation.
    intro f _hf_fiber _hf_annihilate ρ

    -- Step 1: Apply majorant decomposition
    have h_norm := norm_zetaZeroSideContribution_le_majorant
      (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩

    -- Step 2: Connect to transform majorant via equality theorem
    have h_majorant_eq : zetaZeroSideContributionMajorant (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ =
      zetaZeroMultiplicityTransformMajorant (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ :=
      zetaZeroSideContributionMajorant_eq_multiplicityTransformMajorant
        (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩

    -- Step 3: Apply the universal envelope bound
    -- The bound h_bound_universal says ∀ φ ∀ ρ, majorant(φ,ρ) ≤ A·height(ρ)^(-(k+3))
    have h_bound_f := h_bound_universal (convolutionAutocorrelation f)

    -- Step 4: Conclude
    calc ‖zetaCenteredZeroSideContribution (ρ : ℂ)
          (convolutionAutocorrelationShifted (1 / 2 : ℝ) f)‖ =
          ‖zetaZeroSideContribution (ρ : ℂ) (convolutionAutocorrelation f)‖ := by
          exact congrArg norm
            (zetaCenteredZeroSideContribution_positiveModulation_eq_raw (ρ : ℂ) f)
      _ ≤ zetaZeroSideContributionMajorant (convolutionAutocorrelation f)
          ⟨ρ.val, ρ.property.1⟩ := h_norm
      _ = zetaZeroMultiplicityTransformMajorant (convolutionAutocorrelation f) ⟨ρ.val, ρ.property.1⟩ := h_majorant_eq
      _ ≤ A * zetaCompletedZeroCenteredHeight (⟨(ρ : ℂ), ρ.2.1⟩ : {ρ : ℂ // ZetaCompletedZero ρ}) ^ (-(k + 3 : ℤ)) :=
          h_bound_f ⟨ρ.val, ρ.property.1⟩

/-- Step 4: Assemble into separated base theorem.

This theorem proves the main Runge theorem by wiring together:
- T₀ selection (step 1)
- Envelope existence (step 2)
- Zero-side bounds (step 3)

The envelope existence requires analytical boundary conditions from the completed
zeta function's properties (via Jensen's formula).
-/
theorem autocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    AutocorrelationSpectralEvalFiberSeparatedCommonPolynomialEnvelopeBase := by
  intro S P f₀ hSeparated

  -- Get T₀ disjoint from dagger-closed set
  obtain ⟨T₀, hT₀_disjoint⟩ :=
    exists_autocorrelationSpectralEvalFiberSeparatedBaseWindow P

  -- Get A, k such that envelope is summable (using analytical boundary conditions)
  obtain ⟨A, k, hA_nonneg, hEnv_summable⟩ :=
    exists_autocorrelationSpectralEvalFiberSeparatedEnvelope
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary

  -- Get the zero-side bound using the envelope theorems
  -- This theorem now produces A, k itself via the envelope machinery
  obtain ⟨A, k, hA_nonneg, hEnv_summable, hBound⟩ :=
    autocorrelationSpectralEvalFiber_separated_zeroSideContribution_bounded
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary
      S P f₀ T₀ hSeparated hT₀_disjoint

  -- Package into data structure
  have hforced :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOfShifted
          (translatedSpectralSampleFinset P (1 / 2 : ℝ))
          (1 / 2 : ℝ) f₀ →
          ∀ ρ : ℂ, ZetaCompletedZero ρ → ρ ∉ S →
            zetaCenteredZero ρ ∈ daggerClosedSpectralSampleFinset P →
              zetaCenteredZeroSideContribution ρ
                (convolutionAutocorrelationShifted (1 / 2 : ℝ) f) = 0 := by
    intro f hf ρ hρZero hρS hρDagger
    exact False.elim (hSeparated ρ hρZero hρS hρDagger)
  exact ⟨T₀, A, k,
    ⟨hT₀_disjoint, hA_nonneg, hEnv_summable, hforced, hBound⟩⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

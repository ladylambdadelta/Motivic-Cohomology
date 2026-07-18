
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.OwnerParts.PresentationParts.Part01_ValueDefinitions

/-!
# Spectral presentation fiber density

Boring owner lemmas for fiber value sets, closure, and finite-window descent.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction) (r : ℝ) :
    r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ↔
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          r = autocorrelationZeroTailRealAbs S f := by
  exact Iff.intro (fun equality => equality) (fun equality => equality)

/-- Values of the fixed-fiber zero-tail absolute-value set are nonnegative. -/
theorem autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
    (S : Finset ℂ) (P : Finset ℂ) (f₀ : ZetaAdmissibleFunction)
    {r : ℝ}
    (hr : r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) :
    0 ≤ r := by
  exact match
      (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
        S P f₀ r).mp hr with
  | ⟨f, hfFiberEvidence, hrf⟩ =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hrf.symm
        (abs_nonneg (Complex.re (zetaZeroTail S (convolutionAutocorrelation f))))

/-- The finite autocorrelation spectral-evaluation presentation fiber of a source probe is
inhabited.

This keeps finite fiber realization separate from the zero-tail minimization step. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_of_paleyRange_ownerRunge
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hPaleyRangeEvidence :
      ∀ T : Finset ℂ, ∀ aT : T → ℂ,
        aT ∈ Set.range (zetaLaplaceTransformFiniteSample T)) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
  exact
    ⟨f₀,
      fun z hzEvidence =>
        Eq.refl (zetaSpectralEval (convolutionAutocorrelation f₀) z)⟩

/-- A fixed finite autocorrelation spectral-evaluation presentation fiber has
representatives with arbitrarily small zero-tail absolute value exactly when its named
zero-tail value set has arbitrarily small values.

This is the corrected radical-control form: the analytic Runge/closure input is the
small-value condition on the fixed presentation fiber's zero-tail value set. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hRadical :
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε :=
  fun ε hε =>
    match hRadical ε hε with
    | ⟨r, hrValues, hrSmall⟩ =>
        match
          (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
            S P f₀ r).mp hrValues with
        | ⟨f, hfFiber, hr⟩ =>
            ⟨f, hfFiber,
              Eq.subst
                (motive := fun value : ℝ => value < ε)
                hr
                hrSmall⟩

/-- If a fixed presentation fiber has representatives with arbitrarily small zero-tail
absolute value, then its named zero-tail value set has arbitrarily small values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_fiber
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hFiber :
      ∀ ε : ℝ, 0 < ε →
        ∃ f : ZetaAdmissibleFunction,
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
            autocorrelationZeroTailRealAbs S f < ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  fun ε hε =>
    match hFiber ε hε with
    | ⟨f, hfFiber, hfSmall⟩ =>
        ⟨autocorrelationZeroTailRealAbs S f,
          ⟨f, hfFiber, Eq.refl (autocorrelationZeroTailRealAbs S f)⟩,
          hfSmall⟩

/-- Distance from zero is the value itself for a nonnegative real. -/
theorem dist_zero_eq_self_of_nonnegative (r : ℝ) (hr : 0 ≤ r) :
    dist 0 r = r :=
  Eq.trans (dist_comm 0 r)
    (Eq.trans (Real.dist_eq r 0)
      (Eq.trans
        (congrArg (fun value : ℝ => |value|) (sub_zero r))
        (abs_of_nonneg hr)))

/-- A fixed finite autocorrelation spectral-evaluation presentation fiber has
representatives with arbitrarily small zero-tail absolute value iff its named zero-tail
value set has arbitrarily small values. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values_iff
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (∀ ε : ℝ, 0 < ε →
      ∃ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
          autocorrelationZeroTailRealAbs S f < ε) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε := by
  exact
    ⟨autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_fiber
        S P f₀,
      autocorrelationSpectralEvalFiber_zeroTailRealAbs_has_arbitrarily_small_values
        S P f₀⟩

/-- Closure of the fixed-fiber zero-tail value set at `0`, together with the
nonnegativity of those values, gives arbitrarily small positive upper bounds.

This is the topological bridge from the Runge/tomography closure theorem to the concrete
small-values statement consumed by downstream zero-tail localization. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hClosure :
      (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ,
        r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
          r < ε :=
  fun ε hε =>
  match (Metric.mem_closure_iff.mp hClosure) ε hε with
  | ⟨r, hrValues, hdist⟩ =>
    have hrNonnegative :
        0 ≤ r :=
      autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
        S P f₀ hrValues
    have hdist_zero_r_eq_r : dist 0 r = r :=
      dist_zero_eq_self_of_nonnegative r hrNonnegative
    ⟨r,
      hrValues,
      Eq.subst
        (motive := fun x : ℝ => x < ε)
        hdist_zero_r_eq_r
        hdist⟩

/-- Arbitrarily small values of the fixed-fiber zero-tail value set put `0` in the
closure of that value set.

This is the reverse topological bridge: the analytic Runge input may be supplied as
small attained values, while the closure formulation is the canonical cone-radical form. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (hSmall :
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) := by
  exact
    Metric.mem_closure_iff.mpr
      (fun ε hε =>
        match hSmall ε hε with
        | ⟨r, hrValues, hrSmall⟩ =>
            have hrNonnegative : 0 ≤ r :=
              autocorrelationSpectralEvalFiberZeroTailRealAbsValues_nonnegative
                S P f₀ hrValues
            have hdistZero : dist 0 r = r :=
              dist_zero_eq_self_of_nonnegative r hrNonnegative
            Exists.intro r
              (And.intro hrValues
                (Eq.subst
                  (motive := fun value : ℝ => value < ε)
                  hdistZero.symm
                  hrSmall)))

/-- For the nonnegative fixed-fiber zero-tail value set, closure at `0` is equivalent to
having values below every positive bound. -/
theorem autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_iff_has_arbitrarily_small_values
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    (0 : ℝ) ∈ closure (autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ r : ℝ,
          r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
            r < ε := by
  exact
    ⟨autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_has_arbitrarily_small_values_of_zero_mem_closure
        S P f₀,
      autocorrelationSpectralEvalFiber_zeroTailRealAbsValues_zero_mem_closure_of_has_arbitrarily_small_values
        S P f₀⟩

/-- The quotient zero-tail values of the positive/autocorrelation cone image are
nonnegative.

This isolates the ordered-heart positivity part of the cone-density argument from the
remaining closure/density theorem. -/
theorem autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage_zeroTail_values_nonnegative
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {r : ℝ}
    (hr :
      r ∈
        (completedBoundaryOrderedHeartZeroTailRealAbs S) ''
          autocorrelationConeSpectralEvalFiberZeroTailOrderedHeartImage P f₀) :
    0 ≤ r := by
  exact match hr with
  | ⟨C, hClassEvidence, hCr⟩ =>
      Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        hCr
        (completedBoundaryOrderedHeartZeroTailRealAbs_nonnegative S C)

/-- Seed interpolation target used to preserve a finite autocorrelation fiber while
annihilating a finite batch of centered zero samples outside the dagger-closed fiber
constraints. -/
def finiteAutocorrelationFiberZeroAnnihilationSeedTarget
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction) :
    ℂ → ℂ :=
  fun z : ℂ =>
    if hzEvidence : z ∈ daggerClosedSpectralSampleFinset P then
      zetaSpectralEval f₀ z
    else
      0

/-- On the dagger-closed fiber constraints, the finite annihilation target agrees with the
source seed spectral evaluation. -/
theorem finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_of_mem_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {z : ℂ}
    (hz : z ∈ daggerClosedSpectralSampleFinset P) :
    finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z =
      zetaSpectralEval f₀ z := by
  exact dif_pos hz

/-- Away from the dagger-closed fiber constraints, the finite annihilation target is zero. -/
theorem finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    {z : ℂ}
    (hz : z ∉ daggerClosedSpectralSampleFinset P) :
    finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z = 0 := by
  exact dif_neg hz

/-- Realizing the seed target on a dagger-closed point preserves the source evaluation. -/
theorem zetaSpectralEval_eq_source_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) (z : ℂ)
    (hz : z ∈ daggerClosedSpectralSampleFinset P)
    (hf : zetaSpectralEval f z =
      finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    zetaSpectralEval f z = zetaSpectralEval f₀ z :=
  Eq.trans hf
    (finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_of_mem_daggerClosed
      P f₀ hz)

/-- Equal seed evaluations at a point and its dagger preserve the autocorrelation value. -/
theorem autocorrelationSpectralEval_eq_of_seed_pair_eq
    (f g : ZetaAdmissibleFunction) (z : ℂ)
    (hz : zetaSpectralEval f z = zetaSpectralEval g z)
    (hreflection : zetaSpectralEval f (-star z) = zetaSpectralEval g (-star z)) :
    zetaSpectralEval (convolutionAutocorrelation f) z =
      zetaSpectralEval (convolutionAutocorrelation g) z := by
  have hleft :
      zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) :=
    zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct f z
  have hright :
      zetaSpectralEval (convolutionAutocorrelation g) z =
        zetaSpectralEval g z * star (zetaSpectralEval g (-star z)) :=
    zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct g z
  have hfirst :
      zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) =
        zetaSpectralEval g z * star (zetaSpectralEval f (-star z)) :=
    congrArg (fun value : ℂ => value * star (zetaSpectralEval f (-star z))) hz
  have hsecond :
      zetaSpectralEval g z * star (zetaSpectralEval f (-star z)) =
        zetaSpectralEval g z * star (zetaSpectralEval g (-star z)) :=
    congrArg (fun value : ℂ => zetaSpectralEval g z * star value) hreflection
  exact Eq.trans hleft (Eq.trans hfirst (Eq.trans hsecond hright.symm))

/-- A seed realizing the finite annihilation target preserves the autocorrelation spectral
fiber on `P`. -/
theorem mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ)
    (f₀ f : ZetaAdmissibleFunction)
    (hf :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    f ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
  fun z hz =>
    have hzDagger : z ∈ daggerClosedSpectralSampleFinset P :=
      mem_daggerClosedSpectralSampleFinset_self P z hz
    have hreflectionDagger : -star z ∈ daggerClosedSpectralSampleFinset P :=
      mem_daggerClosedSpectralSampleFinset_reflection P z hz
    have hzEquality : zetaSpectralEval f z = zetaSpectralEval f₀ z :=
      zetaSpectralEval_eq_source_of_seed_finiteAnnihilationTarget
      P f₀ f z hzDagger (hf z hzDagger)
    have hreflectionEquality :
        zetaSpectralEval f (-star z) = zetaSpectralEval f₀ (-star z) :=
      zetaSpectralEval_eq_source_of_seed_finiteAnnihilationTarget
      P f₀ f (-star z) hreflectionDagger (hf (-star z) hreflectionDagger)
    autocorrelationSpectralEval_eq_of_seed_pair_eq
      f f₀ z hzEquality hreflectionEquality

/-- A zero seed evaluation forces the autocorrelation evaluation to vanish. -/
theorem autocorrelationSpectralEval_eq_zero_of_seed_eval_eq_zero
    (f : ZetaAdmissibleFunction) (z : ℂ)
    (hz : zetaSpectralEval f z = 0) :
    zetaSpectralEval (convolutionAutocorrelation f) z = 0 := by
  have hproduct :
      zetaSpectralEval (convolutionAutocorrelation f) z =
        zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) :=
    zetaSpectralEval_convolutionAutocorrelation_eq_seed_daggerProduct f z
  have hzeroProduct :
      zetaSpectralEval f z * star (zetaSpectralEval f (-star z)) =
        0 * star (zetaSpectralEval f (-star z)) :=
    congrArg
      (fun value : ℂ => value * star (zetaSpectralEval f (-star z)))
      hz
  exact Eq.trans hproduct
    (Eq.trans hzeroProduct (zero_mul (star (zetaSpectralEval f (-star z)))))

/-- Outside the dagger-closed constraints, realizing the target makes the seed value zero. -/
theorem zetaSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ) (f₀ f : ZetaAdmissibleFunction) (ρ : ℂ)
    (hρ : zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hf : zetaSpectralEval f (zetaCenteredZero ρ) =
      finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ (zetaCenteredZero ρ)) :
    zetaSpectralEval f (zetaCenteredZero ρ) = 0 :=
  Eq.trans hf
    (finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
      P f₀ hρ)

/-- A seed realizing the finite annihilation target has zero autocorrelation spectral value
at any centered zero sample outside the dagger-closed fiber constraints. -/
theorem autocorrelationSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
    (P : Finset ℂ)
    (f₀ f : ZetaAdmissibleFunction)
    {ρ : ℂ}
    (hρ :
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hf :
      zetaSpectralEval f (zetaCenteredZero ρ) =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀
          (zetaCenteredZero ρ)) :
    zetaSpectralEval (convolutionAutocorrelation f) (zetaCenteredZero ρ) = 0 := by
  have hf_zero :
      zetaSpectralEval f (zetaCenteredZero ρ) = 0 :=
    zetaSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
      P f₀ f ρ hρ hf
  exact autocorrelationSpectralEval_eq_zero_of_seed_eval_eq_zero
    f (zetaCenteredZero ρ) hf_zero

/-- A sample realized on the union restricts to the dagger-closed constraints. -/
theorem seed_finiteAnnihilationTarget_restrict_daggerClosed
    (P T : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hfUnion :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P ∪ T.image zetaCenteredZero →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    ∀ z : ℂ, z ∈ daggerClosedSpectralSampleFinset P →
      zetaSpectralEval f z =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z :=
  fun z hz => hfUnion z (Finset.mem_union.mpr (Or.inl hz))

/-- A sample realized on the union annihilates every selected centered zero. -/
theorem seed_finiteAnnihilationTarget_zero_on_centeredBatch
    (P T : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hT : ∀ ρ : ℂ, ρ ∈ T →
      zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P)
    (hfUnion :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P ∪ T.image zetaCenteredZero →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    ∀ ρ : ℂ, ρ ∈ T →
      zetaSpectralEval (convolutionAutocorrelation f) (zetaCenteredZero ρ) = 0 :=
  fun ρ hρT =>
    have hcenterMem :
        zetaCenteredZero ρ ∈
          daggerClosedSpectralSampleFinset P ∪ T.image zetaCenteredZero :=
      Finset.mem_union.mpr
        (Or.inr
          (Finset.mem_image.mpr
            ⟨ρ, hρT, Eq.refl (zetaCenteredZero ρ)⟩))
    have hfCenter :
        zetaSpectralEval f (zetaCenteredZero ρ) =
          finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀
            (zetaCenteredZero ρ) :=
      hfUnion (zetaCenteredZero ρ) hcenterMem
    autocorrelationSpectralEval_centeredZero_eq_zero_of_seed_finiteAnnihilationTarget
      P f₀ f (hT ρ hρT) hfCenter

/-- Finite Paley-Wiener interpolation can preserve the fixed finite autocorrelation
spectral fiber while annihilating any finite batch of centered zero samples which lies
outside the dagger-closed fiber constraints. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_and_centeredZero_batch_zero_of_disjoint_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        zetaCenteredZero ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        ∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f)
            (zetaCenteredZero ρ) = 0 := by
  let U : Finset ℂ :=
    daggerClosedSpectralSampleFinset P ∪ T.image zetaCenteredZero
  exact match exists_seed_spectralEval_sample_on_finset
      U (finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀) with
  | ⟨f, hfU⟩ =>
      have hfDagger :
          ∀ z : ℂ,
            z ∈ daggerClosedSpectralSampleFinset P →
              zetaSpectralEval f z =
                finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z :=
        seed_finiteAnnihilationTarget_restrict_daggerClosed P T f₀ f hfU
      have hfFiber :
          f ∈ AutocorrelationSpectralEvalFiberOf P f₀ :=
        mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
          P f₀ f hfDagger
      have hzero :
          ∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              (zetaCenteredZero ρ) = 0 :=
        seed_finiteAnnihilationTarget_zero_on_centeredBatch
          P T f₀ f hT hfU
      ⟨f, hfFiber, hzero⟩

theorem seed_finiteAnnihilationTarget_zero_on_rawBatch
    (P T : Finset ℂ) (f₀ f : ZetaAdmissibleFunction)
    (hT : ∀ ρ : ℂ, ρ ∈ T →
      ρ ∉ daggerClosedSpectralSampleFinset P)
    (hfUnion :
      ∀ z : ℂ,
        z ∈ daggerClosedSpectralSampleFinset P ∪ T →
          zetaSpectralEval f z =
            finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z) :
    ∀ ρ : ℂ, ρ ∈ T →
      zetaSpectralEval (convolutionAutocorrelation f) ρ = 0 := by
  intro ρ hρT
  have hmem : ρ ∈ daggerClosedSpectralSampleFinset P ∪ T := by
    exact Finset.mem_union.mpr (Or.inr hρT)
  have hseed :
      zetaSpectralEval f ρ =
        finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ ρ := by
    exact hfUnion ρ hmem
  have hseedZero : zetaSpectralEval f ρ = 0 := by
    exact Eq.trans hseed
      (finiteAutocorrelationFiberZeroAnnihilationSeedTarget_eq_zero_of_not_mem_daggerClosed
        P f₀ (hT ρ hρT))
  exact autocorrelationSpectralEval_eq_zero_of_seed_eval_eq_zero f ρ hseedZero

theorem exists_mem_autocorrelationSpectralEvalFiberOf_and_raw_batch_zero_of_disjoint_daggerClosed
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        ∀ ρ : ℂ, ρ ∈ T →
          zetaSpectralEval (convolutionAutocorrelation f) ρ = 0 := by
  let U : Finset ℂ := daggerClosedSpectralSampleFinset P ∪ T
  match exists_seed_spectralEval_sample_on_finset
      U (finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀) with
  | ⟨f, hfU⟩ =>
      have hfDagger :
          ∀ z : ℂ,
            z ∈ daggerClosedSpectralSampleFinset P →
              zetaSpectralEval f z =
                finiteAutocorrelationFiberZeroAnnihilationSeedTarget P f₀ z := by
        intro z hz
        exact hfU z (Finset.mem_union.mpr (Or.inl hz))
      have hfFiber : f ∈ AutocorrelationSpectralEvalFiberOf P f₀ := by
        exact mem_autocorrelationSpectralEvalFiberOf_of_seed_finiteAnnihilationTarget
          P f₀ f hfDagger
      have hzero :
          ∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f) ρ = 0 := by
        exact seed_finiteAnnihilationTarget_zero_on_rawBatch
          P T f₀ f hT hfU
      exact ⟨f, hfFiber, hzero⟩

/-- A finite annihilation window plus a uniform tail-control estimate gives a probe with
small named zero-tail absolute value.

This is the finite-set/descent part of the Runge argument: the only analytic input is the
last hypothesis, which says that every interpolating probe annihilating the selected finite
completed-zero window has small complementary zero tail. -/
theorem exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_lt_of_finiteWindow_tailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    ∃ f : ZetaAdmissibleFunction,
      f ∈ AutocorrelationSpectralEvalFiberOf P f₀ ∧
        autocorrelationZeroTailRealAbs S f < ε := by
  exact match
      exists_mem_autocorrelationSpectralEvalFiberOf_and_raw_batch_zero_of_disjoint_daggerClosed
        P f₀ T hT with
  | ⟨f, hfFiber, hfzero⟩ =>
      ⟨f, hfFiber, htail f hfFiber hfzero⟩

/-- A finite annihilation window plus a uniform tail-control estimate gives a value in the
named zero-tail value set below the requested bound. -/
theorem autocorrelationSpectralEvalFiberZeroTailRealAbsValues_exists_lt_of_finiteWindow_tailControl
    (S : Finset ℂ)
    (P : Finset ℂ)
    (f₀ : ZetaAdmissibleFunction)
    (ε : ℝ)
    (T : Finset ℂ)
    (hT :
      ∀ ρ : ℂ, ρ ∈ T →
        ρ ∉ daggerClosedSpectralSampleFinset P)
    (htail :
      ∀ f : ZetaAdmissibleFunction,
        f ∈ AutocorrelationSpectralEvalFiberOf P f₀ →
          (∀ ρ : ℂ, ρ ∈ T →
            zetaSpectralEval (convolutionAutocorrelation f)
              ρ = 0) →
            autocorrelationZeroTailRealAbs S f < ε) :
    ∃ r : ℝ,
      r ∈ autocorrelationSpectralEvalFiberZeroTailRealAbsValues S P f₀ ∧
        r < ε := by
  exact match
      exists_mem_autocorrelationSpectralEvalFiberOf_zeroTailRealAbs_lt_of_finiteWindow_tailControl
        S P f₀ ε T hT htail with
  | ⟨f, hfFiber, hfTail⟩ =>
      ⟨autocorrelationZeroTailRealAbs S f,
        (mem_autocorrelationSpectralEvalFiberZeroTailRealAbsValues_iff
          S P f₀ (autocorrelationZeroTailRealAbs S f)).mpr
          ⟨f, hfFiber, Eq.refl (autocorrelationZeroTailRealAbs S f)⟩,
        hfTail⟩


end ZetaAdmissibleFunction
end
end LFunctions
end Boundary

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryLogAssembly.BoundaryCircleZeros

/-!
# Boundary-log regularity for Jensen formula

This file owns the finite logarithmic-singularity regularity chain for Jensen
boundary logarithmic integrands.  It sits between the boundary-circle zero
infrastructure and the boundary-log assembly owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The boundary sample `θ ↦ F((2R) · exp(iθ))` is analytic as a real-variable
function. This is the owner-level transport input for the Jensen local model. -/
theorem jensenBoundaryLogSample_analyticAt
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ) :
    AnalyticAt ℝ
      (fun θ : ℝ => F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀ := by
  have hθI : AnalyticAt ℝ (fun θ : ℝ => θ * Complex.I) θ₀ := by
    have hθC : AnalyticAt ℝ (fun θ : ℝ => (θ : ℂ)) θ₀ :=
      Complex.ofRealCLM.analyticAt θ₀
    have hI : AnalyticAt ℝ (fun _ : ℝ => Complex.I) θ₀ :=
      analyticAt_const
    exact hθC.mul hI
  have hexp : AnalyticAt ℝ (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) θ₀ := by
    have houter : AnalyticAt ℝ (fun z : ℂ => Complex.exp z) ((θ₀ : ℝ) * Complex.I) :=
      (analyticAt_cexp (z := (θ₀ : ℝ) * Complex.I)).restrictScalars
    exact
      AnalyticAt.comp
        (g := fun z : ℂ => Complex.exp z)
        (f := fun θ : ℝ => (θ : ℂ) * Complex.I)
        houter
        hθI
  have hsample : AnalyticAt ℝ (fun θ : ℝ => ((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) θ₀ := by
    have hscale : AnalyticAt ℝ (fun _ : ℝ => ((2 * R : ℝ) : ℂ)) θ₀ :=
      analyticAt_const
    exact hscale.mul hexp
  have hFreal : AnalyticAt ℝ F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) :=
    (hF _).restrictScalars
  exact
    AnalyticAt.comp
      (g := F)
      (f := fun θ : ℝ => ((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      hFreal
      hsample

/-- If the sampled boundary function is not locally zero at the parameter `θ₀`,
it admits the exact local Taylor factorization needed for the Jensen local model. -/
theorem jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ u : ℝ → ℂ,
      AnalyticAt ℝ u θ₀ ∧
      u θ₀ ≠ 0 ∧
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
          (θ - θ₀) ^ n • u θ := by
  have hsample :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  exact
    Exists.elim ((hsample.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnot)
      (fun n hn =>
        Exists.elim hn
          (fun u hu =>
            ⟨n, u, hu.1, hu.2.1, hu.2.2⟩))

/-- An analytic real-parameter unit has locally interval-integrable log norm.

This is the exact analytic-unit remainder input needed by the Jensen local
model.  Analyticity gives continuity on a neighborhood of `θ₀`; nonvanishing
at `θ₀` shrinks that neighborhood to one where `u` is nonzero; therefore
`θ ↦ Real.log ‖u θ‖` is continuous on a small compact interval and hence
interval-integrable there. -/
theorem analyticAt_log_norm_unit_locally_intervalIntegrable
    (u : ℝ → ℂ)
    {θ₀ : ℝ}
    (hu_an : AnalyticAt ℝ u θ₀)
    (hu_ne : u θ₀ ≠ 0) :
    ∃ a b : ℝ,
      a < θ₀ ∧ θ₀ < b ∧
      IntervalIntegrable
        (fun θ : ℝ => Real.log ‖u θ‖)
        MeasureTheory.volume a b := by
  have hlocal_an : ∀ᶠ (θ : ℝ) in 𝓝 θ₀, AnalyticAt ℝ u θ :=
    hu_an.eventually_analyticAt
  have hlocal_ne : ∀ᶠ (θ : ℝ) in 𝓝 θ₀, u θ ≠ 0 :=
    hu_an.continuousAt.eventually_ne hu_ne
  have hlocal :
      {θ : ℝ | AnalyticAt ℝ u θ ∧ u θ ≠ 0} ∈ 𝓝 θ₀ := by
    exact hlocal_an.and hlocal_ne
  exact
    Exists.elim (mem_nhds_iff_exists_Ioo_subset.mp hlocal)
      (fun a ha =>
        Exists.elim ha
          (fun b hb =>
            Exists.elim (exists_between hb.1.1)
              (fun a' ha' =>
                Exists.elim (exists_between hb.1.2)
                  (fun b' hb' =>
                    let ha'_b' : a' ≤ b' := (ha'.2.trans hb'.1).le
                    let hIcc_subset : Set.Icc a' b' ⊆ Set.Ioo a b :=
                      fun θ hθ =>
                        ⟨lt_of_lt_of_le ha'.1 hθ.1,
                          lt_of_le_of_lt hθ.2 hb'.2⟩
                    let hcont :
                        ContinuousOn
                          (fun θ : ℝ => Real.log ‖u θ‖)
                          (Set.Icc a' b') :=
                      fun θ hθ =>
                        let hθ_data : AnalyticAt ℝ u θ ∧ u θ ≠ 0 :=
                          hb.2 (hIcc_subset hθ)
                        ((hθ_data.1.continuousAt.norm).log
                          (norm_ne_zero_iff.mpr hθ_data.2)).continuousWithinAt
                    ⟨a', b', ha'.2, hb'.1,
                      hcont.intervalIntegrable_of_Icc ha'_b'⟩))))

/-- The analytic unit remainder in the local Jensen logarithmic model is
locally interval-integrable near the singular parameter. -/
theorem jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (hnot :
      ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
        Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  exact
    Exists.elim
      (jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero
        F hF R θ₀ hnot)
      (fun n hn =>
        Exists.elim hn
          (fun u hu =>
            let g : ℝ → ℝ := fun θ : ℝ => Real.log ‖u θ‖
            let hg :
                ∃ a b : ℝ,
                  a < θ₀ ∧ θ₀ < b ∧
                  IntervalIntegrable g MeasureTheory.volume a b :=
              analyticAt_log_norm_unit_locally_intervalIntegrable u hu.1 hu.2.1
            let hfirst :
                ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
                  F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
                    (θ - θ₀) ^ n • u θ :=
              hu.2.2.filter_mono nhdsWithin_le_nhds
            let hsecond : ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, u θ ≠ 0 :=
              (hu.1.continuousAt.eventually_ne hu.2.1).filter_mono nhdsWithin_le_nhds
            let hthird : ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀, θ ∈ {θ | θ ≠ θ₀} :=
              self_mem_nhdsWithin
            let hcombined :=
              (hfirst.and hsecond).and hthird
            let hmodel :
                ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
                  Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                    (n : ℝ) * Real.log |θ - θ₀| + g θ :=
              hcombined.mono
                (fun θ hθ =>
                  let hsample := hθ.1.1
                  let huθ_ne := hθ.1.2
                  let hne := hθ.2
                  let hsub_ne : θ - θ₀ ≠ 0 := sub_ne_zero.mpr hne
                  let hnorm_ne : ‖θ - θ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hsub_ne
                  let hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 := pow_ne_zero n hnorm_ne
                  let huθ_ne' : ‖u θ‖ ≠ 0 := norm_ne_zero_iff.mpr huθ_ne
                  calc
                    Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                        Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
                      exact congrArg Real.log (congrArg norm hsample)
                    _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
                      exact
                        congrArg Real.log
                          (calc
                            ‖(θ - θ₀) ^ n • u θ‖ = ‖(θ - θ₀) ^ n‖ * ‖u θ‖ := by
                              exact norm_smul _ _
                            _ = ‖θ - θ₀‖ ^ n * ‖u θ‖ := by
                              exact congrArg (fun t : ℝ => t * ‖u θ‖) (norm_pow _ _))
                    _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
                      exact Real.log_mul hpow_ne huθ_ne'
                    _ = (n : ℝ) * Real.log |θ - θ₀| + g θ := by
                      have hnormabs : ‖θ - θ₀‖ = |θ - θ₀| := by
                        exact Real.norm_eq_abs _
                      have hlogpow :
                          Real.log (‖θ - θ₀‖ ^ n) =
                            (n : ℝ) * Real.log |θ - θ₀| := by
                        calc
                          Real.log (‖θ - θ₀‖ ^ n) = (n : ℝ) * Real.log ‖θ - θ₀‖ := by
                            exact Real.log_pow _ _
                          _ = (n : ℝ) * Real.log |θ - θ₀| := by
                            exact congrArg (fun t : ℝ => (n : ℝ) * Real.log t) hnormabs
                      exact congrArg (fun t : ℝ => t + g θ) hlogpow)
            ⟨n, g, hg, hmodel⟩))

/-- The Jensen boundary logarithmic integrand has a punctured local
log-distance model with a locally interval-integrable remainder near each
singular parameter. -/
theorem jensenBoundaryLogLocalModel_intervalIntegrable_near_parameterZero
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ :
      θ₀ ∈ Set.Icc 0 (2 * Real.pi) ∧
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
      ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
    intro hzero
    have htwoR : 0 < 2 * R := by
      exact mul_pos zero_lt_two hR
    have hzero_scaled :
        ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
      hzero
    have hglobal :
        ∀ z : ℂ, F z = 0 :=
      entireFunction_eq_zero_of_eventually_zero_on_positiveRadius_exp_arc
        F hF (2 * R) htwoR θ₀ hzero_scaled
    exact
      Exists.elim hnontrivial
        (fun z hz => hz (hglobal z))
  exact
    Exists.elim
      (jensenBoundaryLogSample_localLogContribution_remainder_intervalIntegrable
        F hF R θ₀ hnot)
      (fun n hn =>
        Exists.elim hn
          (fun g hg =>
            let hmodel :
                ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
                  entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
                    (n : ℝ) * Real.log |θ - θ₀| + g θ :=
              hg.2.mono
                (fun θ hθ =>
                  calc
                    entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
                        Real.log
                          ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ :=
                      entireFunctionJensenBoundaryLogIntegrand_def_ownerRoot F (2 * R) θ
                    _ = (n : ℝ) * Real.log |θ - θ₀| + g θ :=
                      hθ)
            ⟨n, g, hg.1, hmodel⟩))

/-- The finite circle-zero set induces a finite parameter singular set on the
fundamental boundary arc. -/
theorem entireFunction_jensenBoundaryCircleZeroParameters_finite
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R) :
    Set.Finite
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0} := by
  let f : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} → ℂ :=
    fun θ => ((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
  have hCircle : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} :=
    entireFunction_jensenCircleZeros_finite F hF hnontrivial R
  have hInj : Function.Injective f := by
    intro a b hEq
    have hscale : ((2 * R : ℝ) : ℂ) = (2 : ℂ) * (R : ℂ) :=
      Complex.ofReal_mul 2 R
    have hEq_for_owner :
        (2 : ℂ) * (R : ℂ) * Complex.exp (((a : ℝ) : ℂ) * Complex.I) =
          (2 : ℂ) * (R : ℂ) * Complex.exp (((b : ℝ) : ℂ) * Complex.I) := by
      calc
        (2 : ℂ) * (R : ℂ) * Complex.exp (((a : ℝ) : ℂ) * Complex.I) =
            ((2 * R : ℝ) : ℂ) * Complex.exp (((a : ℝ) : ℂ) * Complex.I) := by
          exact
            congrArg
              (fun c : ℂ => c * Complex.exp (((a : ℝ) : ℂ) * Complex.I))
              hscale.symm
        _ = f a :=
          rfl
        _ = f b :=
          hEq
        _ = ((2 * R : ℝ) : ℂ) * Complex.exp (((b : ℝ) : ℂ) * Complex.I) :=
          rfl
        _ = (2 : ℂ) * (R : ℂ) * Complex.exp (((b : ℝ) : ℂ) * Complex.I) := by
          exact
            congrArg
              (fun c : ℂ => c * Complex.exp (((b : ℝ) : ℂ) * Complex.I))
              hscale
    apply Subtype.ext
    exact entireFunction_jensenBoundaryCircleParam_injectiveOn_Ioc hR a.2 b.2 hEq_for_owner
  have hpre : (f ⁻¹' {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}).Finite :=
    hCircle.preimage fun _ _ _ _ hEq => hInj hEq
  have h2R_nonneg : 0 ≤ 2 * R := by
    exact mul_nonneg zero_le_two (le_of_lt hR)
  have htarget :
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0} =
        Subtype.val '' (f ⁻¹' {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) := by
    apply Set.Subset.antisymm
    · intro θ hθ
      let θsub : {θ : ℝ // θ ∈ Set.Ioc 0 (2 * Real.pi)} := ⟨θ, hθ.1⟩
      have hnorm :
          ‖f θsub‖ = 2 * R :=
        entireFunctionJensenBoundaryCircle_norm
          (R := 2 * R) (θ := θ) h2R_nonneg
      exact
        ⟨θsub, ⟨hnorm, hθ.2⟩, rfl⟩
    · intro θ hθ
      exact
        Exists.elim hθ
          (fun θsub hθsub =>
            Eq.subst
              (motive := fun t : ℝ =>
                t ∈ Set.Ioc 0 (2 * Real.pi) ∧
                  F (((2 * R : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) = 0)
              hθsub.2
              ⟨θsub.2, hθsub.1.2⟩)
  exact
    Eq.subst
      (motive := fun T : Set ℝ => T.Finite)
      htarget.symm
      (hpre.image Subtype.val)

/-- Jensen boundary specialization of finite logarithmic-singularity gluing.

The singular set is the finite set of parameters on the fundamental arc whose
circle samples are zeros.  Each such parameter is handled by the analytic
Taylor/log local model, and the zero-free complement is continuous. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let S : Set ℝ :=
    {θ : ℝ | θ ∈ Set.Icc 0 (2 * Real.pi) ∧
      F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0}
  have hS : S.Finite := by
    let T : Set ℝ :=
      {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0}
    have hT : T.Finite := by
      exact
        entireFunction_jensenBoundaryCircleZeroParameters_finite F hF hnontrivial R hR
    have hsubset : S ⊆ insert (0 : ℝ) T := by
      intro θ hθ
      exact
        match eq_or_ne θ 0 with
        | Or.inl hθ0 => hθ0 ▸ Set.mem_insert (0 : ℝ) T
        | Or.inr hθ0 =>
            Set.mem_insert_iff.mpr
              (Or.inr ⟨⟨lt_of_le_of_ne hθ.1.1 hθ0.symm, hθ.1.2⟩, hθ.2⟩)
    exact (hT.insert (0 : ℝ)).subset hsubset
  have hlocal :
      ∀ θ₀ ∈ S, ∃ n : ℕ, ∃ g : ℝ → ℝ,
        (∃ u v : ℝ,
          u < θ₀ ∧ θ₀ < v ∧
          IntervalIntegrable g MeasureTheory.volume u v) ∧
        ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
          entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
            (n : ℝ) * Real.log |θ - θ₀| + g θ := by
    intro θ₀ hθ₀
    exact
      jensenBoundaryLogLocalModel_intervalIntegrable_near_parameterZero
        F hF hnontrivial R hR θ₀ hθ₀
  have hcont :
      ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        ({θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ θ ∉ S}) := by
    have hmul : Continuous (fun θ : ℝ => θ * Complex.I) := by
      exact Complex.continuous_ofReal.mul continuous_const
    have hparam : Continuous
        (fun θ : ℝ => ((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ => ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    have hraw :
        ContinuousOn
          (fun θ : ℝ => Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖)
          ({θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧ θ ∉ S}) :=
      hcont_norm.continuousOn.log
        (fun θ hθ =>
          norm_ne_zero_iff.mpr
            (fun hzero => hθ.2 ⟨hθ.1, hzero⟩))
    exact
      hraw.congr
        (fun θ _ =>
          entireFunctionJensenBoundaryLogIntegrand_def_ownerRoot F (2 * R) θ)
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      (0 : ℝ) (2 * Real.pi) S
      (mul_nonneg zero_le_two Real.pi_pos.le)
      hS hlocal hcont

/-- Finite gluing of local logarithmic singularity models on the Jensen
fundamental interval. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- Finite logarithmic singularity gluing for Jensen boundary integrability. -/
theorem intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_glue
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_localSingularityModel
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact
    intervalIntegrable_jensenBoundaryLogIntegrand_of_finite_log_singularities_core
      F hF hnontrivial R hR hzeros

/-- The Jensen boundary logarithmic average is interval-integrable once the
circle zero set has been split into finitely many isolated logarithmic
singularities, each handled by the local factorization and logarithmic
contribution API. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  exact entireFunction_jensenBoundaryLogAverage_localSingularityModel F hF hnontrivial R hR hzeros

/-- Interval-integrability of the boundary logarithmic integrand at an arbitrary
positive radius, obtained from the doubled-radius Jensen API by using the
half-radius. -/
theorem entireFunction_boundaryLogIntegrand_intervalIntegrable_of_finiteCircleZeros
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    {r : ℝ}
    (hr : 0 < r)
    (hzeros : Set.Finite {z : ℂ | ‖z‖ = r ∧ F z = 0}) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F r)
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
  let R : ℝ := r / 2
  have hR : 0 < R :=
    half_pos hr
  have hscale : 2 * R = r := by
    calc
      2 * R = 2 * (r / 2) := rfl
      _ = r / 2 + r / 2 := two_mul (r / 2)
      _ = r := add_halves r
  have hzerosR :
      Set.Finite {z : ℂ | ‖z‖ = 2 * R ∧ F z = 0} := by
    exact Eq.subst
      (motive := fun s : ℝ =>
        Set.Finite {z : ℂ | ‖z‖ = s ∧ F z = 0})
      hscale.symm
      hzeros
  have hIntR :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
      F hF hnontrivial R hR hzerosR
  exact Eq.subst
    (motive := fun s : ℝ =>
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F s)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi))
    hscale
    hIntR

end

end LFunctions
end Boundary

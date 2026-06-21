import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.OriginTaylorTransport.NonzeroZeroSums.Owner

/-!
# Origin Taylor transport and zero-counting consequences

This owner layer was split from `OriginTaylorTransport.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Interval-integral transport across a finite exceptional set.

This theorem is the measure-theoretic root underneath the origin-factor
boundary integral comparison.  Once a finite set `S` contains all logarithmic
singular parameters and the two integrands agree off `S` on `[0,2π]`, the
interval integral sees only the off-exception identity. -/
theorem intervalIntegral_eq_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  have hAeNotMem :
      ∀ᵐ θ ∂MeasureTheory.volume, θ ∉ S :=
    hS.countable.ae_not_mem MeasureTheory.volume
  exact
    intervalIntegral.integral_congr_ae
      (hAeNotMem.mono
        (fun θ hθ_not_mem hθ_interval =>
          have hθ_uIcc :
              θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi) :=
            Set.uIoc_subset_uIcc hθ_interval
          have hθ_Icc :
              θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
            have hle : (0 : ℝ) ≤ 2 * Real.pi :=
              le_of_lt Real.two_pi_pos
            exact Eq.subst
              (motive := fun T : Set ℝ => θ ∈ T)
              (Set.uIcc_of_le hle)
              hθ_uIcc
          hcongr θ hθ_Icc hθ_not_mem))

/-- Finite-exception transport to a constant-plus integrand. -/
theorem intervalIntegral_eq_const_add_of_finite_exception_congr
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ := by
  exact
    intervalIntegral_eq_of_finite_exception_congr
      u
      (fun θ : ℝ => c + v θ)
      S
      hS
      hcongr

/-- Interval integration of a constant plus an interval-integrable remainder. -/
theorem intervalIntegral_const_add_eq_length_smul_add
    (v : ℝ → ℝ)
    (c a b : ℝ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume a b) :
    (∫ θ in a..b, c + v θ) =
      (b - a) • c + ∫ θ in a..b, v θ := by
  have hconst :
      IntervalIntegrable (fun _θ : ℝ => c) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable continuous_const a b
  calc
    (∫ θ in a..b, c + v θ) =
        ∫ θ in a..b, (fun _θ : ℝ => c) θ + v θ := rfl
    _ =
        (∫ _θ in a..b, c) + ∫ θ in a..b, v θ := by
      exact intervalIntegral.integral_add hconst hv
    _ =
        (b - a) • c + ∫ θ in a..b, v θ := by
      exact congrArg
        (fun x : ℝ => x + ∫ θ in a..b, v θ)
        (intervalIntegral.integral_const c)

/-- Finite-exception constant-plus transport, including the constant-integral
evaluation, on the Jensen boundary interval. -/
theorem intervalIntegral_finiteException_const_add_eq_twoPi_smul_add
    (u v : ℝ → ℝ)
    (c : ℝ)
    (S : Set ℝ)
    (hS : S.Finite)
    (hcongr :
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ S →
        u θ = c + v θ)
    (hv :
      IntervalIntegrable v MeasureTheory.volume
        (0 : ℝ) (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
      (2 * Real.pi - 0) • c +
        ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), u θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), c + v θ :=
      intervalIntegral_eq_const_add_of_finite_exception_congr
        u v c S hS hcongr
    _ =
        (2 * Real.pi - 0) • c +
          ∫ θ in (0 : ℝ)..(2 * Real.pi), v θ :=
      intervalIntegral_const_add_eq_length_smul_add
        v c (0 : ℝ) (2 * Real.pi) hv

/-- The origin Taylor quotient gives the expected boundary-circle norm
factorization at every sample. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 ≤ R) :
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
      R ^ entireFunctionZeroMultiplicity F hF 0 *
        ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
  let z : ℂ := (R : ℂ) * Complex.exp (θ * Complex.I)
  have hz_norm : ‖z‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR
  calc
    ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        ‖F z‖ := rfl
    _ = ‖z ^ entireFunctionZeroMultiplicity F hF 0 • G z‖ := by
      exact congrArg norm (hfactor z)
    _ =
        ‖z ^ entireFunctionZeroMultiplicity F hF 0‖ * ‖G z‖ := by
      exact norm_smul (z ^ entireFunctionZeroMultiplicity F hF 0) (G z)
    _ =
        ‖z‖ ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖G z‖)
        (norm_pow z (entireFunctionZeroMultiplicity F hF 0))
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖ := by
      exact congrArg
        (fun x : ℝ => x ^ entireFunctionZeroMultiplicity F hF 0 * ‖G z‖)
        hz_norm
    _ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl

/-- At boundary samples where the quotient does not vanish and the radius is
positive, the origin Taylor quotient contributes exactly `m log R` to the
Jensen logarithmic integrand. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hR_nonneg : 0 ≤ R := hR.le
  have hnorm :
      ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ =
        R ^ entireFunctionZeroMultiplicity F hF 0 *
          ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ :=
    entireFunction_originTaylorFactor_boundaryCircle_norm_factorization
      F G hF hfactor hR_nonneg
  have hpow_ne :
      R ^ entireFunctionZeroMultiplicity F hF 0 ≠ 0 :=
    pow_ne_zero (entireFunctionZeroMultiplicity F hF 0) hR.ne'
  have hG_norm_ne :
      ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hG
  calc
    entireFunctionJensenBoundaryLogIntegrand F R θ =
        Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl
    _ =
        Real.log
          (R ^ entireFunctionZeroMultiplicity F hF 0 *
            ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖) := by
      exact congrArg Real.log hnorm
    _ =
        Real.log (R ^ entireFunctionZeroMultiplicity F hF 0) +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact Real.log_mul hpow_ne hG_norm_ne
    _ =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
          Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := by
      exact congrArg
        (fun x : ℝ =>
          x + Real.log ‖G ((R : ℂ) * Complex.exp (θ * Complex.I))‖)
        (Real.log_pow R (entireFunctionZeroMultiplicity F hF 0))
    _ =
        (entireFunctionZeroMultiplicity F hF 0 : ℝ) * Real.log R +
          entireFunctionJensenBoundaryLogIntegrand G R θ := rfl

/-- Off the finite quotient boundary-zero set, the origin Taylor factor gives
the pointwise logarithmic boundary identity. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R)
    (hθ :
      θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R)
    (hθI : θ ∈ Set.Icc 0 (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogIntegrand F R θ =
      entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
        entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hG :
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunctionJensenQuotientBoundary_sample_ne_of_not_mem_zeroParameters
      G hθ hθI
  exact
    entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_of_quotient_ne
      F G hF hfactor hR hG

/-- The finite-exception data needed by origin Taylor boundary-integral
transport: the quotient-zero exceptional set is finite, and away from it the
boundary logarithmic integrands differ by the constant origin contribution. -/
theorem entireFunction_originTaylorFactor_boundaryLogIntegrand_finiteExceptionCertificate
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR_pos : 0 < R)
    (hInj :
      Set.InjOn
        (fun θ : ℝ => (R : ℂ) * Complex.exp (θ * Complex.I))
        (Set.Ioc 0 (2 * Real.pi)))
    (hCircle : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite ∧
      ∀ θ : ℝ,
        θ ∈ Set.Icc 0 (2 * Real.pi) →
        θ ∉ entireFunctionJensenQuotientBoundaryZeroParameters G R →
        entireFunctionJensenBoundaryLogIntegrand F R θ =
          entireFunctionOriginMultiplicityLogRadiusContribution F hF R +
            entireFunctionJensenBoundaryLogIntegrand G R θ := by
  have hfinite :
      (entireFunctionJensenQuotientBoundaryZeroParameters G R).Finite :=
    entireFunctionJensenQuotientBoundaryZeroParameters_finite_of_injectiveOn
      G R hR_pos.le hInj hCircle
  exact
    And.intro
      hfinite
      (fun θ hθI hθnot =>
        entireFunction_originTaylorFactor_boundaryLogIntegrand_eq_off_quotientZeroParameters
          F G hF hfactor hR_pos hθnot hθI)

/-- A positive-radius Jensen boundary sample is away from the origin. -/
theorem entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos
    {R θ : ℝ}
    (hR : 0 < R) :
    (R : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
  have hnorm :
      ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ = R :=
    entireFunctionJensenBoundaryCircle_norm hR.le
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖(R : ℂ) * Complex.exp (θ * Complex.I)‖ := hnorm.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius Jensen circle, the origin Taylor quotient has the
same boundary-zero parameters as the original function. -/
theorem entireFunction_originTaylorFactor_boundaryCircle_zero_iff_quotient_zero
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R θ : ℝ}
    (hR : 0 < R) :
    F ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 ↔
      G ((R : ℂ) * Complex.exp (θ * Complex.I)) = 0 := by
  exact
    entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
      F G hF hfactor
      (entireFunctionJensenBoundaryCircle_sample_ne_zero_of_pos hR)

/-- A point on a positive-radius circle is away from the origin. -/
theorem complex_ne_zero_of_norm_eq_pos_radius
    {z : ℂ}
    {R : ℝ}
    (hR : 0 < R)
    (hz : ‖z‖ = R) :
    z ≠ 0 := by
  intro hzero
  have hR_zero : R = 0 := by
    calc
      R = ‖z‖ := hz.symm
      _ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  exact hR.ne' hR_zero

/-- On a positive-radius circle, the origin Taylor quotient has exactly the
same circle-zero set as the original function. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R) :
    {z : ℂ | ‖z‖ = R ∧ F z = 0} =
      {z : ℂ | ‖z‖ = R ∧ G z = 0} := by
  ext z
  constructor
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mp hz.2⟩
  · intro hz
    have hz_ne : z ≠ 0 :=
      complex_ne_zero_of_norm_eq_pos_radius hR hz.1
    exact
      ⟨hz.1,
        (entireFunction_originTaylorFactor_nonzero_zero_iff_quotient_zero
          F G hF hfactor hz_ne).mpr hz.2⟩

/-- Finiteness of quotient zeros on a positive-radius circle transports back
through the origin Taylor factor. -/
theorem entireFunction_originTaylorFactor_circleZeroSet_finite_of_quotient
    (F G : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hfactor :
      ∀ z : ℂ,
        F z = z ^ entireFunctionZeroMultiplicity F hF 0 • G z)
    {R : ℝ}
    (hR : 0 < R)
    (hGfinite : Set.Finite {z : ℂ | ‖z‖ = R ∧ G z = 0}) :
    Set.Finite {z : ℂ | ‖z‖ = R ∧ F z = 0} := by
  exact
    Eq.subst
      (motive := fun S : Set ℂ => Set.Finite S)
      (entireFunction_originTaylorFactor_circleZeroSet_eq_quotient_circleZeroSet
        F G hF hfactor hR).symm
      hGfinite

/-- The boundary logarithmic integrand is bounded by the logarithmic maximum once the
circle log set is known to be bounded above. -/
theorem entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (θ : ℝ) :
    entireFunctionJensenBoundaryLogIntegrand F R θ ≤
      entireFunctionLogMaxOnCircle F R := by
  calc
    entireFunctionJensenBoundaryLogIntegrand F R θ =
        Real.log ‖F ((R : ℂ) * Complex.exp (θ * Complex.I))‖ := rfl
    _ ≤ sSup {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖} :=
      le_csSup hbdd
        ⟨(R : ℂ) * Complex.exp (θ * Complex.I),
          entireFunctionJensenBoundaryCircle_norm hR,
          rfl⟩
    _ = entireFunctionLogMaxOnCircle F R := rfl

/-- The normalized Jensen boundary average is bounded by the logarithmic maximum. -/
theorem entireFunctionJensenBoundaryLogAverage_le_logMaxOnCircle
    (F : ℂ → ℂ)
    {R : ℝ}
    (hR : 0 ≤ R)
    (hbdd :
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = R ∧ x = Real.log ‖F z‖})
    (hint :
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi)) :
    entireFunctionJensenBoundaryLogAverage F R ≤
      entireFunctionLogMaxOnCircle F R := by
  have htwo_pi_nonneg : 0 ≤ 2 * Real.pi :=
    le_of_lt Real.two_pi_pos
  have hconst_int :
      IntervalIntegrable
        (fun _ : ℝ => entireFunctionLogMaxOnCircle F R)
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) :=
    Continuous.intervalIntegrable continuous_const (0 : ℝ) (2 * Real.pi)
  have hintegral_le :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        ∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R := by
    exact intervalIntegral.integral_mono_on
      htwo_pi_nonneg
      hint
      hconst_int
      (fun θ _hθ =>
        entireFunctionJensenBoundaryLogIntegrand_le_logMaxOnCircle F hR hbdd θ)
  have hconst_eval :
      (∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R) =
        (2 * Real.pi) * entireFunctionLogMaxOnCircle F R := by
    calc
      (∫ _θ in (0 : ℝ)..(2 * Real.pi),
          entireFunctionLogMaxOnCircle F R) =
          (2 * Real.pi - 0) • entireFunctionLogMaxOnCircle F R := by
        exact intervalIntegral.integral_const
          (entireFunctionLogMaxOnCircle F R)
      _ = (2 * Real.pi) • entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x • entireFunctionLogMaxOnCircle F R)
          (sub_zero (2 * Real.pi))
      _ = (2 * Real.pi) * entireFunctionLogMaxOnCircle F R := rfl
  have hscale_nonneg : 0 ≤ (2 * Real.pi)⁻¹ :=
    inv_nonneg.mpr htwo_pi_nonneg
  have hscaled :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F R θ) ≤
        (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) := by
    exact mul_le_mul_of_nonneg_left
      (hintegral_le.trans_eq hconst_eval)
      hscale_nonneg
  have hcollapse :
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
        entireFunctionLogMaxOnCircle F R := by
    calc
      (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) =
          ((2 * Real.pi)⁻¹ * (2 * Real.pi)) *
            entireFunctionLogMaxOnCircle F R := by
        exact
          (mul_assoc
            (2 * Real.pi)⁻¹
            (2 * Real.pi)
            (entireFunctionLogMaxOnCircle F R)).symm
      _ = 1 * entireFunctionLogMaxOnCircle F R := by
        exact congrArg
          (fun x : ℝ => x * entireFunctionLogMaxOnCircle F R)
          (inv_mul_cancel₀ Real.two_pi_pos.ne')
      _ = entireFunctionLogMaxOnCircle F R := one_mul _
  calc
    entireFunctionJensenBoundaryLogAverage F R =
        (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            entireFunctionJensenBoundaryLogIntegrand F R θ) := rfl
    _ ≤
        (2 * Real.pi)⁻¹ *
          ((2 * Real.pi) * entireFunctionLogMaxOnCircle F R) :=
      hscaled
    _ = entireFunctionLogMaxOnCircle F R :=
      hcollapse

/-- Boundary regularity for Jensen's logarithmic average on doubled circles.

For a nontrivial entire function, the boundary logarithm has only isolated
logarithmic singularities on each circle.  Consequently the circle log set is
bounded above and the logarithmic boundary integrand is interval-integrable. -/
theorem entireFunction_jensenBoundaryLogSet_bddAbove
  (F : ℂ → ℂ)
  (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
  (R : ℝ) :
    BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} := by
  have hcontF : Continuous F :=
    continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
  have hcont_norm : Continuous fun z : ℂ => ‖F z‖ :=
    continuous_norm.comp hcontF
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) (2 * R)) := by
    exact isCompact_closedBall (0 : ℂ) (2 * R)
  exact
    Exists.elim
      (hcompact.bddAbove_image (hcont_norm.continuousOn))
      (fun M hM =>
        Exists.intro M
          (fun x hx =>
            Exists.elim hx
              (fun z hz_data =>
                  match hz_data with
                  | ⟨hz, hx_eq⟩ =>
                      have hzball : z ∈ Metric.closedBall (0 : ℂ) (2 * R) :=
                        have hdist_norm : dist z 0 = ‖z‖ := by
                          calc
                            dist z 0 = ‖z - 0‖ :=
                              dist_eq_norm z 0
                            _ = ‖z‖ := by
                              exact congrArg norm (sub_zero z)
                        Metric.mem_closedBall.2
                          (Eq.subst
                            (motive := fun x : ℝ => x ≤ 2 * R)
                            hdist_norm.symm
                            (le_of_eq hz))
                    have hnorm_le : ‖F z‖ ≤ M :=
                      hM ⟨z, hzball, rfl⟩
                    have hlog_le : Real.log ‖F z‖ ≤ M :=
                      le_trans (Real.log_le_self (norm_nonneg (F z))) hnorm_le
                    Eq.subst
                      (motive := fun y : ℝ => y ≤ M)
                      hx_eq.symm
                      hlog_le)))

/-- The Jensen boundary logarithmic integrand is continuous when the doubled circle
contains no zeros. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree
    (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (hzero : ∀ θ : ℝ,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
      Continuous (entireFunctionJensenBoundaryLogIntegrand F (2 * R)) := by
    have hmul : Continuous (fun θ : ℝ => (θ : ℂ) * Complex.I) := by
      exact Complex.continuous_ofReal.mul continuous_const
    have hparam :
        Continuous
          (fun θ : ℝ =>
            (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ =>
            ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.log (fun θ => norm_ne_zero_iff.mpr (hzero θ))

/-- If the doubled circle has no zeros, the Jensen boundary logarithmic average
is interval-integrable by continuity. -/
theorem entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_circleZeroFree
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
      (hzero : ∀ θ : ℝ,
        F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
    IntervalIntegrable
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      MeasureTheory.volume
      (0 : ℝ)
      (2 * Real.pi) := by
    exact
      Continuous.intervalIntegrable
        (entireFunction_jensenBoundaryLogIntegrand_continuous_of_circleZeroFree F hF R hzero)
        (0 : ℝ)
        (2 * Real.pi)

/-- The local Taylor factorization of the boundary sample yields the expected
log-distance plus continuous remainder identity on the punctured neighborhood. -/
theorem jensenBoundaryLogSample_localLogContribution
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (θ₀ : ℝ)
      (hnot :
        ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
        ContinuousAt g θ₀ ∧
        ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
          Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
            (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  exact
    Exists.elim
      (jensenBoundaryLogSample_exists_eventuallyEq_pow_smul_nonzero F hF R θ₀ hnot)
      (fun n hn =>
        Exists.elim hn
          (fun u hu =>
            match hu with
            | ⟨hu_an, hu_tail⟩ =>
                match hu_tail with
                | ⟨hu_ne, hu_eq⟩ =>
                    have hcont :
                        ContinuousAt (fun θ : ℝ => Real.log ‖u θ‖) θ₀ :=
                      (hu_an.continuousAt.norm).log (norm_ne_zero_iff.mpr hu_ne)
                    have hmodel :
                        ∀ᶠ (θ : ℝ) in 𝓝[≠] θ₀,
                          Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                            (n : ℝ) * Real.log |θ - θ₀| +
                              Real.log ‖u θ‖ :=
                      (((hu_eq.filter_mono nhdsWithin_le_nhds).and
                          ((hu_an.continuousAt.eventually_ne hu_ne).filter_mono
                            nhdsWithin_le_nhds)).and
                        self_mem_nhdsWithin).mono
                        (fun θ hθ_all =>
                          have hθ : F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
                              (θ - θ₀) ^ n • u θ :=
                            hθ_all.1.1
                          have huθ_ne : u θ ≠ 0 :=
                            hθ_all.1.2
                          have hne : θ ≠ θ₀ :=
                            hθ_all.2
                          have hsub_ne : θ - θ₀ ≠ 0 :=
                            sub_ne_zero.mpr hne
                          have hnorm_ne : ‖θ - θ₀‖ ≠ 0 :=
                            norm_ne_zero_iff.mpr hsub_ne
                          have hpow_ne : ‖θ - θ₀‖ ^ n ≠ 0 :=
                            pow_ne_zero n hnorm_ne
                          have huθ_ne' : ‖u θ‖ ≠ 0 :=
                            norm_ne_zero_iff.mpr huθ_ne
                          have hpoint :
                              Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                                (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
                            calc
                              Real.log ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ =
                                  Real.log ‖(θ - θ₀) ^ n • u θ‖ := by
                                exact congrArg Real.log (congrArg norm hθ)
                              _ = Real.log (‖θ - θ₀‖ ^ n * ‖u θ‖) := by
                                have hnorm_product :
                                    ‖(θ - θ₀) ^ n • u θ‖ =
                                      ‖θ - θ₀‖ ^ n * ‖u θ‖ := by
                                  calc
                                    ‖(θ - θ₀) ^ n • u θ‖ =
                                        ‖(θ - θ₀) ^ n‖ * ‖u θ‖ := by
                                      exact norm_smul _ _
                                    _ = ‖θ - θ₀‖ ^ n * ‖u θ‖ := by
                                      exact congrArg
                                        (fun t : ℝ => t * ‖u θ‖)
                                        (norm_pow _ _)
                                exact congrArg Real.log hnorm_product
                              _ = Real.log (‖θ - θ₀‖ ^ n) + Real.log ‖u θ‖ := by
                                exact Real.log_mul hpow_ne huθ_ne'
                              _ = (n : ℝ) * Real.log |θ - θ₀| + Real.log ‖u θ‖ := by
                                have hnormabs : ‖θ - θ₀‖ = |θ - θ₀| := by
                                  exact Real.norm_eq_abs _
                                have hpowlog :
                                    Real.log (‖θ - θ₀‖ ^ n) =
                                      (n : ℝ) * Real.log |θ - θ₀| := by
                                  calc
                                    Real.log (‖θ - θ₀‖ ^ n) =
                                        (n : ℝ) * Real.log ‖θ - θ₀‖ := by
                                      exact Real.log_pow _ _
                                    _ = (n : ℝ) * Real.log |θ - θ₀| := by
                                      exact congrArg
                                        (fun t : ℝ => (n : ℝ) * Real.log t)
                                        hnormabs
                                exact congrArg
                                  (fun x : ℝ => x + Real.log ‖u θ‖)
                                  hpowlog
                          hpoint)
                    Exists.intro n
                      (Exists.intro
                        (fun θ : ℝ => Real.log ‖u θ‖)
                        (And.intro hcont hmodel))))

/-- The sampled Jensen boundary function is not eventually zero near a singular
parameter once the entire function is nontrivial. -/
theorem jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0)
    (R : ℝ)
    (hR : 0 < R)
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ Set.Ioc 0 (2 * Real.pi)) :
    ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
      F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 := by
  intro hzero
  have hsample :
      AnalyticAt ℝ
        (fun θ : ℝ =>
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀ :=
    jensenBoundaryLogSample_analyticAt F hF R θ₀
  have hlocal_zero :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        (fun θ : ℝ =>
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0 :=
    hzero
  have hradius_eq : (((2 * R : ℝ) : ℂ)) = (2 * R : ℂ) :=
    Complex.ofReal_mul 2 R
  have hsample_product :
      AnalyticAt ℝ
        (fun θ : ℝ =>
          F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ₀ :=
    Eq.subst
      (motive := fun c : ℂ =>
        AnalyticAt ℝ
          (fun θ : ℝ => F (c * Complex.exp ((θ : ℂ) * Complex.I))) θ₀)
      hradius_eq
      hsample
  have hlocal_zero_product :
      ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
        (fun θ : ℝ =>
          F ((2 * R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0 :=
    Eq.subst
      (motive := fun c : ℂ =>
        ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          (fun θ : ℝ => F (c * Complex.exp ((θ : ℂ) * Complex.I))) θ = 0)
      hradius_eq
      hlocal_zero
  have hpropagate :
      ∀ z : ℂ, F z = 0 := by
    exact entireFunction_eq_zero_of_jensenBoundarySample_eventually_zero
      F hF R hR θ₀ hθ₀ hsample_product hlocal_zero_product
  exact
    Exists.elim hnontrivial
      (fun z hz => hz (hpropagate z))

/-- Local remainder extraction for a punctured-neighborhood Jensen boundary
model. -/
theorem jensenBoundaryLogIntegrand_continuousAt_localRemainder
    (F : ℂ → ℂ)
    (_hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (R : ℝ)
    (θ₀ : ℝ)
    (n : ℕ)
    (g : ℝ → ℝ)
    (hg : ContinuousAt g θ₀)
    (hmodel :
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ) :
    ∃ g' : ℝ → ℝ,
      ContinuousAt g' θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g' θ := by
  exact
    continuousRemainderExtensionOn_Icc_of_puncturedLocalModel
      (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
      θ₀ n g hg hmodel

/-- The boundary logarithmic integrand has the expected local log-distance plus
continuous expansion near each singular parameter, on the punctured
neighborhood where the logarithmic singularity is modeled. -/
theorem jensenBoundaryLogIntegrand_punctured_logDistance_plus_continuousAt_near_parameterZero
    (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (hnontrivial : ∃ z : ℂ, F z ≠ 0)
      (R : ℝ)
      (hR : 0 < R)
      (θ₀ : ℝ)
      (hθ₀ :
        θ₀ ∈ Set.Ioc 0 (2 * Real.pi) ∧
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ₀ : ℂ) * Complex.I)) = 0) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      ContinuousAt g θ₀ ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        entireFunctionJensenBoundaryLogIntegrand F (2 * R) θ =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hnot :
        ¬ ∀ᶠ (θ : ℝ) in 𝓝 θ₀,
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = 0 :=
      jensenBoundaryLogSample_not_eventually_zero_of_nontrivial
        F hF hnontrivial R hR θ₀ hθ₀.1
  exact
    match jensenBoundaryLogSample_localLogContribution F hF R θ₀ hnot with
    | ⟨n, g, hg, hmodel⟩ =>
        match jensenBoundaryLogIntegrand_continuousAt_localRemainder
            F hF R θ₀ n g hg hmodel with
        | ⟨g', hg', hg'eventually⟩ =>
            Exists.intro n
              (Exists.intro g'
                (And.intro hg' hg'eventually))

/-- Away from the singular parameters, the Jensen boundary logarithmic
integrand is continuous on the fundamental arc. -/
theorem entireFunction_jensenBoundaryLogIntegrand_continuousOn_compl_circleZeroParameters
      (F : ℂ → ℂ)
      (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
      (R : ℝ)
      (hzero : ∀ θ : ℝ,
        θ ∈ Set.Ioc 0 (2 * Real.pi) →
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0) :
      ContinuousOn (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        {θ : ℝ | θ ∈ Set.Ioc 0 (2 * Real.pi) ∧
          F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ≠ 0} := by
    have hmul : Continuous (fun θ : ℝ => (θ : ℂ) * Complex.I) := by
      exact Complex.continuous_ofReal.mul continuous_const
    have hparam :
        Continuous
          (fun θ : ℝ =>
            (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))) := by
      exact continuous_const.mul (Complex.continuous_exp.comp hmul)
    have hcontF : Continuous F :=
      continuous_iff_continuousAt.mpr (fun z => (hF z).continuousAt)
    have hcont_norm :
        Continuous
          (fun θ : ℝ =>
            ‖F (((2 * R : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖) :=
      continuous_norm.comp (hcontF.comp hparam)
    exact hcont_norm.continuousOn.log
      (fun θ hθ => norm_ne_zero_iff.mpr (hzero θ hθ.1))

theorem entireFunction_jensenBoundaryLogAverage_regularity
    (F : ℂ → ℂ)
    (hF : ∀ z : ℂ, AnalyticAt ℂ F z)
    (hnontrivial : ∃ z : ℂ, F z ≠ 0) :
    ∀ R : ℝ,
      1 ≤ R →
      BddAbove {x : ℝ | ∃ z : ℂ, ‖z‖ = 2 * R ∧ x = Real.log ‖F z‖} ∧
      IntervalIntegrable
        (entireFunctionJensenBoundaryLogIntegrand F (2 * R))
        MeasureTheory.volume
        (0 : ℝ)
        (2 * Real.pi) := by
  intro R hR
  exact
      And.intro
        (entireFunction_jensenBoundaryLogSet_bddAbove F hF R)
      (entireFunction_jensenBoundaryLogAverage_intervalIntegrable_of_finiteCircleZeros
        F hF hnontrivial R
        (lt_of_lt_of_le zero_lt_one hR)
        (entireFunction_jensenCircleZeros_finite F hF hnontrivial R))


end
end LFunctions
end Boundary

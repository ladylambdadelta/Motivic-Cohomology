import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.GammaCore

/-!
# Boundary completed-log-derivative control

This file owns the strip-control package for the completed zeta negative
logarithmic derivative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Exact derivative formula for Deligne's `Gammaℝ` away from its
nonpositive-even singular locus. -/
theorem Gammaℝ_hasDerivAt_of_ne_zero_locus
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ))) :
    HasDerivAt Complex.Gammaℝ
      (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
          (-(1 / 2 : ℂ))) *
          Complex.Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) *
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
      z :=
  let hgamma_arg :
      ∀ n : ℕ, z / 2 ≠ -(n : ℂ) :=
    halfArgument_ne_negative_nat_of_ne_negative_even hz
  let hpi :
      HasDerivAt
        (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-z / 2) *
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
        z :=
    Gammaℝ_piFactor_hasDerivAt z
  let hgamma :
      HasDerivAt
        (fun s : ℂ => Complex.Gamma (s / 2))
        (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ))
        z :=
    Gammaℝ_halfGammaFactor_hasDerivAt hgamma_arg
  let hprod :
      HasDerivAt
        (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))
        (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
            (-(1 / 2 : ℂ))) *
            Complex.Gamma (z / 2) +
          (Real.pi : ℂ) ^ (-z / 2) *
            (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
        z :=
    hpi.mul hgamma
  let hfun :
      (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
        Complex.Gammaℝ :=
    Gammaℝ_eq_piFactor_mul_halfGamma_fun
  Eq.subst
    (motive := fun φ : ℂ → ℂ =>
      HasDerivAt φ
        (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
            (-(1 / 2 : ℂ))) *
            Complex.Gamma (z / 2) +
          (Real.pi : ℂ) ^ (-z / 2) *
            (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
        z)
    hfun
    hprod

/-- Exact logarithmic derivative decomposition for Deligne's `Gammaℝ`. -/
theorem Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ)))
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
          Complex.Gamma (z / 2) :=
  let p : ℂ := (Real.pi : ℂ) ^ (-z / 2)
  let p' : ℂ := p * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  let g : ℂ := Complex.Gamma (z / 2)
  let g' : ℂ := deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)
  let hp : p ≠ 0 :=
    cpow_ofReal_pi_ne_zero z
  let hΓ_def : Complex.Gammaℝ z = p * g :=
    Complex.Gammaℝ_def z
  let hg : g ≠ 0 :=
    fun hg_zero =>
    let hprod_zero : p * g = 0 :=
      mul_eq_zero_of_right p hg_zero
    hΓ (hΓ_def.trans hprod_zero)
  let hderiv :
      deriv Complex.Gammaℝ z = p' * g + p * g' :=
    (Gammaℝ_hasDerivAt_of_ne_zero_locus hz).deriv
  let hquot_first :
      deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        (p' * g + p * g') / Complex.Gammaℝ z :=
    congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hderiv
  let hquot_second :
      (p' * g + p * g') / Complex.Gammaℝ z =
        (p' * g + p * g') / (p * g) :=
    congrArg (fun x : ℂ => (p' * g + p * g') / x) hΓ_def
  let hquot :
      deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        (p' * g + p * g') / (p * g) :=
    Eq.trans hquot_first hquot_second
  let hproduct :
      (p' * g + p * g') / (p * g) = p' / p + g' / g :=
    mul_logDeriv_algebra hp hg
  let hpi :
      p' / p = Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) :=
    Gammaℝ_piFactor_logDeriv_eq z
  let htail :
      p' / p + g' / g =
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2) :=
    congrArg₂ HAdd.hAdd hpi (Eq.refl (g' / g))
  Eq.trans hquot (Eq.trans hproduct htail)

/-- Conditional bridge from the inverse-`Gammaℝ` normalization used in the
completed-zeta split to the ordinary `Gammaℝ` logarithmic derivative. -/
theorem inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    {z : ℂ}
    (hΓdiff : DifferentiableAt ℂ Complex.Gammaℝ z)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    inverseGammaCompletionLogDeriv z =
      -deriv Complex.Gammaℝ z / Complex.Gammaℝ z :=
  let hdef :
      inverseGammaCompletionLogDeriv z =
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ :=
    inverseGammaCompletionLogDeriv_eq z
  let hinv :
      deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ =
        -deriv Complex.Gammaℝ z / Complex.Gammaℝ z :=
    deriv_inv_div_inv_eq_neg_deriv_div hΓdiff hΓ
  Eq.trans hdef hinv

/-- The negative logarithmic derivative of the ordinary Riemann zeta factor. -/
noncomputable def riemannZetaNegLogDeriv (z : ℂ) : ℂ :=
  - deriv riemannZeta z / riemannZeta z

/-- The ordinary Riemann-zeta negative logarithmic derivative unfolds to the derivative
quotient. -/
theorem riemannZetaNegLogDeriv_eq
    (z : ℂ) :
    riemannZetaNegLogDeriv z =
      - deriv riemannZeta z / riemannZeta z :=
  Eq.refl (riemannZetaNegLogDeriv z)

/-- A zero-excised vertical strip carrier for the completed zeta logarithmic derivative.

This is geometric data only: it records the vertical strip and singular-locus exclusions.
Polynomial logarithmic-derivative bounds are owned by `CompletedZetaNegLogDerivControl`,
so scheduled carriers can be constructed from avoidance without circular analytic fields. -/
structure CompletedZetaZeroExcisedStrip (a b : ℝ) where
  carrier : Set ℂ
  in_strip : ∀ z : ℂ, z ∈ carrier → a ≤ z.re ∧ z.re ≤ b
  ne_zero : ∀ z : ℂ, z ∈ carrier → z ≠ 0
  ne_one : ∀ z : ℂ, z ∈ carrier → z ≠ 1
  zeta_ne_zero : ∀ z : ℂ, z ∈ carrier → completedRiemannZeta z ≠ 0
  gamma_ne_zero : ∀ z : ℂ, z ∈ carrier → Complex.Gammaℝ z ≠ 0

theorem singleton_norm_le_value_add_one
    (g : ℂ → ℂ) (z₀ z : ℂ)
    (hz : z ∈ ({z₀} : Set ℂ)) :
    ‖g z‖ ≤ ‖g z₀‖ + 1 :=
  let hzz₀ : z = z₀ :=
    Set.eq_of_mem_singleton hz
  let hnorm_eq : ‖g z‖ = ‖g z₀‖ :=
    congrArg (fun w : ℂ => ‖g w‖) hzz₀
  let hnorm_le_at_z₀ : ‖g z₀‖ ≤ ‖g z₀‖ + 1 :=
    le_add_of_nonneg_right zero_le_one
  Eq.subst
    (motive := fun y : ℝ => y ≤ ‖g z₀‖ + 1)
    hnorm_eq.symm
    hnorm_le_at_z₀

theorem one_le_one_add_norm_pow
    (x : ℝ) (N : ℕ) :
    1 ≤ (1 + ‖x‖) ^ N :=
  one_le_pow₀
    (le_add_of_nonneg_right (norm_nonneg x))

theorem singleton_norm_le_value_add_one_mul_height
    (g : ℂ → ℂ) (z₀ z : ℂ) (N : ℕ)
    (hz : z ∈ ({z₀} : Set ℂ)) :
    ‖g z‖ ≤ (‖g z₀‖ + 1) * (1 + ‖z.im‖) ^ N :=
  let C : ℝ := ‖g z₀‖ + 1
  let hCpos : 0 < C :=
    add_pos_of_nonneg_of_pos (norm_nonneg (g z₀)) zero_lt_one
  let hCnonneg : 0 ≤ C :=
    le_of_lt hCpos
  let hvalue : ‖g z‖ ≤ C :=
    singleton_norm_le_value_add_one g z₀ z hz
  let hheight : 1 ≤ (1 + ‖z.im‖) ^ N :=
    one_le_one_add_norm_pow z.im N
  hvalue.trans
    (le_mul_of_one_le_right hCnonneg hheight)

/-- A singleton carrier has a polynomial bound for any fixed complex-valued function. -/
theorem singleton_polynomial_bound
    (g : ℂ → ℂ) (z₀ : ℂ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ ({z₀} : Set ℂ) →
        ‖g z‖ ≤ C * (1 + ‖z.im‖) ^ N :=
  let C : ℝ := ‖g z₀‖ + 1
  let hCpos : 0 < C :=
    add_pos_of_nonneg_of_pos (norm_nonneg (g z₀)) zero_lt_one
  Exists.intro C
    (And.intro hCpos
      (fun z hz =>
        singleton_norm_le_value_add_one_mul_height g z₀ z N hz))

/-- The singleton zero-excised strip at a point satisfying the zero-excision predicates. -/
def CompletedZetaZeroExcisedStrip.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := {z₀}
    in_strip :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => a ≤ w.re ∧ w.re ≤ b)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_strip
    ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_zero
    ne_one :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => w ≠ 1)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_one
    zeta_ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_zeta
    gamma_ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => Complex.Gammaℝ w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_gamma }

/-- The point of a singleton zero-excised strip belongs to its carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma).carrier :=
  Set.mem_singleton z₀

/-- The empty carrier is a zero-excised strip with vacuous polynomial bounds. -/
def CompletedZetaZeroExcisedStrip.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := ∅
    in_strip :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    ne_one :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    zeta_ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    gamma_ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz) }

/-- The union of two zero-excised strips over the same vertical strip is again a
zero-excised strip. -/
def CompletedZetaZeroExcisedStrip.union
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := E₁.carrier ∪ E₂.carrier
    in_strip :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.in_strip z hz₁
        | Or.inr hz₂ => E₂.in_strip z hz₂
    ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.ne_zero z hz₁
        | Or.inr hz₂ => E₂.ne_zero z hz₂
    ne_one :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.ne_one z hz₁
        | Or.inr hz₂ => E₂.ne_one z hz₂
    zeta_ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.zeta_ne_zero z hz₁
        | Or.inr hz₂ => E₂.zeta_ne_zero z hz₂
    gamma_ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.gamma_ne_zero z hz₁
        | Or.inr hz₂ => E₂.gamma_ne_zero z hz₂ }

/-- The left component of a zero-excised strip union is contained in the union carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_union_left
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    {z : ℂ} (hz : z ∈ E₁.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier :=
  Set.mem_union_left E₂.carrier hz

/-- The right component of a zero-excised strip union is contained in the union carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_union_right
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    {z : ℂ} (hz : z ∈ E₂.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier :=
  Set.mem_union_right E₁.carrier hz

theorem zetaSideNegLogDeriv_eq_def
    (z : ℂ) :
    zetaSideNegLogDeriv z =
      - deriv zetaSideFactor z / zetaSideFactor z :=
  Eq.refl (zetaSideNegLogDeriv z)

theorem zetaSideNegLogDeriv_transport_to_riemann
    {z : ℂ}
    (hderiv : deriv zetaSideFactor z = deriv riemannZeta z)
    (hfactor : zetaSideFactor z = riemannZeta z) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z :=
  let hdef :
      zetaSideNegLogDeriv z =
        - deriv zetaSideFactor z / zetaSideFactor z :=
    zetaSideNegLogDeriv_eq_def z
  let hderiv_step :
      - deriv zetaSideFactor z / zetaSideFactor z =
        - deriv riemannZeta z / zetaSideFactor z :=
    congrArg (fun x : ℂ => -x / zetaSideFactor z) hderiv
  let hfactor_step :
      - deriv riemannZeta z / zetaSideFactor z =
        - deriv riemannZeta z / riemannZeta z :=
    congrArg (fun x : ℂ => - deriv riemannZeta z / x) hfactor
  let htarget :
      - deriv riemannZeta z / riemannZeta z =
        riemannZetaNegLogDeriv z :=
    (riemannZetaNegLogDeriv_eq z).symm
  Eq.trans hdef
    (Eq.trans hderiv_step
      (Eq.trans hfactor_step htarget))

/-- Pointwise compatibility between the completed zeta-side factor and the ordinary
Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    {z : ℂ}
    (hz0 : z ≠ 0)
    (_hΛ : completedRiemannZeta z ≠ 0)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z :=
  let hderiv :
      deriv zetaSideFactor z = deriv riemannZeta z :=
    deriv_zetaSideFactor_eq_deriv_riemannZeta hz0 hΓ
  let hfactor :
      zetaSideFactor z = riemannZeta z :=
    zetaSideFactor_eq_riemannZeta hz0 hΓ
  zetaSideNegLogDeriv_transport_to_riemann hderiv hfactor

/-- On a zero-excised completed strip, the finite zeta-side logarithmic derivative is the
ordinary Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv_of_mem_zeroExcisedStrip
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (z : ℂ) (hz : z ∈ E.carrier) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z :=
  zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    (E.ne_zero z hz)
    (E.zeta_ne_zero z hz)
    (E.gamma_ne_zero z hz)

theorem completedZetaNegLogDeriv_eq_zetaSide_add_inverseGammaCorrection
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ) (hz : z ∈ E.carrier) :
    completedZetaNegLogDeriv z = zetaSideNegLogDeriv z + inverseGammaCompletionLogDeriv z :=
  let hside :
      zetaSideNegLogDeriv z =
        completedZetaNegLogDeriv z - inverseGammaCompletionLogDeriv z :=
    zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
      (E.ne_zero z hz) (E.ne_one z hz)
      (E.zeta_ne_zero z hz) (E.gamma_ne_zero z hz)
  (eq_sub_iff_add_eq.mp hside).symm

theorem completedZetaNegLogDeriv_norm_le_zetaSide_norm_add_inverseGammaCorrection_norm
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ :=
  let hsplit :
      completedZetaNegLogDeriv z =
        zetaSideNegLogDeriv z + inverseGammaCompletionLogDeriv z :=
    completedZetaNegLogDeriv_eq_zetaSide_add_inverseGammaCorrection E z hz
  Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖)
    hsplit.symm
    (norm_add_le (zetaSideNegLogDeriv z) (inverseGammaCompletionLogDeriv z))

theorem inverseGammaCorrection_norm_le_of_deriv_inv_bound
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (Cgamma : ℝ)
    (z : ℂ) (hz : z ∈ E.carrier)
    (hCgamma_bound : ∀ w : ℂ, w ∈ E.carrier →
        ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
          (Complex.Gammaℝ w)⁻¹‖ ≤ Cgamma * (1 + ‖w.im‖) ^ N) :
    ‖inverseGammaCompletionLogDeriv z‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N :=
  let hcorrection :
      inverseGammaCompletionLogDeriv z =
        deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ :=
    inverseGammaCompletionLogDeriv_eq z
  Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N)
    hcorrection.symm
    (hCgamma_bound z hz)

theorem zetaSide_add_inverseGammaCorrection_norm_bound
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (Czeta Cgamma : ℝ)
    (z : ℂ) (hz : z ∈ E.carrier)
    (hCzeta_bound : ∀ w : ℂ, w ∈ E.carrier →
      ‖zetaSideNegLogDeriv w‖ ≤ Czeta * (1 + ‖w.im‖) ^ N)
    (hCgamma_bound : ∀ w : ℂ, w ∈ E.carrier →
        ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
          (Complex.Gammaℝ w)⁻¹‖ ≤ Cgamma * (1 + ‖w.im‖) ^ N) :
    ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ ≤
      Czeta * (1 + ‖z.im‖) ^ N + Cgamma * (1 + ‖z.im‖) ^ N :=
  let hgamma :
      ‖inverseGammaCompletionLogDeriv z‖ ≤
        Cgamma * (1 + ‖z.im‖) ^ N :=
    inverseGammaCorrection_norm_le_of_deriv_inv_bound
      E N Cgamma z hz hCgamma_bound
  add_le_add (hCzeta_bound z hz) hgamma

theorem completedZetaNegLogDeriv_norm_bound_of_factor_bounds
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (Czeta Cgamma : ℝ)
    (z : ℂ) (hz : z ∈ E.carrier)
    (hCzeta_bound : ∀ w : ℂ, w ∈ E.carrier →
      ‖zetaSideNegLogDeriv w‖ ≤ Czeta * (1 + ‖w.im‖) ^ N)
    (hCgamma_bound : ∀ w : ℂ, w ∈ E.carrier →
        ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
          (Complex.Gammaℝ w)⁻¹‖ ≤ Cgamma * (1 + ‖w.im‖) ^ N) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N :=
  let hnorm :
      ‖completedZetaNegLogDeriv z‖ ≤
        ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ :=
    completedZetaNegLogDeriv_norm_le_zetaSide_norm_add_inverseGammaCorrection_norm
      E z hz
  let hbounds :
      ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ ≤
        Czeta * (1 + ‖z.im‖) ^ N +
          Cgamma * (1 + ‖z.im‖) ^ N :=
    zetaSide_add_inverseGammaCorrection_norm_bound
      E N Czeta Cgamma z hz hCzeta_bound hCgamma_bound
  let hfactor :
      Czeta * (1 + ‖z.im‖) ^ N +
          Cgamma * (1 + ‖z.im‖) ^ N =
        (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N :=
    (add_mul Czeta Cgamma ((1 + ‖z.im‖) ^ N)).symm
  hnorm.trans (hbounds.trans_eq hfactor)

/-- The completed negative log-derivative is bounded by the zeta-side and archimedean
completion logarithmic derivative bounds on vertical strips. -/
theorem completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hzeta : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤ C * (1 + ‖z.im‖) ^ N)
    (hgamma : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
        ≤ C * (1 + ‖z.im‖) ^ N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  match hzeta with
  | ⟨Czeta, hCzeta⟩ =>
      match hgamma with
      | ⟨Cgamma, hCgamma⟩ =>
          Exists.intro (Czeta + Cgamma)
            (And.intro
              (add_pos hCzeta.1 hCgamma.1)
              (fun z hz =>
                completedZetaNegLogDeriv_norm_bound_of_factor_bounds
                  E N Czeta Cgamma z hz hCzeta.2 hCgamma.2))

/-- Strip control data for the completed zeta negative logarithmic derivative. -/
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) where
  /-- Fixed-degree polynomial growth for the completed negative log derivative on a
  zero-excised strip.  This is the stable growth API used by rapid-decay products. -/
  zero_excised_polynomial_growth :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      ∃ K : ℕ,
        ∃ C : ℝ,
          0 < C ∧
          ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ K
  zero_excised_polynomial_strip_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ N
  zero_excised_polynomial_strip_bound_constant :
    ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  zero_excised_polynomial_strip_bound_constant_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      0 < zero_excised_polynomial_strip_bound_constant a b E N
  zero_excised_polynomial_strip_bound_constant_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
      (z : ℂ),
      z ∈ E.carrier →
      ‖completedZetaNegLogDeriv z‖ ≤
        zero_excised_polynomial_strip_bound_constant a b E N *
          (1 + ‖z.im‖) ^ N

/-- Build completed log-derivative strip control from concrete strip constants. -/
def CompletedZetaNegLogDerivControl.ofSuppliedConstants
    (f : ZetaAdmissibleFunction)
    (C : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < C a b E N)
    (hCbound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
        (z : ℂ),
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤ C a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivControl f :=
  { zero_excised_polynomial_growth :=
      fun a b E =>
        ⟨1, C a b E 1, hCpos a b E 1, hCbound a b E 1⟩
    zero_excised_polynomial_strip_bound :=
      fun a b E N => ⟨C a b E N, hCpos a b E N, hCbound a b E N⟩
    zero_excised_polynomial_strip_bound_constant :=
      C
    zero_excised_polynomial_strip_bound_constant_pos :=
      hCpos
    zero_excised_polynomial_strip_bound_constant_bound :=
      hCbound }

theorem CompletedZetaNegLogDerivControl.zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K :=
  h.zero_excised_polynomial_growth a b E

theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N :=
  h.zero_excised_polynomial_strip_bound a b E N

def CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) : ℝ :=
  h.zero_excised_polynomial_strip_bound_constant a b E N

theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant_pos
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    0 < h.zeroExcisedStripBoundConstant a b E N :=
  h.zero_excised_polynomial_strip_bound_constant_pos a b E N

theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant_bound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      h.zeroExcisedStripBoundConstant a b E N * (1 + ‖z.im‖) ^ N :=
  h.zero_excised_polynomial_strip_bound_constant_bound a b E N z hz

/-- The completed negative log-derivative control is the owner-level strip package. -/
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Type :=
  CompletedZetaNegLogDerivControl f

/-- The package is exactly the strip-control data. -/
def CompletedZetaNegLogDerivControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivControlPackage f = CompletedZetaNegLogDerivControl f :=
  Eq.refl (CompletedZetaNegLogDerivControl f)

/-- A critical-line specialization of the zero-excised polynomial strip bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineBound_of_mem
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (E : CompletedZetaZeroExcisedStrip (1 / 2 : ℝ) (1 / 2 : ℝ)) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ((1 / 2 : ℂ) + t * Complex.I) ∈ E.carrier →
        ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ N :=
  match h.zeroExcisedStripBound (1 / 2 : ℝ) (1 / 2 : ℝ) E N with
  | ⟨C, hCdata⟩ =>
      Exists.intro C
        (And.intro hCdata.1
          (fun t ht =>
            let him : ((1 / 2 : ℂ) + t * Complex.I).im = t :=
              im_half_plus_t_i t
            let hbound :
                ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
                  ≤ C *
                    (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ N :=
              hCdata.2 ((1 / 2 : ℂ) + t * Complex.I) ht
            let hRHS :
                C * (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ N =
                  C * (1 + ‖t‖) ^ N :=
              congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ N) him
            hbound.trans (le_of_eq hRHS)))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

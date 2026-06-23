import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner

/-!
# Boundary completed-log-derivative control

This file owns the strip-control package for the completed zeta negative
logarithmic derivative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: Imaginary part of (1/2 + t*I) is t. -/
private lemma im_half_plus_t_i (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
  have h1 : (1 / 2 : ℂ).im = 0 := by
    norm_num
  have h2 : (t * Complex.I).im = t := by
    calc (t * Complex.I).im = t * Complex.I.im + 0 * Complex.I.re := Complex.mul_im _ _
      _ = t * 1 + 0 := by simp
      _ = t := by simp
  calc ((1 / 2 : ℂ) + t * Complex.I).im
      = (1 / 2 : ℂ).im + (t * Complex.I).im := Complex.add_im _ _
    _ = 0 + t := by rw [h1, h2]
    _ = t := zero_add t

/-- The inverse-Gamma correction in the completed logarithmic derivative split. -/
noncomputable def inverseGammaCompletionLogDeriv (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹

/-- The inverse-Gamma correction unfolds to the derivative quotient. -/
theorem inverseGammaCompletionLogDeriv_eq
    (z : ℂ) :
    inverseGammaCompletionLogDeriv z =
      deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
  rfl

/-- The negative logarithmic derivative of the ordinary Riemann zeta factor. -/
noncomputable def riemannZetaNegLogDeriv (z : ℂ) : ℂ :=
  - deriv riemannZeta z / riemannZeta z

/-- The ordinary Riemann-zeta negative logarithmic derivative unfolds to the derivative
quotient. -/
theorem riemannZetaNegLogDeriv_eq
    (z : ℂ) :
    riemannZetaNegLogDeriv z =
      - deriv riemannZeta z / riemannZeta z :=
  rfl

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

/-- A singleton carrier has a polynomial bound for any fixed complex-valued function. -/
theorem singleton_polynomial_bound
    (g : ℂ → ℂ) (z₀ : ℂ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ ({z₀} : Set ℂ) →
        ‖g z‖ ≤ C * (1 + ‖z.im‖) ^ N := by
  let C : ℝ := ‖g z₀‖ + 1
  have hCpos : 0 < C :=
    add_pos_of_nonneg_of_pos (norm_nonneg (g z₀)) zero_lt_one
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have hzz₀ : z = z₀ :=
    Set.eq_of_mem_singleton hz
  have hnorm_eq : ‖g z‖ = ‖g z₀‖ :=
    congrArg (fun w : ℂ => ‖g w‖) hzz₀
  have hnorm_le_C_at_z₀ : ‖g z₀‖ ≤ C :=
    le_add_of_nonneg_right zero_le_one
  have hnorm_le_C : ‖g z‖ ≤ C :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ C)
      hnorm_eq.symm
      hnorm_le_C_at_z₀
  have hbase : 1 ≤ 1 + ‖z.im‖ :=
    le_add_of_nonneg_right (norm_nonneg z.im)
  have hpow : 1 ≤ (1 + ‖z.im‖) ^ N :=
    one_le_pow₀ hbase
  have hCnonneg : 0 ≤ C :=
    le_of_lt hCpos
  exact hnorm_le_C.trans
    (le_mul_of_one_le_right hCnonneg hpow)

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

/-- Pointwise compatibility between the completed zeta-side factor and the ordinary
Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    {z : ℂ}
    (hz0 : z ≠ 0)
    (_hΛ : completedRiemannZeta z ≠ 0)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  have hderiv :
      deriv zetaSideFactor z = deriv riemannZeta z :=
    deriv_zetaSideFactor_eq_deriv_riemannZeta hz0 hΓ
  have hfactor :
      zetaSideFactor z = riemannZeta z :=
    zetaSideFactor_eq_riemannZeta hz0 hΓ
  unfold zetaSideNegLogDeriv
  calc
    - deriv zetaSideFactor z / zetaSideFactor z =
        - deriv riemannZeta z / zetaSideFactor z := by
      exact congrArg (fun x : ℂ => -x / zetaSideFactor z) hderiv
    _ = - deriv riemannZeta z / riemannZeta z := by
      exact congrArg (fun x : ℂ => - deriv riemannZeta z / x) hfactor
    _ = riemannZetaNegLogDeriv z := by
      exact (riemannZetaNegLogDeriv_eq z).symm

/-- On a zero-excised completed strip, the finite zeta-side logarithmic derivative is the
ordinary Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv_of_mem_zeroExcisedStrip
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (z : ℂ) (hz : z ∈ E.carrier) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  exact zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    (E.ne_zero z hz)
    (E.zeta_ne_zero z hz)
    (E.gamma_ne_zero z hz)

/-- The completed negative log-derivative is bounded by the zeta-side and archimedean
completion logarithmic derivative bounds on vertical strips. -/
theorem completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hzeta :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖zetaSideNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hgamma :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
            ≤ C * (1 + ‖z.im‖) ^ N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  rcases hzeta with ⟨Czeta, hCzeta_pos, hCzeta_bound⟩
  rcases hgamma with ⟨Cgamma, hCgamma_pos, hCgamma_bound⟩
  refine ⟨Czeta + Cgamma, add_pos hCzeta_pos hCgamma_pos, ?_⟩
  intro z hz
  let correction :=
    inverseGammaCompletionLogDeriv z
  have hsplit :
      completedZetaNegLogDeriv z =
        zetaSideNegLogDeriv z + correction := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hside :
        zetaSideNegLogDeriv z =
          completedZetaNegLogDeriv z - correction := by
      exact Eq.subst
        (motive := fun w : ℂ =>
          zetaSideNegLogDeriv z = completedZetaNegLogDeriv z - w)
        hcorrection.symm
        (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
          (E.ne_zero z hz) (E.ne_one z hz)
          (E.zeta_ne_zero z hz) (E.gamma_ne_zero z hz))
    exact (eq_sub_iff_add_eq.mp hside).symm
  have hnorm_split :
      ‖completedZetaNegLogDeriv z‖ ≤
        ‖zetaSideNegLogDeriv z‖ + ‖correction‖ := by
    exact Eq.subst
      (motive := fun w : ℂ =>
        ‖w‖ ≤ ‖zetaSideNegLogDeriv z‖ + ‖correction‖)
      hsplit.symm
      (norm_add_le (zetaSideNegLogDeriv z) correction)
  have hbounds :
      ‖zetaSideNegLogDeriv z‖ + ‖correction‖ ≤
        Czeta * (1 + ‖z.im‖) ^ N +
          Cgamma * (1 + ‖z.im‖) ^ N := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hgamma_bound_correction :
        ‖correction‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N :=
      Eq.subst
        (motive := fun w : ℂ =>
          ‖w‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N)
        hcorrection.symm
        (hCgamma_bound z hz)
    exact add_le_add (hCzeta_bound z hz) hgamma_bound_correction
  have hfactor :
      Czeta * (1 + ‖z.im‖) ^ N + Cgamma * (1 + ‖z.im‖) ^ N =
        (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
    exact (add_mul Czeta Cgamma ((1 + ‖z.im‖) ^ N)).symm
  exact hnorm_split.trans (hbounds.trans_eq hfactor)

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
  /-- Polynomial growth for the completed negative log derivative on a zero-excised strip. -/
  zero_excised_polynomial_strip_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ N
  /-- A concrete polynomial-growth constant for each zero-excised strip and degree. -/
  zero_excised_polynomial_strip_bound_constant :
    ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  /-- The concrete zero-excised strip-bound constant is positive. -/
  zero_excised_polynomial_strip_bound_constant_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      0 < zero_excised_polynomial_strip_bound_constant a b E N
  /-- The concrete zero-excised strip-bound constant bounds the completed negative
  logarithmic derivative on the excised carrier. -/
  zero_excised_polynomial_strip_bound_constant_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
      (z : ℂ),
      z ∈ E.carrier →
      ‖completedZetaNegLogDeriv z‖ ≤
        zero_excised_polynomial_strip_bound_constant a b E N *
          (1 + ‖z.im‖) ^ N

/-- The strip-control package exposes fixed-degree zero-excised polynomial growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact h.zero_excised_polynomial_growth a b E

/-- The strip-control package exposes zero-excised polynomial pointwise growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.zero_excised_polynomial_strip_bound a b E N

/-- The recorded zero-excised strip-bound constant. -/
def CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) : ℝ :=
  h.zero_excised_polynomial_strip_bound_constant a b E N

/-- The recorded zero-excised strip-bound constant is positive. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant_pos
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    0 < h.zeroExcisedStripBoundConstant a b E N :=
  h.zero_excised_polynomial_strip_bound_constant_pos a b E N

/-- The recorded zero-excised strip-bound constant bounds the completed negative
logarithmic derivative on the excised carrier. -/
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
    CompletedZetaNegLogDerivControlPackage f = CompletedZetaNegLogDerivControl f := by
  rfl

/-- A critical-line specialization of the zero-excised polynomial strip bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineBound_of_mem
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (E : CompletedZetaZeroExcisedStrip (1 / 2 : ℝ) (1 / 2 : ℝ)) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ((1 / 2 : ℂ) + t * Complex.I) ∈ E.carrier →
        ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ N := by
  rcases h.zeroExcisedStripBound (1 / 2 : ℝ) (1 / 2 : ℝ) E N with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  have him : ((1 / 2 : ℂ) + t * Complex.I).im = t :=
    im_half_plus_t_i t
  have hbound' :=
    hbound ((1 / 2 : ℂ) + t * Complex.I) ht
  have hRHS :
      C * (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ N =
        C * (1 + ‖t‖) ^ N := by
    exact congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ N) him
  exact hbound'.trans (le_of_eq hRHS)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

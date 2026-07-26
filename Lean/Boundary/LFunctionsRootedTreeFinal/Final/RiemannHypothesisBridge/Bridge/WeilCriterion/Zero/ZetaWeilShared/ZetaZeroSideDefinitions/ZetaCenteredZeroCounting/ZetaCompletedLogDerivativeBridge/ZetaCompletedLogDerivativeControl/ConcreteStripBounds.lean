import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyLogDerivative
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.Core
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner

/-!
# Concrete completed-log-derivative strip bounds

This file peels the completed-log-derivative control package into the two
concrete estimates used in the product decomposition: the zeta-side logarithmic
derivative bound and the inverse-Gamma completion bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Canonical singleton zero-excised carriers are compact. -/
theorem CompletedZetaZeroExcisedStrip.isCompact_singleton
    {a b : ℝ} (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    IsCompact
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma).carrier := by
  exact isCompact_singleton

/-- Compactness is preserved by the finite-union carrier constructor. -/
theorem CompletedZetaZeroExcisedStrip.isCompact_union
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    (hE₁ : IsCompact E₁.carrier)
    (hE₂ : IsCompact E₂.carrier) :
    IsCompact (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier := by
  exact hE₁.union hE₂

/-- A zero-excised strip carrier is uniformly separated from the completed-log-derivative
singular locus by one positive distance.  This is the geometric input supplied
by the separated strip owner: pointwise exclusions alone do not provide uniform
bounds near poles or zeros. -/
def CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
      (∀ z : ℂ, z ∈ E.carrier → δ ≤ ‖z‖) ∧
      (∀ z : ℂ, z ∈ E.carrier → δ ≤ ‖z - 1‖) ∧
      (∀ z : ℂ, z ∈ E.carrier →
        ∀ ρ : {ρ : ℂ // _root_.Boundary.LFunctions.ZetaCompletedZero ρ},
          δ ≤ ‖z - ((1 / 2 : ℂ) + (ρ : ℂ))‖) ∧
      (∀ z : ℂ, z ∈ E.carrier →
        ∀ n : ℕ, δ ≤ ‖z - (-(2 * (n : ℂ)))‖)

/-- The empty carrier is separated from every singular locus. -/
theorem CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.empty
    (a b : ℝ) :
    (CompletedZetaZeroExcisedStrip.empty a b).HasPositiveSingularSeparation :=
  Exists.intro 1
    (And.intro zero_lt_one
      (And.intro
        (fun z hz => False.elim (Set.not_mem_empty z hz))
        (And.intro
          (fun z hz => False.elim (Set.not_mem_empty z hz))
          (And.intro
            (fun z hz rho => False.elim (Set.not_mem_empty z hz))
            (fun z hz n => False.elim (Set.not_mem_empty z hz))))))

/-- Positive singular separation is preserved by finite union of carriers over the same strip. -/
theorem CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.union
    {a b : ℝ} (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    (hE₁ : E₁.HasPositiveSingularSeparation)
    (hE₂ : E₂.HasPositiveSingularSeparation) :
    (CompletedZetaZeroExcisedStrip.union E₁ E₂).HasPositiveSingularSeparation :=
  Exists.elim hE₁
    (fun δ₁ hδ₁ =>
      Exists.elim hE₂
        (fun δ₂ hδ₂ =>
          let δ : ℝ := min δ₁ δ₂
          ⟨δ,
            lt_min hδ₁.1 hδ₂.1,
            And.intro
              (fun z hz =>
                match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
                | Or.inl hz₁ =>
                    le_trans (min_le_left δ₁ δ₂) (hδ₁.2.1 z hz₁)
                | Or.inr hz₂ =>
                    le_trans (min_le_right δ₁ δ₂) (hδ₂.2.1 z hz₂))
              (And.intro
                (fun z hz =>
                  match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
                  | Or.inl hz₁ =>
                      le_trans (min_le_left δ₁ δ₂) (hδ₁.2.2.1 z hz₁)
                  | Or.inr hz₂ =>
                      le_trans (min_le_right δ₁ δ₂) (hδ₂.2.2.1 z hz₂))
                (And.intro
                  (fun z hz ρ =>
                    match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
                    | Or.inl hz₁ =>
                        le_trans (min_le_left δ₁ δ₂) (hδ₁.2.2.2.1 z hz₁ ρ)
                    | Or.inr hz₂ =>
                        le_trans (min_le_right δ₁ δ₂) (hδ₂.2.2.2.1 z hz₂ ρ))
                  (fun z hz n =>
                    match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
                    | Or.inl hz₁ =>
                        le_trans (min_le_left δ₁ δ₂) (hδ₁.2.2.2.2 z hz₁ n)
                    | Or.inr hz₂ =>
                        le_trans (min_le_right δ₁ δ₂) (hδ₂.2.2.2.2 z hz₂ n))))⟩))

/-- Concrete zeta-side strip bounds on one separated zero-excised carrier. -/
structure CompletedZetaZeroExcisedStrip.ZetaSideBoundData
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) where
  /-- The carrier is uniformly separated from the singular locus. -/
  separated : E.HasPositiveSingularSeparation
  /-- Concrete constants for each requested polynomial degree. -/
  constant : ℕ → ℝ
  /-- The constants are positive. -/
  constant_pos : ∀ N : ℕ, 0 < constant N
  /-- The constants bound the zeta-side logarithmic derivative on the carrier. -/
  bound :
    ∀ (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤ constant N * (1 + ‖z.im‖) ^ N

/-- Explicit constants and pointwise estimates build zeta-side bound data. -/
def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofConstants
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (constant : ℕ → ℝ)
    (constant_pos : ∀ N : ℕ, 0 < constant N)
    (bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤ constant N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData E :=
  { separated := separated
    constant := constant
    constant_pos := constant_pos
    bound := bound }

theorem CompletedZetaZeroExcisedStrip.ZetaSideBoundData.union_bound_owner
    {a b : ℝ} {E₁ E₂ : CompletedZetaZeroExcisedStrip a b}
    (data₁ : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E₁)
    (data₂ : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E₂)
    (N : ℕ) (z : ℂ) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier →
    ‖zetaSideNegLogDeriv z‖ ≤
      (data₁.constant N + data₂.constant N) * (1 + ‖z.im‖) ^ N := by
  intro hz
  let q : ℝ := (1 + ‖z.im‖) ^ N
  have qNonneg : 0 ≤ q :=
    pow_nonneg (add_nonneg zero_le_one (norm_nonneg z.im)) N
  match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
  | Or.inl hz₁ =>
      (data₁.bound N z hz₁).trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (le_of_lt (data₂.constant_pos N)))
          qNonneg)
  | Or.inr hz₂ =>
      (data₂.bound N z hz₂).trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (le_of_lt (data₁.constant_pos N)))
          qNonneg)

/-- Empty zeta-side bound data. -/
def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData
      (CompletedZetaZeroExcisedStrip.empty a b) :=
  CompletedZetaZeroExcisedStrip.ZetaSideBoundData.ofConstants
    (CompletedZetaZeroExcisedStrip.empty a b)
    (CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.empty a b)
    (fun N : ℕ => 1)
    (fun N : ℕ => zero_lt_one)
    (fun N z hz => False.elim (Set.not_mem_empty z hz))

/-- Zeta-side concrete bound data are preserved by finite carrier union. -/
def CompletedZetaZeroExcisedStrip.ZetaSideBoundData.union
    {a b : ℝ} {E₁ E₂ : CompletedZetaZeroExcisedStrip a b}
    (data₁ : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E₁)
    (data₂ : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E₂) :
    CompletedZetaZeroExcisedStrip.ZetaSideBoundData
      (CompletedZetaZeroExcisedStrip.union E₁ E₂) :=
  { separated :=
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.union
        E₁ E₂ data₁.separated data₂.separated
    constant :=
      fun N : ℕ => data₁.constant N + data₂.constant N
    constant_pos :=
      fun N : ℕ => add_pos (data₁.constant_pos N) (data₂.constant_pos N)
    bound :=
      fun N z hz =>
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData.union_bound_owner
          data₁ data₂ N z hz }

/-- Concrete inverse-Gamma strip bounds on one separated zero-excised carrier. -/
structure CompletedZetaZeroExcisedStrip.InverseGammaBoundData
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b) where
  /-- The carrier is uniformly separated from the singular locus. -/
  separated : E.HasPositiveSingularSeparation
  /-- Concrete constants for each requested polynomial degree. -/
  constant : ℕ → ℝ
  /-- The constants are positive. -/
  constant_pos : ∀ N : ℕ, 0 < constant N
  /-- The constants bound the inverse-Gamma completion logarithmic derivative. -/
  bound :
    ∀ (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        constant N * (1 + ‖z.im‖) ^ N

/-- Explicit constants and pointwise estimates build inverse-Gamma bound data. -/
def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofConstants
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (constant : ℕ → ℝ)
    (constant_pos : ∀ N : ℕ, 0 < constant N)
    (bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          constant N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData E :=
  { separated := separated
    constant := constant
    constant_pos := constant_pos
    bound := bound }

/-! The canonical owner input for the inverse-Gamma factor is its logarithmic
derivative estimate itself.  In particular, this constructor does not ask for
a magnitude estimate for `(Gammaℝ z)⁻¹`; such an estimate has exponential
vertical growth and is not the analytic input used by the explicit formula.
-/

/-- Direct inverse-Gamma logarithmic-derivative estimates build the concrete
bound package without passing through a Cauchy-circle magnitude estimate. -/
def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofLogDerivBound
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (separated : E.HasPositiveSingularSeparation)
    (constant : ℕ → ℝ)
    (constant_pos : ∀ N : ℕ, 0 < constant N)
    (bound :
      ∀ (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          constant N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData E :=
  CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofConstants
    E separated constant constant_pos bound

/-- Empty inverse-Gamma bound data. -/
def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData
      (CompletedZetaZeroExcisedStrip.empty a b) :=
  CompletedZetaZeroExcisedStrip.InverseGammaBoundData.ofConstants
    (CompletedZetaZeroExcisedStrip.empty a b)
    (CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.empty a b)
    (fun N : ℕ => 1)
    (fun N : ℕ => zero_lt_one)
    (fun N z hz => False.elim (Set.not_mem_empty z hz))

theorem CompletedZetaZeroExcisedStrip.InverseGammaBoundData.union_bound_owner
    {a b : ℝ} {E₁ E₂ : CompletedZetaZeroExcisedStrip a b}
    (data₁ : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E₁)
    (data₂ : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E₂)
    (N : ℕ) (z : ℂ) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier →
    ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤
      (data₁.constant N + data₂.constant N) * (1 + ‖z.im‖) ^ N := by
  intro hz
  let q : ℝ := (1 + ‖z.im‖) ^ N
  have qNonneg : 0 ≤ q :=
    pow_nonneg (add_nonneg zero_le_one (norm_nonneg z.im)) N
  match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
  | Or.inl hz₁ =>
      (data₁.bound N z hz₁).trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (le_of_lt (data₂.constant_pos N)))
          qNonneg)
  | Or.inr hz₂ =>
      (data₂.bound N z hz₂).trans
        (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (le_of_lt (data₁.constant_pos N)))
          qNonneg)

/-- Inverse-Gamma concrete bound data are preserved by finite carrier union. -/
def CompletedZetaZeroExcisedStrip.InverseGammaBoundData.union
    {a b : ℝ} {E₁ E₂ : CompletedZetaZeroExcisedStrip a b}
    (data₁ : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E₁)
    (data₂ : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E₂) :
    CompletedZetaZeroExcisedStrip.InverseGammaBoundData
      (CompletedZetaZeroExcisedStrip.union E₁ E₂) :=
  { separated :=
      CompletedZetaZeroExcisedStrip.HasPositiveSingularSeparation.union
        E₁ E₂ data₁.separated data₂.separated
    constant :=
      fun N : ℕ => data₁.constant N + data₂.constant N
    constant_pos :=
      fun N : ℕ => add_pos (data₁.constant_pos N) (data₂.constant_pos N)
    bound :=
      fun N z hz =>
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData.union_bound_owner
          data₁ data₂ N z hz }

/-- Concrete zeta-side and inverse-Gamma bounds imply the completed negative
logarithmic derivative bound with the sum of the two constants. -/
theorem completedZetaNegLogDeriv_bound_of_concrete_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (Czeta Cgamma : ℝ)
    (hCzeta_bound :
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤ Czeta * (1 + ‖z.im‖) ^ N)
    (hCgamma_bound :
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma * (1 + ‖z.im‖) ^ N)
    (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N :=
  completedZetaNegLogDeriv_norm_bound_of_factor_bounds
    E N Czeta Cgamma z hz hCzeta_bound hCgamma_bound

/-- Separated carrier factor bounds imply a completed-log-derivative bound on that
carrier, with the sum of the two concrete constants. -/
theorem completedZetaNegLogDeriv_bound_of_separated_factorBoundData
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (zetaData : CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData : CompletedZetaZeroExcisedStrip.InverseGammaBoundData E)
    (N : ℕ) (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (zetaData.constant N + gammaData.constant N) *
        (1 + ‖z.im‖) ^ N :=
  completedZetaNegLogDeriv_bound_of_concrete_zetaSide_and_gamma
    (a := a) (b := b) (E := E) (N := N)
    (Czeta := zetaData.constant N) (Cgamma := gammaData.constant N)
    (hCzeta_bound := zetaData.bound N)
    (hCgamma_bound := gammaData.bound N)
    z hz

/-- Concrete zeta-side and inverse-Gamma strip constants construct the full completed
negative log-derivative control package. -/
def CompletedZetaNegLogDerivControl.ofConcreteZetaSideAndGammaBounds
    (f : ZetaAdmissibleFunction)
    (Czeta Cgamma :
      ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCzeta_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Czeta a b E N)
    (hCgamma_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Cgamma a b E N)
    (hCzeta_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
        (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta a b E N * (1 + ‖z.im‖) ^ N)
    (hCgamma_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
        (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivControl f :=
  CompletedZetaNegLogDerivControl.ofSuppliedConstants
    f
    (fun a b E N => Czeta a b E N + Cgamma a b E N)
    (fun a b E N => add_pos (hCzeta_pos a b E N) (hCgamma_pos a b E N))
    (fun a b E N z hz =>
      completedZetaNegLogDeriv_bound_of_concrete_zetaSide_and_gamma
        a b E N (Czeta a b E N) (Cgamma a b E N)
        (hCzeta_bound a b E N)
        (hCgamma_bound a b E N)
        z hz)

/-- Constructive zeta-side factor bounds on zero-excised strips. -/
structure CompletedZetaNegLogDerivZetaSideControl where
  Czeta :
    ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  Czeta_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      0 < Czeta a b E N
  Czeta_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        Czeta a b E N * (1 + ‖z.im‖) ^ N

def CompletedZetaNegLogDerivZetaSideControl.ofConstants
    (Czeta : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Czeta_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Czeta a b E N)
    (Czeta_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivZetaSideControl :=
  { Czeta := Czeta
    Czeta_pos := Czeta_pos
    Czeta_bound := Czeta_bound }

/-- Constructive inverse-Gamma factor bounds on zero-excised strips. -/
structure CompletedZetaNegLogDerivInverseGammaControl where
  Cgamma :
    ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  Cgamma_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      0 < Cgamma a b E N
  Cgamma_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        Cgamma a b E N * (1 + ‖z.im‖) ^ N

def CompletedZetaNegLogDerivInverseGammaControl.ofConstants
    (Cgamma : ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Cgamma_pos :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Cgamma a b E N)
    (Cgamma_bound :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivInverseGammaControl :=
  { Cgamma := Cgamma
    Cgamma_pos := Cgamma_pos
    Cgamma_bound := Cgamma_bound }

/-- Per-strip zeta-side bound data assemble into global zeta-side strip
control. -/
def CompletedZetaNegLogDerivZetaSideControl.ofBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E) :
    CompletedZetaNegLogDerivZetaSideControl :=
  { Czeta :=
      fun a b E N => (data a b E).constant N
    Czeta_pos :=
      fun a b E N => (data a b E).constant_pos N
    Czeta_bound :=
      fun a b E N z hz => (data a b E).bound N z hz }

def CompletedZetaNegLogDerivZetaSideControl.ofBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E) :
    CompletedZetaNegLogDerivZetaSideControl :=
  CompletedZetaNegLogDerivZetaSideControl.ofBoundData data

/-- Per-strip inverse-Gamma bound data assemble into global inverse-Gamma
strip control. -/
def CompletedZetaNegLogDerivInverseGammaControl.ofBoundData
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaNegLogDerivInverseGammaControl :=
  { Cgamma :=
      fun a b E N => (data a b E).constant N
    Cgamma_pos :=
      fun a b E N => (data a b E).constant_pos N
    Cgamma_bound :=
      fun a b E N z hz => (data a b E).bound N z hz }

def CompletedZetaNegLogDerivInverseGammaControl.ofBoundData_owner
    (data :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaNegLogDerivInverseGammaControl :=
  CompletedZetaNegLogDerivInverseGammaControl.ofBoundData data

/-- Constructive zeta-side factor bounds on all autocorrelation probes. -/
structure CompletedZetaNegLogDerivAutocorrelationZetaSideControl where
  Czeta :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
      CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  Czeta_pos :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ),
      0 < Czeta f a b E N
  Czeta_bound :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖zetaSideNegLogDeriv z‖ ≤
        Czeta f a b E N * (1 + ‖z.im‖) ^ N

def CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofConstants
    (Czeta :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Czeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Czeta f a b E N)
    (Czeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta f a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivAutocorrelationZetaSideControl :=
  { Czeta := Czeta
    Czeta_pos := Czeta_pos
    Czeta_bound := Czeta_bound }

/-- Constructive inverse-Gamma factor bounds on all autocorrelation probes. -/
structure CompletedZetaNegLogDerivAutocorrelationInverseGammaControl where
  Cgamma :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
      CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  Cgamma_pos :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ),
      0 < Cgamma f a b E N
  Cgamma_bound :
    ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
      (E : CompletedZetaZeroExcisedStrip a b)
      (N : ℕ) (z : ℂ),
      z ∈ E.carrier →
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤
        Cgamma f a b E N * (1 + ‖z.im‖) ^ N

def CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofConstants
    (Cgamma :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (Cgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Cgamma f a b E N)
    (Cgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivAutocorrelationInverseGammaControl :=
  { Cgamma := Cgamma
    Cgamma_pos := Cgamma_pos
    Cgamma_bound := Cgamma_bound }

/-- Global zeta-side strip control induces the autocorrelation-indexed control
surface by ignoring the seed probe. -/
def CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
    (h : CompletedZetaNegLogDerivZetaSideControl) :
    CompletedZetaNegLogDerivAutocorrelationZetaSideControl :=
  { Czeta :=
      fun seed a b E N => h.Czeta a b E N
    Czeta_pos :=
      fun seed a b E N => h.Czeta_pos a b E N
    Czeta_bound :=
      fun seed a b E N z hz => h.Czeta_bound a b E N z hz }

/-- Global inverse-Gamma strip control induces the autocorrelation-indexed
control surface by ignoring the seed probe. -/
def CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
    (h : CompletedZetaNegLogDerivInverseGammaControl) :
    CompletedZetaNegLogDerivAutocorrelationInverseGammaControl :=
  { Cgamma :=
      fun seed a b E N => h.Cgamma a b E N
    Cgamma_pos :=
      fun seed a b E N => h.Cgamma_pos a b E N
    Cgamma_bound :=
      fun seed a b E N z hz => h.Cgamma_bound a b E N z hz }

/-- Constructive concrete split factor data for completed-log-derivative control
on all autocorrelation probes. -/
structure CompletedZetaNegLogDerivAutocorrelationConcreteControl where
  zetaSide : CompletedZetaNegLogDerivAutocorrelationZetaSideControl
  inverseGamma : CompletedZetaNegLogDerivAutocorrelationInverseGammaControl

/-- Zeta-side and inverse-Gamma controls assemble into the concrete split-factor
surface for completed-log-derivative control. -/
def completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (zetaSide : CompletedZetaNegLogDerivAutocorrelationZetaSideControl)
    (inverseGamma : CompletedZetaNegLogDerivAutocorrelationInverseGammaControl) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  { zetaSide := zetaSide
    inverseGamma := inverseGamma }

/-- Global zeta-side and inverse-Gamma controls assemble into the concrete
autocorrelation log-derivative control surface. -/
def completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
    (zetaSide : CompletedZetaNegLogDerivZetaSideControl)
    (inverseGamma : CompletedZetaNegLogDerivInverseGammaControl) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofZetaSideControl
      zetaSide)
    (CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofInverseGammaControl
      inverseGamma)

/-- Per-strip zeta-side and inverse-Gamma bound data assemble into the concrete
autocorrelation log-derivative control surface. -/
def completedZetaNegLogDerivAutocorrelationConcreteControl_of_boundData
    (zetaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
    (CompletedZetaNegLogDerivZetaSideControl.ofBoundData zetaData)
    (CompletedZetaNegLogDerivInverseGammaControl.ofBoundData gammaData)

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_boundData_owner
    (zetaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_globalFactorControls
    (CompletedZetaNegLogDerivZetaSideControl.ofBoundData_owner zetaData)
    (CompletedZetaNegLogDerivInverseGammaControl.ofBoundData_owner gammaData)

def completedZetaNegLogDerivAutocorrelationConcreteControl_of_concreteConstants
    (Czeta Cgamma :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCzeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Czeta f a b E N)
    (hCgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
        0 < Cgamma f a b E N)
    (hCzeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta f a b E N * (1 + ‖z.im‖) ^ N)
    (hCgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f a b E N * (1 + ‖z.im‖) ^ N) :
    CompletedZetaNegLogDerivAutocorrelationConcreteControl :=
  completedZetaNegLogDerivAutocorrelationConcreteControl_of_factorControls
    (CompletedZetaNegLogDerivAutocorrelationZetaSideControl.ofConstants
      Czeta hCzeta_pos hCzeta_bound)
    (CompletedZetaNegLogDerivAutocorrelationInverseGammaControl.ofConstants
      Cgamma hCgamma_pos hCgamma_bound)

/-- Concrete split factor bounds build completed-log-derivative control
packages on all autocorrelation probes. -/
def completedZetaNegLogDerivControl_autocorrelation_of_concreteConstants
    (Czeta Cgamma :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCzeta_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Czeta f a b E N)
    (hCgamma_pos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < Cgamma f a b E N)
    (hCzeta_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖zetaSideNegLogDeriv z‖ ≤
          Czeta f a b E N * (1 + ‖z.im‖) ^ N)
    (hCgamma_bound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
            (Complex.Gammaℝ z)⁻¹‖ ≤
          Cgamma f a b E N * (1 + ‖z.im‖) ^ N) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  fun f =>
    CompletedZetaNegLogDerivControl.ofConcreteZetaSideAndGammaBounds
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (Czeta f)
      (Cgamma f)
      (hCzeta_pos f)
      (hCgamma_pos f)
      (hCzeta_bound f)
      (hCgamma_bound f)

/-- A named concrete split factor surface builds completed-log-derivative
control packages on all autocorrelation probes. -/
def completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    (hLogConcrete :
      CompletedZetaNegLogDerivAutocorrelationConcreteControl) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_concreteConstants
    (Czeta := hLogConcrete.zetaSide.Czeta)
    (Cgamma := hLogConcrete.inverseGamma.Cgamma)
    (hCzeta_pos := hLogConcrete.zetaSide.Czeta_pos)
    (hCgamma_pos := hLogConcrete.inverseGamma.Cgamma_pos)
    (hCzeta_bound := hLogConcrete.zetaSide.Czeta_bound)
    (hCgamma_bound := hLogConcrete.inverseGamma.Cgamma_bound)

def completedZetaNegLogDerivControl_autocorrelation_of_suppliedConstants_owner
    (C :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ),
        CompletedZetaZeroExcisedStrip a b → ℕ → ℝ)
    (hCpos :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ),
        0 < C f a b E N)
    (hCbound :
      ∀ (f : ZetaAdmissibleFunction) (a b : ℝ)
        (E : CompletedZetaZeroExcisedStrip a b)
        (N : ℕ) (z : ℂ),
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ ≤
          C f a b E N * (1 + ‖z.im‖) ^ N) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  fun f =>
    CompletedZetaNegLogDerivControl.ofSuppliedConstants
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)
      (C f)
      (hCpos f)
      (hCbound f)

def completedZetaNegLogDerivControl_autocorrelation_of_boundData_owner
    (zetaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.ZetaSideBoundData E)
    (gammaData :
      ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
        CompletedZetaZeroExcisedStrip.InverseGammaBoundData E) :
    ∀ f : ZetaAdmissibleFunction,
      CompletedZetaNegLogDerivControl
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) :=
  completedZetaNegLogDerivControl_autocorrelation_of_concreteControl
    (completedZetaNegLogDerivAutocorrelationConcreteControl_of_boundData_owner
      zetaData
      gammaData)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

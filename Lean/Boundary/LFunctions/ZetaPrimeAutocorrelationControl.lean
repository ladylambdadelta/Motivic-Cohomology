import Boundary.LFunctions.ZetaPrimeRapidPower

/-!
# Autocorrelation analytic control for prime tomography

This file owns the analytic-control estimates for autocorrelation probes used by
completed prime horizontal decay.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The reflected dagger spectral face is entire when the seed transform has analytic
control. -/
theorem reflectedDaggerSeedPhi_entire_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) :
    AnalyticOn ℂ
      (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z)))
      Set.univ := by
  have hdagger :
      AnalyticOn ℂ
        (fun z => zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z)
        Set.univ :=
    zetaPhi_entire_of_compactSupport (zetaAdmissibleDagger f)
  have hrewrite :
      (fun z => zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z) =
        (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z))) := by
    funext z
    exact zetaCompletedExplicitFormulaPhi_dagger f z
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => AnalyticOn ℂ Φ Set.univ)
    hrewrite
    hdagger

/-- The factorized autocorrelation transform is entire when the seed transform has analytic
control. -/
theorem convolutionAutocorrelation_zetaPhi_entire_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) :
    AnalyticOn ℂ
      (fun z =>
        zetaCompletedExplicitFormulaPhi f z *
          star (zetaCompletedExplicitFormulaPhi f (-star z)))
      Set.univ := by
  have hleft :
      AnalyticOn ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) Set.univ :=
    hseed.entire
  have hright :
      AnalyticOn ℂ
        (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z)))
        Set.univ :=
    reflectedDaggerSeedPhi_entire_of_seedControl f hseed
  exact hleft.mul hright

/-- The autocorrelation transform is entire by factorization through the seed transform and
its dagger-reflected face. -/
theorem convolutionAutocorrelation_zetaPhi_entire
    (f : ZetaAdmissibleFunction) :
    AnalyticOn ℂ
      (fun z => zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z)
      Set.univ := by
  have hseed : ZetaPhiAnalyticControl f :=
    zetaPhiAnalyticControl_of_admissible f
  have hfactorized :
      AnalyticOn ℂ
        (fun z =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z)))
        Set.univ :=
    convolutionAutocorrelation_zetaPhi_entire_of_seedControl f hseed
  have hrewrite :
      (fun z => zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z) =
        (fun z =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z))) := by
    funext z
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f z
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => AnalyticOn ℂ Φ Set.univ)
    hrewrite.symm
    hfactorized

/-- The reflected dagger spectral face is differentiable when the seed transform has analytic
control. -/
theorem reflectedDaggerSeedPhi_differentiableAt_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ
      (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z)))
      z := by
  have hdagger :
      DifferentiableAt ℂ
        (fun z => zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z)
        z :=
    zetaPhi_differentiableAt_of_compactSupport (zetaAdmissibleDagger f) z
  have hrewrite :
      (fun z => zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z) =
        (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z))) := by
    funext w
    exact zetaCompletedExplicitFormulaPhi_dagger f w
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => DifferentiableAt ℂ Φ z)
    hrewrite
    hdagger

/-- The autocorrelation probe transform is differentiable at every spectral point. -/
theorem convolutionAutocorrelation_zetaPhi_differentiableAt_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) (z : ℂ) :
    DifferentiableAt ℂ
      (fun z =>
        zetaCompletedExplicitFormulaPhi f z *
          star (zetaCompletedExplicitFormulaPhi f (-star z)))
      z := by
  have hleft :
      DifferentiableAt ℂ (fun z => zetaCompletedExplicitFormulaPhi f z) z :=
    hseed.differentiableAt z
  have hright :
      DifferentiableAt ℂ
        (fun z => star (zetaCompletedExplicitFormulaPhi f (-star z)))
        z :=
    reflectedDaggerSeedPhi_differentiableAt_of_seedControl f hseed z
  exact hleft.mul hright

/-- The autocorrelation probe transform is differentiable at every spectral point. -/
theorem convolutionAutocorrelation_zetaPhi_differentiableAt
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    DifferentiableAt ℂ
      (fun z => zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z)
      z := by
  have hseed : ZetaPhiAnalyticControl f :=
    zetaPhiAnalyticControl_of_admissible f
  have hfactorized :
      DifferentiableAt ℂ
        (fun z =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z)))
        z :=
    convolutionAutocorrelation_zetaPhi_differentiableAt_of_seedControl f hseed z
  have hrewrite :
      (fun z => zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z) =
        (fun z =>
          zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z))) := by
    funext w
    exact zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f w
  exact Eq.subst
    (motive := fun Φ : ℂ → ℂ => DifferentiableAt ℂ Φ z)
    hrewrite.symm
    hfactorized

/-- The reflected dagger spectral face has rapid vertical-strip decay when the seed transform
has analytic control. -/
theorem reflectedDaggerSeedPhi_verticalStripRapidDecay_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖star (zetaCompletedExplicitFormulaPhi f (-star z))‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases zetaPhi_verticalStripRapidDecay_of_admissible
    (zetaAdmissibleDagger f) a b N
    with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hleft hright
  have hdagger :
      zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z =
        star (zetaCompletedExplicitFormulaPhi f (-star z)) :=
    zetaCompletedExplicitFormulaPhi_dagger f z
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
    hdagger
    (hCbound z hleft hright)

/-- Pointwise product estimate for two rapidly decaying faces. -/
theorem rapidTimesRapidPointwise_le
    (N : ℕ) (C₁ C₂ X A B : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hX : 1 ≤ X)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hA : A ≤ C₁ * X ^ (-(N + 1 : ℤ)))
    (hB : B ≤ C₂ * X ^ (-(N + 1 : ℤ))) :
    A * B ≤ (C₁ * C₂) * X ^ (-(N : ℤ)) := by
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hX_zpow_nonneg :
      0 ≤ X ^ (-(N + 1 : ℤ)) := by
    exact le_of_lt (zpow_pos hX_pos (-(N + 1 : ℤ)))
  have hrightA_nonneg : 0 ≤ C₁ * X ^ (-(N + 1 : ℤ)) := by
    exact mul_nonneg (le_of_lt hC₁) hX_zpow_nonneg
  have hmul :
      A * B ≤
        (C₁ * X ^ (-(N + 1 : ℤ))) *
          (C₂ * X ^ (-(N + 1 : ℤ))) := by
    exact mul_le_mul hA hB hB_nonneg hrightA_nonneg
  have hrearrange :
      (C₁ * X ^ (-(N + 1 : ℤ))) *
          (C₂ * X ^ (-(N + 1 : ℤ))) =
        (C₁ * C₂) *
          (X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ))) := by
    calc
      (C₁ * X ^ (-(N + 1 : ℤ))) *
          (C₂ * X ^ (-(N + 1 : ℤ))) =
          C₁ * (X ^ (-(N + 1 : ℤ)) *
            (C₂ * X ^ (-(N + 1 : ℤ)))) := by
        exact mul_assoc C₁ (X ^ (-(N + 1 : ℤ)))
          (C₂ * X ^ (-(N + 1 : ℤ)))
      _ = C₁ * (C₂ *
            (X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)))) := by
        exact congrArg (fun y : ℝ => C₁ * y)
          (by
            calc
              X ^ (-(N + 1 : ℤ)) *
                  (C₂ * X ^ (-(N + 1 : ℤ))) =
                  (X ^ (-(N + 1 : ℤ)) * C₂) *
                    X ^ (-(N + 1 : ℤ)) := by
                exact (mul_assoc (X ^ (-(N + 1 : ℤ))) C₂
                  (X ^ (-(N + 1 : ℤ)))).symm
              _ = (C₂ * X ^ (-(N + 1 : ℤ))) *
                    X ^ (-(N + 1 : ℤ)) := by
                exact congrArg
                  (fun y : ℝ => y * X ^ (-(N + 1 : ℤ)))
                  (mul_comm (X ^ (-(N + 1 : ℤ))) C₂)
              _ = C₂ *
                    (X ^ (-(N + 1 : ℤ)) *
                      X ^ (-(N + 1 : ℤ))) := by
                exact mul_assoc C₂
                  (X ^ (-(N + 1 : ℤ)))
                  (X ^ (-(N + 1 : ℤ))))
      _ = (C₁ * C₂) *
            (X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ))) := by
        exact (mul_assoc C₁ C₂
          (X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)))).symm
  have hpower :
      X ^ (-(N + 1 : ℤ)) * X ^ (-(N + 1 : ℤ)) ≤
        X ^ (-(N : ℤ)) :=
    rapidTimesRapidPower_le_requestedRapidPower N X hX
  have hconstant_nonneg : 0 ≤ C₁ * C₂ := by
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt hC₂)
  have hafter_rearrange :
      (C₁ * X ^ (-(N + 1 : ℤ))) *
          (C₂ * X ^ (-(N + 1 : ℤ))) ≤
        (C₁ * C₂) * X ^ (-(N : ℤ)) := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (C₁ * C₂) * X ^ (-(N : ℤ)))
      hrearrange.symm
      (mul_le_mul_of_nonneg_left hpower hconstant_nonneg)
  exact hmul.trans hafter_rearrange

/-- Generic strip product estimate for two rapidly decaying faces. -/
theorem stripProductDecay_of_two_rapidDecay
    (Φ Ψ : ℂ → ℂ) (a b : ℝ) (N : ℕ)
    (hΦ :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Φ z‖ ≤ C * (1 + ‖z.im‖) ^ (-(N + 1 : ℤ)))
    (hΨ :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Ψ z‖ ≤ C * (1 + ‖z.im‖) ^ (-(N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖Φ z * Ψ z‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases hΦ with ⟨CΦ, hCΦpos, hCΦbound⟩
  rcases hΨ with ⟨CΨ, hCΨpos, hCΨbound⟩
  refine ⟨CΦ * CΨ, mul_pos hCΦpos hCΨpos, ?_⟩
  intro z hleft hright
  have hX : 1 ≤ 1 + ‖z.im‖ := by
    exact le_add_of_nonneg_right (norm_nonneg z.im)
  have hproduct_norm :
      ‖Φ z * Ψ z‖ ≤ ‖Φ z‖ * ‖Ψ z‖ :=
    norm_mul_le _ _
  have hpoint :
      ‖Φ z‖ * ‖Ψ z‖ ≤
        (CΦ * CΨ) * (1 + ‖z.im‖) ^ (-(N : ℤ)) :=
    rapidTimesRapidPointwise_le
      N CΦ CΨ (1 + ‖z.im‖) ‖Φ z‖ ‖Ψ z‖
      hCΦpos hCΨpos hX
      (norm_nonneg (Φ z)) (norm_nonneg (Ψ z))
      (hCΦbound z hleft hright)
      (hCΨbound z hleft hright)
  exact hproduct_norm.trans hpoint

/-- The autocorrelation probe transform has rapid decay in every vertical strip. -/
theorem convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay_of_seedControl
    (f : ZetaAdmissibleFunction)
    (hseed : ZetaPhiAnalyticControl f) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi f z *
            star (zetaCompletedExplicitFormulaPhi f (-star z))‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact
    stripProductDecay_of_two_rapidDecay
      (fun z : ℂ => zetaCompletedExplicitFormulaPhi f z)
      (fun z : ℂ => star (zetaCompletedExplicitFormulaPhi f (-star z)))
      a b N
      (hseed.vertical_strip_rapid_decay a b (N + 1))
      (reflectedDaggerSeedPhi_verticalStripRapidDecay_of_seedControl
        f hseed a b (N + 1))

/-- The autocorrelation probe transform has rapid decay in every vertical strip. -/
theorem convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  have hseed : ZetaPhiAnalyticControl f :=
    zetaPhiAnalyticControl_of_admissible f
  rcases convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay_of_seedControl
      f hseed a b N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hleft hright
  have hfactor :
      zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z =
        zetaCompletedExplicitFormulaPhi f z *
          star (zetaCompletedExplicitFormulaPhi f (-star z)) :=
    zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation f z
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)))
    hfactor.symm
    (hCbound z hleft hright)

/-- The autocorrelation probe has the Paley--Wiener transform control required for the
completed prime contour-transport family. -/
theorem convolutionAutocorrelation_zetaPhiAnalyticControl
    (f : ZetaAdmissibleFunction) :
    ZetaPhiAnalyticControl (convolutionAutocorrelation f) := by
  exact
    { entire_phi := convolutionAutocorrelation_zetaPhi_entire f
      differentiableAt_phi :=
        fun z => convolutionAutocorrelation_zetaPhi_differentiableAt f z
      vertical_strip_rapid_decay :=
        fun a b N =>
          convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay f a b N }

/-- Constant and power bookkeeping for the strip product estimate. -/
theorem stripProductPointwise_le
    (N : ℕ) (C₁ C₂ X A B : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hX : 1 ≤ X)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hA : A ≤ C₁ * X ^ N)
    (hB : B ≤ C₂ * X ^ (-(N + N + 1 : ℤ))) :
    A * B ≤ (C₁ * C₂) * X ^ (-(N : ℤ)) := by
  have hX_pos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hX_pow_nonneg : 0 ≤ X ^ N := by
    exact pow_nonneg (le_of_lt hX_pos) N
  have hX_zpow_nonneg :
      0 ≤ X ^ (-(N + N + 1 : ℤ)) := by
    exact le_of_lt (zpow_pos hX_pos (-(N + N + 1 : ℤ)))
  have hrightA_nonneg : 0 ≤ C₁ * X ^ N := by
    exact mul_nonneg (le_of_lt hC₁) hX_pow_nonneg
  have hmul :
      A * B ≤ (C₁ * X ^ N) *
          (C₂ * X ^ (-(N + N + 1 : ℤ))) := by
    exact mul_le_mul hA hB hB_nonneg hrightA_nonneg
  have hrearrange :
      (C₁ * X ^ N) * (C₂ * X ^ (-(N + N + 1 : ℤ))) =
        (C₁ * C₂) * (X ^ N * X ^ (-(N + N + 1 : ℤ))) := by
    calc
      (C₁ * X ^ N) * (C₂ * X ^ (-(N + N + 1 : ℤ))) =
          C₁ * (X ^ N * (C₂ * X ^ (-(N + N + 1 : ℤ)))) := by
        exact mul_assoc C₁ (X ^ N) (C₂ * X ^ (-(N + N + 1 : ℤ)))
      _ = C₁ * (C₂ * (X ^ N * X ^ (-(N + N + 1 : ℤ)))) := by
        exact congrArg (fun y : ℝ => C₁ * y)
          (by
            calc
              X ^ N * (C₂ * X ^ (-(N + N + 1 : ℤ))) =
                  (X ^ N * C₂) * X ^ (-(N + N + 1 : ℤ)) := by
                exact (mul_assoc (X ^ N) C₂ (X ^ (-(N + N + 1 : ℤ)))).symm
              _ = (C₂ * X ^ N) * X ^ (-(N + N + 1 : ℤ)) := by
                exact congrArg (fun y : ℝ => y * X ^ (-(N + N + 1 : ℤ)))
                  (mul_comm (X ^ N) C₂)
              _ = C₂ * (X ^ N * X ^ (-(N + N + 1 : ℤ))) := by
                exact mul_assoc C₂ (X ^ N) (X ^ (-(N + N + 1 : ℤ))))
      _ = (C₁ * C₂) * (X ^ N * X ^ (-(N + N + 1 : ℤ))) := by
        exact (mul_assoc C₁ C₂ (X ^ N * X ^ (-(N + N + 1 : ℤ)))).symm
  have hpower :
      X ^ N * X ^ (-(N + N + 1 : ℤ)) ≤ X ^ (-(N : ℤ)) :=
    polynomialTimesRapidPower_le_requestedRapidPower N X hX
  have hconstant_nonneg : 0 ≤ C₁ * C₂ := by
    exact mul_nonneg (le_of_lt hC₁) (le_of_lt hC₂)
  have hafter_rearrange :
      (C₁ * X ^ N) * (C₂ * X ^ (-(N + N + 1 : ℤ))) ≤
        (C₁ * C₂) * X ^ (-(N : ℤ)) := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (C₁ * C₂) * X ^ (-(N : ℤ)))
      hrearrange.symm
      (mul_le_mul_of_nonneg_left hpower hconstant_nonneg)
  exact hmul.trans hafter_rearrange

/-- Generic strip product estimate: polynomial growth times sufficiently rapid decay is
rapid decay of the requested order. -/
theorem stripProductDecay_of_polynomialGrowth_and_rapidDecay
    (Φ : ℂ → ℂ) (a b : ℝ) (N : ℕ)
    (hlog :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hphi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Φ z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N + N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖ * ‖Φ z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases hlog with ⟨Clog, hClogPos, hClogBound⟩
  rcases hphi with ⟨Cphi, hCphiPos, hCphiBound⟩
  refine ⟨Clog * Cphi, mul_pos hClogPos hCphiPos, ?_⟩
  intro z hleft hright
  have hX : 1 ≤ 1 + ‖z.im‖ := by
    exact le_add_of_nonneg_right (norm_nonneg z.im)
  exact stripProductPointwise_le
    N Clog Cphi (1 + ‖z.im‖)
    ‖completedZetaNegLogDeriv z‖
    ‖Φ z‖
    hClogPos hCphiPos hX
    (norm_nonneg (completedZetaNegLogDeriv z))
    (norm_nonneg (Φ z))
	    (hClogBound z hleft hright)
	    (hCphiBound z hleft hright)

/-- Generic zero-excised strip product estimate: polynomial log-derivative growth on the
zero-excised region times sufficiently rapid decay is rapid product decay on that region. -/
theorem stripProductDecay_of_zeroExcisedPolynomialGrowth_and_rapidDecay
    (Φ : ℂ → ℂ) (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hlog :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hphi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Φ z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N + N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ * ‖Φ z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases hlog with ⟨Clog, hClogPos, hClogBound⟩
  rcases hphi with ⟨Cphi, hCphiPos, hCphiBound⟩
  refine ⟨Clog * Cphi, mul_pos hClogPos hCphiPos, ?_⟩
  intro z hz
  have hstrip : a ≤ z.re ∧ z.re ≤ b := E.in_strip z hz
  have hX : 1 ≤ 1 + ‖z.im‖ := by
    exact le_add_of_nonneg_right (norm_nonneg z.im)
  exact stripProductPointwise_le
    N Clog Cphi (1 + ‖z.im‖)
    ‖completedZetaNegLogDeriv z‖
    ‖Φ z‖
    hClogPos hCphiPos hX
    (norm_nonneg (completedZetaNegLogDeriv z))
    (norm_nonneg (Φ z))
    (hClogBound z hz)
    (hCphiBound z hstrip.1 hstrip.2)

/-- Constant and power bookkeeping for a product where the polynomial growth degree `K`
is independent of the requested rapid-decay order `N`. -/
theorem stripProductPointwise_le_of_polynomialDegree
    (K N : ℕ) (C₁ C₂ X A B : ℝ)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hX : 1 ≤ X)
    (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B)
    (hA : A ≤ C₁ * X ^ K)
    (hB : B ≤ C₂ * X ^ (-(K + N + 1 : ℤ))) :
    A * B ≤ (C₁ * C₂) * X ^ (-(N : ℤ)) := by
  have hX_pos : 0 < X :=
    lt_of_lt_of_le zero_lt_one hX
  have hX_pow_nonneg : 0 ≤ X ^ K :=
    pow_nonneg (le_of_lt hX_pos) K
  have hrightA_nonneg : 0 ≤ C₁ * X ^ K :=
    mul_nonneg (le_of_lt hC₁) hX_pow_nonneg
  have hproduct_le :
      A * B ≤ (C₁ * X ^ K) *
        (C₂ * X ^ (-(K + N + 1 : ℤ))) :=
    mul_le_mul hA hB hB_nonneg hrightA_nonneg
  have hrearrange :
      (C₁ * X ^ K) * (C₂ * X ^ (-(K + N + 1 : ℤ))) =
        (C₁ * C₂) * (X ^ K * X ^ (-(K + N + 1 : ℤ))) := by
    calc
      (C₁ * X ^ K) * (C₂ * X ^ (-(K + N + 1 : ℤ))) =
          C₁ * (X ^ K * (C₂ * X ^ (-(K + N + 1 : ℤ)))) := by
        exact mul_assoc C₁ (X ^ K) (C₂ * X ^ (-(K + N + 1 : ℤ)))
      _ = C₁ * (C₂ * (X ^ K * X ^ (-(K + N + 1 : ℤ)))) := by
        exact congrArg (fun y : ℝ => C₁ * y)
          (by
            calc
              X ^ K * (C₂ * X ^ (-(K + N + 1 : ℤ))) =
                  (X ^ K * C₂) * X ^ (-(K + N + 1 : ℤ)) := by
                exact
                  (mul_assoc (X ^ K) C₂
                    (X ^ (-(K + N + 1 : ℤ)))).symm
              _ = (C₂ * X ^ K) * X ^ (-(K + N + 1 : ℤ)) := by
                exact congrArg
                  (fun y : ℝ => y * X ^ (-(K + N + 1 : ℤ)))
                  (mul_comm (X ^ K) C₂)
              _ = C₂ * (X ^ K * X ^ (-(K + N + 1 : ℤ))) := by
                exact
                  mul_assoc C₂ (X ^ K)
                    (X ^ (-(K + N + 1 : ℤ))))
      _ = (C₁ * C₂) * (X ^ K * X ^ (-(K + N + 1 : ℤ))) := by
        exact
          (mul_assoc C₁ C₂
            (X ^ K * X ^ (-(K + N + 1 : ℤ)))).symm
  have hpower :
      X ^ K * X ^ (-(K + N + 1 : ℤ)) ≤ X ^ (-(N : ℤ)) :=
    polynomialDegreeTimesRapidPower_le_requestedRapidPower K N X hX
  have hconstant_nonneg : 0 ≤ C₁ * C₂ :=
    mul_nonneg (le_of_lt hC₁) (le_of_lt hC₂)
  have hafter_rearrange :
      (C₁ * X ^ K) * (C₂ * X ^ (-(K + N + 1 : ℤ))) ≤
        (C₁ * C₂) * X ^ (-(N : ℤ)) := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (C₁ * C₂) * X ^ (-(N : ℤ)))
      hrearrange.symm
      (mul_le_mul_of_nonneg_left hpower hconstant_nonneg)
  exact hproduct_le.trans hafter_rearrange

/-- Generic zero-excised strip product estimate with an independent polynomial growth
degree. This is the stable API for multiplying a fixed polynomial-growth log derivative by
an arbitrarily rapidly decaying probe transform. -/
theorem stripProductDecay_of_zeroExcisedPolynomialGrowthDegree_and_rapidDecay
    (Φ : ℂ → ℂ) (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (K N : ℕ)
    (hlog :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K)
    (hphi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖Φ z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(K + N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ * ‖Φ z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases hlog with ⟨Clog, hClogPos, hClogBound⟩
  rcases hphi with ⟨Cphi, hCphiPos, hCphiBound⟩
  refine ⟨Clog * Cphi, mul_pos hClogPos hCphiPos, ?_⟩
  intro z hz
  have hstrip : a ≤ z.re ∧ z.re ≤ b := E.in_strip z hz
  have hX : 1 ≤ 1 + ‖z.im‖ := by
    exact le_add_of_nonneg_right (norm_nonneg z.im)
  exact stripProductPointwise_le_of_polynomialDegree
    K N Clog Cphi (1 + ‖z.im‖)
    ‖completedZetaNegLogDeriv z‖
    ‖Φ z‖
    hClogPos hCphiPos hX
    (norm_nonneg (completedZetaNegLogDeriv z))
    (norm_nonneg (Φ z))
    (hClogBound z hz)
    (hCphiBound z hstrip.1 hstrip.2)

/-- Polynomial completed-zeta log-derivative growth, paired with rapid transform decay, gives
the product decay actually used by the horizontal contour estimate. -/
theorem completedZetaNegLogDeriv_times_autocorrelationPhi_rapidStripDecay_of_growth_and_phiDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ)
    (hlog :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hphi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N + N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact
	    stripProductDecay_of_polynomialGrowth_and_rapidDecay
	      (fun z : ℂ =>
	        zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z)
	      a b N hlog hphi

/-- Zero-excised completed-zeta log-derivative growth, paired with rapid transform decay, gives
the product decay actually used by a zero-avoiding horizontal contour estimate. -/
theorem completedZetaNegLogDeriv_times_autocorrelationPhi_zeroExcisedRapidStripDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth a b E with
    ⟨K, Clog, hClogPos, hClogBound⟩
  exact
    stripProductDecay_of_zeroExcisedPolynomialGrowthDegree_and_rapidDecay
      (fun z : ℂ =>
        zetaCompletedExplicitFormulaPhi (convolutionAutocorrelation f) z)
      a b E K N
      ⟨Clog, hClogPos, hClogBound⟩
      (convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay f a b (K + N + 1))

/-- Subtracting the central half shifts the real coordinate by `1 / 2`. -/
theorem complex_sub_half_re (z : ℂ) :
    (z - (1 / 2 : ℂ)).re = z.re - (1 / 2 : ℝ) := by
  calc
    (z - (1 / 2 : ℂ)).re = z.re - (1 / 2 : ℂ).re := by
      exact Complex.sub_re z (1 / 2 : ℂ)
    _ = z.re - (1 / 2 : ℝ) := by
      exact congrArg (fun x : ℝ => z.re - x) complex_half_re

/-- Subtracting the central half does not change the imaginary coordinate. -/
theorem complex_sub_half_im (z : ℂ) :
    (z - (1 / 2 : ℂ)).im = z.im := by
  have hhalf_im : (1 / 2 : ℂ).im = 0 := by
    exact Eq.trans
      (congrArg Complex.im complex_half_eq_ofReal_half)
      (Complex.ofReal_im (1 / 2 : ℝ))
  calc
    (z - (1 / 2 : ℂ)).im = z.im - (1 / 2 : ℂ).im := by
      exact Complex.sub_im z (1 / 2 : ℂ)
    _ = z.im - 0 := by
      exact congrArg (fun x : ℝ => z.im - x) hhalf_im
    _ = z.im := by
      exact sub_zero z.im

/-- Subtracting the central half does not change the imaginary norm. -/
theorem complex_sub_half_im_norm (z : ℂ) :
    ‖(z - (1 / 2 : ℂ)).im‖ = ‖z.im‖ := by
  exact congrArg norm (complex_sub_half_im z)

/-- Vertical-strip decay for the autocorrelation transform after the contour half-shift. -/
theorem shiftedAutocorrelationPhi_verticalStripRapidDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases convolutionAutocorrelation_zetaPhi_verticalStripRapidDecay
      f (a - 1 / 2) (b - 1 / 2) N with ⟨C, hCpos, hCbound⟩
  refine ⟨C, hCpos, ?_⟩
  intro z hleft hright
  have hshift_left :
      a - 1 / 2 ≤ (z - (1 / 2 : ℂ)).re := by
    exact Eq.subst
      (motive := fun x : ℝ => a - 1 / 2 ≤ x)
      (complex_sub_half_re z).symm
      (sub_le_sub_right hleft (1 / 2 : ℝ))
  have hshift_right :
      (z - (1 / 2 : ℂ)).re ≤ b - 1 / 2 := by
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ b - 1 / 2)
      (complex_sub_half_re z).symm
      (sub_le_sub_right hright (1 / 2 : ℝ))
  have hdecay :
      ‖zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + ‖(z - (1 / 2 : ℂ)).im‖) ^ (-(N : ℤ)) :=
    hCbound (z - 1 / 2) hshift_left hshift_right
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (z - 1 / 2)‖
        ≤ C * (1 + x) ^ (-(N : ℤ)))
    (complex_sub_half_im_norm z)
    hdecay

/-- Polynomial completed-zeta log-derivative growth, paired with shifted rapid transform
decay, gives the product decay actually used by the horizontal contour estimate. -/
theorem completedZetaNegLogDeriv_times_shiftedAutocorrelationPhi_rapidStripDecay_of_growth_and_phiDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (N : ℕ)
    (hlog :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hphi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
            ≤ C * (1 + ‖z.im‖) ^ (-(N + N + 1 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  exact
    stripProductDecay_of_polynomialGrowth_and_rapidDecay
      (fun z : ℂ =>
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (z - 1 / 2))
      a b N hlog hphi

/-- Product-form horizontal decay for the shifted contour integrand.  The completed contour
integrand contains `Φ(g)(z - 1/2)`, not `Φ(g)(z)`, so the horizontal-control API must own
this shifted estimate explicitly. -/
theorem completedZetaNegLogDeriv_times_shiftedAutocorrelationPhi_zeroExcisedRapidStripDecay
    (f : ZetaAdmissibleFunction) (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖ *
            ‖zetaCompletedExplicitFormulaPhi
              (convolutionAutocorrelation f) (z - 1 / 2)‖
          ≤ C * (1 + ‖z.im‖) ^ (-(N : ℤ)) := by
  rcases completedZetaNegLogDeriv_zeroExcisedPolynomialGrowth a b E with
    ⟨K, Clog, hClogPos, hClogBound⟩
  exact
    stripProductDecay_of_zeroExcisedPolynomialGrowthDegree_and_rapidDecay
      (fun z : ℂ =>
        zetaCompletedExplicitFormulaPhi
          (convolutionAutocorrelation f) (z - 1 / 2))
      a b E K N
      ⟨Clog, hClogPos, hClogBound⟩
      (shiftedAutocorrelationPhi_verticalStripRapidDecay f a b (K + N + 1))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

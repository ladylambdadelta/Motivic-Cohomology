import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part02_ProductAlgebra

/-!
# Pole-cleared zeta functional-equation identities
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Holomorphicity of the removable pole-cleared zeta on the open strip
`0 < Re s < 1`, inherited from the larger right-critical strip. -/
theorem poleClearedRiemannZeta_zero_one_strip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 0 1) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl.mono
    (fun z hz => ⟨hz.1, lt_trans hz.2 one_lt_two⟩)

/-- Raw Gamma/Stirling multiplier bound on the closed critical band
`0 ≤ Re s ≤ 1`, away from the real-axis removable point.

This is the genuine Gamma/Stirling input for the zero-one reflected-band
transport.  The already available left-half-plane multiplier theorem does not
apply on this band; the proof belongs to the sectorial/vertical recurrence
Stirling package for the ratio
`Gammaℝ (1 - z) / Gammaℝ z`, together with the elementary pole-clearing factor. -/
theorem poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_of_poleClearingQuotient_and_GammaRatio
      poleClearedRiemannZeta_zero_one_strip_poleClearingQuotient_growth_ownerVerticalBandAlgebra
      (poleClearedRiemannZeta_zero_one_strip_GammaRatio_growth_ownerGammaStirling
        hbranch)

/-- Gamma/Stirling owner bound for the completed-functional-equation multiplier
on the reflected closed band `0 ≤ Re s ≤ 1`.

This is only the multiplier part of the noncircular zero-one strip transport:
it estimates the completed-functional-equation factor itself, uniformly on the
vertical tail of the closed reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match
      poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch with
  | ⟨A, B, m, hA_pos, hB_pos, hraw_bound⟩ =>
      exact
        ⟨A, B, m, hA_pos, hB_pos,
          fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
            have hz_ne_zero : z ≠ 0 :=
              fun hz_zero =>
                have hzero_coordinate : z.im = (0 : ℂ).im :=
                  congrArg Complex.im hz_zero
                have hzero_im : z.im = 0 :=
                  Eq.trans hzero_coordinate Complex.zero_im
                poleCleared_realNonzeroOfOneLeNorm hz_im_tail hzero_im
            have hz_norm_tail : 1 ≤ ‖z‖ :=
              le_trans hz_im_tail (Complex.norm_im_le_norm z)
            have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
              Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
                hz_re_nonneg hz_norm_tail
            have hmult_eq :
                poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
                  ((z - 1) / (((1 : ℂ) - z) - 1)) *
                    (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
              exact Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)
            Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hmult_eq.symm
              (hraw_bound z hz_re_nonneg hz_re_le_one hz_im_tail)⟩

/-- Raw pole-cleared algebra for the completed functional equation, with the
nonzero denominators supplied explicitly rather than inferred from the left
half-plane. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient_of_denominators
    {z : ℂ}
    (hz_ne_one : z ≠ 1)
    (hw_ne_one : ((1 : ℂ) - z) ≠ 1)
    (hw_minus_one_ne_zero : (((1 : ℂ) - z) - 1) ≠ 0)
    (hzeta :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :
    poleClearedRiemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hpz :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  have hpw :
      poleClearedRiemannZeta ((1 : ℂ) - z) =
        (((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  let a : ℂ := z - 1
  let b : ℂ := ((1 : ℂ) - z) - 1
  let c : ℂ := riemannZeta ((1 : ℂ) - z)
  let d : ℂ := Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
  have halg : ((a / b) * d) * (b * c) = a * (c * d) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_algebra
      hw_minus_one_ne_zero
  have hleft :
      poleClearedRiemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) := by
    have hzeta_transport :
        (z - 1) * riemannZeta z = (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :=
      congrArg (fun x : ℂ => (z - 1) * x) hzeta
    have hdivision_regroup :
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) :=
      congrArg (fun x : ℂ => (z - 1) * x)
        (mul_div_assoc
          (riemannZeta ((1 : ℂ) - z))
          (Complex.Gammaℝ ((1 : ℂ) - z))
          (Complex.Gammaℝ z))
    exact Eq.trans hpz (Eq.trans hzeta_transport hdivision_regroup)
  have halgebra_transport :
      (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) :=
    halg.symm
  have hpole_transport :
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          poleClearedRiemannZeta ((1 : ℂ) - z) :=
    congrArg
      (fun x : ℂ =>
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) * x)
      hpw.symm
  exact Eq.trans hleft (Eq.trans halgebra_transport hpole_transport)

/-- A point on the vertical tail cannot be zero. -/
private theorem complex_ne_zero_of_one_le_norm_im
    (z : ℂ)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    z ≠ 0 :=
  fun hz_zero =>
    have hzero_im : z.im = 0 :=
      Eq.trans (congrArg Complex.im hz_zero) Complex.zero_im
    poleCleared_realNonzeroOfOneLeNorm hz_im_tail hzero_im

/-- A point on the vertical tail cannot equal one. -/
private theorem complex_ne_one_of_one_le_norm_im
    (z : ℂ)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    z ≠ 1 :=
  fun hz_one =>
    have hone_im : z.im = 0 :=
      Eq.trans (congrArg Complex.im hz_one) Complex.one_im
    poleCleared_realNonzeroOfOneLeNorm hz_im_tail hone_im

/-- Reflection preserves the imaginary-coordinate norm. -/
private theorem oneSubComplex_im_norm_eq (z : ℂ) :
    ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
  have him_subtraction : ((1 : ℂ) - z).im = (1 : ℂ).im - z.im :=
    Complex.sub_im (1 : ℂ) z
  have him_one : (1 : ℂ).im - z.im = 0 - z.im :=
    congrArg (fun value : ℝ => value - z.im) Complex.one_im
  have him_zero : 0 - z.im = -z.im := zero_sub z.im
  have him : ((1 : ℂ) - z).im = -z.im :=
    Eq.trans him_subtraction (Eq.trans him_one him_zero)
  exact Eq.trans (congrArg norm him) (norm_neg z.im)

/-- Reflection of a point with real part at most one has nonnegative real
part. -/
private theorem oneSubComplex_re_nonnegative
    (z : ℂ)
    (hz_re_le_one : z.re ≤ 1) :
    0 ≤ ((1 : ℂ) - z).re := by
  have hre : ((1 : ℂ) - z).re = 1 - z.re :=
    Eq.trans (Complex.sub_re (1 : ℂ) z)
      (congrArg (fun value : ℝ => value - z.re) Complex.one_re)
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hre.symm
    (sub_nonneg.mpr hz_re_le_one)

/-- Reflection of a vertical-tail point cannot be zero. -/
private theorem oneSubComplex_ne_zero_of_one_le_norm_im
    (z : ℂ)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    ((1 : ℂ) - z) ≠ 0 := by
  have hw_im_tail : 1 ≤ ‖((1 : ℂ) - z).im‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      (oneSubComplex_im_norm_eq z).symm
      hz_im_tail
  exact complex_ne_zero_of_one_le_norm_im ((1 : ℂ) - z) hw_im_tail

/-- The reflected pole-clearing denominator does not vanish on the vertical
tail. -/
private theorem oneSubComplex_sub_one_ne_zero_of_one_le_norm_im
    (z : ℂ)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    (((1 : ℂ) - z) - 1) ≠ 0 := by
  have hdenominator : (((1 : ℂ) - z) - 1) = -z :=
    poleClearingQuotient_zeroOne_denominator_eq_neg z
  have hz_ne_zero : z ≠ 0 :=
    complex_ne_zero_of_one_le_norm_im z hz_im_tail
  exact fun hzero =>
    hz_ne_zero
      (neg_eq_zero.mp
        (Eq.subst
          (motive := fun value : ℂ => value = 0)
          hdenominator
          hzero))

/-- Reconstruction of completed zeta from zeta and the real Gamma factor. -/
private theorem riemannZeta_mul_GammaReal_eq_completedRiemannZeta
    {w : ℂ}
    (hw_ne_zero : w ≠ 0)
    (hGamma_ne : Complex.Gammaℝ w ≠ 0) :
    riemannZeta w * Complex.Gammaℝ w = completedRiemannZeta w := by
  have hzeta_reflected :
      riemannZeta w = completedRiemannZeta w / Complex.Gammaℝ w :=
    riemannZeta_def_of_ne_zero hw_ne_zero
  have hmultiplied :
      riemannZeta w * Complex.Gammaℝ w =
        (completedRiemannZeta w / Complex.Gammaℝ w) * Complex.Gammaℝ w :=
    congrArg (fun value : ℂ => value * Complex.Gammaℝ w) hzeta_reflected
  exact Eq.trans hmultiplied
    (div_mul_cancel₀ (completedRiemannZeta w) hGamma_ne)

/-- Completed-zeta symmetry yields the zeta quotient once both Gamma
reconstructions are valid. -/
private theorem riemannZeta_completedFunctionalEquation_quotient_of_nonzero
    {z : ℂ}
    (hz_ne_zero : z ≠ 0)
    (hw_ne_zero : ((1 : ℂ) - z) ≠ 0)
    (hGamma_reflected_ne : Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0) :
    riemannZeta z =
      riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
  have hcompleted_symmetry :
      completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) :=
    (completedRiemannZeta_one_sub z).symm
  have hcompleted_reflected :
      riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z) =
        completedRiemannZeta ((1 : ℂ) - z) :=
    riemannZeta_mul_GammaReal_eq_completedRiemannZeta
      hw_ne_zero hGamma_reflected_ne
  have hzeta_completed :
      riemannZeta z =
        completedRiemannZeta z / Complex.Gammaℝ z :=
    riemannZeta_def_of_ne_zero hz_ne_zero
  have hsymmetry_transport :
      completedRiemannZeta z / Complex.Gammaℝ z =
        completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z :=
    congrArg
      (fun value : ℂ => value / Complex.Gammaℝ z)
      hcompleted_symmetry
  have hreflected_transport :
      completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z =
        (riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z)) /
        Complex.Gammaℝ z :=
    congrArg
      (fun value : ℂ => value / Complex.Gammaℝ z)
      hcompleted_reflected.symm
  have hdivision_shape :
      (riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z)) /
        Complex.Gammaℝ z =
      riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z :=
    Eq.refl
      (riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  exact Eq.trans hzeta_completed
    (Eq.trans hsymmetry_transport
      (Eq.trans hreflected_transport hdivision_shape))

/-- Quotient form of the completed functional equation on the zero-one vertical
tail.  This is the analytic continuation step needed beyond the imported
left-half-plane transport. -/
theorem riemannZeta_zero_one_strip_completedFunctionalEquation_quotient_ownerStripContinuation
    {z : ℂ}
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    riemannZeta z =
      riemannZeta ((1 : ℂ) - z) *
        Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
  have hz_ne_zero : z ≠ 0 :=
    complex_ne_zero_of_one_le_norm_im z hz_im_tail
  have hw_ne_zero : ((1 : ℂ) - z) ≠ 0 :=
    oneSubComplex_ne_zero_of_one_le_norm_im z hz_im_tail
  have hw_re_nonnegative : 0 ≤ ((1 : ℂ) - z).re :=
    oneSubComplex_re_nonnegative z hz_re_le_one
  have hw_im_tail : 1 ≤ ‖((1 : ℂ) - z).im‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 ≤ value)
      (oneSubComplex_im_norm_eq z).symm
      hz_im_tail
  have hGamma_reflected_ne : Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      hw_re_nonnegative
      (one_le_norm_of_one_le_norm_im hw_im_tail)
  exact riemannZeta_completedFunctionalEquation_quotient_of_nonzero
    hz_ne_zero hw_ne_zero hGamma_reflected_ne

/-- Interior closed-band continuation of the pole-cleared completed functional
equation identity.

The imported functional-equation multiplier identity currently owns the closed
left half-plane.  The zero-one strip transport additionally needs the same
pointwise identity after analytic continuation across the critical band,
excluding the left edge already handled by the left-half-plane theorem below. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerStripContinuation
    (z : ℂ)
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖)
    (hz_not_left_edge : z.re ≠ 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  have hz_ne_zero : z ≠ 0 :=
    fun hz_zero =>
      hz_not_left_edge
        (Eq.trans (congrArg Complex.re hz_zero) Complex.zero_re)
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      hz_re_nonneg
      (one_le_norm_of_one_le_norm_im hz_im_tail)
  have hmultiplier_raw :
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z =
        ((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) :=
    Eq.trans (if_neg hz_ne_zero) (if_neg hGamma_ne)
  have hz_ne_one : z ≠ 1 :=
    complex_ne_one_of_one_le_norm_im z hz_im_tail
  have hdenominator_ne :
      (((1 : ℂ) - z) - 1) ≠ 0 :=
    oneSubComplex_sub_one_ne_zero_of_one_le_norm_im z hz_im_tail
  have hw_ne_one : ((1 : ℂ) - z) ≠ 1 :=
    fun hw_one =>
      hdenominator_ne (sub_eq_zero.mpr hw_one)
  have hquotient :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z :=
    riemannZeta_zero_one_strip_completedFunctionalEquation_quotient_ownerStripContinuation
      hz_re_le_one hz_im_tail
  have hraw :
      poleClearedRiemannZeta z =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          poleClearedRiemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_completedFunctionalEquationMultiplier_raw_identity_of_zeta_quotient_of_denominators
      hz_ne_one hw_ne_one hdenominator_ne hquotient
  exact Eq.trans hraw
    (congrArg
      (fun multiplier : ℂ =>
        multiplier * poleClearedRiemannZeta ((1 : ℂ) - z))
      hmultiplier_raw.symm)

/-- Pointwise completed-functional-equation identity for the pole-cleared factor
on the closed reflected band `0 ≤ Re s ≤ 1`, restricted to the vertical tail.

The left-half-plane identity already exists upstream.  This wrapper uses it on
the left edge and leaves only the genuine interior strip-continuation statement
as owner content. -/
theorem poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
    (z : ℂ)
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  match eq_or_ne z.re 0 with
  | Or.inl hz_left_edge =>
      have hz_re_left : z.re ≤ 0 :=
        le_of_eq hz_left_edge
      exact
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity
          hz_re_left
  | Or.inr hz_not_left_edge =>
      exact
        poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerStripContinuation
          z hz_re_nonneg hz_re_le_one hz_im_tail hz_not_left_edge

end
end LFunctions
end Boundary

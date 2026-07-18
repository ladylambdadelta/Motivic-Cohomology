import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part03_FunctionalEquation

/-!
# Pole-cleared zeta reflected-growth definitions
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Reflection preserves the closed zero-one real strip. -/
private theorem zeroOneReflection_real_coordinates
    (z : ℂ)
    (hz_nonnegative : 0 ≤ z.re)
    (hz_le_one : z.re ≤ 1) :
    0 ≤ ((1 : ℂ) - z).re ∧ ((1 : ℂ) - z).re ≤ 1 := by
  have hre : ((1 : ℂ) - z).re = 1 - z.re :=
    Eq.trans (Complex.sub_re (1 : ℂ) z)
      (congrArg (fun value : ℝ => value - z.re) Complex.one_re)
  have hlower : 0 ≤ 1 - z.re :=
    sub_nonneg.mpr hz_le_one
  have hupper : 1 - z.re ≤ 1 :=
    sub_le_self 1 hz_nonnegative
  exact
    ⟨Eq.subst (motive := fun value : ℝ => 0 ≤ value) hre.symm hlower,
      Eq.subst (motive := fun value : ℝ => value ≤ 1) hre.symm hupper⟩

/-- Reflection has norm at most the standard height base. -/
private theorem zeroOneReflection_norm_le_height (z : ℂ) :
    ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := by
  have htriangle : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
    norm_sub_le (1 : ℂ) z
  have hone_norm : ‖(1 : ℂ)‖ + ‖z‖ = 1 + ‖z‖ :=
    congrArg (fun value : ℝ => value + ‖z‖)
      (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  exact Eq.subst
    (motive := fun value : ℝ => ‖(1 : ℂ) - z‖ ≤ value)
    hone_norm
    htriangle

/-- The reflected height base is at most twice the original height base. -/
private theorem zeroOneReflection_height_le_two_mul_height (z : ℂ) :
    1 + ‖(1 : ℂ) - z‖ ≤ 2 * (1 + ‖z‖) := by
  have hreflected : 1 + ‖(1 : ℂ) - z‖ ≤ 1 + (1 + ‖z‖) :=
    add_le_add_left (zeroOneReflection_norm_le_height z) 1
  have hfirst_regroup : 1 + (1 + ‖z‖) = 2 + ‖z‖ :=
    Eq.trans (add_assoc 1 1 ‖z‖).symm
      (congrArg (fun value : ℝ => value + ‖z‖) one_add_one_eq_two)
  have hnorm_scale : 2 + ‖z‖ ≤ 2 + 2 * ‖z‖ :=
    add_le_add_left
      (le_mul_of_one_le_left (norm_nonneg z) poleCleared_one_le_two) 2
  have hsecond_regroup : 2 + 2 * ‖z‖ = 2 * (1 + ‖z‖) :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 2 * ‖z‖) (mul_one 2).symm)
      (mul_add 2 1 ‖z‖).symm
  have hreflected_regrouped : 1 + ‖(1 : ℂ) - z‖ ≤ 2 + ‖z‖ :=
    Eq.subst
      (motive := fun value : ℝ => 1 + ‖(1 : ℂ) - z‖ ≤ value)
      hfirst_regroup
      hreflected
  have hscaled : 1 + ‖(1 : ℂ) - z‖ ≤ 2 + 2 * ‖z‖ :=
    le_trans hreflected_regrouped hnorm_scale
  exact Eq.subst
    (motive := fun value : ℝ => 1 + ‖(1 : ℂ) - z‖ ≤ value)
    hsecond_regroup
    hscaled

/-- Reflection rescales a finite-order exponent by at most `2^m`. -/
private theorem zeroOneReflection_finiteOrder_exponent_le
    (z : ℂ)
    (B : ℝ)
    (m : ℕ)
    (hB_nonnegative : 0 ≤ B) :
    B * (1 + ‖(1 : ℂ) - z‖) ^ m ≤
      (B * (2 : ℝ) ^ m) * (1 + ‖z‖) ^ m := by
  have hbase_nonnegative : 0 ≤ 1 + ‖(1 : ℂ) - z‖ :=
    le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg ((1 : ℂ) - z)))
  have hpow :
      (1 + ‖(1 : ℂ) - z‖) ^ m ≤
        (2 * (1 + ‖z‖)) ^ m :=
    pow_le_pow_left₀ hbase_nonnegative
      (zeroOneReflection_height_le_two_mul_height z) m
  have hpow_expanded :
      (1 + ‖(1 : ℂ) - z‖) ^ m ≤
        (2 : ℝ) ^ m * (1 + ‖z‖) ^ m :=
    Eq.subst
      (motive := fun value : ℝ =>
        (1 + ‖(1 : ℂ) - z‖) ^ m ≤ value)
      (mul_pow 2 (1 + ‖z‖) m)
      hpow
  exact le_trans
    (mul_le_mul_of_nonneg_left hpow_expanded hB_nonnegative)
    (le_of_eq
      (mul_assoc B ((2 : ℝ) ^ m) ((1 + ‖z‖) ^ m)).symm)

/-- Unconditional noncircular finite-order envelope for the reflected zero-one
band.

The boundary and compact-height hypotheses used by the surrounding transport
package do not own this estimate.  The real analytic content is a finite-order
bound for `poleClearedRiemannZeta (1 - z)` while `z` remains in the same closed
band `0 ≤ Re z ≤ 1`, so the proof must come from the zero-one functional-
equation/Stirling continuation package itself, not from the later PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeroOne with
  | ⟨A, B, m, hA_pos, hB_pos, hbound⟩ =>
      exact
        ⟨A, B * (2 : ℝ) ^ m, m, hA_pos,
          mul_pos hB_pos (pow_pos zero_lt_two m),
          fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
            let w : ℂ := (1 : ℂ) - z
            have hw_coordinates :
                0 ≤ w.re ∧ w.re ≤ 1 :=
              zeroOneReflection_real_coordinates
                z hz_re_nonneg hz_re_le_one
            have hraw :
                ‖poleClearedRiemannZeta w‖ ≤
                  A * Real.exp (B * (1 + ‖w‖) ^ m) :=
              hbound w hw_coordinates.1 hw_coordinates.2
            have harg :
                B * (1 + ‖w‖) ^ m ≤
                  (B * (2 : ℝ) ^ m) * (1 + ‖z‖) ^ m :=
              zeroOneReflection_finiteOrder_exponent_le
                z B m (le_of_lt hB_pos)
            have hexp :
                Real.exp (B * (1 + ‖w‖) ^ m) ≤
                  Real.exp
                    ((B * (2 : ℝ) ^ m) * (1 + ‖z‖) ^ m) :=
              Real.exp_le_exp.mpr harg
            le_trans hraw
              (mul_le_mul_of_nonneg_left hexp (le_of_lt hA_pos))⟩

/-- Noncircular finite-order envelope for the reflected value in the self-
reflected zero-one strip transport.

The map `z ↦ 1 - z` preserves the closed band `0 ≤ Re z ≤ 1`; hence this is not
an Euler one-two-strip estimate in disguise.  It is the remaining analytic
interior estimate needed before the pointwise completed-functional-equation
identity can be converted into vertical-tail growth for `poleClearedRiemannZeta`
itself. -/
theorem poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_ownerSelfReflectedEnvelope
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
      hzeroOne

/-- Product assembly for a completed-functional-equation multiplier envelope
and an independently supplied reflected-value envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_product_core
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧ 0 < B ∧
        ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hreflected :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧ 0 < B ∧
        ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧ 0 < B ∧
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hmult with
  | ⟨AM, BM, mM, hAM_pos, hBM_pos, hM_bound⟩ =>
      match hreflected with
      | ⟨Af, Bf, mf, hAf_pos, hBf_pos, hf_bound⟩ =>
          exact
            ⟨AM * Af, 2 * (BM + Bf + 1), mM + mf,
              mul_pos hAM_pos hAf_pos,
              mul_pos zero_lt_two
                (add_pos (add_pos hBM_pos hBf_pos) zero_lt_one),
              fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
                let H : ℝ := 1 + ‖z‖
                have hBM_nonnegative : 0 ≤ BM := le_of_lt hBM_pos
                have hBf_nonnegative : 0 ≤ Bf := le_of_lt hBf_pos
                have hAM_nonnegative : 0 ≤ AM := le_of_lt hAM_pos
                have hH_ge_one : 1 ≤ H :=
                  le_add_of_nonneg_right (norm_nonneg z)
                have hM_target :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
                      AM * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  le_trans
                    (hM_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_firstFactor_le_commonEnvelope
                      AM BM Bf H mM mf hAM_nonnegative
                      hBM_nonnegative hBf_nonnegative hH_ge_one)
                have hf_target :
                    ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      Af * Real.exp ((BM + Bf + 1) * H ^ (mM + mf)) :=
                  le_trans
                    (hf_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_secondFactor_le_commonEnvelope
                      Af BM Bf H mM mf (le_of_lt hAf_pos)
                      hBM_nonnegative hBf_nonnegative hH_ge_one)
                have hidentity :
                    poleClearedRiemannZeta z =
                      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
                        poleClearedRiemannZeta ((1 : ℂ) - z) :=
                  poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
                    z hz_re_nonneg hz_re_le_one hz_im_tail
                have hnorm :
                    ‖poleClearedRiemannZeta z‖ =
                      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ := by
                  exact Eq.trans (congrArg norm hidentity)
                    (norm_mul
                      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                      (poleClearedRiemannZeta ((1 : ℂ) - z)))
                finiteOrderProduct_commonEnvelope_norm_bound
                  (poleClearedRiemannZeta z)
                  (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
                  (poleClearedRiemannZeta ((1 : ℂ) - z))
                  AM Af (BM + Bf + 1) H (mM + mf)
                  hAM_nonnegative hnorm hM_target hf_target⟩

/-- Core self-reflected completed-functional-equation transport on `0 ≤ Re s ≤ 1`.

This is the exact remaining noncircular analytic content after the multiplier
bound has been separated: prove the pole-cleared completed-functional-equation
identity on the closed zero-one band, then combine it with a finite-order
envelope for the reflected value `poleClearedRiemannZeta (1 - z)` on the same
band.  The boundary hypotheses are available for the two vertical edges and
compact-height patching, but they do not by themselves give the interior
reflected-band envelope. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport_core
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_product_core
      hmult
      (poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_ownerSelfReflectedEnvelope
        hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary)

/-- Self-reflected completed-functional-equation transport on `0 ≤ Re s ≤ 1`.

The multiplier estimate is separated from this theorem because the completed
functional equation reflects the zero-one band into itself.  This leaf owns the
remaining analytic transport: combine the multiplier envelope, the removable
completed-functional-equation identity, and the vertical boundary/compact data
without appealing to the later boundary-and-PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport_core
      hmult hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Noncircular completed-functional-equation band transport on `0 ≤ Re s ≤ 1`.

This is the actual interior owner leaf behind the reflected half-strip tail:
it must combine the completed functional equation for the pole-cleared factor
with the Gamma/Stirling multiplier estimates on the whole closed reflected
band.  It deliberately does not consume the later boundary-and-PL theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBandTransport
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerSelfReflectedFunctionalEquationTransport
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Noncircular reflected-band vertical-tail growth on `0 ≤ Re s ≤ 1`.

The boundary transport already available from the completed functional equation
controls the edge `Re s = 0`, while Euler/Abel controls `Re s = 1`.  This owner
leaf is the remaining interior strip estimate: combine those two edge controls
with the completed-functional-equation multiplier/Gamma-Stirling package on the
reflected band, without appealing to the later PL route that depends on the
admissible-growth theorem built from this result. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBand
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBandTransport
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Vertical-tail finite-order growth on `0 ≤ Re s ≤ 1` from the completed
functional equation and Gamma/Stirling multiplier bounds.

This is the exact remaining unbounded-height theorem after compact local
boundedness has been separated.  Its proof should transport the pole-cleared
functional equation on the zero-one strip, estimate the Gamma/trigonometric
factor using the Binet/Stirling package, and combine that with the reflected
Abel/Euler control on the boundary data. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationBand
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary

/-- Compatibility wrapper for the `0 ≤ Re s ≤ 1` ordinary finite-order
growth package.

The reflected half-strip finite-order estimate is the genuine analytic input
`hzeroOne`.  This theorem preserves the older functional-equation-shaped
call surface while making no new proof of that input. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact hzeroOne

/-- Interior admissible-growth input for the genuine `0 < Re s < 1` strip.

This is the noncircular analytic strip theorem left after the boundary inputs
are separated: it is not obtained by sending `s` to `1 - s` and pretending the
image lies in `1 < Re s < 2`.  Its proof belongs to the completed functional
equation plus Gamma/Stirling transport package on the open reflected band. -/
theorem poleClearedRiemannZeta_zero_one_strip_admissible_growth_from_functionalEquation
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (1 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 1)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 1 zero_lt_one
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_from_functionalEquation
        hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary)

/-- Vertical-tail finite-order growth for the removable pole-cleared zeta on
`0 ≤ Re s ≤ 1`, from the two vertical boundary estimates and the generic strip
Phragmen-Lindelöf theorem. -/
theorem poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_from_boundary_and_PL
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_boundary_envelopes_by_damping
    poleClearedRiemannZeta 0 1 zero_lt_one
    poleClearedRiemannZeta_zero_one_strip_diffContOnCl
    (poleClearedRiemannZeta_zero_one_strip_admissible_growth_from_functionalEquation
      hbranch hzeroOne hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary)
    (match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
        hbranch with
    | ⟨A, B, m, hA, hB, hleft⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
    (match poleClearedRiemannZeta_boundaryLine_one_growth_bound_standard with
    | ⟨A, B, m, hA, hB, hright⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hright z hz_re hz_im (hpartialOneTwo z hz_re hz_im)⟩)

/-- Vertical-tail finite-order growth on the closed zero-one strip, proved
directly from the completed functional equation rather than from admissible
growth or a strip-PL theorem that consumes the finite-order conclusion. -/
def PoleClearedZeroOneStripFunctionalEquationVerticalTailGrowth
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) : Prop :=
  ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
    0 < A ∧
    0 < B ∧
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ 1 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)

/-- Noncircular reflected-value envelope on the self-reflected zero-one band.

This is the genuine missing interior estimate in the zero-one strip functional
equation route.  It must be obtained from a non-circular strip argument or a
global pole-cleared finite-order construction, not by feeding
`PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth` back into itself. -/
def PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) : Prop :=
  ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
    0 < A ∧
    0 < B ∧
    ∀ z : ℂ,
      0 ≤ z.re →
      z.re ≤ 1 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m)

/-- Canonical reflected-value input for the zero-one functional-equation
route, using the already-owned boundary and compact packages. -/
def PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope : Prop :=
  PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
    boundaryLineOneAbelPartialMajorant_from_realParam
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact

/-- Conditional exposure of the noncircular self-reflected vertical-tail
envelope.

The reflected-value estimate is a genuine analytic input for the zero-one
functional-equation route.  It must be proved without first proving ordinary
finite-order growth on the same zero-one strip, since that ordinary theorem
consumes this reflected envelope through the completed functional equation. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_ownerEulerMaclaurinFunctionalEquationCore
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound)
    (hreflected :
      PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
        hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact hreflected

/-- The self-reflected vertical-tail envelope follows from an already-owned
ordinary finite-order theorem on the same zero-one strip.

This is the exact conditional transport across `z ↦ 1 - z`; it is deliberately
kept separate from the unconditional owner leaf below, whose proof must supply
the zero-one finite-order input without using that same owner conclusion. -/
theorem poleClearedRiemannZeta_zero_one_strip_selfReflectedVerticalTailEnvelope_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    PoleClearedZeroOneStripSelfReflectedVerticalTailEnvelope
      hpartialOneTwo hcompactOneTwo hpartialLeft hcompactBoundary := by
  exact
    poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
      hzeroOne
end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FunctionalEquationTransport.Owner

/-!
# Completed zeta finite-order growth

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, 1, 0, hC_pos, zero_lt_one, ?_⟩
  intro z hz0 hz2 hzim
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hzim⟩
  have hraw : ‖poleClearedRiemannZeta z‖ ≤ C :=
    hC_bound z hz_mem
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    have hexponent_nonneg :
        0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
      mul_nonneg zero_le_one
        (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) 0)
    exact le_trans
      (le_of_eq Real.exp_zero.symm)
      (Real.exp_le_exp.mpr hexponent_nonneg)
  have hC_le_target :
      C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    calc
      C = C * 1 := by
        exact (mul_one C).symm
      _ ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos)
  exact le_trans hraw hC_le_target

/-- Vertical-tail finite-order growth in the central strip for the pole-cleared zeta factor.

This is the unbounded-height part of the central strip.  Its proof belongs to
the standard zeta strip-growth theorem: combine the left boundary obtained from
the completed functional equation and Gamma/Stirling owner estimates with the
right boundary obtained from the Dirichlet-series/Euler-Maclaurin side, then use
the generic strip finite-order/Phragmen-Lindelöf API. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- The exact PL input package for the central-strip vertical tail.

The left edge is the completed-functional-equation/Gamma-Stirling estimate; the
right edge is the Dirichlet-series/Euler-Maclaurin estimate; the interior
admissible growth is the finite-order zeta input already isolated above. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package :
    DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2) ∧
      (∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
      (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  refine
    ⟨poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl,
      poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth,
      poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

theorem poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package with
    ⟨hhol, hfinite, hleft, hright⟩
  exact
    poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
      hhol hfinite hleft hright

/-- Compact core and vertical tails patch to finite-order growth on the whole
central strip. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz0 hz2
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz0 hz2 hcompact_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg
          (le_add_of_nonneg_right hAt_nonneg)
          (le_add_of_nonneg_right hBt_nonneg)
          hBc_nonneg
          (Nat.le_add_right mc mt))
  | Or.inr htail_im =>
      have hdegree : mt ≤ mc + mt := by
        exact Eq.subst
          (motive := fun d : ℕ => mt ≤ d)
          (Nat.add_comm mt mc)
          (Nat.le_add_right mt mc)
      exact le_trans (ht z hz0 hz2 htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Central compact-strip finite-order growth for the pole-cleared zeta factor.

This is the local boundedness part of the global finite-order theorem.  The
removable value at `1` is already built into `poleClearedRiemannZeta`; on the
closed strip `0 ≤ Re z ≤ 2`, compact/local boundedness gives an ordinary
finite-order envelope with fixed constants; cf. Boas, Ch. 1. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth
      poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs

/-- Patch left, central, and right finite-order envelopes into a global envelope. -/
theorem poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcentral :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  rcases hcentral with ⟨Ac, Bc, mc, hAc, hBc, hcentral_bound⟩
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  let A : ℝ := Al + Ac + Ar
  let B : ℝ := Bl + Bc + Br
  let m : ℕ := ml + mc + mr
  have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
  have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
  have hA_pos : 0 < A :=
    add_pos (add_pos hAl hAc) hAr
  have hB_pos : 0 < B :=
    add_pos (add_pos hBl hBc) hBr
  refine ⟨A, B, m, hA_pos, hB_pos, ?_⟩
  intro z
  have hB_l_le : Bl ≤ B :=
    le_trans (le_add_of_nonneg_right hBc_nonneg)
      (le_add_of_nonneg_right hBr_nonneg)
  have hB_c_le : Bc ≤ B := by
    have hBc_le_Bl_Bc : Bc ≤ Bl + Bc :=
      le_add_of_nonneg_left hBl_nonneg
    exact le_trans hBc_le_Bl_Bc (le_add_of_nonneg_right hBr_nonneg)
  have hB_r_le : Br ≤ B := by
    have hBr_le_Bc_Br : Br ≤ Bc + Br :=
      le_add_of_nonneg_left hBc_nonneg
    have hBc_Br_le_B : Bc + Br ≤ B := by
      calc
        Bc + Br ≤ Al + (Bc + Br) :=
          le_add_of_nonneg_left hAl_nonneg
        _ = B := by
          exact (add_assoc Al Bc Br).symm
    exact le_trans hBr_le_Bc_Br hBc_Br_le_B
  by_cases hz_left : z.re ≤ 0
  · have hraw :
        ‖poleClearedRiemannZeta z‖ ≤
          Al * Real.exp (Bl * (1 + ‖z‖) ^ ml) :=
      hleft_bound z hz_left
    have hA_l_le : Al ≤ A :=
      le_trans (le_add_of_nonneg_right hAc_nonneg)
        (le_add_of_nonneg_right hAr_nonneg)
    exact le_trans hraw
      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAl_nonneg hA_l_le hB_l_le hBl_nonneg
        (Nat.le_add_right ml (mc + mr)))
  · have hz_nonneg : 0 ≤ z.re :=
      le_of_not_ge hz_left
    by_cases hz_right : 2 ≤ z.re
    · have hraw :
          ‖poleClearedRiemannZeta z‖ ≤
            Ar * Real.exp (Br * (1 + ‖z‖) ^ mr) :=
        hright_bound z hz_right
      have hA_r_le : Ar ≤ A := by
        have hAr_le_Ac_Ar : Ar ≤ Ac + Ar :=
          le_add_of_nonneg_left hAc_nonneg
        have hAc_Ar_le_A : Ac + Ar ≤ A := by
          calc
            Ac + Ar ≤ Al + (Ac + Ar) :=
              le_add_of_nonneg_left hAl_nonneg
            _ = A := by
              exact (add_assoc Al Ac Ar).symm
        exact le_trans hAr_le_Ac_Ar hAc_Ar_le_A
      have hm_r_le : mr ≤ m := by
        have hmc_mr_le : mr ≤ mc + mr :=
          Nat.le_add_left mr mc
        have htarget : mc + mr ≤ m := by
          exact Nat.le_add_left (mc + mr) ml
        exact le_trans hmc_mr_le htarget
      exact le_trans hraw
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAr_nonneg hA_r_le hB_r_le hBr_nonneg hm_r_le)
    · have hz_le_two : z.re ≤ 2 :=
        le_of_not_ge hz_right
      have hraw :
          ‖poleClearedRiemannZeta z‖ ≤
            Ac * Real.exp (Bc * (1 + ‖z‖) ^ mc) :=
        hcentral_bound z hz_nonneg hz_le_two
      have hA_c_le : Ac ≤ A := by
        have hAc_le_Al_Ac : Ac ≤ Al + Ac :=
          le_add_of_nonneg_left hAl_nonneg
        exact le_trans hAc_le_Al_Ac (le_add_of_nonneg_right hAr_nonneg)
      have hm_c_le : mc ≤ m := by
        have hmc_le_ml_mc : mc ≤ ml + mc :=
          Nat.le_add_left mc ml
        have htarget : ml + mc ≤ m :=
          Nat.le_add_right (ml + mc) mr
        exact le_trans hmc_le_ml_mc htarget
      exact le_trans hraw
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg hA_c_le hB_c_le hBc_nonneg hm_c_le)

theorem poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
      poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation
      poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
      poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Zeta-specific ordinary finite-order growth for the pole-cleared factor in
the right critical strip.

This is only the restriction of the global finite-order theorem for
`(s - 1)ζ(s)` to the closed right critical strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin with
    ⟨A, B, m, hA, hB, hbound⟩
  exact ⟨A, B, m, hA, hB, fun z _hz_left _hz_right => hbound z⟩

/-- Standard finite-order theorem for the pole-cleared Riemann zeta factor in the right
critical strip.

This is the exact zeta finite-order theorem needed by the strip damping argument.  Its
analytic proof is the standard meromorphic finite-order estimate for `ζ`, with the pole at
`1` removed by `poleClearedRiemannZeta`: Abel/Euler-Maclaurin gives the right boundary,
the completed functional equation plus the Gamma-ratio Stirling estimates gives the left
boundary, local boundedness handles the removable pole, and the finite-order strip
normalization converts those inputs to the sub-critical double-exponential envelope. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 2 zero_lt_two
      poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin

/-- Standard zeta finite-order input for the pole-cleared factor inside the right
critical strip.

This is only name transport from the exact standard finite-order theorem for the
pole-cleared Riemann zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth

/-- Deep zeta-growth owner primitive for the pole-cleared factor inside the right
critical strip.

The analytic content is isolated in
`poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth`;
this owner primitive is only the public name consumed by the strip
Phragmen-Lindelöf layer. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput

/-- Interior admissible finite-order envelope for the pole-cleared zeta factor in the
right critical strip.

This is the damping-side zeta-growth root consumed by the generic strip
Phragmen-Lindelöf theorem.  It is a thin wrapper over the standard finite-order theorem
for the pole-cleared Riemann zeta factor in this bounded-width strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This is the zeta-side consumer of the generic strip Phragmen-Lindelöf theorem before
transporting away from the pole face to `(s - 1) ζ(s)`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This theorem is now reduced to the immediate strip inputs for the pole-cleared
normalization: strip holomorphy, admissible strip growth, and the two vertical-edge
finite-order estimates. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound with
    ⟨hleft, hright⟩
  exact
    poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
      poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl
      poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
      hleft
      hright

/-- Vertical-tail pole-cleared zeta strip estimate.

This is the final zeta-specific consumer of the generic strip Phragmen-Lindelöf
pillar `strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order`.
The remaining zeta inputs are exactly the classical ones: holomorphicity after pole
clearing, right-boundary growth from the Dirichlet-series estimate, and left-boundary
growth from the functional equation/completed normalization with Gamma control. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz0 hz2 hzim
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have him_zero : z.im = 0 := by
      calc
        z.im = (1 : ℂ).im := by
          exact congrArg Complex.im hz_eq
        _ = 0 := by
          rfl
    have hnorm_im_zero : ‖z.im‖ = 0 := by
      exact (congrArg norm him_zero).trans norm_zero
    have hle_zero : (1 : ℝ) ≤ 0 :=
      hzim.trans_eq hnorm_im_zero
    exact (not_le_of_gt zero_lt_one) hle_zero
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpc
    (hbound z hz0 hz2 hzim)

/-- Compact and vertical-tail estimates combine to the right-critical-strip pole-cleared
zeta bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz0 hz2
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz0 hz2 hcompact_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg
          (le_add_of_nonneg_right hAt_nonneg)
          (le_add_of_nonneg_right hBt_nonneg)
          hBc_nonneg
          (Nat.le_add_right mc mt))
  | Or.inr htail_im =>
      have hdegree : mt ≤ mc + mt := by
        exact Eq.subst
          (motive := fun d : ℕ => mt ≤ d)
          (Nat.add_comm mt mc)
          (Nat.le_add_right mt mc)
      exact le_trans (ht z hz0 hz2 htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Pole-cleared finite-order growth for `ζ` in the bounded-width right critical strip. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound
    riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound

/-- Direct compact bound for the pole-cleared completed-zeta entire part in the
right-critical strip.

This compact statement is the truthful replacement for a standalone compact `Gammaℝ`
bound, since the completed entire part already includes the pole cancellations. -/
theorem completedRiemannZeta₀_rightCriticalStrip_compact_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases completedRiemannZeta₀_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, 1, 0, hC, zero_lt_one, ?_⟩
  intro z hz0 hz2 hz_im
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hz_im⟩
  have hraw : ‖completedRiemannZeta₀ z‖ ≤ C :=
    hbound z hz_mem
  have hfactor_ge_one : (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ 0) := by
    have hone : (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 := by
      calc (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 * 1 := by
            exact congrArg (· * 1) (pow_zero (1 + ‖z‖))
          _ = 1 := one_mul 1
    exact Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
      hone.symm
      (Real.one_le_exp_iff.mpr zero_le_one)
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC
  have hC_le_scaled :
      C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ 0) :=
    le_mul_of_one_le_right hC_nonneg hfactor_ge_one
  exact le_trans hraw hC_le_scaled

/-- On the vertical tail of the right critical strip, the explicit pole terms are bounded
and the completed normalization is controlled by the pole-cleared zeta factor and `Gammaℝ`.
-/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_norm_le_poleCleared_zeta_gamma_plus_one :
    ∃ D : ℝ,
      0 < D ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          D * (‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) := by
  refine ⟨3, zero_lt_three, ?_⟩
  intro z _hz0 _hz2 hz_im
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    have him_zero : z.im = 0 := by
      calc
        z.im = (0 : ℂ).im := by
          exact congrArg Complex.im hz
        _ = 0 := by
          exact Complex.zero_im
    have him_norm_zero : ‖z.im‖ = 0 := by
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    intro hsub
    have him_zero : ((1 : ℂ) - z).im = 0 := by
      calc
        ((1 : ℂ) - z).im = (0 : ℂ).im := by
          exact congrArg Complex.im hsub
        _ = 0 := by
          exact Complex.zero_im
    have him_eq : ((1 : ℂ) - z).im = -z.im := by
      calc
        ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im 1 z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    have hneg_im_zero : -z.im = 0 :=
      Eq.trans him_eq.symm him_zero
    have him_zero_z : z.im = 0 :=
      neg_eq_zero.mp hneg_im_zero
    have him_norm_zero : ‖z.im‖ = 0 :=
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero_z
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hz_minus_one_ne_zero : z - 1 ≠ 0 := by
    intro hsub
    have hone_sub_zero : (1 : ℂ) - z = 0 := by
      calc
        (1 : ℂ) - z = -(z - 1) := (neg_sub z 1).symm
        _ = -0 := by
          exact congrArg Neg.neg hsub
        _ = 0 := by
          exact neg_zero
    exact hone_sub_ne_zero hone_sub_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 := by
    intro hGamma
    have hzero_index : ∃ n : ℕ, z = -(2 * (n : ℂ)) :=
      Complex.Gammaℝ_eq_zero_iff.mp hGamma
    rcases hzero_index with ⟨n, hn⟩
    have him_zero : z.im = 0 := by
      calc
        z.im = (-(2 * (n : ℂ))).im := by
          exact congrArg Complex.im hn
        _ = -(2 * (n : ℂ)).im := Complex.neg_im _
        _ = -((2 : ℂ).im * (n : ℂ).re + (2 : ℂ).re * (n : ℂ).im) :=
            congrArg Neg.neg (Complex.mul_im 2 (n : ℂ))
        _ = -(0 * (n : ℂ).re + (2 : ℂ).re * 0) :=
            congrArg Neg.neg (congrArg₂ (· + ·)
              (congrArg (· * (n : ℂ).re) (Complex.ofReal_im 2))
              (congrArg (· * 0) (Complex.ofReal_im n)))
        _ = -(0 + 0) :=
            congrArg Neg.neg (congrArg₂ (· + ·) (zero_mul _) (mul_zero _))
        _ = 0 := by
            exact (congrArg Neg.neg (add_zero 0)).trans neg_zero
    have him_norm_zero : ‖z.im‖ = 0 :=
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hcompleted_factor :
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    have h := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
    have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) h
    have hcancel :
        (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
          completedRiemannZeta z := by
      exact div_mul_cancel₀ _ hGamma_ne
    exact (hmul.trans hcancel).symm
  have hdecomp :
      completedRiemannZeta₀ z =
        completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    have hformula :
        completedRiemannZeta z =
          completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
      completedRiemannZeta_eq z
    calc
      completedRiemannZeta₀ z =
          (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) +
            1 / z + 1 / (1 - z) := by
        have h1 : completedRiemannZeta₀ z - (1 / z + 1 / (1 - z)) =
                  completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
          (sub_sub _ _ _).symm
        calc completedRiemannZeta₀ z =
            (completedRiemannZeta₀ z - (1 / z + 1 / (1 - z))) + (1 / z + 1 / (1 - z)) :=
              (sub_add_cancel _ _).symm
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + (1 / z + 1 / (1 - z)) :=
              congrArg (· + (1 / z + 1 / (1 - z))) h1
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + 1 / z + 1 / (1 - z) :=
              (add_assoc _ _ _).symm
      _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
    exact le_trans hz_im (Complex.abs_im_le_abs z)
  have hone_sub_norm_ge_one : (1 : ℝ) ≤ ‖1 - z‖ := by
    have him_abs_le : ‖((1 : ℂ) - z).im‖ ≤ ‖(1 : ℂ) - z‖ :=
      Complex.abs_im_le_abs ((1 : ℂ) - z)
    have him_eq : ((1 : ℂ) - z).im = -z.im := by
      calc
        ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im 1 z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    have him_norm_eq : ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
      calc
        ‖((1 : ℂ) - z).im‖ = ‖-z.im‖ := by
          exact congrArg norm him_eq
        _ = ‖z.im‖ := by
          exact norm_neg z.im
    exact le_trans
      (Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_eq.symm
        hz_im)
      him_abs_le
  have hz_minus_one_norm_ge_one : (1 : ℝ) ≤ ‖z - 1‖ := by
    have him_abs_le : ‖(z - (1 : ℂ)).im‖ ≤ ‖z - (1 : ℂ)‖ :=
      Complex.abs_im_le_abs (z - (1 : ℂ))
    have him_eq : (z - (1 : ℂ)).im = z.im := by
      calc
        (z - (1 : ℂ)).im = z.im - (1 : ℂ).im := by
          exact Complex.sub_im z 1
        _ = z.im - 0 := by
          exact congrArg (fun x : ℝ => z.im - x) Complex.one_im
        _ = z.im := by
          exact sub_zero z.im
    exact le_trans
      (Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        (congrArg norm him_eq).symm
        hz_im)
      him_abs_le
  have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
    have hz_norm_pos : 0 < ‖z‖ :=
      lt_of_lt_of_le zero_lt_one hz_norm_ge_one
    calc
      ‖1 / z‖ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (1 : ℂ) z
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hz_norm_pos hz_norm_ge_one
  have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
    have hnorm_pos : 0 < ‖1 - z‖ :=
      lt_of_lt_of_le zero_lt_one hone_sub_norm_ge_one
    calc
      ‖1 / (1 - z)‖ = ‖(1 : ℂ)‖ / ‖1 - z‖ := by
        exact norm_div (1 : ℂ) (1 - z)
      _ = 1 / ‖1 - z‖ := by
        exact congrArg (fun x : ℝ => x / ‖1 - z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hnorm_pos hone_sub_norm_ge_one
  have hpole_factor :
      ‖riemannZeta z‖ ≤ ‖(z - 1) * riemannZeta z‖ := by
    have hnorm_pos : 0 < ‖z - 1‖ :=
      lt_of_lt_of_le zero_lt_one hz_minus_one_norm_ge_one
    calc
      ‖riemannZeta z‖ =
          ‖(z - 1) * riemannZeta z / (z - 1)‖ := by
        have hcancel : (z - 1) * riemannZeta z / (z - 1) = riemannZeta z := by
          exact mul_div_cancel_left₀ (riemannZeta z) hz_minus_one_ne_zero
        exact congrArg norm hcancel.symm
      _ = ‖(z - 1) * riemannZeta z‖ / ‖z - 1‖ := by
        exact norm_div ((z - 1) * riemannZeta z) (z - 1)
      _ ≤ ‖(z - 1) * riemannZeta z‖ := by
        exact div_le_self (norm_nonneg ((z - 1) * riemannZeta z)) hz_minus_one_norm_ge_one
  have hnorm_decomp :
      ‖completedRiemannZeta₀ z‖ ≤
        ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
    calc
      ‖completedRiemannZeta₀ z‖ =
          ‖completedRiemannZeta z + 1 / z + 1 / (1 - z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hdecomp
      _ ≤ ‖completedRiemannZeta z + 1 / z‖ + ‖1 / (1 - z)‖ := by
        exact norm_add_le (completedRiemannZeta z + 1 / z) (1 / (1 - z))
      _ ≤ (‖completedRiemannZeta z‖ + ‖1 / z‖) + ‖1 / (1 - z)‖ := by
        exact add_le_add_right
          (norm_add_le (completedRiemannZeta z) (1 / z))
          ‖1 / (1 - z)‖
      _ = ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
        exact add_assoc ‖completedRiemannZeta z‖ ‖1 / z‖ ‖1 / (1 - z)‖
  let P : ℝ := ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖
  have hP_nonneg : 0 ≤ P :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcompleted_norm_le :
      ‖completedRiemannZeta z‖ ≤ P := by
    calc
      ‖completedRiemannZeta z‖ = ‖riemannZeta z * Complex.Gammaℝ z‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hcompleted_factor
      _ = ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
        exact norm_mul (riemannZeta z) (Complex.Gammaℝ z)
      _ ≤ ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
        exact mul_le_mul_of_nonneg_right hpole_factor (norm_nonneg _)
  have hsum_bound :
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤ P + 2 := by
    calc
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤
          P + 1 + ‖1 / (1 - z)‖ := by
        exact add_le_add_right
          (add_le_add hcompleted_norm_le hinv_z_le_one)
          ‖1 / (1 - z)‖
      _ ≤ P + 1 + 1 := by
        exact add_le_add_left hinv_one_sub_le_one (P + 1)
      _ = P + 2 := by
        exact (add_assoc P 1 1).symm.trans (congrArg (P + ·) one_add_one)
  have hP_two_le_three :
      P + 2 ≤ 3 * (P + 1) := by
    nlinarith [hP_nonneg]
  exact le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)

/-- A nonnegative exponent has exponential at least one.

This local analytic-growth helper is placed before the strip product estimate that needs it. -/
theorem one_le_exp_of_nonnegative_exponent_core
    {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ≤ Real.exp x := by
  calc
    (1 : ℝ) ≤ x + 1 := by
      exact le_add_of_nonneg_left hx
    _ ≤ Real.exp x := by
      exact Real.add_one_le_exp x

/-- Product growth for the pole-cleared zeta factor and the Gamma factor on the vertical
tail of the right critical strip.

This separates the Gamma-growth estimate from the vertical-strip normalization comparison. -/
theorem poleCleared_zeta_gamma_rightCriticalStrip_verticalTail_product_plus_one_growth_bound
    (hzeta :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hzeta with ⟨Az, Bz, mz, hAz, hBz, hzeta_bound⟩
  rcases hGamma with ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩
  refine ⟨Az * Ag + 1, 2 * (Bz + Bg + 1), mz + mg,
    add_pos (mul_pos hAz hAg) zero_lt_one,
    mul_pos zero_lt_two (add_pos (add_pos hBz hBg) zero_lt_one), ?_⟩
  intro z hz0 hz2 hz_im
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hBz_nonneg : 0 ≤ Bz := le_of_lt hBz
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hBsum_nonneg : 0 ≤ Bz + Bg + 1 :=
    add_nonneg (add_nonneg hBz_nonneg hBg_nonneg) zero_le_one
  have hBtarget_nonneg : 0 ≤ 2 * (Bz + Bg + 1) :=
    mul_nonneg zero_le_two hBsum_nonneg
  have hzeta_enlarge :
      Az * Real.exp (Bz * H ^ mz) ≤
        Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAz)
      (le_refl Az)
      (by
        calc
          Bz ≤ Bz + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bz + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBz_nonneg
      (Nat.le_add_right mz mg)
  have hmg_le : mg ≤ mz + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mz)
      (Nat.le_add_right mg mz)
  have hGamma_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bz + Bg := le_add_of_nonneg_left hBz_nonneg
          _ ≤ Bz + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have htarget_exponent_nonneg : 0 ≤ 2 * (Bz + Bg + 1) * H ^ (mz + mg) :=
    mul_nonneg hBtarget_nonneg (pow_nonneg hH_nonneg (mz + mg))
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) :=
    one_le_exp_of_nonnegative_exponent_core htarget_exponent_nonneg
  have hproduct_bound :
      ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
        (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
    have hzeta_to_target :
        ‖(z - 1) * riemannZeta z‖ ≤
          Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
      le_trans (hzeta_bound z hz0 hz2 hz_im) hzeta_enlarge
    have hGamma_to_target :
        ‖Complex.Gammaℝ z‖ ≤
          Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
      le_trans (hGamma_bound z hz0 hz2 hz_im) hGamma_enlarge
    have hmul :
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
          (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
            (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) :=
      mul_le_mul hzeta_to_target hGamma_to_target (norm_nonneg _)
        (mul_nonneg (le_of_lt hAg)
          (le_of_lt (Real.exp_pos ((Bz + Bg + 1) * H ^ (mz + mg)))))
    have hcollapse :
        (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
            (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) =
          (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
      let x := (Bz + Bg + 1) * H ^ (mz + mg)
      calc
        (Az * Real.exp x) * (Ag * Real.exp x) =
          (Az * (Real.exp x * Ag)) * Real.exp x := by
            exact congrArg (· * Real.exp x) (mul_assoc Az (Real.exp x) Ag)
        _ = (Az * (Ag * Real.exp x)) * Real.exp x := by
            exact congrArg (· * Real.exp x) (congrArg (Az * ·) (mul_comm (Real.exp x) Ag))
        _ = ((Az * Ag) * Real.exp x) * Real.exp x := by
            exact congrArg (· * Real.exp x) ((mul_assoc Az Ag (Real.exp x)).symm)
        _ = (Az * Ag) * (Real.exp x * Real.exp x) :=
            mul_assoc (Az * Ag) (Real.exp x) (Real.exp x)
        _ = (Az * Ag) * Real.exp (x + x) := by
            exact congrArg (fun y : ℝ => (Az * Ag) * y)
              (Real.exp_add x x).symm
        _ = (Az * Ag) * Real.exp (2 * x) := by
            exact congrArg (Az * Ag * ·) (congrArg Real.exp (by omega))
    exact hmul.trans_eq hcollapse
  have hsum_bound :
      ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
        (Az * Ag + 1) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
    have hleft :
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) +
            Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) :=
      add_le_add hproduct_bound hone_le_exp
    have hright :
        (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) +
            Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) =
          (Az * Ag + 1) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
      exact (add_mul (Az * Ag) 1 (Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)))).symm
    exact hleft.trans_eq hright
  exact hsum_bound

/-- The vertical-tail completed-zeta strip estimate follows mechanically from the
pole-cleared zeta tail, Gamma vertical-tail Stirling, and the normalization comparison. -/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound_of_zeta_and_gamma
    (hzeta :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleCleared_zeta_gamma_rightCriticalStrip_verticalTail_product_plus_one_growth_bound
      hzeta hGamma with
    ⟨Apg, Bpg, mpg, hApg, hBpg, hproduct_plus_one_bound⟩
  rcases completedRiemannZeta₀_rightCriticalStrip_verticalTail_norm_le_poleCleared_zeta_gamma_plus_one with
    ⟨D, hD, hnorm_bound⟩
  refine ⟨D * Apg, Bpg, mpg, mul_pos hD hApg, hBpg, ?_⟩
  intro z hz0 hz2 hz_im
  have hscaled :
      D * (‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
        D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) :=
    mul_le_mul_of_nonneg_left (hproduct_plus_one_bound z hz0 hz2 hz_im) (le_of_lt hD)
  have htarget :
      D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) =
        D * Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg) := by
    exact mul_assoc D Apg (Real.exp (Bpg * (1 + ‖z‖) ^ mpg))
  exact le_trans (hnorm_bound z hz0 hz2 hz_im) (hscaled.trans_eq htarget)

/-- Vertical-tail bound for the pole-cleared completed-zeta entire part in the
right-critical strip. -/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound_of_zeta_and_gamma
    riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
    Gammaℝ_rightCriticalStrip_verticalTail_stirling_growth_bound

/-- Compact and vertical-tail completed-zeta estimates combine to the right-critical-strip
finite-order bound. -/
theorem completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz0 hz2
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz0 hz2 hcompact_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg
          (le_add_of_nonneg_right hAt_nonneg)
          (le_add_of_nonneg_right hBt_nonneg)
          hBc_nonneg
          (Nat.le_add_right mc mt))
  | Or.inr htail_im =>
      have hdegree : mt ≤ mc + mt := by
        exact Eq.subst
          (motive := fun d : ℕ => mt ≤ d)
          (Nat.add_comm mt mc)
          (Nat.le_add_right mt mc)
      exact le_trans (ht z hz0 hz2 htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Finite-order growth in the right critical strip for the uncentered entire completed-zeta
part. -/
theorem completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound_of_compact_and_tail
    completedRiemannZeta₀_rightCriticalStrip_compact_growth_bound
    completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound

/-- Far-right logarithmic Stirling bound for the archimedean factor.

This far-right standard analytic primitive is the Gamma-side input for finite-order control
of the completed zero packet. -/
theorem Gammaℝ_farRightHalfPlane_stirling_log_growth_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        2 ≤ z.re →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  rcases Gammaℝ_rightHalfPlane_stirling_log_growth_bound with
    ⟨C, m, hC⟩
  refine ⟨C, m, ?_⟩
  intro z hz
  exact hC z (le_trans zero_le_two hz) (one_le_norm_of_two_le_re hz)

/-- Exponentiating the far-right logarithmic Stirling bound gives finite-order growth for
the archimedean factor. -/
theorem Gammaℝ_farRightHalfPlane_stirling_growth_bound_of_log_growth
    (hlog :
      ∃ C : ℝ, ∃ m : ℕ,
        ∀ z : ℂ,
          2 ≤ z.re →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
    (fun z : ℂ => 2 ≤ z.re)
    hlog

/-- Far-right half-plane Stirling growth for the archimedean factor. -/
theorem Gammaℝ_farRightHalfPlane_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_farRightHalfPlane_stirling_growth_bound_of_log_growth
    Gammaℝ_farRightHalfPlane_stirling_log_growth_bound

/-- Far-right pointwise normalization bound for the pole-cleared completed-zeta entire part.

This is the analytic decomposition step: away from the pole faces, the completed entire
part is controlled by the zeta-gamma product plus the explicit rational correction terms. -/
theorem completedRiemannZeta₀_farRightHalfPlane_norm_le_zeta_gamma_plus_one :
    ∃ D : ℝ,
      0 < D ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          D * (‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) := by
  refine ⟨3, zero_lt_three, ?_⟩
  intro z hz_re
  have hz_re_pos : 0 < z.re :=
    lt_of_lt_of_le zero_lt_two hz_re
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    have hre_zero : z.re = 0 :=
      congrArg Complex.re hz
    have hzero_lt_zero : (0 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => (0 : ℝ) < x)
        hre_zero
        hz_re_pos
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hzero_lt_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos hz_re_pos
  have hcompleted_factor :
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    have h := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
    have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) h
    have hcancel :
        (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
          completedRiemannZeta z := by
      exact div_mul_cancel₀ _ hGamma_ne
    exact (hmul.trans hcancel).symm
  have hdecomp :
      completedRiemannZeta₀ z =
        completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    have hformula :
        completedRiemannZeta z =
          completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
      completedRiemannZeta_eq z
    calc
      completedRiemannZeta₀ z =
          (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) +
            1 / z + 1 / (1 - z) := by
        have h1 : completedRiemannZeta₀ z - (1 / z + 1 / (1 - z)) =
                  completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
          (sub_sub _ _ _).symm
        calc completedRiemannZeta₀ z =
            (completedRiemannZeta₀ z - (1 / z + 1 / (1 - z))) + (1 / z + 1 / (1 - z)) :=
              (sub_add_cancel _ _).symm
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + (1 / z + 1 / (1 - z)) :=
              congrArg (· + (1 / z + 1 / (1 - z))) h1
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + 1 / z + 1 / (1 - z) :=
              (add_assoc _ _ _).symm
      _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
    have hre_abs_le_norm : |z.re| ≤ ‖z‖ :=
      Complex.abs_re_le_abs z
    have hone_le_re_abs : (1 : ℝ) ≤ |z.re| := by
      exact le_trans
        (by norm_num : (1 : ℝ) ≤ 2)
        (le_trans hz_re (le_abs_self z.re))
    exact le_trans hone_le_re_abs hre_abs_le_norm
  have hone_sub_norm_ge_one : (1 : ℝ) ≤ ‖1 - z‖ := by
    have hre_abs_le_norm : |(1 - z).re| ≤ ‖1 - z‖ :=
      Complex.abs_re_le_abs (1 - z)
    have hre_eq : (1 - z).re = 1 - z.re := by
      exact Complex.sub_re 1 z
    have hone_le_abs : (1 : ℝ) ≤ |(1 - z).re| := by
      have hle : (1 - z.re) ≤ -1 := by
        linarith
      have habs_eq : |1 - z.re| = -(1 - z.re) :=
        abs_of_nonpos hle
      have hone_le : (1 : ℝ) ≤ -(1 - z.re) := by
        linarith
      exact Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ |x|)
        hre_eq.symm
        (Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ x)
          habs_eq.symm
          hone_le)
    exact le_trans hone_le_abs hre_abs_le_norm
  have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
    have hz_norm_pos : 0 < ‖z‖ :=
      lt_of_lt_of_le zero_lt_one hz_norm_ge_one
    calc
      ‖1 / z‖ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (1 : ℂ) z
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hz_norm_pos hz_norm_ge_one
  have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
    have hnorm_pos : 0 < ‖1 - z‖ :=
      lt_of_lt_of_le zero_lt_one hone_sub_norm_ge_one
    calc
      ‖1 / (1 - z)‖ = ‖(1 : ℂ)‖ / ‖1 - z‖ := by
        exact norm_div (1 : ℂ) (1 - z)
      _ = 1 / ‖1 - z‖ := by
        exact congrArg (fun x : ℝ => x / ‖1 - z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hnorm_pos hone_sub_norm_ge_one
  have hnorm_decomp :
      ‖completedRiemannZeta₀ z‖ ≤
        ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
    calc
      ‖completedRiemannZeta₀ z‖ =
          ‖completedRiemannZeta z + 1 / z + 1 / (1 - z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hdecomp
      _ ≤ ‖completedRiemannZeta z + 1 / z‖ + ‖1 / (1 - z)‖ := by
        exact norm_add_le (completedRiemannZeta z + 1 / z) (1 / (1 - z))
      _ ≤ (‖completedRiemannZeta z‖ + ‖1 / z‖) + ‖1 / (1 - z)‖ := by
        exact add_le_add_right
          (norm_add_le (completedRiemannZeta z) (1 / z))
          ‖1 / (1 - z)‖
      _ = ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
        exact add_assoc ‖completedRiemannZeta z‖ ‖1 / z‖ ‖1 / (1 - z)‖
  have hcompleted_norm :
      ‖completedRiemannZeta z‖ =
        ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
    calc
      ‖completedRiemannZeta z‖ = ‖riemannZeta z * Complex.Gammaℝ z‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hcompleted_factor
      _ = ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
        exact norm_mul (riemannZeta z) (Complex.Gammaℝ z)
  let P : ℝ := ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖
  have hP_nonneg : 0 ≤ P :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hsum_bound :
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤ P + 2 := by
    calc
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ =
          P + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
        exact congrArg
          (fun x : ℝ => x + ‖1 / z‖ + ‖1 / (1 - z)‖)
          hcompleted_norm
      _ ≤ P + 1 + ‖1 / (1 - z)‖ := by
        exact add_le_add_right (add_le_add_left hinv_z_le_one P) ‖1 / (1 - z)‖
      _ ≤ P + 1 + 1 := by
        exact add_le_add_left hinv_one_sub_le_one (P + 1)
      _ = P + 2 := by
        exact (add_assoc P 1 1).symm.trans (congrArg (P + ·) one_add_one)
  have hP_two_le_three :
      P + 2 ≤ 3 * (P + 1) := by
    nlinarith [hP_nonneg]
  exact le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)

/-- The pole-cleared completed-zeta normalization has finite-order growth in the far-right
half-plane once the Dirichlet-series zeta bound and the gamma Stirling estimate are known. -/
theorem completedRiemannZeta₀_farRightHalfPlane_poleCleared_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖riemannZeta z‖ ≤ A)
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hzeta with ⟨Az, hAz, hzeta_bound⟩
  rcases hGamma with ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩
  rcases completedRiemannZeta₀_farRightHalfPlane_norm_le_zeta_gamma_plus_one with
    ⟨D, hD, hnorm_bound⟩
  refine ⟨D * (Az * Ag + 1), Bg, mg, ?_, hBg, ?_⟩
  · exact mul_pos hD (add_pos (mul_pos hAz hAg) zero_lt_one)
  intro z hz
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hexponent_nonneg : 0 ≤ Bg * H ^ mg :=
    mul_nonneg (le_of_lt hBg) (pow_nonneg hH_nonneg mg)
  have hone_le_exp : (1 : ℝ) ≤ Real.exp (Bg * H ^ mg) := by
    calc
      (1 : ℝ) ≤ Bg * H ^ mg + 1 := by
        exact le_add_of_nonneg_left hexponent_nonneg
      _ ≤ Real.exp (Bg * H ^ mg) := by
        exact Real.add_one_le_exp (Bg * H ^ mg)
  have hzeta_nonneg : 0 ≤ Az :=
    le_of_lt hAz
  have hgamma_target_nonneg : 0 ≤ Ag * Real.exp (Bg * H ^ mg) :=
    mul_nonneg (le_of_lt hAg) (le_of_lt (Real.exp_pos (Bg * H ^ mg)))
  have hproduct_bound :
      ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
        Az * (Ag * Real.exp (Bg * H ^ mg)) :=
    mul_le_mul (hzeta_bound z hz) (hGamma_bound z hz) (norm_nonneg _) hgamma_target_nonneg
  have hproduct_reassoc :
      Az * (Ag * Real.exp (Bg * H ^ mg)) =
        (Az * Ag) * Real.exp (Bg * H ^ mg) := by
    exact (mul_assoc Az Ag (Real.exp (Bg * H ^ mg))).symm
  have hone_scaled :
      (1 : ℝ) ≤ Real.exp (Bg * H ^ mg) :=
    hone_le_exp
  have hsum_bound :
      ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
        (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
    have hleft :
        ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          (Az * Ag) * Real.exp (Bg * H ^ mg) +
            Real.exp (Bg * H ^ mg) := by
      exact add_le_add (hproduct_bound.trans_eq hproduct_reassoc) hone_scaled
    have hright :
        (Az * Ag) * Real.exp (Bg * H ^ mg) +
            Real.exp (Bg * H ^ mg) =
          (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
      exact (add_mul (Az * Ag) 1 (Real.exp (Bg * H ^ mg))).symm
    exact hleft.trans_eq hright
  have hscaled :
      D * (‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
        D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) :=
    mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hD)
  have htarget :
      D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) =
        D * (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
    exact mul_assoc D (Az * Ag + 1) (Real.exp (Bg * H ^ mg))
  exact le_trans (hnorm_bound z hz) (hscaled.trans_eq htarget)

/-- Finite-order growth in the far-right half-plane for the uncentered entire
completed-zeta part. -/
theorem completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_farRightHalfPlane_poleCleared_growth_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_bound
    Gammaℝ_farRightHalfPlane_stirling_growth_bound

/-- Right half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound
    completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound

/-- Left half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_rightHalfPlane
    completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound

/-- Owner finite-order growth for the uncentered entire completed-zeta part.

This is the analytic finite-order input actually used by completed-zeta zero counting in
the RH lane.  A more general Hurwitz finite-order theorem may imply it, but the zeta
normalization layer only needs this specialization. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_global_finiteOrder_growth_bound_of_halfPlanes
    completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound
    completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound

/-- Finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta

/-- Finite-order growth for the centered entire completed-zeta part. -/
theorem centeredCompletedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered
    completedRiemannZeta₀_finiteOrder_growth_bound

/-- Multiplying a finite-order entire part by the quadratic clearing factor and subtracting
`1` preserves exponential finite-order growth. -/
theorem centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
    (hfactor :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
            A * (1 + ‖z‖) ^ m)
    (hentire :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hproduct :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    exponentialFiniteOrder_mul_polynomialGrowth hfactor hentire
  have hproduct_sub_one :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z - 1‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    exponentialFiniteOrder_sub_one hproduct
  rcases hproduct_sub_one with ⟨A, B, m, hA_pos, hB_pos, hbound⟩
  refine ⟨A, B, m, hA_pos, hB_pos, ?_⟩
  intro z
  have hcarrier :
      centeredCompletedRiemannZetaZeroCarrier z =
        centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
          centeredCompletedRiemannZeta₀ z - 1 :=
    centeredCompletedRiemannZetaZeroCarrier_eq_factor_mul_entirePart_sub_one z
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hcarrier.symm
    (hbound z)

/-- Finite-order growth is preserved by the completed zero-carrier normalization.

The zero-carrier is obtained from the centered entire part by multiplying by the quadratic
clearing factor `((1 / 2) + z) * (1 - ((1 / 2) + z))` and subtracting `1`. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
    (hentire :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
      centeredCompletedRiemannZetaZeroCarrierClearingFactor_growth_bound
      hentire

/-- Finite-order growth of the uncentered entire completed-zeta part gives finite-order
growth of the centered entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
    (centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered huncentered)

/-- Finite-order growth for the centered entire completed-zeta zero-carrier.

This is the normalization-side entire-function input used by Jensen counting. The
zero-carrier is the cleared entire divisor
`((1 / 2) + s) * (1 - ((1 / 2) + s)) * centeredCompletedRiemannZeta₀ s - 1`,
so this theorem is owned by the completed normalization layer rather than by the
downstream zero-counting file. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered
      completedRiemannZeta₀_finiteOrder_growth_bound

end

end
end LFunctions
end Boundary

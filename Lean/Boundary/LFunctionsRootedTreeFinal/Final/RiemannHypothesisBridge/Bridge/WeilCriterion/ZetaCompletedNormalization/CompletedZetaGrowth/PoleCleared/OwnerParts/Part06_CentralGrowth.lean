import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part02_SelfReflectionGrowth

/-!
# Pole-cleared zeta global and right-strip growth
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
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz0 hz2 hzim =>
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
              exact Eq.subst
                (motive := fun value : ℝ => value ≤
                  C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)))
                (mul_one C)
                (mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos))
            le_trans hraw hC_le_target⟩

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
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_boundary_envelopes_by_damping
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- The exact PL input package for the central-strip vertical tail.

The left edge is the completed-functional-equation/Gamma-Stirling estimate; the
right edge is the Dirichlet-series/Euler-Maclaurin estimate; the interior
admissible growth is the finite-order zeta input already isolated above. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
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
  exact
    ⟨poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl,
      hfinite,
      match poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound
          hbranch with
      | ⟨A, B, m, hA, hB, hleft⟩ =>
          ⟨A, B, m, hA, hB,
            fun z hz_re hz_im =>
              hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

theorem poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary with
  | ⟨hhol, hfinite, hleft, hright⟩ =>
      poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
        hhol hfinite hleft hright hcompactBoundary

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
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz0 hz2 hcompact_im)
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
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Central compact-strip finite-order growth for the pole-cleared zeta factor.

This is the local boundedness part of the global finite-order theorem.  The
removable value at `1` is already built into `poleClearedRiemannZeta`; on the
closed strip `0 ≤ Re z ≤ 2`, compact/local boundedness gives an ordinary
finite-order envelope with fixed constants; cf. Boas, Ch. 1. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary :
      ∃ C : ℝ,
        0 < C ∧
        (∀ z : ℂ,
          z.re = 0 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C) ∧
        (∀ z : ℂ,
          z.re = 2 →
          ¬ 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤ C)) :
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
      (poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

end
end LFunctions
end Boundary

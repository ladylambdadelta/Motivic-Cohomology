import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part07_GlobalAssembly

/-!
# Pole-cleared zeta right-critical-strip growth
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Ordinary finite-order growth on the full right critical strip implies the
subcritical double-exponential admissible-growth envelope used by strip PL. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 2 zero_lt_two hordinary

/-- The exact remaining half-strip theorem closes the right-critical
admissible-growth owner together with the existing Euler-Maclaurin
`1 ≤ Re s ≤ 2` finite-order estimate. -/
theorem poleClearedRightCriticalStripAdmissibleGrowth_of_zeroOneOrdinaryFiniteOrder
    (hzeroOne : PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
      (poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_of_zeroOne_and_oneTwo
        hzeroOne
        poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation)

/-- Owner package: ordinary finite-order growth on the reflected half-strip
`0 ≤ Re s ≤ 1` for the pole-cleared zeta factor.

The unresolved analytic content has been peeled into
`poleClearedRiemannZeta_zero_one_strip_verticalTail_growth_ownerFunctionalEquationNoncircular`.
This theorem only supplies the already-owned Binet/Stirling and boundary
packages, then patches the compact core with that vertical-tail estimate. -/
theorem poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_nonCircular
      hbranch
      boundaryLineOneAbelPartialMajorant_from_realParam
      poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
      (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
        boundaryLineOneAbelPartialMajorant_from_realParam)
      poleClearedRightCriticalStripCompactBoundaryBound_from_compact
      hreflected

/-- Owner package for admissible growth in the right critical strip, assembled
from the reflected half-strip finite-order theorem and the already proved
Euler-Maclaurin finite-order estimate on `1 ≤ Re s ≤ 2`. -/
theorem poleClearedRightCriticalStripAdmissibleGrowth_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hreflected :
      PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope) :
    PoleClearedRightCriticalStripAdmissibleGrowth := by
  exact
    poleClearedRightCriticalStripAdmissibleGrowth_of_zeroOneOrdinaryFiniteOrder
      (poleClearedRiemannZeta_zero_one_strip_ordinaryFiniteOrder_growth_owner
        hbranch hreflected)

/-- Standard finite-order theorem for the pole-cleared Riemann zeta factor in the right
critical strip.

This is the exact zeta finite-order theorem needed by the strip damping argument.  Its
analytic proof is now factored into the ordinary finite-order theorem on
`0 ≤ Re s ≤ 2`, followed by the generic finite-order-to-admissible conversion. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    poleClearedRiemannZeta_rightCriticalStrip_admissible_growth_of_ordinaryFiniteOrder
      hordinary

/-- Standard zeta finite-order input for the pole-cleared factor inside the right
critical strip.

This is only name transport from the exact standard finite-order theorem for the
pole-cleared Riemann zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

/-- Deep zeta-growth owner primitive for the pole-cleared factor inside the right
critical strip.

The analytic content is isolated in
`poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth`;
this owner primitive is only the public name consumed by the strip
Phragmen-Lindelöf layer. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

/-- Interior admissible finite-order envelope for the pole-cleared zeta factor in the
right critical strip.

This is the damping-side zeta-growth root consumed by the generic strip
Phragmen-Lindelöf theorem.  It is a thin wrapper over the standard finite-order theorem
for the pole-cleared Riemann zeta factor in this bounded-width strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive
    hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary

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
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
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

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This theorem is now reduced to the immediate strip inputs for the pole-cleared
normalization: strip holomorphy, admissible strip growth, and the two vertical-edge
finite-order estimates. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) :=
  match poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound hbranch with
  | ⟨hleft, hright⟩ =>
      poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
        poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl
        (poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
          hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary)
        (match hleft with
        | ⟨A, B, m, hA, hB, hleftBound⟩ =>
            ⟨A, B, m, hA, hB,
              fun z hz_re hz_im =>
                hleftBound z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
        hright
        hcompactBoundary

/-- Vertical-tail pole-cleared zeta strip estimate.

This is the final zeta-specific consumer of the generic strip Phragmen-Lindelöf
pillar `strip_finite_order_growth_of_boundary_envelopes_by_damping`.
The remaining zeta inputs are exactly the classical ones: holomorphicity after pole
clearing, right-boundary growth from the Dirichlet-series estimate, and left-boundary
growth from the functional equation/completed normalization with Gamma control. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun z hz0 hz2 hzim =>
            have hz_ne_one : z ≠ 1 := fun hz_eq =>
              have him_one : z.im = (1 : ℂ).im :=
                congrArg Complex.im hz_eq
              have him_zero : z.im = 0 :=
                Eq.trans him_one Complex.one_im
              have hnorm_im_zero : ‖z.im‖ = 0 := by
                exact (congrArg norm him_zero).trans norm_zero
              have hle_zero : (1 : ℝ) ≤ 0 :=
                hzim.trans_eq hnorm_im_zero
              (not_le_of_gt zero_lt_one) hle_zero
            have hpc :
                poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
              poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
            Eq.subst
              (motive := fun w : ℂ =>
                ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
              hpc
              (hbound z hz0 hz2 hzim)⟩

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

/-- Pole-cleared finite-order growth for `ζ` in the bounded-width right critical strip. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hordinary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
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
    (riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hordinary hpartialLeft hcompactBoundary)

end
end LFunctions
end Boundary

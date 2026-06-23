import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part01

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- At a scheduled height, the contour integral is the finite residue-window sum plus the
named finite-rectangle residue equality error.

This is only the bookkeeping identity for the named error term; the analytic boundary
avoidance hypothesis belongs to the finite residue theorem below. -/
theorem explicitFormulaScheduledRectangleContourIntegral_eq_residueSum_add_error
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaContourIntegral f
        (F.rectangle (h.height_schedule.height u)) =
      explicitFormulaScheduledRectangleResidueSum f F h u +
        explicitFormulaScheduledRectangleResidueEqualityError f F h u := by
  let T : ℝ := h.height_schedule.height u
  have hbase :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T +
          explicitFormulaFamilyResidueWindowError f F T :=
    zetaCompletedExplicitFormulaContourIntegral_eq_heightWindowResidueSum_add_error f F T
  have hpointwise :
      explicitFormulaScheduledRectangleResidueSum f F h u =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
    rfl
  have herror :
      explicitFormulaScheduledRectangleResidueEqualityError f F h u =
        explicitFormulaFamilyResidueWindowError f F T := by
    rfl
  exact Eq.trans hbase
    (congrArg₂ (fun a b : ℂ => a + b) hpointwise.symm herror.symm)

/-- The package schedule gives boundary avoidance at the chosen scheduled rectangle. -/
theorem explicitFormulaScheduledRectangle_avoidsSingularBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    explicitFormulaContourFamilyAvoidsSingularBoundary F
      (h.height_schedule.height u) :=
  h.height_schedule.avoids_boundary u

/-- At a scheduled height, every boundary point is off the completed contour-integrand
singular set. -/
theorem completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    z ∉ completedZetaContourIntegrandSingularSet := by
  exact
    completedZetaContourIntegrand_not_mem_singularSet_of_avoidsBoundary
      F (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- The completed contour integrand is regular at every boundary point of the chosen
scheduled rectangle. -/
theorem completedZetaContourIntegrand_regularAt_scheduledBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) {z : ℂ}
    (hboundary :
      z ∈ explicitFormulaContourFamilyBoundary F
        (h.height_schedule.height u)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_regularAt_boundary_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
      hboundary

/-- Transport wrapper for an already-proved project-contour finite residue equality.

This theorem does not assert that boundary avoidance alone proves the project-normalized
zero-window equality; the equality is an explicit input.  The analytic Cauchy-residue
owner theorem in this file is tangent-normalized and has the pole-corrected target. -/
theorem explicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerFiniteRectangleResidueTheorem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T)
    (hfinite :
      zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
        explicitFormulaCompletedZeroHeightWindowResidueSum f T) :
    zetaCompletedExplicitFormulaContourIntegral f (F.rectangle T) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  exact
    zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_of_finiteRectangleResidueTheorem
      f F h T havoid hfinite

/-- Boundary regularity for the pointwise avoided rectangle used by finite Cauchy residues. -/
theorem explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (T : ℝ)
    (havoid : explicitFormulaContourFamilyAvoidsSingularBoundary F T) :
    ∀ z : ℂ,
      z ∈ explicitFormulaContourFamilyBoundary F T →
        ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
          DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z := by
  exact
    completedZetaContourIntegrand_regularAt_all_boundary_points_of_avoidsBoundary
      f F h T havoid

/-- The completed-zero window used by the residue theorem is exactly the centered-height
window in finite-set form. -/
theorem explicitFormulaCompletedZeroHeightWindow_mem_iff_centeredHeight
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
      ρ ∈ completedZerosInCenteredHeightBall T := by
  exact mem_explicitFormulaCompletedZeroHeightWindow_iff T ρ

/-- Local completed-zero residues are the summands of the named residue window. -/
theorem explicitFormulaRectangle_completedZeroResidueWindow_summand
    (f : ZetaAdmissibleFunction) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) =
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ) := by
  rfl

/-- Finite residue-sum transport from the explicit completed-zero window sum to the named
height-window residue sum. -/
theorem explicitFormulaRectangle_completedZeroResidueWindowSum_eq_heightWindowResidueSum
    (f : ZetaAdmissibleFunction) (T : ℝ) :
    (∑ ρ in explicitFormulaCompletedZeroHeightWindow T,
      explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)) =
      explicitFormulaCompletedZeroHeightWindowResidueSum f T := by
  rfl

/-- Membership in the completed-zero height window unfolds to the centered-height cutoff. -/
theorem explicitFormulaCompletedZeroHeightWindow_mem_iff_centeredHeight_le
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
      zetaCompletedZeroCenteredHeight ρ ≤ T := by
  exact mem_explicitFormulaCompletedZeroHeightWindow_iff T ρ

/-- A completed zero in the finite height window has its centered height bounded by `T`. -/
theorem explicitFormulaCompletedZeroHeightWindow_centeredHeight_le
    (T : ℝ) {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T) :
    zetaCompletedZeroCenteredHeight ρ ≤ T := by
  exact
    (explicitFormulaCompletedZeroHeightWindow_mem_iff_centeredHeight_le T ρ).mp hρ

/-- A centered-height bound places a completed zero in the finite height window. -/
theorem explicitFormulaCompletedZeroHeightWindow_mem_of_centeredHeight_le
    (T : ℝ) {ρ : {ρ : ℂ // ZetaCompletedZero ρ}}
    (hρ : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    ρ ∈ explicitFormulaCompletedZeroHeightWindow T := by
  exact
    (explicitFormulaCompletedZeroHeightWindow_mem_iff_centeredHeight_le T ρ).mpr hρ

/-- Exact coordinate blocker for the forward residue-window classification: completed
zero-side coordinates must be transported to the contour-integrand singular set. -/
theorem explicitFormulaCompletedZero_mem_contourIntegrandSingularSet_ownerGap :
    ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
      completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet := by
  intro ρ
  have hne_zero : completedZeroResidueCoordinate ρ ≠ 0 := by
    intro hzero
    have hρneg : (ρ : ℂ) = -(1 / 2 : ℂ) := by
      calc
        (ρ : ℂ) = completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
          unfold completedZeroResidueCoordinate
          exact (add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)).symm
        _ = 0 - (1 / 2 : ℂ) := by
          exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hzero
        _ = -(1 / 2 : ℂ) := by
          exact zero_sub (1 / 2 : ℂ)
    exact zetaCompletedZero_ne_negHalf ρ hρneg
  have hne_one : completedZeroResidueCoordinate ρ ≠ 1 := by
    intro hone
    have hρpos : (ρ : ℂ) = (1 / 2 : ℂ) := by
      calc
        (ρ : ℂ) = completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
          unfold completedZeroResidueCoordinate
          exact (add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)).symm
        _ = 1 - (1 / 2 : ℂ) := by
          exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hone
        _ = (1 / 2 : ℂ) := by
          exact sub_half (1 : ℂ)
    exact zetaCompletedZero_ne_posHalf ρ hρpos
  have hzeta :
      completedRiemannZeta (completedZeroResidueCoordinate ρ) = 0 := by
    calc
      completedRiemannZeta (completedZeroResidueCoordinate ρ) =
          completedRiemannZeta ((1 / 2 : ℂ) + (ρ : ℂ)) := by
        rfl
      _ = centeredCompletedRiemannZeta (ρ : ℂ) := by
        exact (centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift (ρ : ℂ)).symm
      _ = centeredCompletedRiemannZetaFunction (ρ : ℂ) := by
        exact (centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm
      _ = 0 := by
        exact zetaCompletedZero_zero ρ
  exact Or.inr (Or.inr ⟨hne_zero, hne_one, hzeta⟩)

/-- Generic local analytic residue theorem for the logarithmic derivative at a zero of
finite analytic order.

This is the analytic owner leaf for the finite-rectangle local residue computation:
if an analytic germ has a zero of finite order and is not locally identically zero, then
`(z - z₀) * f'/f` tends to the analytic order. -/
theorem analyticAt_logDeriv_residue_tendsto_order_ownerGap
    (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : AnalyticAt ℂ f z₀)
    (hzero : f z₀ = 0)
    (hnot : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    Tendsto
      (fun z : ℂ => (z - z₀) * logDeriv f z)
      (𝓝[≠] z₀)
      (𝓝 (hf.order.toNat : ℂ)) := by
  have hntop : hf.order ≠ ⊤ := fun h => hnot (hf.order_eq_top_iff.mp h)
  set n : ℕ := hf.order.toNat with hn_def
  have horder : hf.order = (n : ℕ∞) := (ENat.coe_toNat hntop).symm
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := (hf.order_eq_nat_iff n).mp horder
  have hg_ne_near : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 :=
    hg_an.continuousAt.eventually_ne hg_ne
  have hfg_nhds : ∀ᶠ z in 𝓝 z₀, ∀ᶠ w in 𝓝 z, f w = (w - z₀) ^ n • g w :=
    hfg.eventually_nhds
  obtain ⟨s, hs_mem, hs_an⟩ := hg_an.exists_mem_nhds_analyticOnNhd
  have hderiv_cont : ContinuousAt (deriv g) z₀ :=
    (hs_an.deriv z₀ (mem_of_mem_nhds hs_mem)).continuousAt
  have hlogDeriv_g_cont : ContinuousAt (logDeriv g) z₀ :=
    hderiv_cont.div hg_an.continuousAt hg_ne
  have hg_diff_near : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z :=
    eventually_of_mem hs_mem (fun z hz => (hs_an z hz).differentiableAt)
  have key :
      ∀ᶠ z in 𝓝[≠] z₀,
        (z - z₀) * logDeriv f z = (n : ℂ) + (z - z₀) * logDeriv g z := by
    have h2 : ∀ᶠ z in 𝓝[≠] z₀, ∀ᶠ w in 𝓝 z, f w = (w - z₀) ^ n • g w :=
      hfg_nhds.filter_mono nhdsWithin_le_nhds
    have h3 : ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 :=
      hg_ne_near.filter_mono nhdsWithin_le_nhds
    have h4 : ∀ᶠ z in 𝓝[≠] z₀, DifferentiableAt ℂ g z :=
      hg_diff_near.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, h2, h3, h4] with z hzne hzeq hgz hgdiff
    have ha : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
    have hloc : f =ᶠ[𝓝 z] fun w : ℂ => (w - z₀) ^ n * g w := by
      filter_upwards [hzeq] with w hw
      exact hw.trans (smul_eq_mul ℂ)
    have hfz : f z = (z - z₀) ^ n * g z := hloc.self_of_nhds
    have hdfz : deriv f z = deriv (fun w : ℂ => (w - z₀) ^ n * g w) z := hloc.deriv_eq
    have hlogf : logDeriv f z = logDeriv (fun w : ℂ => (w - z₀) ^ n * g w) z :=
      (logDeriv_apply f z).trans
        ((congrArg₂ (· / ·) hdfz hfz).trans (logDeriv_apply _ z).symm)
    have hsub_diff : DifferentiableAt ℂ (fun w : ℂ => w - z₀) z :=
      differentiableAt_id'.sub_const z₀
    have hp_ne : (fun w : ℂ => (w - z₀) ^ n) z ≠ 0 := pow_ne_zero n ha
    have hp_diff : DifferentiableAt ℂ (fun w : ℂ => (w - z₀) ^ n) z := hsub_diff.pow n
    have hmul : logDeriv (fun w : ℂ => (w - z₀) ^ n * g w) z
        = logDeriv (fun w : ℂ => (w - z₀) ^ n) z + logDeriv g z :=
      logDeriv_mul z hp_ne hgz hp_diff hgdiff
    have hHD : HasDerivAt (fun w : ℂ => w - z₀) 1 z :=
      (hasDerivAt_id z).sub_const z₀
    have hsub_deriv : deriv (fun w : ℂ => w - z₀) z = 1 := hHD.deriv
    have hsub_log : logDeriv (fun w : ℂ => w - z₀) z = 1 / (z - z₀) :=
      (logDeriv_apply _ z).trans (congrArg (· / (z - z₀)) hsub_deriv)
    have hpow_log : logDeriv (fun w : ℂ => (w - z₀) ^ n) z = (n : ℂ) / (z - z₀) :=
      calc logDeriv (fun w : ℂ => (w - z₀) ^ n) z
          = (n : ℂ) * logDeriv (fun w : ℂ => w - z₀) z := logDeriv_fun_pow hsub_diff n
        _ = (n : ℂ) * (1 / (z - z₀)) := congrArg (fun t : ℂ => (n : ℂ) * t) hsub_log
        _ = (n : ℂ) / (z - z₀) := mul_one_div (n : ℂ) (z - z₀)
    have hlogf2 : logDeriv f z = (n : ℂ) / (z - z₀) + logDeriv g z :=
      hlogf.trans (hmul.trans (congrArg (· + logDeriv g z) hpow_log))
    have hcancel : (z - z₀) * ((n : ℂ) / (z - z₀)) = (n : ℂ) :=
      (mul_comm (z - z₀) ((n : ℂ) / (z - z₀))).trans (div_mul_cancel₀ (n : ℂ) ha)
    calc (z - z₀) * logDeriv f z
        = (z - z₀) * ((n : ℂ) / (z - z₀) + logDeriv g z) :=
          congrArg (fun t : ℂ => (z - z₀) * t) hlogf2
      _ = (z - z₀) * ((n : ℂ) / (z - z₀)) + (z - z₀) * logDeriv g z :=
          mul_add (z - z₀) ((n : ℂ) / (z - z₀)) (logDeriv g z)
      _ = (n : ℂ) + (z - z₀) * logDeriv g z :=
          congrArg (· + (z - z₀) * logDeriv g z) hcancel
  have hsub_tendsto : Tendsto (fun z : ℂ => z - z₀) (𝓝[≠] z₀) (𝓝 (0 : ℂ)) := by
    have h0 : Tendsto (fun z : ℂ => z - z₀) (𝓝 z₀) (𝓝 (z₀ - z₀)) :=
      (continuous_id.sub continuous_const).tendsto z₀
    have e : z₀ - z₀ = (0 : ℂ) := sub_self z₀
    exact (e ▸ h0).mono_left nhdsWithin_le_nhds
  have hg_tendsto : Tendsto (logDeriv g) (𝓝[≠] z₀) (𝓝 (logDeriv g z₀)) :=
    hlogDeriv_g_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hmul_tendsto :
      Tendsto (fun z : ℂ => (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 (0 : ℂ)) := by
    have hm : Tendsto (fun z : ℂ => (z - z₀) * logDeriv g z) (𝓝[≠] z₀)
        (𝓝 ((0 : ℂ) * logDeriv g z₀)) := hsub_tendsto.mul hg_tendsto
    have e : (0 : ℂ) * logDeriv g z₀ = 0 := zero_mul _
    exact e ▸ hm
  have hfinal :
      Tendsto (fun z : ℂ => (n : ℂ) + (z - z₀) * logDeriv g z) (𝓝[≠] z₀) (𝓝 (n : ℂ)) := by
    have hadd : Tendsto (fun z : ℂ => (n : ℂ) + (z - z₀) * logDeriv g z) (𝓝[≠] z₀)
        (𝓝 ((n : ℂ) + 0)) := tendsto_const_nhds.add hmul_tendsto
    have hN : (𝓝 ((n : ℂ) + 0)) = 𝓝 (n : ℂ) := congrArg 𝓝 (add_zero (n : ℂ))
    exact hN ▸ hadd
  exact hfinal.congr' (key.mono (fun z h => h.symm))

/-- The residue coordinate attached to a completed zero is not the pole at `0`. -/
theorem completedZeroResidueCoordinate_ne_zero
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroResidueCoordinate ρ ≠ 0 := by
  intro hzero
  have hρneg : (ρ : ℂ) = -(1 / 2 : ℂ) := by
    calc
      (ρ : ℂ) = completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
        unfold completedZeroResidueCoordinate
        exact (add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)).symm
      _ = 0 - (1 / 2 : ℂ) := by
        exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hzero
      _ = -(1 / 2 : ℂ) := by
        exact zero_sub (1 / 2 : ℂ)
  exact zetaCompletedZero_ne_negHalf ρ hρneg

/-- The residue coordinate attached to a completed zero is not the pole at `1`. -/
theorem completedZeroResidueCoordinate_ne_one
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroResidueCoordinate ρ ≠ 1 := by
  intro hone
  have hρpos : (ρ : ℂ) = (1 / 2 : ℂ) := by
    calc
      (ρ : ℂ) = completedZeroResidueCoordinate ρ - (1 / 2 : ℂ) := by
        unfold completedZeroResidueCoordinate
        exact (add_sub_cancel_left (1 / 2 : ℂ) (ρ : ℂ)).symm
      _ = 1 - (1 / 2 : ℂ) := by
        exact congrArg (fun z : ℂ => z - (1 / 2 : ℂ)) hone
      _ = (1 / 2 : ℂ) := by
        exact sub_half (1 : ℂ)
  exact zetaCompletedZero_ne_posHalf ρ hρpos

/-- A completed zero is a zero of the uncentered completed zeta at its residue
coordinate. -/
theorem completedRiemannZeta_zero_at_completedZeroResidueCoordinate
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedRiemannZeta (completedZeroResidueCoordinate ρ) = 0 := by
  calc
    completedRiemannZeta (completedZeroResidueCoordinate ρ) =
        completedRiemannZeta ((1 / 2 : ℂ) + (ρ : ℂ)) := by
      rfl
    _ = centeredCompletedRiemannZeta (ρ : ℂ) := by
      exact (centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift (ρ : ℂ)).symm
    _ = centeredCompletedRiemannZetaFunction (ρ : ℂ) := by
      exact (centeredCompletedRiemannZetaFunction_eq (ρ : ℂ)).symm
    _ = 0 := by
      exact zetaCompletedZero_zero ρ

/-- The uncentered completed zeta is analytic at the residue coordinate attached to a
completed-zero residue window. -/
theorem completedRiemannZeta_analyticAt_completedZeroResidueCoordinate_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    AnalyticAt ℂ completedRiemannZeta (completedZeroResidueCoordinate ρ) := by
  have hne0 : ∀ᶠ y in 𝓝 (completedZeroResidueCoordinate ρ), y ≠ 0 :=
    eventually_ne_nhds (completedZeroResidueCoordinate_ne_zero ρ)
  have hne1 : ∀ᶠ y in 𝓝 (completedZeroResidueCoordinate ρ), y ≠ 1 :=
    eventually_ne_nhds (completedZeroResidueCoordinate_ne_one ρ)
  have hboth : ∀ᶠ y in 𝓝 (completedZeroResidueCoordinate ρ), y ≠ 0 ∧ y ≠ 1 :=
    hne0.and hne1
  have hdiff :
      ∀ᶠ y in 𝓝 (completedZeroResidueCoordinate ρ),
        DifferentiableAt ℂ completedRiemannZeta y :=
    hboth.mono
      (fun y hy => differentiableAt_completedZeta hy.1 hy.2)
  exact Complex.analyticAt_iff_eventually_differentiableAt.2 hdiff

/-- Coordinate transport from the completed-zero datum to an uncentered completed-zeta zero.

This is the precise local coordinate obligation exposed by the finite-rectangle residue
surface: `ZetaCompletedZero ρ` is defined through the centered function, while the
rectangle residue theorem uses `completedRiemannZeta` at `1 / 2 + ρ`. -/
theorem completedRiemannZeta_zero_at_completedZeroResidueCoordinate_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedRiemannZeta (completedZeroResidueCoordinate ρ) = 0 := by
  exact completedRiemannZeta_zero_at_completedZeroResidueCoordinate ρ

/-- The completed-zeta germ is not locally identically zero at the residue coordinate
attached to a completed-zero datum. -/
theorem completedRiemannZeta_not_eventually_zero_at_completedZeroResidueCoordinate_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ¬ ∀ᶠ z in 𝓝 (completedZeroResidueCoordinate ρ), completedRiemannZeta z = 0 := by
  exact
    completedRiemannZeta_not_eventually_zero
      (completedZeroResidueCoordinate ρ)
      (completedZeroResidueCoordinate_ne_zero ρ)
      (completedZeroResidueCoordinate_ne_one ρ)

/-- The local order transport from the uncentered completed zeta at `1 / 2 + ρ` to the
centered zero carrier at `ρ`. This is the analytic translation/unit-factor leaf exposed by
the finite-rectangle residue coordinate normalization. -/
theorem completedRiemannZeta_order_toNat_eq_centeredCarrier_order_at_completedZeroResidueCoordinate_from_shiftUnit_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hf : AnalyticAt ℂ completedRiemannZeta (completedZeroResidueCoordinate ρ)) :
    hf.order.toNat =
      (centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)).order.toNat := by
  let center : ℂ := (ρ : ℂ)
  let shift : ℂ := (1 / 2 : ℂ)
  let centered : ℂ → ℂ := centeredCompletedRiemannZetaFunction
  let carrier : ℂ → ℂ := centeredCompletedRiemannZetaZeroCarrier
  let denom : ℂ → ℂ := centeredCompletedRiemannZetaDenominator
  let shiftedCentered : ℂ → ℂ := fun s : ℂ => centered (s - shift)
  let shiftedCarrier : ℂ → ℂ := fun s : ℂ => carrier (s - shift)
  let shiftedDenom : ℂ → ℂ := fun s : ℂ => denom (s - shift)
  have hcoord :
      completedZeroResidueCoordinate ρ = shift + center := by
    rfl
  have hshift_center :
      completedZeroResidueCoordinate ρ - shift = center := by
    exact completedZeroResidueCoordinate_sub_half ρ
  have hcompleted_shift :
      completedRiemannZeta =ᶠ[𝓝 (completedZeroResidueCoordinate ρ)] shiftedCentered := by
    filter_upwards [] with s
    have hhalf_sub : shift + (s - shift) = s := by
      calc
        shift + (s - shift) = shift + (s + -shift) := by
          exact congrArg (fun u : ℂ => shift + u) (sub_eq_add_neg s shift)
        _ = (shift + s) + -shift := by
          exact (add_assoc shift s (-shift)).symm
        _ = (s + shift) + -shift := by
          exact congrArg (fun u : ℂ => u + -shift) (add_comm shift s)
        _ = s + (shift + -shift) := by
          exact add_assoc s shift (-shift)
        _ = s + 0 := by
          exact congrArg (fun u : ℂ => s + u) (add_neg_cancel shift)
        _ = s := by
          exact add_zero s
    calc
      completedRiemannZeta s =
          completedRiemannZeta (shift + (s - shift)) := by
        exact congrArg completedRiemannZeta hhalf_sub.symm
      _ = centeredCompletedRiemannZeta (s - shift) := by
        exact (centeredCompletedRiemannZeta_eq_completedRiemannZeta_shift (s - shift)).symm
      _ = shiftedCentered s := by
        exact (centeredCompletedRiemannZetaFunction_eq (s - shift)).symm
  have hshiftedCentered_analytic :
      AnalyticAt ℂ shiftedCentered (completedZeroResidueCoordinate ρ) :=
    hf.congr hcompleted_shift
  have hcompleted_order_shiftedCentered :
      hf.order = hshiftedCentered_analytic.order :=
    analyticAt_order_eq_of_eventuallyEq
      hf
      hshiftedCentered_analytic
      hcompleted_shift
  have hcarrier_at_center :
      AnalyticAt ℂ carrier center :=
    centeredCompletedRiemannZetaZeroCarrier_analyticAt center
  let hcoord_id :
      AnalyticAt ℂ (fun s : ℂ => s) (completedZeroResidueCoordinate ρ) :=
    analyticAt_id
  let hcoord_shift_const :
      AnalyticAt ℂ (fun _ : ℂ => shift) (completedZeroResidueCoordinate ρ) :=
    analyticAt_const
  let hcoord_sub_shift :
      AnalyticAt ℂ (fun s : ℂ => s - shift) (completedZeroResidueCoordinate ρ) :=
    hcoord_id.sub hcoord_shift_const
  have hshiftedCarrier_analytic :
      AnalyticAt ℂ shiftedCarrier (completedZeroResidueCoordinate ρ) :=
  hcarrier_at_center.comp_of_eq
      hcoord_sub_shift
      hshift_center
  have hshiftedDenom_analytic :
      AnalyticAt ℂ shiftedDenom (completedZeroResidueCoordinate ρ) := by
    have hdenom_at_center :
        AnalyticAt ℂ denom center := by
      let hcenter_id : AnalyticAt ℂ (fun s : ℂ => s) center :=
        analyticAt_id
      let hcenter_const_half : AnalyticAt ℂ (fun _ : ℂ => shift) center :=
        analyticAt_const
      let hcenter_const_one : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) center :=
        analyticAt_const
      unfold denom centeredCompletedRiemannZetaDenominator
      exact
        (hcenter_const_half.add hcenter_id).mul
          (hcenter_const_one.sub
            (hcenter_const_half.add hcenter_id))
    exact hdenom_at_center.comp_of_eq
      hcoord_sub_shift
      hshift_center
  have hshiftedDenom_ne :
      shiftedDenom (completedZeroResidueCoordinate ρ) ≠ 0 := by
    have hleft_ne : shift + center ≠ 0 :=
      centeredShift_leftDenominator_ne_zero_of_ne_negHalf
        (zetaCompletedZero_ne_negHalf ρ)
    have hright_ne : 1 - (shift + center) ≠ 0 :=
      centeredShift_rightDenominator_ne_zero_of_ne_posHalf
        (zetaCompletedZero_ne_posHalf ρ)
    have hdenom_ne : denom center ≠ 0 :=
      centeredCompletedRiemannZetaDenominator_ne_zero hleft_ne hright_ne
    exact Eq.subst
      (motive := fun u : ℂ => denom u ≠ 0)
      hshift_center.symm
      hdenom_ne
  have hshiftedCarrier_model :
      shiftedCarrier =ᶠ[𝓝 (completedZeroResidueCoordinate ρ)]
        fun s : ℂ => shiftedDenom s * shiftedCentered s := by
    have hcore :
        carrier =ᶠ[𝓝 center] fun w : ℂ => denom w * centered w :=
      (centeredCompletedRiemannZetaZeroCarrier_eventuallyEq_denominator_mul_core ρ).mono
        (fun w hw => hw)
    have htend :
        Tendsto (fun s : ℂ => s - shift)
          (𝓝 (completedZeroResidueCoordinate ρ)) (𝓝 center) := by
      exact Eq.subst
        (motive := fun u : ℂ =>
          Tendsto (fun s : ℂ => s - shift)
            (𝓝 (completedZeroResidueCoordinate ρ)) (𝓝 u))
        hshift_center
        (continuous_id.sub continuous_const).continuousAt.tendsto
    exact htend.eventually hcore
  have hshiftedCarrier_order_centered :
      hshiftedCarrier_analytic.order = hshiftedCentered_analytic.order :=
    analyticAt_order_eq_of_eventuallyEq_mul_left
      hshiftedCarrier_analytic
      hshiftedCentered_analytic
      hshiftedDenom_analytic
      hshiftedDenom_ne
      hshiftedCarrier_model
  have hcarrier_translation :
      hcarrier_at_center.order = hshiftedCarrier_analytic.order := by
    let hcanonical :
        AnalyticAt ℂ shiftedCarrier (completedZeroResidueCoordinate ρ) :=
      hcarrier_at_center.comp_of_eq hcoord_sub_shift hshift_center
    have hraw : hcarrier_at_center.order = hcanonical.order :=
      Boundary.LFunctions.analyticAt_order_eq_comp_sub_const hcarrier_at_center
    have hproof : hcanonical.order = hshiftedCarrier_analytic.order :=
      congrArg
        (fun h : AnalyticAt ℂ shiftedCarrier (completedZeroResidueCoordinate ρ) => h.order)
        (Subsingleton.elim hcanonical hshiftedCarrier_analytic)
    exact hraw.trans hproof
  have horder :
      hf.order = hcarrier_at_center.order :=
    hcompleted_order_shiftedCentered.trans
      (hshiftedCarrier_order_centered.symm.trans hcarrier_translation.symm)
  exact congrArg ENat.toNat horder

/-- The local analytic order of the uncentered completed-zeta germ at the uncentered
residue coordinate is the named centered completed-zero multiplicity. This is the remaining
unit-factor order transport between the uncentered completed zeta and the centered cleared
zero-carrier. -/
theorem completedRiemannZeta_order_toNat_eq_centeredCarrier_order_at_completedZeroResidueCoordinate_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hf : AnalyticAt ℂ completedRiemannZeta (completedZeroResidueCoordinate ρ)) :
    hf.order.toNat =
      (centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)).order.toNat := by
  exact
    completedRiemannZeta_order_toNat_eq_centeredCarrier_order_at_completedZeroResidueCoordinate_from_shiftUnit_ownerGap
      ρ hf

/-- The local analytic order of the uncentered completed-zeta germ at the uncentered
residue coordinate is the named centered completed-zero multiplicity. -/
theorem completedRiemannZeta_order_toNat_eq_zetaZeroMultiplicity_at_completedZeroResidueCoordinate_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hf : AnalyticAt ℂ completedRiemannZeta (completedZeroResidueCoordinate ρ)) :
    hf.order.toNat = zetaZeroMultiplicity (ρ : ℂ) := by
  have hcarrier :
      hf.order.toNat =
        (centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)).order.toNat :=
    completedRiemannZeta_order_toNat_eq_centeredCarrier_order_at_completedZeroResidueCoordinate_ownerGap
      ρ hf
  have hmult :
      (centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)).order.toNat =
        zetaZeroMultiplicity (ρ : ℂ) := by
    calc
      (centeredCompletedRiemannZetaZeroCarrier_analyticAt (ρ : ℂ)).order.toNat =
          completedZetaZeroMultiplicity (ρ : ℂ) := by
        exact (completedZetaZeroMultiplicity_eq_carrier_order (ρ : ℂ)).symm
      _ = zetaZeroMultiplicity (ρ : ℂ) := by
        rfl
  exact Eq.trans hcarrier hmult

/-- At a completed-zero residue coordinate, the completed-zeta logarithmic derivative has
local residue equal to the completed-zero multiplicity. -/
theorem completedRiemannZeta_logDeriv_completedZero_residue_tendsto_ownerGap
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Tendsto
      (fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * logDeriv completedRiemannZeta z)
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (zetaZeroMultiplicity (ρ : ℂ) : ℂ)) := by
  let z₀ : ℂ := completedZeroResidueCoordinate ρ
  let hf : AnalyticAt ℂ completedRiemannZeta z₀ :=
    completedRiemannZeta_analyticAt_completedZeroResidueCoordinate_ownerGap ρ
  have hzero : completedRiemannZeta z₀ = 0 :=
    completedRiemannZeta_zero_at_completedZeroResidueCoordinate_ownerGap ρ
  have hnot : ¬ ∀ᶠ z in 𝓝 z₀, completedRiemannZeta z = 0 :=
    completedRiemannZeta_not_eventually_zero_at_completedZeroResidueCoordinate_ownerGap ρ
  have hlocal :
      Tendsto
        (fun z : ℂ => (z - z₀) * logDeriv completedRiemannZeta z)
        (𝓝[≠] z₀)
        (𝓝 (hf.order.toNat : ℂ)) :=
    analyticAt_logDeriv_residue_tendsto_order_ownerGap
      completedRiemannZeta z₀ hf hzero hnot
  have horder :
      hf.order.toNat = zetaZeroMultiplicity (ρ : ℂ) :=
    completedRiemannZeta_order_toNat_eq_zetaZeroMultiplicity_at_completedZeroResidueCoordinate_ownerGap
      ρ hf
  have htarget :
      (hf.order.toNat : ℂ) = (zetaZeroMultiplicity (ρ : ℂ) : ℂ) :=
    congrArg (fun n : ℕ => (n : ℂ)) horder
  exact
    Eq.subst
      (motive := fun a : ℂ =>
        Tendsto
          (fun z : ℂ => (z - z₀) * logDeriv completedRiemannZeta z)
          (𝓝[≠] z₀)
          (𝓝 a))
      htarget
      hlocal

/-- Multiplying the completed-zeta logarithmic-derivative residue by `-1` gives the
negative logarithmic-derivative residue. -/
theorem completedRiemannZeta_negLogDeriv_completedZero_residue_tendsto
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    Tendsto
      (fun z : ℂ => (z - completedZeroResidueCoordinate ρ) *
        (-logDeriv completedRiemannZeta z))
      (𝓝[≠] (completedZeroResidueCoordinate ρ))
      (𝓝 (-(zetaZeroMultiplicity (ρ : ℂ) : ℂ))) := by
  let m : ℂ := (zetaZeroMultiplicity (ρ : ℂ) : ℂ)
  let raw : ℂ → ℂ :=
    fun z : ℂ => (z - completedZeroResidueCoordinate ρ) * logDeriv completedRiemannZeta z
  let negRaw : ℂ → ℂ :=
    fun z : ℂ => (z - completedZeroResidueCoordinate ρ) *
      (-logDeriv completedRiemannZeta z)
  have hraw :
      Tendsto raw (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 m) :=
    completedRiemannZeta_logDeriv_completedZero_residue_tendsto_ownerGap ρ
  have hneg :
      Tendsto (fun z : ℂ => - raw z)
        (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 (-m)) :=
    hraw.neg
  have hfun :
      negRaw = fun z : ℂ => - raw z := by
    funext z
    calc
      negRaw z =
          (z - completedZeroResidueCoordinate ρ) *
            (-(logDeriv completedRiemannZeta z)) := by
        rfl
      _ = -((z - completedZeroResidueCoordinate ρ) * logDeriv completedRiemannZeta z) := by
        exact mul_neg (z - completedZeroResidueCoordinate ρ) (logDeriv completedRiemannZeta z)
      _ = - raw z := by
        rfl
  exact
    Eq.subst
      (motive := fun ψ : ℂ → ℂ =>
        Tendsto ψ (𝓝[≠] (completedZeroResidueCoordinate ρ)) (𝓝 (-m)))
      hfun.symm
      hneg

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary

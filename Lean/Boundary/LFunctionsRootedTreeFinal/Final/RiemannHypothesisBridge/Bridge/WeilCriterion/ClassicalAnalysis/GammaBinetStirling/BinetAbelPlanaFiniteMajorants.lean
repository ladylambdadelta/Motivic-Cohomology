import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteAlgebra

/-!
# Finite Abel-Plana majorant owners

This file owns the explicit finite-contour majorants and their zero-limit estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- Explicit finite-contour majorant for the upper Abel-Plana endpoint
residual.

The standard finite-contour proof bounds the upper vertical residual by the
endpoint scale `O(1 / N)`.  The exponential factor belongs to the integration
kernel in the vertical variable, not to the endpoint parameter `N` itself. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperContourResidualMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  8 * (1 + ‖w‖) ^ 2 *
    (1 + |Complex.binetAbelPlanaVerticalKernelMass|) / (N + 1 : ℝ)

/-- Definition unfolding for the finite upper-contour residual majorant. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_unfold
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N =
      8 * (1 + ‖w‖) ^ 2 *
        (1 + |Complex.binetAbelPlanaVerticalKernelMass|) /
          (N + 1 : ℝ) := rfl

/-- Explicit majorant for the lower Abel-Plana tail omitted by truncating the
lower boundary at height `N`.

This is intentionally a tail integral of the already-owned Binet vertical
kernel majorant.  The lower contour tail has exponential decay, but the
owner-level API available here proves decay through integrability of the
kernel, not through the upper-endpoint `O(1 / (N + 1))` scale used for the
finite upper residual. -/
noncomputable def Complex.binetAbelPlanaFiniteLowerContourTailMajorant
    (_w : ℂ)
    (N : ℕ) : ℝ :=
  2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
    Complex.binetAbelPlanaVerticalKernelMajorant t

/-- Definition unfolding for the finite lower-contour tail majorant. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTailMajorant_unfold
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N =
      2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
        Complex.binetAbelPlanaVerticalKernelMajorant t := rfl

/-- Explicit finite-contour majorant for the honest total Abel-Plana
remainder. -/
noncomputable def Complex.binetAbelPlanaFiniteContourRemainderMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N

/-- Definition unfolding for the total finite-contour remainder majorant. -/
theorem Complex.binetAbelPlanaFiniteContourRemainderMajorant_unfold
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteContourRemainderMajorant w N =
      Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := rfl

/-- The upper endpoint-residual majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero
    (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Filter.Tendsto
        (fun _N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
        Filter.atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|))) :=
    tendsto_const_nhds
  have hinv :
      Filter.Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Filter.Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          Filter.atTop
          Filter.atTop := by
      exact
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Filter.Tendsto
        (fun N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
              ((N + 1 : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) * 0)) :=
    hconst.mul hinv
  have hevent :
      (fun N : ℕ =>
        8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
            ((N + 1 : ℝ))⁻¹) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Eq.trans
          (Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_unfold w N)
          (div_eq_mul_inv
            (8 * (1 + ‖w‖) ^ 2 *
              (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
            (N + 1 : ℝ))).symm)
  exact
    (mul_zero (8 * (1 + ‖w‖) ^ 2 *
      (1 + |Complex.binetAbelPlanaVerticalKernelMass|))).symm ▸
      (hmul.congr' hevent)

/-- The lower-tail majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero
    (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have htail :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        Filter.atTop
        (𝓝 (∫ t : ℝ in ⋂ N : ℕ, Set.Ioi (N : ℝ),
          Complex.binetAbelPlanaVerticalKernelMajorant t)) := by
    exact
      tendsto_setIntegral_of_antitone
        (fun _N => measurableSet_Ioi)
        (fun N M hNM => Set.Ioi_subset_Ioi (Nat.cast_le.mpr hNM))
        ⟨0, by
          have hzero : (((0 : ℕ) : ℝ)) = (0 : ℝ) :=
            Nat.cast_zero
          exact hzero.symm ▸
            Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn⟩
  have hInter :
      (⋂ N : ℕ, Set.Ioi (N : ℝ)) = (∅ : Set ℝ) := by
    exact
      Set.ext
        (fun t =>
          Iff.intro
            (fun ht =>
              match exists_nat_gt t with
              | ⟨N, hN⟩ =>
                False.elim
                  ((lt_asymm hN) ((Set.mem_iInter.mp ht) N)))
            (fun ht => False.elim ht))
  have htail_zero :
      Filter.Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        Filter.atTop
        (𝓝 (0 : ℝ)) := by
    have hintegral_zero :
        (∫ t : ℝ in ⋂ N : ℕ, Set.Ioi (N : ℝ),
          Complex.binetAbelPlanaVerticalKernelMajorant t) = 0 := by
      exact hInter ▸
        (setIntegral_empty :
          (∫ t : ℝ in (∅ : Set ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t) = 0)
    exact hintegral_zero ▸ htail
  have hscale :
      Filter.Tendsto
        (fun N : ℕ =>
          2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        Filter.atTop
        (𝓝 ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul htail_zero
  have hevent :
      (fun N : ℕ =>
        2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
          Complex.binetAbelPlanaVerticalKernelMajorant t) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) :=
    Filter.Eventually.of_forall
      (fun _N => rfl)
  exact (mul_zero (2 : ℝ)).symm ▸ (hscale.congr' hevent)

/-- The finite-contour majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteContourRemainderMajorant_tendsto_zero
    (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hlower :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
  have hupper :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        Filter.atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hlower.add hupper
  have hevent :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Complex.binetAbelPlanaFiniteContourRemainderMajorant_unfold w N).symm)
  exact (zero_add (0 : ℝ)).symm ▸ (hsum.congr' hevent)

end

end LFunctions
end Boundary

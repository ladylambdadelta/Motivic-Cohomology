import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.Owner

/-!
# Logarithmic phase canonical prefix curvature transport

This file owns the compact transport from the real-phase curvature block
estimate to the concrete canonical positive-index prefix sum.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-- One-block second-derivative van der Corput estimate for the logarithmic
phase on a sub-block of the canonical prefix. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhase_canonicalPrefix_curvatureSubblock_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (_hb : b ≤ ⌊2 + ‖t‖⌋₊)
    (hab : a ≤ b) :
  ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhase_curvature_integer_block_bound
      t ht ha hab

/-- Transport the single canonical prefix block to the positive-index
logarithmic phase partial sum. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhase_canonicalPrefix_curvatureBlock_transport
    (t : ℝ)
    {C : ℕ}
    (hblock_C :
      ‖∑ n ∈ Finset.Icc 1 C,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        80 * ((((C + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t C‖ ≤
      80 * ((((C + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hphase :
      Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t C =
        ∑ n ∈ Finset.Icc 1 C,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
      (t := t)
      (N := C)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          80 * ((((C + 1 : ℕ) : ℝ) / ‖t‖ +
            Real.sqrt (1 + ‖t‖))))
      hphase.symm
      hblock_C

/-- Resonance-safe second-derivative block estimate for the logarithmic phase
on the canonical prefix window. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_canonicalPrefix_curvatureBlock_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
        t ⌊2 + ‖t‖⌋₊‖ ≤
      80 * ((((⌊2 + ‖t‖⌋₊ + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  let C : ℕ := ⌊2 + ‖t‖⌋₊
  have hC_pos : 0 < C := by
    have hone_le_two : (1 : ℝ) ≤ 2 :=
      one_le_two
    have htwo_le_arg : (2 : ℝ) ≤ 2 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact Nat.floor_pos.mpr (le_trans hone_le_two htwo_le_arg)
  have hone_le_C : 1 ≤ C :=
    Nat.succ_le_of_lt hC_pos
  have hblock_C :
      ‖∑ n ∈ Finset.Icc 1 C,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        80 * ((((C + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhase_canonicalPrefix_curvatureSubblock_norm_le
      (t := t)
      (ht := ht)
      (a := 1)
      (b := C)
      (ha := Nat.le_refl 1)
      (_hb := Nat.le_refl C)
      (hab := hone_le_C)
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhase_canonicalPrefix_curvatureBlock_transport
      (t := t)
      (C := C)
      (hblock_C := hblock_C)

end

end LFunctions
end Boundary

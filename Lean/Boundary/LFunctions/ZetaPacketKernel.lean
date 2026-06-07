import Boundary.LFunctions.ZetaPacketTransform

/-!
# Boundary zeta packet kernel

This file builds the finite-support packet ensemble and the basic dot-product
kernel on it. The purpose is to have a concrete owner-level kernel precursor
for the later Gram architecture.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite packet ensemble: a finitely supported real combination of packet labels. -/
abbrev ZetaPacketEnsemble := ZetaPacketLabel →₀ ℝ

namespace ZetaPacketEnsemble

/-- The coefficient-wise dot product of two finite packet ensembles. -/
def dotProduct (x y : ZetaPacketEnsemble) : ℝ :=
  ∑ ℓ in x.support ∪ y.support, x ℓ * y ℓ

/-- The squared norm associated to the packet dot product. -/
def normSq (x : ZetaPacketEnsemble) : ℝ :=
  dotProduct x x

theorem dotProduct_comm (x y : ZetaPacketEnsemble) :
    dotProduct x y = dotProduct y x := by
  unfold dotProduct
  rw [Finset.union_comm]
  congr with ℓ
  exact mul_comm _ _

/-- If two packet ensembles have disjoint supports, then their dot product vanishes. -/
theorem dotProduct_eq_zero_of_disjoint_support {x y : ZetaPacketEnsemble}
    (hxy : Disjoint x.support y.support) : dotProduct x y = 0 := by
  have hxy' : ∀ ℓ, ℓ ∈ x.support → ℓ ∈ y.support → False := by
    rw [Finset.disjoint_left] at hxy
    exact hxy
  unfold dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  have hmem : ℓ ∈ x.support ∨ ℓ ∈ y.support := Finset.mem_union.mp hℓ
  rcases hmem with hx | hy
  · have hy' : ℓ ∉ y.support := by
      intro hy
      exact hxy' ℓ hx hy
    have hx0 : x ℓ ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hx
    have hy0 : y ℓ = 0 := by
      by_contra hy0
      have hy_mem : ℓ ∈ y.support := by
        simpa [Finsupp.mem_support_iff] using hy0
      exact hy' hy_mem
    rw [hy0]
    ring
  · have hx' : ℓ ∉ x.support := by
      intro hx
      exact hxy' ℓ hx hy
    have hx0 : x ℓ = 0 := by
      by_contra hx0
      have hx_mem : ℓ ∈ x.support := by
        simpa [Finsupp.mem_support_iff] using hx0
      exact hx' hx_mem
    have hy0 : y ℓ ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hy
    rw [hx0]
    ring

theorem normSq_nonneg (x : ZetaPacketEnsemble) : 0 ≤ normSq x := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg (fun ℓ _ => mul_self_nonneg (x ℓ))

end ZetaPacketEnsemble

/-- If two packet ensembles have disjoint supports, then their dot product vanishes. -/
theorem packetDotProduct_eq_zero_of_disjoint_support {x y : ZetaPacketEnsemble}
    (hxy : Disjoint x.support y.support) : ZetaPacketEnsemble.dotProduct x y = 0 := by
  have hxy' : ∀ ℓ, ℓ ∈ x.support → ℓ ∈ y.support → False := by
    rw [Finset.disjoint_left] at hxy
    exact hxy
  unfold ZetaPacketEnsemble.dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  have hmem : ℓ ∈ x.support ∨ ℓ ∈ y.support := Finset.mem_union.mp hℓ
  rcases hmem with hx | hy
  · have hy' : ℓ ∉ y.support := by
      intro hy
      exact hxy' ℓ hx hy
    have hy0 : y ℓ = 0 := by
      by_contra hy0
      have hy_mem : ℓ ∈ y.support := by
        simpa [Finsupp.mem_support_iff] using hy0
      exact hy' hy_mem
    rw [hy0]
    ring
  · have hx' : ℓ ∉ x.support := by
      intro hx
      exact hxy' ℓ hx hy
    have hx0 : x ℓ = 0 := by
      by_contra hx0
      have hx_mem : ℓ ∈ x.support := by
        simpa [Finsupp.mem_support_iff] using hx0
      exact hx' hx_mem
    rw [hx0]
    ring

/-- The canonical bilinear packet kernel: the dot product on finite ensembles. -/
def zetaPacketKernel (x y : ZetaPacketEnsemble) : ℝ :=
  ZetaPacketEnsemble.dotProduct x y

theorem zetaPacketKernel_comm (x y : ZetaPacketEnsemble) :
    zetaPacketKernel x y = zetaPacketKernel y x := by
  exact ZetaPacketEnsemble.dotProduct_comm x y

theorem zetaPacketKernel_nonneg (x : ZetaPacketEnsemble) :
    0 ≤ zetaPacketKernel x x := by
  exact ZetaPacketEnsemble.normSq_nonneg x

end
end LFunctions
end Boundary

import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaPacketComparison.ZetaCompletedBoundaryDefect.ZetaPacketReconstruction.ZetaPacketDecomposition.ZetaPacketKernel.ZetaPacketTransform.ZetaPacketTransform

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

/-- Helper: a disjoint-support summand vanishes at a label. -/
theorem dotProduct_eq_zero_of_disjoint_support_aux {x y : ZetaPacketEnsemble} (ℓ : ZetaPacketLabel)
    (hxy : Disjoint x.support y.support) :
    ℓ ∈ x.support ∪ y.support → x ℓ * y ℓ = 0 := by
  intro hℓ
  have hxy' : ∀ ℓ, ℓ ∈ x.support → ℓ ∈ y.support → False := by
    exact Finset.disjoint_left.mp hxy
  have hmem : ℓ ∈ x.support ∨ ℓ ∈ y.support := Finset.mem_union.mp hℓ
  rcases hmem with hx | hy
  · have hy' : ℓ ∉ y.support := by
      intro hy
      exact hxy' ℓ hx hy
    have hy0 : y ℓ = 0 := by
      by_contra hy0
      have hy_mem : ℓ ∈ y.support := by
        exact Finsupp.mem_support_iff.mpr hy0
      exact hy' hy_mem
    calc
      x ℓ * y ℓ = x ℓ * 0 := by
        exact congrArg (fun t => x ℓ * t) hy0
      _ = 0 := by
        exact mul_zero _
  · have hx' : ℓ ∉ x.support := by
      intro hx
      exact hxy' ℓ hx hy
    have hx0 : x ℓ = 0 := by
      by_contra hx0
      have hx_mem : ℓ ∈ x.support := by
        exact Finsupp.mem_support_iff.mpr hx0
      exact hx' hx_mem
    calc
      x ℓ * y ℓ = 0 * y ℓ := by
        exact congrArg (fun t => t * y ℓ) hx0
      _ = 0 := by
        exact zero_mul _

/-- If two packet ensembles have disjoint supports, then their dot product vanishes. -/
theorem dotProduct_eq_zero_of_disjoint_support {x y : ZetaPacketEnsemble}
    (hxy : Disjoint x.support y.support) : dotProduct x y = 0 := by
  unfold dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ hℓ
  exact dotProduct_eq_zero_of_disjoint_support_aux (x := x) (y := y) ℓ hxy hℓ

theorem normSq_nonneg (x : ZetaPacketEnsemble) : 0 ≤ normSq x := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg (fun ℓ _ => mul_self_nonneg (x ℓ))

/-- If a finite packet has zero norm square, every coordinate of the packet vanishes. -/
theorem apply_eq_zero_of_normSq_eq_zero
    (x : ZetaPacketEnsemble)
    (hx : normSq x = 0)
    (ℓ : ZetaPacketLabel) :
    x ℓ = 0 := by
  by_cases hℓ : ℓ ∈ x.support
  · have hsum :
        ∑ a in x.support, x a * x a = 0 := by
      unfold normSq dotProduct at hx
      exact Eq.subst
        (motive := fun s : Finset ZetaPacketLabel =>
          ∑ a in s, x a * x a = 0)
        (Finset.union_self x.support)
        hx
    have hterm :
        x ℓ * x ℓ = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun a _ha => mul_self_nonneg (x a))).mp hsum ℓ hℓ
    exact mul_self_eq_zero.mp hterm
  · exact Finsupp.not_mem_support_iff.mp hℓ

/-- A zero-norm packet lies in the left radical of the packet dot product. -/
theorem dotProduct_left_eq_zero_of_normSq_eq_zero
    {x y : ZetaPacketEnsemble}
    (hx : normSq x = 0) :
    dotProduct x y = 0 := by
  unfold dotProduct
  refine Finset.sum_eq_zero ?_
  intro ℓ _hℓ
  have hxℓ : x ℓ = 0 :=
    apply_eq_zero_of_normSq_eq_zero x hx ℓ
  calc
    x ℓ * y ℓ = 0 * y ℓ := by
      exact congrArg (fun a : ℝ => a * y ℓ) hxℓ
    _ = 0 := by
      exact zero_mul (y ℓ)

/-- A zero-norm packet lies in the right radical of the packet dot product. -/
theorem dotProduct_right_eq_zero_of_normSq_eq_zero
    {x y : ZetaPacketEnsemble}
    (hy : normSq y = 0) :
    dotProduct x y = 0 := by
  calc
    dotProduct x y = dotProduct y x := by
      exact dotProduct_comm x y
    _ = 0 := by
      exact dotProduct_left_eq_zero_of_normSq_eq_zero hy

end ZetaPacketEnsemble

/-- If two packet ensembles have disjoint supports, then their dot product vanishes. -/
theorem packetDotProduct_eq_zero_of_disjoint_support {x y : ZetaPacketEnsemble}
    (hxy : Disjoint x.support y.support) : ZetaPacketEnsemble.dotProduct x y = 0 := by
  have hxy' : ∀ ℓ, ℓ ∈ x.support → ℓ ∈ y.support → False := by
    exact Finset.disjoint_left.mp hxy
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
        exact Finsupp.mem_support_iff.mpr hy0
      exact hy' hy_mem
    calc
      x ℓ * y ℓ = x ℓ * 0 := by
        exact congrArg (fun t => x ℓ * t) hy0
      _ = 0 := by
        exact mul_zero _
  · have hx' : ℓ ∉ x.support := by
      intro hx
      exact hxy' ℓ hx hy
    have hx0 : x ℓ = 0 := by
      by_contra hx0
      have hx_mem : ℓ ∈ x.support := by
        exact Finsupp.mem_support_iff.mpr hx0
      exact hx' hx_mem
    calc
      x ℓ * y ℓ = 0 * y ℓ := by
        exact congrArg (fun t => t * y ℓ) hx0
      _ = 0 := by
        exact zero_mul _

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

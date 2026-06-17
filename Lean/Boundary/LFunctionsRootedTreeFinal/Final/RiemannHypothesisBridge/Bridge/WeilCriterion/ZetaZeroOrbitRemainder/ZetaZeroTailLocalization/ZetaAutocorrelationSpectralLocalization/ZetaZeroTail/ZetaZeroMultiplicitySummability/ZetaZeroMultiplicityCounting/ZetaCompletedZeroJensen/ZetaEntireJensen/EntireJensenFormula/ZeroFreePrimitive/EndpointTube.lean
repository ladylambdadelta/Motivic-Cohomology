import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.BoundaryZeroFactors.Owner

/-!
# Endpoint tube stability for center segments

This file owns the topology-only tube lemmas used by the zero-free primitive
construction. It is split out of `ZeroFreePrimitive.Owner` so the analytic
owner file does not repeatedly elaborate the generalized tube proof.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Continuity of the two-parameter center-segment map
`(x,t) ↦ lineMap 0 x t`. -/
theorem complex_centerSegment_endpointParameter_continuous :
    Continuous
      (fun p : ℂ × ℝ =>
        AffineMap.lineMap (0 : ℂ) p.1 p.2) := by
  have hmul :
      Continuous
        (fun p : ℂ × ℝ => (p.2 : ℂ) * p.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul continuous_fst
  have hfun :
      (fun p : ℂ × ℝ =>
        AffineMap.lineMap (0 : ℂ) p.1 p.2) =
        fun p : ℂ × ℝ => (p.2 : ℂ) * p.1 :=
    funext
      (fun p : ℂ × ℝ =>
        calc
          AffineMap.lineMap (0 : ℂ) p.1 p.2 =
              p.2 • (p.1 - 0) + 0 :=
            AffineMap.lineMap_apply_module' (0 : ℂ) p.1 p.2
          _ = (p.2 : ℂ) * (p.1 - 0) + 0 :=
            rfl
          _ = (p.2 : ℂ) * p.1 + 0 :=
            congrArg (fun a : ℂ => (p.2 : ℂ) * a + 0) (sub_zero p.1)
          _ = (p.2 : ℂ) * p.1 :=
            add_zero ((p.2 : ℂ) * p.1))
  exact
    Eq.subst
      (motive := fun f : ℂ × ℝ → ℂ => Continuous f)
      hfun.symm
      hmul

/-- The base segment containment as a product containment for the
two-parameter center-segment map. -/
theorem complex_centerSegment_openTube_productSubset
    (z : ℂ)
    (U : Set ℂ)
    (hseg :
      ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
          Set.Icc (0 : ℝ) 1) ⊆ U) :
    ({z} : Set ℂ) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
      {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} := by
  intro p hp
  have hp_left : p.1 = z :=
    Set.mem_singleton_iff.1 hp.1
  have hline :
      AffineMap.lineMap (k := ℝ) (0 : ℂ) z p.2 =
        AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 :=
    congrArg
      (fun q : ℂ => AffineMap.lineMap (k := ℝ) (0 : ℂ) q p.2)
      hp_left.symm
  exact
    hseg
      ⟨p.2, hp.2,
        hline⟩

/-- The generalized tube lemma specialized to the two-parameter center-segment
map. -/
theorem complex_centerSegment_openTube_tubeWitness
    (z : ℂ)
    (U : Set ℂ)
    (hU_open : IsOpen U)
    (hseg :
      ((fun t : ℝ => AffineMap.lineMap (k := ℝ) (0 : ℂ) z t) ''
          Set.Icc (0 : ℝ) 1) ⊆ U) :
    ∃ u : Set ℂ,
      ∃ v : Set ℝ,
        IsOpen u ∧
        IsOpen v ∧
        ({z} : Set ℂ) ⊆ u ∧
        Set.Icc (0 : ℝ) 1 ⊆ v ∧
        u ×ˢ v ⊆
          {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} := by
  have hn :
      IsOpen {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    IsOpen.preimage complex_centerSegment_endpointParameter_continuous hU_open
  have hprod :
      ({z} : Set ℂ) ×ˢ Set.Icc (0 : ℝ) 1 ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    complex_centerSegment_openTube_productSubset z U hseg
  exact
    generalized_tube_lemma
      (isCompact_singleton (x := z))
      isCompact_Icc
      hn
      hprod

/-- A product-tube containment transports one endpoint and one interval
parameter to membership in the open tube. -/
theorem complex_centerSegment_openTube_lineMem_of_tube
    (U : Set ℂ)
    (u : Set ℂ)
    (v : Set ℝ)
    (hv_subset : Set.Icc (0 : ℝ) 1 ⊆ v)
    (huv :
      u ×ˢ v ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U})
    (x : ℂ)
    (hx : x ∈ u)
    (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap (k := ℝ) (0 : ℂ) x t ∈ U := by
  have hp : (x, t) ∈ u ×ˢ v :=
    And.intro hx (hv_subset ht)
  have hpair :
      (x, t) ∈
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    huv hp
  exact hpair

/-- An open endpoint neighborhood gives a positive endpoint ball whose center
segments remain in the product tube. -/
theorem complex_centerSegment_openTube_ballWitness
    (U : Set ℂ)
    (u : Set ℂ)
    (v : Set ℝ)
    (hu_open : IsOpen u)
    (hv_subset : Set.Icc (0 : ℝ) 1 ⊆ v)
    (huv :
      u ×ˢ v ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U})
    (w : ℂ)
    (hw : w ∈ u) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∀ x : ℂ,
        x ∈ Metric.ball w ε →
          ∀ t : ℝ,
            t ∈ Set.Icc (0 : ℝ) 1 →
              AffineMap.lineMap (k := ℝ) (0 : ℂ) x t ∈ U := by
  let ε : ℝ := Classical.choose (Metric.isOpen_iff.1 hu_open w hw)
  have hε_data :
      0 < ε ∧ Metric.ball w ε ⊆ u :=
    Classical.choose_spec (Metric.isOpen_iff.1 hu_open w hw)
  have hε_pos : 0 < ε :=
    hε_data.1
  have hε_subset : Metric.ball w ε ⊆ u :=
    hε_data.2
  exact
    Exists.intro ε
      (And.intro hε_pos
        (fun x hx t ht =>
          complex_centerSegment_openTube_lineMem_of_tube
            U u v hv_subset huv x (hε_subset hx) t ht))

/-- A tube witness gives uniform endpoint-ball stability for all points in the
endpoint neighborhood. -/
theorem complex_centerSegment_openTube_stabilityFromTube
    (z : ℂ)
    (U : Set ℂ)
    (u : Set ℂ)
    (v : Set ℝ)
    (hu_open : IsOpen u)
    (hz_subset : ({z} : Set ℂ) ⊆ u)
    (hv_subset : Set.Icc (0 : ℝ) 1 ⊆ v)
    (huv :
      u ×ˢ v ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U}) :
    z ∈ u ∧
      u ∈ 𝓝 z ∧
      ∀ w : ℂ,
        w ∈ u →
          ∃ ε : ℝ,
            0 < ε ∧
            ∀ x : ℂ,
              x ∈ Metric.ball w ε →
                ∀ t : ℝ,
                  t ∈ Set.Icc (0 : ℝ) 1 →
                    AffineMap.lineMap (k := ℝ) (0 : ℂ) x t ∈ U := by
  have hz_mem : z ∈ u :=
    Set.singleton_subset_iff.1 hz_subset
  have hu_nhds : u ∈ 𝓝 z :=
    hu_open.mem_nhds hz_mem
  have hstable :
      ∀ w : ℂ,
        w ∈ u →
          ∃ ε : ℝ,
            0 < ε ∧
            ∀ x : ℂ,
              x ∈ Metric.ball w ε →
                ∀ t : ℝ,
                  t ∈ Set.Icc (0 : ℝ) 1 →
                    AffineMap.lineMap (k := ℝ) (0 : ℂ) x t ∈ U :=
    fun w hw =>
      complex_centerSegment_openTube_ballWitness
        U u v hu_open hv_subset huv w hw
  exact And.intro hz_mem (And.intro hu_nhds hstable)

/-- Endpoint stability for center segments into an arbitrary open tube around
the compact base segment.

This is the pure topology lemma behind the finite analytic tube construction:
if an open set `U` contains the compact segment from `0` to `z`, then endpoints
near `z` have a small ball of nearby endpoints whose whole center segments
remain in `U`. -/
theorem complex_centerSegment_endpointStability_openTube
    (z : ℂ)
    (U : Set ℂ)
    (hU_open : IsOpen U)
    (hseg :
      ((fun t : ℝ => AffineMap.lineMap (k := ℝ) (0 : ℂ) z t) ''
          Set.Icc (0 : ℝ) 1) ⊆ U) :
    ∃ u : Set ℂ,
      z ∈ u ∧
      u ∈ 𝓝 z ∧
      ∀ w : ℂ,
        w ∈ u →
          ∃ ε : ℝ,
            0 < ε ∧
            ∀ x : ℂ,
              x ∈ Metric.ball w ε →
                ∀ t : ℝ,
                  t ∈ Set.Icc (0 : ℝ) 1 →
                    AffineMap.lineMap (k := ℝ) (0 : ℂ) x t ∈ U := by
  have htube :
      ∃ u : Set ℂ,
        ∃ v : Set ℝ,
          IsOpen u ∧
          IsOpen v ∧
          ({z} : Set ℂ) ⊆ u ∧
          Set.Icc (0 : ℝ) 1 ⊆ v ∧
          u ×ˢ v ⊆
            {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    complex_centerSegment_openTube_tubeWitness z U hU_open hseg
  let u : Set ℂ := Classical.choose htube
  have hu_exists :
      ∃ v : Set ℝ,
        IsOpen u ∧
        IsOpen v ∧
        ({z} : Set ℂ) ⊆ u ∧
        Set.Icc (0 : ℝ) 1 ⊆ v ∧
        u ×ˢ v ⊆
          {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    Classical.choose_spec htube
  let v : Set ℝ := Classical.choose hu_exists
  have huv_data :
      IsOpen u ∧
      IsOpen v ∧
      ({z} : Set ℂ) ⊆ u ∧
      Set.Icc (0 : ℝ) 1 ⊆ v ∧
      u ×ˢ v ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    Classical.choose_spec hu_exists
  have hu_open : IsOpen u :=
    huv_data.1
  have hz_subset : ({z} : Set ℂ) ⊆ u :=
    huv_data.2.2.1
  have hv_subset : Set.Icc (0 : ℝ) 1 ⊆ v :=
    huv_data.2.2.2.1
  have huv :
      u ×ˢ v ⊆
        {p : ℂ × ℝ | AffineMap.lineMap (k := ℝ) (0 : ℂ) p.1 p.2 ∈ U} :=
    huv_data.2.2.2.2
  exact
    Exists.intro u
      (complex_centerSegment_openTube_stabilityFromTube
        z U u v hu_open hz_subset hv_subset huv)

/-- Endpoint stability for center segments into a finite analytic tube.

If a finite union of analytic-at neighborhoods covers the compact center
segment from `0` to `z`, then after shrinking the endpoint, all center
segments from `0` to endpoints in a small ball remain inside that finite
tube.  This is the Lebesgue-number/tube step for the affine segment family. -/
theorem complex_centerSegment_endpointStability_finiteAnalyticTube
    (φ : ℂ → ℂ)
    (z : ℂ)
    (centers : Finset ℂ)
    (hcover :
      ((fun t : ℝ => AffineMap.lineMap (0 : ℂ) z t) ''
          Set.Icc (0 : ℝ) 1) ⊆
        ⋃ c ∈ centers, {w : ℂ | AnalyticAt ℂ φ w}) :
    ∃ u : Set ℂ,
      z ∈ u ∧
      u ∈ 𝓝 z ∧
      ∀ w : ℂ,
        w ∈ u →
          ∃ ε : ℝ,
            0 < ε ∧
            ∀ x : ℂ,
              x ∈ Metric.ball w ε →
                ∀ t : ℝ,
                  t ∈ Set.Icc (0 : ℝ) 1 →
                    AffineMap.lineMap (0 : ℂ) x t ∈
                      ⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q} := by
  exact
    complex_centerSegment_endpointStability_openTube
      z
      (⋃ c ∈ centers, {q : ℂ | AnalyticAt ℂ φ q})
      (isOpen_iUnion fun c =>
        isOpen_iUnion fun _hc =>
          isOpen_analyticAt ℂ φ)
      hcover

end

end LFunctions
end Boundary
